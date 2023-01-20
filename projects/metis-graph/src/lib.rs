//! Metis relation semantics on [`athena_graph`].
//!
//! - Bottom layer: ordinary discrete adjacency via [`GraphBuilder`] with [`NodePayload`] /
//!   [`EdgePayload`] (not CAS M-Graph). Indexed scans use athena `out_edges` / `in_edges`.
//! - Metis layer: hash-cons, label atoms, structural vs judgment edges, EQ paths.
//! - Staging keeps an unfinished builder. Seal with [`Graph::seal`] / [`Graph::seal_on_heap`].
//! - Core contract stubs: [`admission`], [`connection`], [`derivation`], [`evidence`], [`transform`], [`conflict`], [`rules`], [`eval`].

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
    rc::Rc,
};

use athena_gc::{GcHeap, HeapBudget};
use athena_graph::{
    GraphBuilder, GraphDirection, GraphSemantics, ImmutableGraph, MultiplicityPolicy, PublishedImmutableGraph, SelfLoopDegree,
};
use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

pub mod admission;
pub mod closure;
pub mod conflict;
pub mod connection;
pub mod derivation;
pub mod derivation_rules;
pub mod eval;
pub mod evidence;
pub mod evidence_dag;
pub mod inner;
pub mod payload;
pub mod relation;
pub mod rules;
pub mod transform;

pub use payload::{EdgePayload, NodePayload};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum EdgeKindKey {
    Equal,
    In,
    Eval,
    Custom(u16),
}

impl From<EdgeKind> for EdgeKindKey {
    fn from(value: EdgeKind) -> Self {
        match value {
            EdgeKind::Equal => Self::Equal,
            EdgeKind::In => Self::In,
            EdgeKind::Eval => Self::Eval,
            EdgeKind::Custom(v) => Self::Custom(v),
        }
    }
}

impl From<EdgeKindKey> for EdgeKind {
    fn from(value: EdgeKindKey) -> Self {
        match value {
            EdgeKindKey::Equal => Self::Equal,
            EdgeKindKey::In => Self::In,
            EdgeKindKey::Eval => Self::Eval,
            EdgeKindKey::Custom(v) => Self::Custom(v),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct OutKey {
    kind: EdgeKindKey,
    to: u64,
}

/// Directed step along a judgment edge, possibly reversed (for symmetric kinds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Step {
    pub edge: EdgeId,
    pub forward: bool,
}

fn metis_semantics() -> GraphSemantics {
    GraphSemantics {
        direction: GraphDirection::Directed,
        multiplicity: MultiplicityPolicy::Multi,
        allows_self_loops: true,
        self_loop_degree: SelfLoopDegree::One,
    }
}

/// Mutable working graph (staging or accepted island body before snapshot freeze).
pub struct Graph {
    builder: GraphBuilder<NodePayload, EdgePayload>,
    cons: HashMap<Vec<OutKey>, NodeId>,
    labels: HashMap<Vec<u8>, NodeId>,
    label_of: HashMap<NodeId, Vec<u8>>,
    heap: Rc<RefCell<GcHeap>>,
    /// When true, mutating APIs reject. Query / replay stay available (Living `10` snapshot).
    snapshot_frozen: bool,
}

impl Default for Graph {
    fn default() -> Self {
        Self::new()
    }
}

impl Graph {
    pub fn new() -> Self {
        Self::with_heap(GcHeap::new(HeapBudget::default()))
    }

    pub fn with_heap(heap: Rc<RefCell<GcHeap>>) -> Self {
        Self {
            builder: GraphBuilder::new(metis_semantics()),
            cons: HashMap::new(),
            labels: HashMap::new(),
            label_of: HashMap::new(),
            heap,
            snapshot_frozen: false,
        }
    }

    pub fn heap(&self) -> &Rc<RefCell<GcHeap>> {
        &self.heap
    }

    /// Freeze mutations while keeping Metis cons / judgment tables queryable.
    ///
    /// Distinct from [`Self::seal`], which drops Metis tables into an ordinary immutable graph.
    pub fn freeze_snapshot(&mut self) {
        self.snapshot_frozen = true;
    }

    pub const fn is_snapshot_frozen(&self) -> bool {
        self.snapshot_frozen
    }

    fn ensure_mutable(&self) -> Result<(), MetisError> {
        if self.snapshot_frozen {
            return Err(MetisError::GraphRejected);
        }
        Ok(())
    }

    /// Underlying athena builder (ordinary discrete graph).
    pub fn base(&self) -> &GraphBuilder<NodePayload, EdgePayload> {
        &self.builder
    }

    /// Seal into an immutable ordinary graph (drops Metis cons tables).
    pub fn seal(self) -> ImmutableGraph<NodePayload, EdgePayload> {
        self.builder.finish()
    }

    /// Seal and publish snapshot roots on the shared [`GcHeap`].
    pub fn seal_on_heap(self) -> Result<PublishedImmutableGraph<NodePayload, EdgePayload>, MetisError> {
        let mut heap = self.heap.borrow_mut();
        self.builder.finish_on_heap(&mut heap).map_err(|_| MetisError::GraphRejected)
    }

    pub fn label_of(&self, id: NodeId) -> Result<Option<&[u8]>, MetisError> {
        self.ensure_known(id)?;
        Ok(self.label_of.get(&id).map(|v| v.as_slice()))
    }

    fn fingerprint(outs: &[(EdgeKind, NodeId)]) -> Vec<OutKey> {
        let mut keys: Vec<OutKey> = outs.iter().map(|(kind, to)| OutKey { kind: EdgeKindKey::from(*kind), to: to.0 }).collect();
        keys.sort();
        keys
    }

    fn ensure_known(&self, id: NodeId) -> Result<(), MetisError> {
        if id.0 >= self.builder.graph().node_count() {
            return Err(MetisError::NodeNotFound);
        }
        Ok(())
    }

    fn add_base_edge(&mut self, from: NodeId, to: NodeId, payload: EdgePayload) -> Result<EdgeId, MetisError> {
        self.builder.add_edge(from, to, payload).ok_or(MetisError::GraphRejected)
    }

    /// Intern a named atom. Same bytes → same [`NodeId`].
    pub fn intern_label(&mut self, name: impl AsRef<[u8]>) -> Result<NodeId, MetisError> {
        self.ensure_mutable()?;
        let key = name.as_ref().to_vec();
        if let Some(id) = self.labels.get(&key).copied() {
            return Ok(id);
        }
        let id = self.builder.add_node(NodePayload::labeled(&key));
        self.labels.insert(key.clone(), id);
        self.label_of.insert(id, key);
        Ok(id)
    }

    /// Intern a node by its **structural** outgoing multiset (extensional hash-cons).
    pub fn intern(&mut self, outs: &[(EdgeKind, NodeId)]) -> Result<NodeId, MetisError> {
        self.ensure_mutable()?;
        for (_kind, to) in outs {
            self.ensure_known(*to)?;
        }
        let key = Self::fingerprint(outs);
        if let Some(id) = self.cons.get(&key).copied() {
            return Ok(id);
        }

        let id = self.builder.add_node(NodePayload::unlabeled());
        for (kind, to) in outs {
            self.add_base_edge(id, *to, EdgePayload::structural(*kind))?;
        }
        self.cons.insert(key, id);
        Ok(id)
    }

    /// Intern the unique empty structural node.
    pub fn intern_empty(&mut self) -> Result<NodeId, MetisError> {
        self.intern(&[])
    }

    /// Assert a judgment edge. Does not change structural identity of `from`.
    pub fn assert(&mut self, from: NodeId, kind: EdgeKind, to: NodeId) -> Result<EdgeId, MetisError> {
        self.ensure_mutable()?;
        self.ensure_known(from)?;
        self.ensure_known(to)?;
        self.add_base_edge(from, to, EdgePayload::judgment(kind))
    }

    fn outgoing_filtered(&self, id: NodeId, structural: Option<bool>) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        self.ensure_known(id)?;
        let mut out = Vec::new();
        for (edge, neighbor, payload) in self.builder.graph().out_edges(id) {
            if let Some(want) = structural {
                if payload.structural != want {
                    continue;
                }
            }
            out.push((edge, payload.kind, neighbor));
        }
        Ok(out)
    }

    fn incoming_filtered(&self, id: NodeId, structural: Option<bool>) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        self.ensure_known(id)?;
        let mut out = Vec::new();
        for (edge, neighbor, payload) in self.builder.graph().in_edges(id) {
            if let Some(want) = structural {
                if payload.structural != want {
                    continue;
                }
            }
            out.push((edge, payload.kind, neighbor));
        }
        Ok(out)
    }

    /// Structural outgoing edges only.
    pub fn structural_outgoing(&self, id: NodeId) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        self.outgoing_filtered(id, Some(true))
    }

    /// Judgment outgoing edges only.
    pub fn judgment_outgoing(&self, id: NodeId) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        self.outgoing_filtered(id, Some(false))
    }

    /// Judgment incoming edges only (`(edge, kind, predecessor)`).
    pub fn judgment_incoming(&self, id: NodeId) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        self.incoming_filtered(id, Some(false))
    }

    /// Outgoing judgment edges of a specific kind (athena adjacency + payload filter).
    pub fn judgment_outgoing_of_kind(&self, id: NodeId, kind: EdgeKind) -> Result<Vec<(EdgeId, NodeId)>, MetisError> {
        self.ensure_known(id)?;
        let mut out = Vec::new();
        for (edge, neighbor, payload) in self.builder.graph().out_edges(id) {
            if !payload.structural && payload.kind == kind {
                out.push((edge, neighbor));
            }
        }
        Ok(out)
    }

    /// Incoming judgment edges of a specific kind (athena adjacency + payload filter).
    pub fn judgment_incoming_of_kind(&self, id: NodeId, kind: EdgeKind) -> Result<Vec<(EdgeId, NodeId)>, MetisError> {
        self.ensure_known(id)?;
        let mut out = Vec::new();
        for (edge, neighbor, payload) in self.builder.graph().in_edges(id) {
            if !payload.structural && payload.kind == kind {
                out.push((edge, neighbor));
            }
        }
        Ok(out)
    }

    /// All outgoing edges (structural then judgment).
    pub fn outgoing(&self, id: NodeId) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        let mut all = self.structural_outgoing(id)?;
        all.extend(self.judgment_outgoing(id)?);
        Ok(all)
    }

    pub fn edge(&self, id: EdgeId) -> Result<(NodeId, EdgeKind, NodeId), MetisError> {
        let base = self.builder.graph();
        let (from, to) = base.edge_endpoints(id).ok_or(MetisError::EdgeNotFound)?;
        let payload = base.edge_value(id).ok_or(MetisError::EdgeNotFound)?;
        Ok((from, payload.kind, to))
    }

    pub fn is_judgment(&self, id: EdgeId) -> Result<bool, MetisError> {
        let payload = self.builder.graph().edge_value(id).ok_or(MetisError::EdgeNotFound)?;
        Ok(!payload.structural)
    }

    /// All judgment edges as `(edge, from, kind, to)` — generators for `Φ_W`.
    pub fn judgment_edges(&self) -> Vec<(EdgeId, NodeId, EdgeKind, NodeId)> {
        let base = self.builder.graph();
        let mut out = Vec::new();
        for (from, to, edge) in base.edges() {
            let Some(payload) = base.edge_value(edge)
            else {
                continue;
            };
            if payload.structural {
                continue;
            }
            out.push((edge, from, payload.kind, to));
        }
        out
    }

    /// Payload stored on the ordinary athena edge.
    pub fn edge_payload(&self, id: EdgeId) -> Result<EdgePayload, MetisError> {
        self.builder.graph().edge_value(id).copied().ok_or(MetisError::EdgeNotFound)
    }

    pub fn node_count(&self) -> usize {
        self.builder.graph().node_count() as usize
    }

    pub fn edge_count(&self) -> usize {
        self.builder.graph().edge_count() as usize
    }

    /// Directed reachability over all outgoing edges.
    pub fn reaches(&self, from: NodeId, to: NodeId) -> Result<bool, MetisError> {
        Ok(self.find_directed_path(from, to)?.is_some())
    }

    pub fn find_directed_path(&self, from: NodeId, to: NodeId) -> Result<Option<Vec<EdgeId>>, MetisError> {
        self.ensure_known(from)?;
        self.ensure_known(to)?;
        if from == to {
            return Ok(Some(Vec::new()));
        }
        let mut q = VecDeque::from([from]);
        let mut prev: HashMap<NodeId, (NodeId, EdgeId)> = HashMap::new();
        let mut seen = HashSet::from([from]);
        while let Some(cur) = q.pop_front() {
            for (eid, _k, nxt) in self.outgoing(cur)? {
                if !seen.insert(nxt) {
                    continue;
                }
                prev.insert(nxt, (cur, eid));
                if nxt == to {
                    let mut path = Vec::new();
                    let mut walk = to;
                    while walk != from {
                        let (p, e) = prev[&walk];
                        path.push(e);
                        walk = p;
                    }
                    path.reverse();
                    return Ok(Some(path));
                }
                q.push_back(nxt);
            }
        }
        Ok(None)
    }

    /// Undirected adjacency via judgment `Equal` edges (for EQ theory).
    pub fn equal_steps(&self, id: NodeId) -> Result<Vec<(Step, NodeId)>, MetisError> {
        self.ensure_known(id)?;
        let mut out = Vec::new();
        for (eid, nxt) in self.judgment_outgoing_of_kind(id, EdgeKind::Equal)? {
            out.push((Step { edge: eid, forward: true }, nxt));
        }
        for (eid, pred) in self.judgment_incoming_of_kind(id, EdgeKind::Equal)? {
            out.push((Step { edge: eid, forward: false }, pred));
        }
        Ok(out)
    }

    /// Search an undirected `Equal` path (symmetry + transitivity of edge composition).
    pub fn find_equal_path(&self, from: NodeId, to: NodeId) -> Result<Option<Vec<Step>>, MetisError> {
        self.ensure_known(from)?;
        self.ensure_known(to)?;
        if from == to {
            return Ok(Some(Vec::new()));
        }
        let mut q = VecDeque::from([from]);
        let mut prev: HashMap<NodeId, (NodeId, Step)> = HashMap::new();
        let mut seen = HashSet::from([from]);
        while let Some(cur) = q.pop_front() {
            for (step, nxt) in self.equal_steps(cur)? {
                if !seen.insert(nxt) {
                    continue;
                }
                prev.insert(nxt, (cur, step));
                if nxt == to {
                    let mut path = Vec::new();
                    let mut walk = to;
                    while walk != from {
                        let (p, s) = prev[&walk];
                        path.push(s);
                        walk = p;
                    }
                    path.reverse();
                    return Ok(Some(path));
                }
                q.push_back(nxt);
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_nodes_hash_cons() {
        let mut g = Graph::new();
        let a = g.intern_empty().unwrap();
        let b = g.intern_empty().unwrap();
        assert_eq!(a, b);
        assert_eq!(g.node_count(), 1);
        assert_eq!(g.edge_count(), 0);
    }

    #[test]
    fn labels_are_distinct_and_consed() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let a2 = g.intern_label(b"a").unwrap();
        assert_ne!(a, b);
        assert_eq!(a, a2);
        assert_eq!(g.node_count(), 2);
    }

    #[test]
    fn judgment_does_not_merge_labels() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        assert_eq!(g.node_count(), 2);
        assert_eq!(g.judgment_outgoing(a).unwrap().len(), 1);
        assert!(g.find_equal_path(a, b).unwrap().is_some());
        assert!(g.find_equal_path(b, a).unwrap().is_some());
    }

    #[test]
    fn structured_nodes_hash_cons_and_reach() {
        let mut g = Graph::new();
        let leaf = g.intern_empty().unwrap();
        let a = g.intern(&[(EdgeKind::In, leaf)]).unwrap();
        let b = g.intern(&[(EdgeKind::In, leaf)]).unwrap();
        assert_eq!(a, b);
        assert_eq!(g.node_count(), 2);
        assert_eq!(g.edge_count(), 1);
        assert!(g.reaches(a, leaf).unwrap());
        assert!(!g.reaches(leaf, a).unwrap());
    }

    #[test]
    fn seal_yields_immutable_base() {
        let mut g = Graph::new();
        let _ = g.intern_label(b"x").unwrap();
        let im = g.seal();
        assert_eq!(im.node_count(), 1);
    }

    #[test]
    fn payloads_mark_label_and_judgment() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let e = g.assert(a, EdgeKind::Equal, b).unwrap();
        assert_eq!(g.label_of(a).unwrap(), Some(b"a".as_slice()));
        let p = g.edge_payload(e).unwrap();
        assert_eq!(p, EdgePayload::judgment(EdgeKind::Equal));
        assert!(!p.structural);
    }

    #[test]
    fn freeze_snapshot_blocks_mutation_keeps_query() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.freeze_snapshot();
        assert!(g.is_snapshot_frozen());
        assert_eq!(g.assert(a, EdgeKind::Equal, b).unwrap_err(), MetisError::GraphRejected);
        assert_eq!(g.intern_label(b"c").unwrap_err(), MetisError::GraphRejected);
        assert!(g.find_equal_path(a, b).unwrap().is_some());
    }
}
