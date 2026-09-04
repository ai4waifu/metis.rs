//! Metis relation semantics on [`athena_graph`].
//!
//! - Bottom layer: ordinary discrete adjacency via [`GraphBuilder`] (not CAS M-Graph).
//! - Metis layer: hash-cons, label atoms, structural vs judgment edges, EQ paths.
//! - Staging keeps an unfinished builder. Seal with [`Graph::seal`] / [`Graph::seal_on_heap`].
//! - Core contract stubs: [`admission`].

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
    rc::Rc,
};

use athena_gc::{GcHeap, HeapBudget};
use athena_graph::{
    GraphBuilder, GraphDirection, GraphSemantics, ImmutableGraph, MultiplicityPolicy, PublishedImmutableGraph,
    SelfLoopDegree,
};
use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

pub mod admission;

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

#[derive(Clone, Copy, Debug)]
struct EdgeMeta {
    kind: EdgeKindKey,
    structural: bool,
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

/// Mutable working graph (staging or accepted island body before seal).
pub struct Graph {
    builder: GraphBuilder<(), ()>,
    cons: HashMap<Vec<OutKey>, NodeId>,
    labels: HashMap<Vec<u8>, NodeId>,
    label_of: HashMap<NodeId, Vec<u8>>,
    edge_meta: HashMap<EdgeId, EdgeMeta>,
    heap: Rc<RefCell<GcHeap>>,
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
            edge_meta: HashMap::new(),
            heap,
        }
    }

    pub fn heap(&self) -> &Rc<RefCell<GcHeap>> {
        &self.heap
    }

    /// Underlying athena builder (ordinary discrete graph).
    pub fn base(&self) -> &GraphBuilder<(), ()> {
        &self.builder
    }

    /// Seal into an immutable ordinary graph (drops Metis cons tables).
    pub fn seal(self) -> ImmutableGraph<(), ()> {
        self.builder.finish()
    }

    /// Seal and publish snapshot roots on the shared [`GcHeap`].
    pub fn seal_on_heap(self) -> Result<PublishedImmutableGraph<(), ()>, MetisError> {
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

    fn add_base_edge(&mut self, from: NodeId, to: NodeId, meta: EdgeMeta) -> Result<EdgeId, MetisError> {
        let eid = self.builder.add_edge(from, to, ()).ok_or(MetisError::GraphRejected)?;
        self.edge_meta.insert(eid, meta);
        Ok(eid)
    }

    /// Intern a named atom. Same bytes → same [`NodeId`].
    pub fn intern_label(&mut self, name: impl AsRef<[u8]>) -> Result<NodeId, MetisError> {
        let key = name.as_ref().to_vec();
        if let Some(id) = self.labels.get(&key).copied() {
            return Ok(id);
        }
        let id = self.builder.add_node(());
        self.labels.insert(key.clone(), id);
        self.label_of.insert(id, key);
        Ok(id)
    }

    /// Intern a node by its **structural** outgoing multiset (extensional hash-cons).
    pub fn intern(&mut self, outs: &[(EdgeKind, NodeId)]) -> Result<NodeId, MetisError> {
        for (_kind, to) in outs {
            self.ensure_known(*to)?;
        }
        let key = Self::fingerprint(outs);
        if let Some(id) = self.cons.get(&key).copied() {
            return Ok(id);
        }

        let id = self.builder.add_node(());
        for (kind, to) in outs {
            self.add_base_edge(
                id,
                *to,
                EdgeMeta { kind: EdgeKindKey::from(*kind), structural: true },
            )?;
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
        self.ensure_known(from)?;
        self.ensure_known(to)?;
        self.add_base_edge(from, to, EdgeMeta { kind: EdgeKindKey::from(kind), structural: false })
    }

    fn outgoing_filtered(
        &self,
        id: NodeId,
        structural: Option<bool>,
    ) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        self.ensure_known(id)?;
        let mut out = Vec::new();
        for (s, t, eid) in self.builder.graph().edges() {
            if s != id {
                continue;
            }
            let meta = self.edge_meta.get(&eid).ok_or(MetisError::EdgeNotFound)?;
            if let Some(want) = structural {
                if meta.structural != want {
                    continue;
                }
            }
            out.push((eid, EdgeKind::from(meta.kind), t));
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

    /// All outgoing edges (structural then judgment).
    pub fn outgoing(&self, id: NodeId) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        let mut all = self.structural_outgoing(id)?;
        all.extend(self.judgment_outgoing(id)?);
        Ok(all)
    }

    pub fn edge(&self, id: EdgeId) -> Result<(NodeId, EdgeKind, NodeId), MetisError> {
        let (from, to) = self.builder.graph().edge_endpoints(id).ok_or(MetisError::EdgeNotFound)?;
        let meta = self.edge_meta.get(&id).ok_or(MetisError::EdgeNotFound)?;
        Ok((from, EdgeKind::from(meta.kind), to))
    }

    pub fn is_judgment(&self, id: EdgeId) -> Result<bool, MetisError> {
        let meta = self.edge_meta.get(&id).ok_or(MetisError::EdgeNotFound)?;
        Ok(!meta.structural)
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
        for (eid, kind, nxt) in self.judgment_outgoing(id)? {
            if kind == EdgeKind::Equal {
                out.push((Step { edge: eid, forward: true }, nxt));
            }
        }
        for (s, t, eid) in self.builder.graph().edges() {
            if t != id {
                continue;
            }
            let Some(meta) = self.edge_meta.get(&eid)
            else {
                continue;
            };
            if meta.structural || meta.kind != EdgeKindKey::Equal {
                continue;
            }
            out.push((Step { edge: eid, forward: false }, s));
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
}
