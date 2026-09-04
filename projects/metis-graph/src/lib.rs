//! Relation graph with structural hash-consing and judgment edges.
//!
//! - **Structural** outs define extensional identity (`intern`).
//! - **Judgment** edges assert facts without rewriting node identity (`assert`).
//! - **Labels** are content-addressed atoms for named proposition subjects.
//!
//! Object lifetime protocol is [`athena_gc`] — Metis does not ship a parallel GC crate.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::num::NonZeroU32;
use std::rc::Rc;

use athena_gc::{GcHeap, HeapBudget};
use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

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
    to: u32,
}

#[derive(Clone, Debug)]
struct NodeRec {
    /// Structural outs (hash-cons identity). Empty for pure labels.
    structural: Vec<(EdgeId, EdgeKindKey, NodeId)>,
    /// Judgment outs (facts). Do not affect hash-cons identity.
    judgments: Vec<(EdgeId, EdgeKindKey, NodeId)>,
    /// Optional label payload for named atoms.
    label: Option<Vec<u8>>,
}

#[derive(Clone, Debug)]
struct EdgeRec {
    from: NodeId,
    to: NodeId,
    kind: EdgeKindKey,
    /// True when the edge is a judgment (asserted fact).
    judgment: bool,
}

/// Directed step along a judgment edge, possibly reversed (for symmetric kinds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Step {
    pub edge: EdgeId,
    pub forward: bool,
}

/// Mutable working graph (staging or accepted island body).
pub struct Graph {
    nodes: Vec<Option<NodeRec>>,
    edges: Vec<Option<EdgeRec>>,
    cons: HashMap<Vec<OutKey>, NodeId>,
    labels: HashMap<Vec<u8>, NodeId>,
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
            nodes: Vec::new(),
            edges: Vec::new(),
            cons: HashMap::new(),
            labels: HashMap::new(),
            heap,
        }
    }

    pub fn heap(&self) -> &Rc<RefCell<GcHeap>> {
        &self.heap
    }

    /// Label bytes if this node was created with [`Self::intern_label`].
    pub fn label_of(&self, id: NodeId) -> Result<Option<&[u8]>, MetisError> {
        Ok(self.node_rec(id)?.label.as_deref())
    }

    fn alloc_node_slot(&mut self) -> Result<NodeId, MetisError> {
        let idx = self.nodes.len() + 1;
        let raw = NonZeroU32::new(idx.try_into().map_err(|_| MetisError::Capacity)?)
            .ok_or(MetisError::Capacity)?;
        self.nodes.push(None);
        Ok(NodeId::from_raw(raw))
    }

    fn alloc_edge_slot(&mut self) -> Result<EdgeId, MetisError> {
        let idx = self.edges.len() + 1;
        let raw = NonZeroU32::new(idx.try_into().map_err(|_| MetisError::Capacity)?)
            .ok_or(MetisError::Capacity)?;
        self.edges.push(None);
        Ok(EdgeId::from_raw(raw))
    }

    fn node_index(id: NodeId) -> Result<usize, MetisError> {
        usize::try_from(id.get().checked_sub(1).ok_or(MetisError::InvalidHandle)?)
            .map_err(|_| MetisError::InvalidHandle)
    }

    fn edge_index(id: EdgeId) -> Result<usize, MetisError> {
        usize::try_from(id.get().checked_sub(1).ok_or(MetisError::InvalidHandle)?)
            .map_err(|_| MetisError::InvalidHandle)
    }

    fn fingerprint(outs: &[(EdgeKind, NodeId)]) -> Vec<OutKey> {
        let mut keys: Vec<OutKey> = outs
            .iter()
            .map(|(kind, to)| OutKey {
                kind: EdgeKindKey::from(*kind),
                to: to.get(),
            })
            .collect();
        keys.sort();
        keys
    }

    fn ensure_known(&self, id: NodeId) -> Result<(), MetisError> {
        let _ = self.node_rec(id)?;
        Ok(())
    }

    fn node_rec(&self, id: NodeId) -> Result<&NodeRec, MetisError> {
        let slot = Self::node_index(id)?;
        self.nodes
            .get(slot)
            .and_then(|n| n.as_ref())
            .ok_or(MetisError::NodeNotFound)
    }

    fn node_rec_mut(&mut self, id: NodeId) -> Result<&mut NodeRec, MetisError> {
        let slot = Self::node_index(id)?;
        self.nodes
            .get_mut(slot)
            .and_then(|n| n.as_mut())
            .ok_or(MetisError::NodeNotFound)
    }

    /// Intern a named atom. Same bytes → same [`NodeId`].
    pub fn intern_label(&mut self, name: impl AsRef<[u8]>) -> Result<NodeId, MetisError> {
        let key = name.as_ref().to_vec();
        if let Some(id) = self.labels.get(&key).copied() {
            return Ok(id);
        }
        let id = self.alloc_node_slot()?;
        let slot = Self::node_index(id)?;
        self.nodes[slot] = Some(NodeRec {
            structural: Vec::new(),
            judgments: Vec::new(),
            label: Some(key.clone()),
        });
        self.labels.insert(key, id);
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

        let id = self.alloc_node_slot()?;
        let mut recorded = Vec::with_capacity(outs.len());
        for (kind, to) in outs {
            let kind_key = EdgeKindKey::from(*kind);
            let eid = self.alloc_edge_slot()?;
            let eslot = Self::edge_index(eid)?;
            self.edges[eslot] = Some(EdgeRec {
                from: id,
                to: *to,
                kind: kind_key,
                judgment: false,
            });
            recorded.push((eid, kind_key, *to));
        }

        let nslot = Self::node_index(id)?;
        self.nodes[nslot] = Some(NodeRec {
            structural: recorded,
            judgments: Vec::new(),
            label: None,
        });
        self.cons.insert(key, id);
        Ok(id)
    }

    /// Intern the unique empty structural node.
    pub fn intern_empty(&mut self) -> Result<NodeId, MetisError> {
        self.intern(&[])
    }

    /// Assert a judgment edge. Does not change structural identity of `from`.
    pub fn assert(
        &mut self,
        from: NodeId,
        kind: EdgeKind,
        to: NodeId,
    ) -> Result<EdgeId, MetisError> {
        self.ensure_known(from)?;
        self.ensure_known(to)?;
        let kind_key = EdgeKindKey::from(kind);
        let eid = self.alloc_edge_slot()?;
        let eslot = Self::edge_index(eid)?;
        self.edges[eslot] = Some(EdgeRec {
            from,
            to,
            kind: kind_key,
            judgment: true,
        });
        self.node_rec_mut(from)?
            .judgments
            .push((eid, kind_key, to));
        Ok(eid)
    }

    /// Structural outgoing edges only.
    pub fn structural_outgoing(
        &self,
        id: NodeId,
    ) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        let rec = self.node_rec(id)?;
        Ok(rec
            .structural
            .iter()
            .map(|(e, k, t)| (*e, EdgeKind::from(*k), *t))
            .collect())
    }

    /// Judgment outgoing edges only.
    pub fn judgment_outgoing(
        &self,
        id: NodeId,
    ) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        let rec = self.node_rec(id)?;
        Ok(rec
            .judgments
            .iter()
            .map(|(e, k, t)| (*e, EdgeKind::from(*k), *t))
            .collect())
    }

    /// All outgoing edges (structural then judgment).
    pub fn outgoing(&self, id: NodeId) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        let mut all = self.structural_outgoing(id)?;
        all.extend(self.judgment_outgoing(id)?);
        Ok(all)
    }

    pub fn edge(&self, id: EdgeId) -> Result<(NodeId, EdgeKind, NodeId), MetisError> {
        let slot = Self::edge_index(id)?;
        let rec = self
            .edges
            .get(slot)
            .and_then(|e| e.as_ref())
            .ok_or(MetisError::EdgeNotFound)?;
        Ok((rec.from, EdgeKind::from(rec.kind), rec.to))
    }

    pub fn is_judgment(&self, id: EdgeId) -> Result<bool, MetisError> {
        let slot = Self::edge_index(id)?;
        let rec = self
            .edges
            .get(slot)
            .and_then(|e| e.as_ref())
            .ok_or(MetisError::EdgeNotFound)?;
        Ok(rec.judgment)
    }

    pub fn node_count(&self) -> usize {
        self.nodes.iter().filter(|n| n.is_some()).count()
    }

    pub fn edge_count(&self) -> usize {
        self.edges.iter().filter(|e| e.is_some()).count()
    }

    /// Directed reachability over all outgoing edges.
    pub fn reaches(&self, from: NodeId, to: NodeId) -> Result<bool, MetisError> {
        Ok(self.find_directed_path(from, to)?.is_some())
    }

    pub fn find_directed_path(
        &self,
        from: NodeId,
        to: NodeId,
    ) -> Result<Option<Vec<EdgeId>>, MetisError> {
        let _ = self.node_rec(from)?;
        let _ = self.node_rec(to)?;
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
        let _ = self.node_rec(id)?;
        let mut out = Vec::new();
        for (eid, kind, nxt) in self.judgment_outgoing(id)? {
            if kind == EdgeKind::Equal {
                out.push((
                    Step {
                        edge: eid,
                        forward: true,
                    },
                    nxt,
                ));
            }
        }
        // Reverse Equal: scan all judgment edges ending at `id`.
        for (slot, maybe) in self.edges.iter().enumerate() {
            let Some(rec) = maybe else { continue };
            if !rec.judgment || rec.kind != EdgeKindKey::Equal || rec.to != id {
                continue;
            }
            let raw = NonZeroU32::new((slot + 1) as u32).ok_or(MetisError::InvalidHandle)?;
            let eid = EdgeId::from_raw(raw);
            out.push((
                Step {
                    edge: eid,
                    forward: false,
                },
                rec.from,
            ));
        }
        Ok(out)
    }

    /// Search an undirected `Equal` path (symmetry + transitivity of edge composition).
    pub fn find_equal_path(
        &self,
        from: NodeId,
        to: NodeId,
    ) -> Result<Option<Vec<Step>>, MetisError> {
        let _ = self.node_rec(from)?;
        let _ = self.node_rec(to)?;
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
}
