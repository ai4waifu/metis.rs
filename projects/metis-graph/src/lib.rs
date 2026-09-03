//! Arena-backed directed relation graph with extensional hash-consing.
//!
//! A node is identified by the sorted multiset of outgoing `(EdgeKind, NodeId)` pairs.
//! Handles stay stable once interned; new structure is always introduced by interning.

use std::collections::{HashMap, HashSet, VecDeque};
use std::num::NonZeroU32;

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
    outs: Vec<(EdgeId, EdgeKindKey, NodeId)>,
}

#[derive(Clone, Debug)]
struct EdgeRec {
    from: NodeId,
    to: NodeId,
    kind: EdgeKindKey,
}

/// Mutable working graph (staging or accepted island body).
#[derive(Default)]
pub struct Graph {
    nodes: Vec<Option<NodeRec>>,
    edges: Vec<Option<EdgeRec>>,
    cons: HashMap<Vec<OutKey>, NodeId>,
}

impl Graph {
    pub fn new() -> Self {
        Self::default()
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

    /// Intern a node by its outgoing multiset (extensional hash-cons).
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
            });
            recorded.push((eid, kind_key, *to));
        }

        let nslot = Self::node_index(id)?;
        self.nodes[nslot] = Some(NodeRec { outs: recorded });
        self.cons.insert(key, id);
        Ok(id)
    }

    /// Intern the unique empty node.
    pub fn intern_empty(&mut self) -> Result<NodeId, MetisError> {
        self.intern(&[])
    }

    pub fn outgoing(&self, id: NodeId) -> Result<Vec<(EdgeId, EdgeKind, NodeId)>, MetisError> {
        let rec = self.node_rec(id)?;
        Ok(rec
            .outs
            .iter()
            .map(|(e, k, t)| (*e, EdgeKind::from(*k), *t))
            .collect())
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

    pub fn node_count(&self) -> usize {
        self.nodes.iter().filter(|n| n.is_some()).count()
    }

    pub fn edge_count(&self) -> usize {
        self.edges.iter().filter(|e| e.is_some()).count()
    }

    /// BFS reachability ignoring edge kinds (foundation path existence).
    pub fn reaches(&self, from: NodeId, to: NodeId) -> Result<bool, MetisError> {
        let _ = self.node_rec(from)?;
        let _ = self.node_rec(to)?;
        if from == to {
            return Ok(true);
        }
        let mut q = VecDeque::from([from]);
        let mut seen = HashSet::from([from]);
        while let Some(cur) = q.pop_front() {
            for (_e, _k, nxt) in self.outgoing(cur)? {
                if nxt == to {
                    return Ok(true);
                }
                if seen.insert(nxt) {
                    q.push_back(nxt);
                }
            }
        }
        Ok(false)
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
    fn distinct_kinds_yield_distinct_nodes() {
        let mut g = Graph::new();
        let leaf = g.intern_empty().unwrap();
        let a = g.intern(&[(EdgeKind::In, leaf)]).unwrap();
        let b = g.intern(&[(EdgeKind::Equal, leaf)]).unwrap();
        assert_ne!(a, b);
        assert_eq!(g.node_count(), 3);
    }
}
