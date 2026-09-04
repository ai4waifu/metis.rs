//! ZFC island finite fragment: empty set, pairing / finite enumeration, extensionality.

use metis_graph::Graph;
use metis_types::{EdgeKind, MetisError, NodeId};

/// Structural edge kind: set → member (hash-cons identity of finite sets).
pub const HAS_MEMBER: EdgeKind = EdgeKind::Custom(1);

/// The empty set `∅` (unique empty structural node).
pub fn empty_set(graph: &mut Graph) -> Result<NodeId, MetisError> {
    graph.intern_empty()
}

/// Urelement / atom by label.
pub fn atom(graph: &mut Graph, name: impl AsRef<[u8]>) -> Result<NodeId, MetisError> {
    graph.intern_label(name)
}

/// Finite set `{m0, m1, …}` with extensional hash-cons and pairing-intro `In` judgments.
pub fn finite_set(graph: &mut Graph, members: &[NodeId]) -> Result<NodeId, MetisError> {
    let mut ms = members.to_vec();
    ms.sort_by_key(|n| n.get());
    ms.dedup();
    let outs: Vec<(EdgeKind, NodeId)> = ms.iter().map(|m| (HAS_MEMBER, *m)).collect();
    let set = graph.intern(&outs)?;
    for m in &ms {
        if !has_in(graph, *m, set)? {
            graph.assert(*m, EdgeKind::In, set)?;
        }
    }
    Ok(set)
}

fn has_in(graph: &Graph, elem: NodeId, set: NodeId) -> Result<bool, MetisError> {
    for (_e, kind, to) in graph.judgment_outgoing(elem)? {
        if kind == EdgeKind::In && to == set {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{prove, Goal};

    #[test]
    fn empty_in_singleton_empty() {
        let mut g = Graph::new();
        let empty = empty_set(&mut g).unwrap();
        let s0 = finite_set(&mut g, &[empty]).unwrap();
        prove(&g, Goal::Member(empty, s0)).unwrap();
    }

    #[test]
    fn pair_idempotent_definitional() {
        let mut g = Graph::new();
        let a = atom(&mut g, b"a").unwrap();
        let s1 = finite_set(&mut g, &[a, a]).unwrap();
        let s2 = finite_set(&mut g, &[a]).unwrap();
        assert_eq!(s1, s2);
        prove(&g, Goal::Equal(s1, s2)).unwrap();
    }
}
