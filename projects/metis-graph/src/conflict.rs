//! Explicit conflict detection without explosion (Living Core constitution).
//!
//! When an Island declares two relation kinds mutually exclusive and both have
//! trusted evidence on the same endpoints, Core reports [`ConflictReport`] and
//! may quarantine that world. It does **not** derive arbitrary conclusions.

use metis_types::{EdgeKind, MetisError, NodeId};

use super::admission::{AdmittedRelation, ConflictReport, QueryStatus, WorldId};
use super::Graph;

/// Island-declared mutual exclusion between two judgment kinds on one endpoint pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Incompatibility {
    pub left_kind: EdgeKind,
    pub right_kind: EdgeKind,
}

impl Incompatibility {
    /// `Equal` vs custom not-equal witness (finite-fragment demo policy).
    pub const fn equal_vs_custom_not_equal(not_equal_tag: u16) -> Self {
        Self { left_kind: EdgeKind::Equal, right_kind: EdgeKind::Custom(not_equal_tag) }
    }
}

/// Look for both sides of an incompatibility as judgment edges.
pub fn detect_judgment_conflict(
    graph: &Graph,
    world: WorldId,
    endpoints: (NodeId, NodeId),
    policy: Incompatibility,
) -> Result<Option<ConflictReport>, MetisError> {
    let left = find_judgment(graph, policy.left_kind, endpoints)?;
    let right = find_judgment(graph, policy.right_kind, endpoints)?;
    match (left, right) {
        (Some(_), Some(_)) => {
            let left = AdmittedRelation::bootstrap_unchecked(world, endpoints, 1);
            let right = AdmittedRelation::bootstrap_unchecked(world, endpoints, 2);
            Ok(Some(ConflictReport { world, left, right }))
        }
        _ => Ok(None),
    }
}

/// Query status under an incompatibility policy (no failure-as-negation).
pub fn query_under_incompatibility(
    graph: &Graph,
    endpoints: (NodeId, NodeId),
    policy: Incompatibility,
) -> Result<QueryStatus, MetisError> {
    let has_left = find_judgment(graph, policy.left_kind, endpoints)?.is_some();
    let has_right = find_judgment(graph, policy.right_kind, endpoints)?.is_some();
    Ok(match (has_left, has_right) {
        (true, true) => QueryStatus::Inconsistent,
        (true, false) => QueryStatus::Proven,
        (false, true) => QueryStatus::Refuted,
        (false, false) => QueryStatus::Unknown,
    })
}

fn find_judgment(graph: &Graph, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> Result<Option<()>, MetisError> {
    let (from, to) = endpoints;
    for (eid, k, nxt) in graph.judgment_outgoing(from)? {
        if k == kind && nxt == to && graph.is_judgment(eid)? {
            return Ok(Some(()));
        }
    }
    if kind == EdgeKind::Equal {
        for (eid, k, nxt) in graph.judgment_outgoing(to)? {
            if k == EdgeKind::Equal && nxt == from && graph.is_judgment(eid)? {
                return Ok(Some(()));
            }
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    const NOT_EQ: u16 = 42;

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn both_sides_are_inconsistent_not_explosion() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(a, EdgeKind::Custom(NOT_EQ), b).unwrap();
        let policy = Incompatibility::equal_vs_custom_not_equal(NOT_EQ);
        assert_eq!(query_under_incompatibility(&g, (a, b), policy).unwrap(), QueryStatus::Inconsistent);
        let report = detect_judgment_conflict(&g, world(), (a, b), policy).unwrap().unwrap();
        assert_eq!(report.world, world());
        // No third conclusion is minted — only the conflict object exists.
        assert_eq!(report.left.endpoints(), (a, b));
        assert_eq!(report.right.endpoints(), (a, b));
    }

    #[test]
    fn only_equal_is_proven() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        let policy = Incompatibility::equal_vs_custom_not_equal(NOT_EQ);
        assert_eq!(query_under_incompatibility(&g, (a, b), policy).unwrap(), QueryStatus::Proven);
        assert!(detect_judgment_conflict(&g, world(), (a, b), policy).unwrap().is_none());
    }

    #[test]
    fn neither_side_is_unknown() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let policy = Incompatibility::equal_vs_custom_not_equal(NOT_EQ);
        assert_eq!(query_under_incompatibility(&g, (a, b), policy).unwrap(), QueryStatus::Unknown);
    }
}
