//! Derivation diagram replay (Living Core constitution, first slice).
//!
//! Full diagrams are DAGs. This foundation accepts the **degenerate** form used by EQ:
//! an ordered list of judgment `Equal` steps. Search may propose a diagram; only replay
//! can mint [`AdmittedRelation`].

use metis_types::{MetisError, NodeId};

use super::admission::{AdmittedRelation, QueryStatus, WorldId};
use super::{Graph, Step};

/// Degenerate derivation diagram: ordered EQ steps under a fixed world version.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivationDiagram {
    pub world: WorldId,
    /// Conclusion `Equal(left, right)` endpoints.
    pub conclusion: (NodeId, NodeId),
    /// Ordered undirected EQ steps from left toward right.
    pub steps: Vec<Step>,
}

/// Replay a diagram against `graph`. On success, mint an opaque [`AdmittedRelation`].
///
/// Does not invent edges. Tampered steps / endpoints fail with [`MetisError::ProofInvalid`].
pub fn replay_equal_derivation(graph: &Graph, diagram: &DerivationDiagram) -> Result<AdmittedRelation, MetisError> {
    let (start, end) = diagram.conclusion;
    verify_equal_steps(graph, start, end, &diagram.steps)?;
    let tag = fingerprint_diagram(diagram);
    Ok(AdmittedRelation::bootstrap_unchecked(diagram.world, diagram.conclusion, tag))
}

/// Search then replay: missing path → [`QueryStatus::Unknown`] (no admission).
pub fn search_and_admit_equal(
    graph: &Graph,
    world: WorldId,
    left: NodeId,
    right: NodeId,
) -> Result<(QueryStatus, Option<AdmittedRelation>), MetisError> {
    if left == right {
        let diagram = DerivationDiagram { world, conclusion: (left, right), steps: Vec::new() };
        let admitted = replay_equal_derivation(graph, &diagram)?;
        return Ok((QueryStatus::Proven, Some(admitted)));
    }
    match graph.find_equal_path(left, right)? {
        Some(steps) => {
            let diagram = DerivationDiagram { world, conclusion: (left, right), steps };
            let admitted = replay_equal_derivation(graph, &diagram)?;
            Ok((QueryStatus::Proven, Some(admitted)))
        }
        None => Ok((QueryStatus::Unknown, None)),
    }
}

fn verify_equal_steps(graph: &Graph, start: NodeId, end: NodeId, steps: &[Step]) -> Result<(), MetisError> {
    use metis_types::EdgeKind;
    if steps.is_empty() {
        return if start == end { Ok(()) } else { Err(MetisError::ProofInvalid) };
    }
    let mut cur = start;
    for step in steps {
        let (from, kind, to) = graph.edge(step.edge)?;
        if kind != EdgeKind::Equal || !graph.is_judgment(step.edge)? {
            return Err(MetisError::ProofInvalid);
        }
        let (expected_from, nxt) = if step.forward { (from, to) } else { (to, from) };
        if cur != expected_from {
            return Err(MetisError::ProofInvalid);
        }
        cur = nxt;
    }
    if cur == end { Ok(()) } else { Err(MetisError::ProofInvalid) }
}

fn fingerprint_diagram(diagram: &DerivationDiagram) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for x in [
        diagram.world.island.get() as u64,
        diagram.world.version,
        diagram.conclusion.0 .0,
        diagram.conclusion.1 .0,
        diagram.steps.len() as u64,
    ] {
        h ^= x;
        h = h.wrapping_mul(0x100000001b3);
    }
    for step in &diagram.steps {
        h ^= step.edge.0;
        h = h.wrapping_mul(0x100000001b3);
        h ^= u64::from(step.forward);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::{EdgeKind, IslandId};

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn admit_reflexive_and_path() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        let w = world();
        let (st, adm) = search_and_admit_equal(&g, w, a, b).unwrap();
        assert_eq!(st, QueryStatus::Proven);
        let adm = adm.unwrap();
        assert_eq!(adm.world(), w);
        assert_eq!(adm.endpoints(), (a, b));
    }

    #[test]
    fn missing_path_is_unknown_without_admission() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let (st, adm) = search_and_admit_equal(&g, world(), a, b).unwrap();
        assert_eq!(st, QueryStatus::Unknown);
        assert!(adm.is_none());
    }

    #[test]
    fn tampered_steps_rejected() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let steps = g.find_equal_path(a, c).unwrap().unwrap();
        let bad = DerivationDiagram {
            world: world(),
            conclusion: (a, b), // wrong conclusion for these steps
            steps,
        };
        assert_eq!(replay_equal_derivation(&g, &bad).unwrap_err(), MetisError::ProofInvalid);
    }

    #[test]
    fn same_diagram_same_evidence_tag() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        let w = world();
        let (_, x) = search_and_admit_equal(&g, w, a, b).unwrap();
        let (_, y) = search_and_admit_equal(&g, w, a, b).unwrap();
        assert_eq!(x.unwrap().evidence_tag(), y.unwrap().evidence_tag());
    }
}
