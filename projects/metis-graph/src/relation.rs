//! Form / compose / admit relation helpers (Living Core constitution).
//!
//! These construct **candidates** or mint admissions only after replay. They do not
//! invent judgment edges.

use metis_types::{EdgeId, MetisError, NodeId};

use super::admission::{AdmittedRelation, CandidateRelation, QueryStatus, WorldId};
use super::derivation::search_and_admit_equal;
use super::Graph;

/// Form an outer-world candidate relation (no admission).
pub fn form_relation(
    world: WorldId,
    endpoints: (NodeId, NodeId),
    kind_edge: Option<EdgeId>,
) -> CandidateRelation {
    CandidateRelation { world, kind_edge, endpoints }
}

/// Compose two admitted EQ relations in the same world when they share an endpoint.
///
/// `a: x ~ y` and `b: y ~ z` yield candidate `x ~ z`. Does **not** mint admission.
pub fn compose_equal_relations(
    left: AdmittedRelation,
    right: AdmittedRelation,
) -> Result<CandidateRelation, MetisError> {
    if left.world() != right.world() {
        return Err(MetisError::ProofInvalid);
    }
    let (x, y) = left.endpoints();
    let (u, z) = right.endpoints();
    if y != u {
        return Err(MetisError::ProofInvalid);
    }
    Ok(form_relation(left.world(), (x, z), None))
}

/// Admit an EQ candidate only when the graph replay succeeds under `world`.
///
/// Missing path → [`MetisError::ProofInvalid`] (admission refused). Query APIs still
/// surface [`QueryStatus::Unknown`] separately.
pub fn admit_equal_relation(
    graph: &Graph,
    world: WorldId,
    candidate: CandidateRelation,
) -> Result<AdmittedRelation, MetisError> {
    if candidate.world != world {
        return Err(MetisError::ProofInvalid);
    }
    let (status, admitted) = search_and_admit_equal(graph, world, candidate.endpoints.0, candidate.endpoints.1)?;
    match (status, admitted) {
        (QueryStatus::Proven, Some(adm)) => Ok(adm),
        _ => Err(MetisError::ProofInvalid),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::{EdgeKind, IslandId};

    fn world(v: u64) -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: v }
    }

    #[test]
    fn form_is_outer_only() {
        let c = form_relation(world(1), (NodeId(0), NodeId(1)), None);
        assert_eq!(c.endpoints, (NodeId(0), NodeId(1)));
        assert_eq!(c.world.version, 1);
    }

    #[test]
    fn compose_requires_shared_endpoint() {
        let w = world(1);
        let a = AdmittedRelation::bootstrap_unchecked(w, (NodeId(0), NodeId(1)), 1);
        let b = AdmittedRelation::bootstrap_unchecked(w, (NodeId(1), NodeId(2)), 2);
        let c = compose_equal_relations(a, b).unwrap();
        assert_eq!(c.endpoints, (NodeId(0), NodeId(2)));

        let bad = AdmittedRelation::bootstrap_unchecked(w, (NodeId(3), NodeId(4)), 3);
        assert_eq!(compose_equal_relations(a, bad).unwrap_err(), MetisError::ProofInvalid);
    }

    #[test]
    fn admit_equal_needs_path() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let w = world(1);
        let cand = form_relation(w, (a, c), None);
        let adm = admit_equal_relation(&g, w, cand).unwrap();
        assert_eq!(adm.endpoints(), (a, c));

        let missing = form_relation(w, (a, g.intern_label(b"z").unwrap()), None);
        assert_eq!(admit_equal_relation(&g, w, missing).unwrap_err(), MetisError::ProofInvalid);
    }
}
