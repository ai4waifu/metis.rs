//! Bootstrap `Φ_W` / `Inner(W)` seeding (Living `10` least-fixed-point slice).
//!
//! Full `μΦ_W` saturation is not claimed. This module admits generating Equal edges
//! as `gen` evidence into [`super::inner::InnerTable`] — the `G_W` base of `Φ_W(X)`.

use metis_types::{EdgeKind, MetisError};

use super::admission::WorldId;
use super::evidence::{Evidence, JudgmentAtom, replay_evidence};
use super::inner::InnerTable;
use super::Graph;

/// Seed `Φ_W⁰` for Equal: every judgment `Equal` edge becomes `gen` evidence in Inner.
///
/// Skips atoms already present. Returns how many new Inner memberships were added.
pub fn seed_equal_generators(
    graph: &Graph,
    world: WorldId,
    inner: &mut InnerTable,
) -> Result<usize, MetisError> {
    let mut added = 0;
    for (eid, from, kind, to) in graph.judgment_edges() {
        if kind != EdgeKind::Equal {
            continue;
        }
        let atom = JudgmentAtom { kind, endpoints: (from, to) };
        if inner.contains_atom(world, atom) {
            continue;
        }
        let evidence = Evidence::Gen { edge: eid };
        let admitted = replay_evidence(graph, world, &evidence, &[])?;
        inner.insert_checked(admitted, evidence)?;
        added += 1;
    }
    Ok(added)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::QueryStatus;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn seed_puts_generators_in_inner() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        let mut inner = InnerTable::new();
        let w = world();
        assert_eq!(seed_equal_generators(&g, w, &mut inner).unwrap(), 1);
        assert_eq!(inner.query(w, EdgeKind::Equal, (a, b)), QueryStatus::Proven);
        assert_eq!(seed_equal_generators(&g, w, &mut inner).unwrap(), 0);
        assert_eq!(inner.evidence_dag().len(), 1);
    }
}
