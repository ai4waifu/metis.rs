//! Bootstrap `Φ_W` / `Inner(W)` seeding (Living `10` least-fixed-point slice).
//!
//! Full `μΦ_W` saturation is not claimed. This module admits generating judgment edges
//! as `gen` evidence into [`super::inner::InnerTable`] — the `G_W` base of `Φ_W(X)` —
//! and applies one Equal symmetry / transitivity layer as a finite `Φ_W` step.

use metis_types::{EdgeKind, MetisError};

use super::admission::WorldId;
use super::derivation_rules::{EQUAL_SYMMETRY, EQUAL_TRANSITIVITY};
use super::evidence::{Evidence, JudgmentAtom, replay_evidence};
use super::inner::InnerTable;
use super::rules::RelationSignature;
use super::Graph;

/// Seed `Φ_W⁰`: every judgment edge whose kind is allowed by `signature` becomes `gen` evidence.
///
/// Skips atoms already present. Returns how many new Inner memberships were added.
pub fn seed_declared_generators(
    graph: &Graph,
    world: WorldId,
    signature: &RelationSignature,
    inner: &mut InnerTable,
) -> Result<usize, MetisError> {
    let mut added = 0;
    for (eid, from, kind, to) in graph.judgment_edges() {
        if !signature.allows(kind) {
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

/// Seed `Φ_W⁰` for Equal only (compat wrapper around [`seed_declared_generators`]).
pub fn seed_equal_generators(
    graph: &Graph,
    world: WorldId,
    inner: &mut InnerTable,
) -> Result<usize, MetisError> {
    let mut sig = RelationSignature::new();
    sig.declare_kind(EdgeKind::Equal);
    seed_declared_generators(graph, world, &sig, inner)
}

/// One Equal `Φ_W` step: add missing symmetry and two-premise transitivity conclusions.
///
/// Uses only judgments already in Inner (plus their evidence). Does not search the graph.
pub fn phi_equal_step(
    graph: &Graph,
    world: WorldId,
    inner: &mut InnerTable,
) -> Result<usize, MetisError> {
    let members = inner.equal_memberships(world);
    let mut added = 0;

    for (atom, evidence) in &members {
        let (x, y) = atom.endpoints;
        if x == y {
            continue;
        }
        let flipped = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (y, x) };
        if inner.contains_atom(world, flipped) {
            continue;
        }
        let sym = Evidence::App {
            rule: EQUAL_SYMMETRY.into(),
            premises: vec![evidence.clone()],
            conclusion: flipped,
        };
        let admitted = replay_evidence(graph, world, &sym, &[])?;
        inner.insert_checked(admitted, sym)?;
        added += 1;
    }

    // Refresh after symmetry so transitivity can use flipped premises in the same caller's
    // subsequent step. Within this step, close over the pre-symmetry snapshot only.
    let members = inner.equal_memberships(world);
    for (a, ea) in &members {
        let (x, y1) = a.endpoints;
        for (b, eb) in &members {
            let (y2, z) = b.endpoints;
            if y1 != y2 {
                continue;
            }
            let concl = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (x, z) };
            if inner.contains_atom(world, concl) {
                continue;
            }
            let app = Evidence::App {
                rule: EQUAL_TRANSITIVITY.into(),
                premises: vec![ea.clone(), eb.clone()],
                conclusion: concl,
            };
            let admitted = replay_evidence(graph, world, &app, &[])?;
            inner.insert_checked(admitted, app)?;
            added += 1;
        }
    }

    Ok(added)
}

/// Seed generators then iterate `phi_equal_step` until a fixed point or `max_steps`.
pub fn saturate_equal_inner(
    graph: &Graph,
    world: WorldId,
    inner: &mut InnerTable,
    max_steps: u32,
) -> Result<usize, MetisError> {
    let mut total = seed_equal_generators(graph, world, inner)?;
    for _ in 0..max_steps {
        let n = phi_equal_step(graph, world, inner)?;
        total += n;
        if n == 0 {
            break;
        }
    }
    Ok(total)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::QueryStatus;
    use crate::rules::RelationSignature;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn seed_declared_generators_includes_custom_kinds() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(a, EdgeKind::Custom(3), b).unwrap();
        let mut sig = RelationSignature::new();
        sig.declare_kind(EdgeKind::Equal);
        sig.declare_kind(EdgeKind::Custom(3));
        let mut inner = InnerTable::new();
        let w = world();
        assert_eq!(seed_declared_generators(&g, w, &sig, &mut inner).unwrap(), 2);
        assert_eq!(inner.query(w, EdgeKind::Equal, (a, b)), QueryStatus::Proven);
        assert_eq!(inner.query(w, EdgeKind::Custom(3), (a, b)), QueryStatus::Proven);
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

    #[test]
    fn phi_step_adds_symmetry_and_transitivity() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let mut inner = InnerTable::new();
        let w = world();
        seed_equal_generators(&g, w, &mut inner).unwrap();
        let n = phi_equal_step(&g, w, &mut inner).unwrap();
        assert!(n >= 2);
        assert_eq!(inner.query(w, EdgeKind::Equal, (b, a)), QueryStatus::Proven);
        let _ = phi_equal_step(&g, w, &mut inner).unwrap();
        assert_eq!(inner.query(w, EdgeKind::Equal, (a, c)), QueryStatus::Proven);
    }

    #[test]
    fn saturate_reaches_path_closure() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let mut inner = InnerTable::new();
        let w = world();
        saturate_equal_inner(&g, w, &mut inner, 8).unwrap();
        assert_eq!(inner.query(w, EdgeKind::Equal, (a, c)), QueryStatus::Proven);
        assert_eq!(inner.query(w, EdgeKind::Equal, (c, a)), QueryStatus::Proven);
    }
}
