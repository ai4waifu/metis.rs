//! Bootstrap `Φ_W` / `Inner(W)` seeding (Living `10` least-fixed-point slice).
//!
//! Full `μΦ_W` saturation is not claimed. This module admits generating judgment edges
//! as `gen` evidence into [`super::inner::InnerTable`] — the `G_W` base of `Φ_W(X)` —
//! and applies one Equal symmetry / transitivity layer as a finite `Φ_W` step.

use metis_types::{EdgeKind, MetisError};

use super::{
    Graph,
    admission::WorldId,
    derivation_rules::{EQUAL_SYMMETRY, EQUAL_TRANSITIVITY, registry_from_rule_table},
    evidence::{Evidence, JudgmentAtom, replay_evidence, replay_evidence_with},
    inner::InnerTable,
    rules::{RelationSignature, RuleTable},
    transform::{TransformationInstance, TransformationSchema},
};

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
pub fn seed_equal_generators(graph: &Graph, world: WorldId, inner: &mut InnerTable) -> Result<usize, MetisError> {
    let mut sig = RelationSignature::new();
    sig.declare_kind(EdgeKind::Equal);
    seed_declared_generators(graph, world, &sig, inner)
}

/// One Equal `Φ_W` step: add missing symmetry and two-premise transitivity conclusions.
///
/// Uses only judgments already in Inner (plus their evidence). Does not search the graph.
pub fn phi_equal_step(graph: &Graph, world: WorldId, inner: &mut InnerTable) -> Result<usize, MetisError> {
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
        let sym = Evidence::App { rule: EQUAL_SYMMETRY.into(), premises: vec![evidence.clone()], conclusion: flipped };
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
            let app =
                Evidence::App { rule: EQUAL_TRANSITIVITY.into(), premises: vec![ea.clone(), eb.clone()], conclusion: concl };
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

/// One `Φ_W` step over declared chain transforms and one-premise flips in the registry.
///
/// Premises are taken from Inner memberships (not fresh graph search). Unknown rule names
/// are skipped — search may propose them later once replay support exists.
pub fn phi_rule_table_step(
    graph: &Graph,
    world: WorldId,
    rules: &RuleTable,
    inner: &mut InnerTable,
) -> Result<usize, MetisError> {
    let registry = registry_from_rule_table(rules);
    let mut added = 0;
    for schema in &rules.transforms {
        if !registry.has_rule(&schema.name) {
            continue;
        }
        added += admit_schema_from_inner(graph, world, schema, &registry, inner)?;
    }
    for flip in &rules.flips {
        if !registry.has_rule(&flip.name) {
            continue;
        }
        added += admit_flip_from_inner(graph, world, flip, &registry, inner)?;
    }
    Ok(added)
}

fn admit_schema_from_inner(
    graph: &Graph,
    world: WorldId,
    schema: &TransformationSchema,
    registry: &super::derivation_rules::DerivationRegistry,
    inner: &mut InnerTable,
) -> Result<usize, MetisError> {
    let lefts = inner.memberships_of(world, schema.premise_a.kind);
    let rights = inner.memberships_of(world, schema.premise_b.kind);
    let mut added = 0;
    for (a, ea) in &lefts {
        for (b, eb) in &rights {
            let Some(inst) = chain_instance(schema, a, b)
            else {
                continue;
            };
            let concl = JudgmentAtom { kind: schema.conclusion_kind, endpoints: inst.conclusion };
            if inner.contains_atom(world, concl) {
                continue;
            }
            let app = Evidence::App { rule: schema.name.clone(), premises: vec![ea.clone(), eb.clone()], conclusion: concl };
            match replay_evidence_with(graph, world, &app, &[], registry) {
                Ok(admitted) => {
                    inner.insert_checked(admitted, app)?;
                    added += 1;
                }
                Err(MetisError::ProofInvalid) => continue,
                Err(e) => return Err(e),
            }
        }
    }
    Ok(added)
}

fn chain_instance(schema: &TransformationSchema, a: &JudgmentAtom, b: &JudgmentAtom) -> Option<TransformationInstance> {
    let (x, y1) = a.endpoints;
    let (y2, z) = b.endpoints;
    if y1 != y2 {
        return None;
    }
    let inst = TransformationInstance { premise_a: (x, y1), premise_b: (y2, z), conclusion: (x, z) };
    if schema.matches_instance(&inst) { Some(inst) } else { None }
}

fn admit_flip_from_inner(
    graph: &Graph,
    world: WorldId,
    flip: &super::derivation_rules::FlipRule,
    registry: &super::derivation_rules::DerivationRegistry,
    inner: &mut InnerTable,
) -> Result<usize, MetisError> {
    let members = inner.memberships_of(world, flip.premise.kind);
    let mut added = 0;
    for (atom, evidence) in &members {
        if !flip.premise.matches_atom(*atom) {
            continue;
        }
        let (x, y) = atom.endpoints;
        if x == y && flip.conclusion == flip.premise.kind {
            continue;
        }
        let concl = JudgmentAtom { kind: flip.conclusion, endpoints: (y, x) };
        if inner.contains_atom(world, concl) {
            continue;
        }
        let app = Evidence::App { rule: flip.name.clone(), premises: vec![evidence.clone()], conclusion: concl };
        match replay_evidence_with(graph, world, &app, &[], registry) {
            Ok(admitted) => {
                inner.insert_checked(admitted, app)?;
                added += 1;
            }
            Err(MetisError::ProofInvalid) => continue,
            Err(e) => return Err(e),
        }
    }
    Ok(added)
}

/// Seed declared generators, then alternate Equal phi and rule-table phi until fixed or capped.
pub fn saturate_rule_table_inner(
    graph: &Graph,
    world: WorldId,
    rules: &RuleTable,
    inner: &mut InnerTable,
    max_steps: u32,
) -> Result<usize, MetisError> {
    let mut total = seed_declared_generators(graph, world, &rules.signature, inner)?;
    for _ in 0..max_steps {
        let mut n = phi_equal_step(graph, world, inner)?;
        n += phi_rule_table_step(graph, world, rules, inner)?;
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
    use crate::{admission::QueryStatus, rules::RelationSignature};
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

    #[test]
    fn rule_table_phi_admits_transitivity_from_inner() {
        use crate::{rules::RuleTable, transform::TransformationSchema};

        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let mut rules = RuleTable::default();
        rules.declare_kind(EdgeKind::Equal);
        rules.add_transform(TransformationSchema::equal_transitivity());
        let mut inner = InnerTable::new();
        let w = world();
        seed_declared_generators(&g, w, &rules.signature, &mut inner).unwrap();
        // Only generators — no symmetry yet. Rule-table phi should still close a→c.
        let n = phi_rule_table_step(&g, w, &rules, &mut inner).unwrap();
        assert!(n >= 1);
        assert_eq!(inner.query(w, EdgeKind::Equal, (a, c)), QueryStatus::Proven);
        saturate_rule_table_inner(&g, w, &rules, &mut inner, 8).unwrap();
        assert_eq!(inner.query(w, EdgeKind::Equal, (c, a)), QueryStatus::Proven);
    }

    #[test]
    fn custom_chain_transform_saturates_in_membership() {
        use crate::{
            rules::RuleTable,
            transform::{PremisePattern, TransformationSchema},
        };

        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::In, b).unwrap();
        g.assert(b, EdgeKind::In, c).unwrap();
        let mut rules = RuleTable::default();
        rules.declare_kind(EdgeKind::In);
        rules.add_transform(TransformationSchema {
            name: "in_compose".into(),
            premise_a: PremisePattern { kind: EdgeKind::In, from: None, to: None },
            premise_b: PremisePattern { kind: EdgeKind::In, from: None, to: None },
            conclusion_kind: EdgeKind::In,
        });
        let mut inner = InnerTable::new();
        let w = world();
        saturate_rule_table_inner(&g, w, &rules, &mut inner, 4).unwrap();
        assert_eq!(inner.query(w, EdgeKind::In, (a, c)), QueryStatus::Proven);
    }

    #[test]
    fn fixed_endpoint_transform_only_fires_from_root() {
        use crate::{
            rules::RuleTable,
            transform::{PremisePattern, TransformationSchema},
        };

        let mut g = Graph::new();
        let root = g.intern_label(b"root").unwrap();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(root, EdgeKind::In, a).unwrap();
        g.assert(a, EdgeKind::In, b).unwrap();
        g.assert(b, EdgeKind::In, c).unwrap();
        let mut rules = RuleTable::default();
        rules.declare_kind(EdgeKind::In);
        rules.add_transform(TransformationSchema {
            name: "from_root".into(),
            premise_a: PremisePattern { kind: EdgeKind::In, from: Some(root), to: None },
            premise_b: PremisePattern { kind: EdgeKind::In, from: None, to: None },
            conclusion_kind: EdgeKind::In,
        });
        let mut inner = InnerTable::new();
        let w = world();
        seed_declared_generators(&g, w, &rules.signature, &mut inner).unwrap();
        phi_rule_table_step(&g, w, &rules, &mut inner).unwrap();
        assert_eq!(inner.query(w, EdgeKind::In, (root, b)), QueryStatus::Proven);
        // a→c would require premise_a from `a`, which the fixed-from-root rule rejects.
        assert_eq!(inner.query(w, EdgeKind::In, (a, c)), QueryStatus::Unknown);
    }
}
