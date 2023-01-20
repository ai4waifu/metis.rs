//! Finite evidence terms (Living `10` Derivation slice).
//!
//! Evidence is an inductive tree:
//! `gen(g) | hyp(J) | app(ρ, σ, e₁…eₙ)`.
//! Owned trees are automatically well-founded; [`height`] is the Living measure.
//!
//! This module is the general Derivation DAG *shape*. EQ linear steps and two-premise
//! transforms remain bootstrap specializations that can be encoded into [`Evidence`].

use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

use super::{
    Graph,
    admission::{AdmittedRelation, JudgmentLane, WorldId},
    derivation_rules::{DerivationRegistry, EQUAL_REFL, EQUAL_SYMMETRY, EQUAL_TRANSITIVITY},
};

/// Atomic judgment `R(p, q)` (binary foundation slice).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct JudgmentAtom {
    pub kind: EdgeKind,
    pub endpoints: (NodeId, NodeId),
}

/// Finite evidence term under a fixed world snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Evidence {
    /// Generator: judgment edge already present in the world graph.
    Gen { edge: EdgeId },
    /// Local hypothesis. Does **not** enter `Inner(W)` by itself.
    Hyp { judgment: JudgmentAtom },
    /// Rule application `app(ρ, σ, e₁…eₙ)` with an explicit conclusion atom (σ result).
    App { rule: String, premises: Vec<Evidence>, conclusion: JudgmentAtom },
}

/// Checked package: world + evidence + claimed conclusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedDerivation {
    pub world: WorldId,
    pub evidence: Evidence,
    pub conclusion: JudgmentAtom,
}

/// Living height: `h(gen)=h(hyp)=0`, `h(app)=1+max h(eᵢ)`.
pub fn height(evidence: &Evidence) -> u32 {
    match evidence {
        Evidence::Gen { .. } | Evidence::Hyp { .. } => 0,
        Evidence::App { premises, .. } => {
            let max_p = premises.iter().map(height).max().unwrap_or(0);
            1 + max_p
        }
    }
}

/// Structural finite check (owned tree ⇒ acyclic). Rejects empty rule names on `App`.
pub fn validate_finite(evidence: &Evidence) -> Result<(), MetisError> {
    match evidence {
        Evidence::Gen { .. } | Evidence::Hyp { .. } => Ok(()),
        Evidence::App { rule, premises, .. } => {
            if rule.is_empty() {
                return Err(MetisError::ProofInvalid);
            }
            for p in premises {
                validate_finite(p)?;
            }
            // Touch height so pathological overflow would surface in debug builds.
            let _ = height(evidence);
            Ok(())
        }
    }
}

/// Read the judgment concluded by `evidence` (Gen reads the edge; App/Hyp use stored atoms).
pub fn concluded_judgment(graph: &Graph, evidence: &Evidence) -> Result<JudgmentAtom, MetisError> {
    match evidence {
        Evidence::Gen { edge } => {
            let (from, kind, to) = graph.edge(*edge)?;
            if !graph.is_judgment(*edge)? {
                return Err(MetisError::ProofInvalid);
            }
            Ok(JudgmentAtom { kind, endpoints: (from, to) })
        }
        Evidence::Hyp { judgment } | Evidence::App { conclusion: judgment, .. } => Ok(*judgment),
    }
}

/// Encode a degenerate EQ step list as evidence under Living `10` shapes.
///
/// - empty + `left == right` → `app(equal_refl, [], Equal(left,right))`
/// - one oriented step → `gen(edge)` or `app(equal_symmetry, [gen], …)` when reversed
/// - many steps → nested `app(equal_transitivity, …)` over oriented step evidence
pub fn evidence_from_equal_steps(
    graph: &Graph,
    left: NodeId,
    right: NodeId,
    steps: &[super::Step],
) -> Result<Evidence, MetisError> {
    if steps.is_empty() {
        if left != right {
            return Err(MetisError::ProofInvalid);
        }
        return Ok(Evidence::App {
            rule: EQUAL_REFL.into(),
            premises: Vec::new(),
            conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (left, right) },
        });
    }

    let mut cur = left;
    let mut oriented: Vec<Evidence> = Vec::with_capacity(steps.len());
    let mut ends: Vec<NodeId> = Vec::with_capacity(steps.len());
    for step in steps {
        let (from, kind, to) = graph.edge(step.edge)?;
        if kind != EdgeKind::Equal || !graph.is_judgment(step.edge)? {
            return Err(MetisError::ProofInvalid);
        }
        let (expected_from, nxt) = if step.forward { (from, to) } else { (to, from) };
        if cur != expected_from {
            return Err(MetisError::ProofInvalid);
        }
        let gen_ev = Evidence::Gen { edge: step.edge };
        let step_ev = if step.forward {
            gen_ev
        }
        else {
            Evidence::App {
                rule: EQUAL_SYMMETRY.into(),
                premises: vec![gen_ev],
                conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (expected_from, nxt) },
            }
        };
        oriented.push(step_ev);
        ends.push(nxt);
        cur = nxt;
    }
    if cur != right {
        return Err(MetisError::ProofInvalid);
    }

    if oriented.len() == 1 {
        return Ok(oriented.pop().unwrap());
    }

    let mut acc = oriented.remove(0);
    for (i, next_ev) in oriented.into_iter().enumerate() {
        let next_end = ends[i + 1];
        acc = Evidence::App {
            rule: EQUAL_TRANSITIVITY.into(),
            premises: vec![acc, next_ev],
            conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (left, next_end) },
        };
    }
    Ok(acc)
}

/// Replay evidence under world `W` with local hypothesis set `gamma`.
///
/// Empty `gamma` is the trusted-path case `W;∅ ⊢ e : J`.
/// Uses the builtin EQ registry only.
pub fn replay_evidence(
    graph: &Graph,
    world: WorldId,
    evidence: &Evidence,
    gamma: &[JudgmentAtom],
) -> Result<AdmittedRelation, MetisError> {
    replay_evidence_with(graph, world, evidence, gamma, &DerivationRegistry::builtins())
}

/// Like [`replay_evidence`], but applies rules from `registry` (builtins + custom chains).
pub fn replay_evidence_with(
    graph: &Graph,
    world: WorldId,
    evidence: &Evidence,
    gamma: &[JudgmentAtom],
    registry: &DerivationRegistry,
) -> Result<AdmittedRelation, MetisError> {
    validate_finite(evidence)?;
    let conclusion = replay_under(graph, evidence, gamma, registry)?;
    let tag = fingerprint_evidence(world, evidence, conclusion);
    Ok(AdmittedRelation::mint(world, conclusion.kind, conclusion.endpoints, tag, JudgmentLane::SingleWorldReplay))
}

/// Replay and require the concluded judgment equals `expected`.
pub fn replay_checked_derivation(
    graph: &Graph,
    derivation: &CheckedDerivation,
    gamma: &[JudgmentAtom],
) -> Result<AdmittedRelation, MetisError> {
    let admitted = replay_evidence(graph, derivation.world, &derivation.evidence, gamma)?;
    if admitted.kind() != derivation.conclusion.kind || admitted.endpoints() != derivation.conclusion.endpoints {
        return Err(MetisError::ProofInvalid);
    }
    Ok(admitted)
}

fn replay_under(
    graph: &Graph,
    evidence: &Evidence,
    gamma: &[JudgmentAtom],
    registry: &DerivationRegistry,
) -> Result<JudgmentAtom, MetisError> {
    match evidence {
        Evidence::Gen { edge } => {
            let atom = concluded_judgment(graph, evidence)?;
            let _ = edge;
            Ok(atom)
        }
        Evidence::Hyp { judgment } => {
            if !gamma.contains(judgment) {
                return Err(MetisError::ProofInvalid);
            }
            Ok(*judgment)
        }
        Evidence::App { rule, premises, conclusion } => {
            let mut premise_atoms = Vec::with_capacity(premises.len());
            for p in premises {
                premise_atoms.push(replay_under(graph, p, gamma, registry)?);
            }
            registry.apply(rule, &premise_atoms, *conclusion)
        }
    }
}

fn kind_tag(k: EdgeKind) -> u64 {
    match k {
        EdgeKind::Equal => 1,
        EdgeKind::In => 2,
        EdgeKind::Eval => 3,
        EdgeKind::Custom(v) => 4u64.wrapping_add(u64::from(v)),
    }
}

fn fingerprint_evidence(world: WorldId, evidence: &Evidence, conclusion: JudgmentAtom) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for x in [
        world.island.get() as u64,
        world.version,
        kind_tag(conclusion.kind),
        conclusion.endpoints.0.0,
        conclusion.endpoints.1.0,
        u64::from(height(evidence)),
    ] {
        h ^= x;
        h = h.wrapping_mul(0x100000001b3);
    }
    fingerprint_shape(evidence, &mut h);
    h
}

fn fingerprint_shape(evidence: &Evidence, h: &mut u64) {
    match evidence {
        Evidence::Gen { edge } => {
            *h ^= 0x1;
            *h = h.wrapping_mul(0x100000001b3);
            *h ^= edge.0;
            *h = h.wrapping_mul(0x100000001b3);
        }
        Evidence::Hyp { judgment } => {
            *h ^= 0x2;
            *h = h.wrapping_mul(0x100000001b3);
            *h ^= kind_tag(judgment.kind);
            *h = h.wrapping_mul(0x100000001b3);
            *h ^= judgment.endpoints.0.0;
            *h = h.wrapping_mul(0x100000001b3);
            *h ^= judgment.endpoints.1.0;
            *h = h.wrapping_mul(0x100000001b3);
        }
        Evidence::App { rule, premises, conclusion } => {
            *h ^= 0x3;
            *h = h.wrapping_mul(0x100000001b3);
            for b in rule.as_bytes() {
                *h ^= u64::from(*b);
                *h = h.wrapping_mul(0x100000001b3);
            }
            *h ^= kind_tag(conclusion.kind);
            *h = h.wrapping_mul(0x100000001b3);
            *h ^= conclusion.endpoints.0.0;
            *h = h.wrapping_mul(0x100000001b3);
            *h ^= conclusion.endpoints.1.0;
            *h = h.wrapping_mul(0x100000001b3);
            for p in premises {
                fingerprint_shape(p, h);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_rules::EQUAL_SYMMETRY;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn refl_app_has_height_one() {
        let e = Evidence::App {
            rule: "equal_refl".into(),
            premises: Vec::new(),
            conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(0), NodeId(0)) },
        };
        assert_eq!(height(&e), 1);
        validate_finite(&e).unwrap();
    }

    #[test]
    fn gen_and_trans_replay() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        let e_ab = g.assert(a, EdgeKind::Equal, b).unwrap();
        let e_bc = g.assert(b, EdgeKind::Equal, c).unwrap();
        let evidence = Evidence::App {
            rule: "equal_transitivity".into(),
            premises: vec![Evidence::Gen { edge: e_ab }, Evidence::Gen { edge: e_bc }],
            conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (a, c) },
        };
        assert_eq!(height(&evidence), 1);
        let adm = replay_evidence(&g, world(), &evidence, &[]).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
        assert!(adm.is_trusted_path_candidate());
    }

    #[test]
    fn hyp_requires_gamma() {
        let g = Graph::new();
        let j = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(0), NodeId(1)) };
        let e = Evidence::Hyp { judgment: j };
        assert!(replay_evidence(&g, world(), &e, &[]).is_err());
        let adm = replay_evidence(&g, world(), &e, &[j]).unwrap();
        assert_eq!(adm.endpoints(), (NodeId(0), NodeId(1)));
    }

    #[test]
    fn equal_steps_encode_to_evidence() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let steps = g.find_equal_path(a, c).unwrap().unwrap();
        let e = evidence_from_equal_steps(&g, a, c, &steps).unwrap();
        assert!(height(&e) >= 1);
        let adm = replay_evidence(&g, world(), &e, &[]).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
    }

    #[test]
    fn reverse_step_uses_symmetry_rule() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        let steps = g.find_equal_path(b, a).unwrap().unwrap();
        assert_eq!(steps.len(), 1);
        assert!(!steps[0].forward);
        let e = evidence_from_equal_steps(&g, b, a, &steps).unwrap();
        match &e {
            Evidence::App { rule, premises, conclusion } => {
                assert_eq!(rule, EQUAL_SYMMETRY);
                assert_eq!(premises.len(), 1);
                assert_eq!(conclusion.endpoints, (b, a));
            }
            _ => panic!("expected symmetry app"),
        }
        let adm = replay_evidence(&g, world(), &e, &[]).unwrap();
        assert_eq!(adm.endpoints(), (b, a));
    }
}
