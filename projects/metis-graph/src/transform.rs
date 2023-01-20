//! Relation transformation schemas (Living Core constitution).
//!
//! A transformation is not a method on objects. It is:
//! premise relation patterns → boundary-preserving rewrite → conclusion pattern.
//! Two-premise replay encodes into [`crate::evidence::Evidence::App`] before minting.

use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

use super::{
    Graph,
    admission::{AdmittedRelation, WorldId},
    derivation_rules::{DerivationRegistry, EQUAL_TRANSITIVITY},
    evidence::{Evidence, JudgmentAtom, replay_evidence_with},
};

/// Pattern for one premise judgment: `kind(from, to)` with optional fixed endpoints.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PremisePattern {
    pub kind: EdgeKind,
    /// If set, the source endpoint must match this node.
    pub from: Option<NodeId>,
    /// If set, the target endpoint must match this node.
    pub to: Option<NodeId>,
}

impl PremisePattern {
    /// True when `atom` has this kind and satisfies any fixed endpoints.
    pub fn matches_atom(self, atom: JudgmentAtom) -> bool {
        if atom.kind != self.kind {
            return false;
        }
        let (from, to) = atom.endpoints;
        if let Some(f) = self.from {
            if from != f {
                return false;
            }
        }
        if let Some(t) = self.to {
            if to != t {
                return false;
            }
        }
        true
    }
}

/// Declared two-premise transformation schema (object-logic rule shape under Core).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransformationSchema {
    pub name: String,
    pub premise_a: PremisePattern,
    pub premise_b: PremisePattern,
    pub conclusion_kind: EdgeKind,
}

/// One concrete instance proposed by search (still a candidate until replay).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TransformationInstance {
    pub premise_a: (NodeId, NodeId),
    pub premise_b: (NodeId, NodeId),
    pub conclusion: (NodeId, NodeId),
}

impl TransformationSchema {
    /// EQ transitivity skeleton: `Equal(x,y)` and `Equal(y,z)` ⇒ `Equal(x,z)`.
    pub fn equal_transitivity() -> Self {
        Self {
            name: EQUAL_TRANSITIVITY.into(),
            premise_a: PremisePattern { kind: EdgeKind::Equal, from: None, to: None },
            premise_b: PremisePattern { kind: EdgeKind::Equal, from: None, to: None },
            conclusion_kind: EdgeKind::Equal,
        }
    }

    /// Check chain shape plus optional fixed endpoints on each premise.
    pub fn matches_instance(&self, inst: &TransformationInstance) -> bool {
        let (x, y1) = inst.premise_a;
        let (y2, z) = inst.premise_b;
        let (cx, cz) = inst.conclusion;
        if !(y1 == y2 && cx == x && cz == z) {
            return false;
        }
        self.premise_a.matches_atom(JudgmentAtom { kind: self.premise_a.kind, endpoints: (x, y1) })
            && self.premise_b.matches_atom(JudgmentAtom { kind: self.premise_b.kind, endpoints: (y2, z) })
    }
}

/// Encode a two-premise instance as `app(ρ, [gen(e₁), gen(e₂)], J)`.
pub fn evidence_from_two_premise(
    graph: &Graph,
    schema: &TransformationSchema,
    inst: &TransformationInstance,
) -> Result<Evidence, MetisError> {
    if !schema.matches_instance(inst) {
        return Err(MetisError::ProofInvalid);
    }
    let edge_a = find_judgment_edge(graph, schema.premise_a.kind, inst.premise_a)?;
    let edge_b = find_judgment_edge(graph, schema.premise_b.kind, inst.premise_b)?;
    if schema.name == EQUAL_TRANSITIVITY {
        let (x, z) = inst.conclusion;
        if graph.find_equal_path(x, z)?.is_none() {
            return Err(MetisError::ProofInvalid);
        }
    }
    Ok(Evidence::App {
        rule: schema.name.clone(),
        premises: vec![Evidence::Gen { edge: edge_a }, Evidence::Gen { edge: edge_b }],
        conclusion: JudgmentAtom { kind: schema.conclusion_kind, endpoints: inst.conclusion },
    })
}

/// Replay a two-premise instance: both premises must already be judgment edges in `graph`.
///
/// Encodes into Living `10` evidence and replays under empty `Γ`.
/// Does **not** insert the conclusion edge — admission is epistemic, not mutation.
pub fn replay_two_premise(
    graph: &Graph,
    world: WorldId,
    schema: &TransformationSchema,
    inst: &TransformationInstance,
) -> Result<AdmittedRelation, MetisError> {
    Ok(replay_two_premise_checked(graph, world, schema, inst)?.0)
}

/// Like [`replay_two_premise`], but also returns the checked evidence AST.
pub fn replay_two_premise_checked(
    graph: &Graph,
    world: WorldId,
    schema: &TransformationSchema,
    inst: &TransformationInstance,
) -> Result<(AdmittedRelation, Evidence), MetisError> {
    replay_two_premise_checked_with(graph, world, schema, inst, &DerivationRegistry::builtins())
}

/// Replay with an explicit derivation registry (builtins + custom chains).
pub fn replay_two_premise_checked_with(
    graph: &Graph,
    world: WorldId,
    schema: &TransformationSchema,
    inst: &TransformationInstance,
    registry: &DerivationRegistry,
) -> Result<(AdmittedRelation, Evidence), MetisError> {
    let evidence = evidence_from_two_premise(graph, schema, inst)?;
    let admitted = replay_evidence_with(graph, world, &evidence, &[], registry)?;
    Ok((admitted, evidence))
}

fn find_judgment_edge(graph: &Graph, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> Result<EdgeId, MetisError> {
    let (from, to) = endpoints;
    for (eid, k, nxt) in graph.judgment_outgoing(from)? {
        if k == kind && nxt == to && graph.is_judgment(eid)? {
            return Ok(eid);
        }
    }
    // Symmetric Equal: allow reverse witness.
    if kind == EdgeKind::Equal {
        for (eid, k, nxt) in graph.judgment_outgoing(to)? {
            if k == EdgeKind::Equal && nxt == from && graph.is_judgment(eid)? {
                return Ok(eid);
            }
        }
    }
    Err(MetisError::ProofInvalid)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    use crate::evidence::height;

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn transitivity_schema_admits_when_premises_exist() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let schema = TransformationSchema::equal_transitivity();
        let inst = TransformationInstance { premise_a: (a, b), premise_b: (b, c), conclusion: (a, c) };
        let evidence = evidence_from_two_premise(&g, &schema, &inst).unwrap();
        assert_eq!(height(&evidence), 1);
        let adm = replay_two_premise(&g, world(), &schema, &inst).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
        assert_eq!(adm.kind(), EdgeKind::Equal);
        assert!(adm.is_trusted_path_candidate());
    }

    #[test]
    fn transitivity_rejects_missing_premise() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        // missing b=c
        let schema = TransformationSchema::equal_transitivity();
        let inst = TransformationInstance { premise_a: (a, b), premise_b: (b, c), conclusion: (a, c) };
        assert_eq!(replay_two_premise(&g, world(), &schema, &inst).unwrap_err(), MetisError::ProofInvalid);
    }

    #[test]
    fn transitivity_rejects_tampered_wiring() {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let schema = TransformationSchema::equal_transitivity();
        let inst = TransformationInstance {
            premise_a: (a, b),
            premise_b: (b, c),
            conclusion: (a, b), // wrong conclusion
        };
        assert_eq!(replay_two_premise(&g, world(), &schema, &inst).unwrap_err(), MetisError::ProofInvalid);
    }
}
