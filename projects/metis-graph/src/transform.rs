//! Relation transformation schemas (Living Core constitution).
//!
//! A transformation is not a method on objects. It is:
//! premise relation patterns → boundary-preserving rewrite → conclusion pattern.
//! This module ships the **two-premise** skeleton used by the first Core acceptance slice.

use metis_types::{EdgeKind, MetisError, NodeId};

use super::admission::{AdmittedRelation, WorldId};
use super::Graph;

/// Pattern for one premise judgment: `kind(from, to)` with optional fixed endpoints.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PremisePattern {
    pub kind: EdgeKind,
    /// If set, the source endpoint must match this node.
    pub from: Option<NodeId>,
    /// If set, the target endpoint must match this node.
    pub to: Option<NodeId>,
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
            name: "equal_transitivity".into(),
            premise_a: PremisePattern { kind: EdgeKind::Equal, from: None, to: None },
            premise_b: PremisePattern { kind: EdgeKind::Equal, from: None, to: None },
            conclusion_kind: EdgeKind::Equal,
        }
    }

    /// Check that an instance matches this schema's shape (shared middle node for transitivity).
    pub fn matches_instance(&self, inst: &TransformationInstance) -> bool {
        if self.name == "equal_transitivity" {
            let (x, y1) = inst.premise_a;
            let (y2, z) = inst.premise_b;
            let (cx, cz) = inst.conclusion;
            return y1 == y2 && cx == x && cz == z;
        }
        // Generic: just require declared kinds; endpoint wiring left to replay against the graph.
        true
    }
}

/// Replay a two-premise instance: both premises must already be judgment edges in `graph`.
///
/// On success, mints an [`AdmittedRelation`] for the conclusion under `world`.
/// Does **not** insert the conclusion edge — admission is epistemic, not mutation.
pub fn replay_two_premise(
    graph: &Graph,
    world: WorldId,
    schema: &TransformationSchema,
    inst: &TransformationInstance,
) -> Result<AdmittedRelation, MetisError> {
    if !schema.matches_instance(inst) {
        return Err(MetisError::ProofInvalid);
    }
    ensure_judgment(graph, schema.premise_a.kind, inst.premise_a)?;
    ensure_judgment(graph, schema.premise_b.kind, inst.premise_b)?;
    // Conclusion must be entailed by the schema wiring; for equal_transitivity the path x-y-z exists.
    if schema.name == "equal_transitivity" {
        let (x, z) = inst.conclusion;
        if graph.find_equal_path(x, z)?.is_none() {
            return Err(MetisError::ProofInvalid);
        }
    }
    let tag = fingerprint_instance(world, schema, inst);
    Ok(AdmittedRelation::bootstrap_unchecked(world, inst.conclusion, tag))
}

fn ensure_judgment(graph: &Graph, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> Result<(), MetisError> {
    let (from, to) = endpoints;
    for (eid, k, nxt) in graph.judgment_outgoing(from)? {
        if k == kind && nxt == to && graph.is_judgment(eid)? {
            return Ok(());
        }
    }
    // Symmetric Equal: allow reverse witness.
    if kind == EdgeKind::Equal {
        for (eid, k, nxt) in graph.judgment_outgoing(to)? {
            if k == EdgeKind::Equal && nxt == from && graph.is_judgment(eid)? {
                return Ok(());
            }
        }
    }
    Err(MetisError::ProofInvalid)
}

fn fingerprint_instance(world: WorldId, schema: &TransformationSchema, inst: &TransformationInstance) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for x in [
        world.island.get() as u64,
        world.version,
        inst.premise_a.0 .0,
        inst.premise_a.1 .0,
        inst.premise_b.0 .0,
        inst.premise_b.1 .0,
        inst.conclusion.0 .0,
        inst.conclusion.1 .0,
        schema.name.len() as u64,
    ] {
        h ^= x;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

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
        let inst = TransformationInstance {
            premise_a: (a, b),
            premise_b: (b, c),
            conclusion: (a, c),
        };
        let adm = replay_two_premise(&g, world(), &schema, &inst).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
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
        let inst = TransformationInstance {
            premise_a: (a, b),
            premise_b: (b, c),
            conclusion: (a, c),
        };
        assert_eq!(
            replay_two_premise(&g, world(), &schema, &inst).unwrap_err(),
            MetisError::ProofInvalid
        );
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
        assert_eq!(
            replay_two_premise(&g, world(), &schema, &inst).unwrap_err(),
            MetisError::ProofInvalid
        );
    }
}
