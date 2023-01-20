//! Hand-authored foundation plans (compile lowering lands later).

use crate::{Effect, Function, Module, Op, Reg, RegKind, RelationId, RuleId};
use metis_types::NodeId;

/// Foundation relation id for judgment `Equal` scans (shared with VM host).
pub const REL_EQUAL: RelationId = RelationId(1);
/// Foundation rule id for Equal transitivity.
pub const RULE_EQUAL_TRANSITIVITY: RuleId = RuleId(1);

/// Nested scan plan: find `Equal(a,y)` and `Equal(y,c)`, build transitivity evidence, emit candidate.
///
/// Does **not** admit. VM status stays `Unknown` until Kernel replay.
pub fn equal_transitivity_join_plan(a: NodeId, c: NodeId) -> Module {
    // regs: 0 a, 1 c, 2 iter1, 3 e1, 4 y, 5 g1, 6 iter2, 7 e2, 8 z, 9 eq, 10 g2, 11 app, 12 status
    Module {
        entry: 0,
        functions: vec![Function {
            name: "equal_transitivity_join".into(),
            regs: vec![
                RegKind::Node,
                RegKind::Node,
                RegKind::Iterator,
                RegKind::Value,
                RegKind::Node,
                RegKind::Evidence,
                RegKind::Iterator,
                RegKind::Value,
                RegKind::Node,
                RegKind::Bool,
                RegKind::Evidence,
                RegKind::Evidence,
                RegKind::Status,
            ],
            effects: vec![Effect::Query, Effect::EmitCandidate],
            ops: vec![
                Op::LoadNode { dst: Reg(0), node: a },
                Op::LoadNode { dst: Reg(1), node: c },
                Op::ScanOut { iter: Reg(2), node: Reg(0), relation_filter: Some(REL_EQUAL) },
                Op::Next { dst: Reg(3), iter: Reg(2) },
                Op::BranchIfEmpty { cond: Reg(3), target: 18 },
                Op::EdgeTarget { dst: Reg(4), edge: Reg(3) },
                Op::GenFromEdge { dst: Reg(5), edge: Reg(3) },
                Op::ScanOut { iter: Reg(6), node: Reg(4), relation_filter: Some(REL_EQUAL) },
                Op::Next { dst: Reg(7), iter: Reg(6) },
                Op::BranchIfEmpty { cond: Reg(7), target: 3 },
                Op::EdgeTarget { dst: Reg(8), edge: Reg(7) },
                Op::NodesEqual { dst: Reg(9), left: Reg(8), right: Reg(1) },
                Op::BranchIfFalse { cond: Reg(9), target: 8 },
                Op::GenFromEdge { dst: Reg(10), edge: Reg(7) },
                Op::BuildEvidence { dst: Reg(11), rule: RULE_EQUAL_TRANSITIVITY, evidence_regs: vec![Reg(5), Reg(10)] },
                Op::EmitCandidate { relation: REL_EQUAL, evidence: Reg(11) },
                Op::Jump { target: 19 },
                Op::ReturnStatus { status: Reg(12) },
                Op::ReturnStatus { status: Reg(12) },
                Op::ReturnStatus { status: Reg(12) },
            ],
        }],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn join_plan_validates() {
        equal_transitivity_join_plan(NodeId(0), NodeId(2)).validate().unwrap();
    }
}
