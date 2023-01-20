//! Typed relation plans and bytecode for Metis.
//!
//! This crate owns plan structure, register kinds, effects, and structural
//! validation. It does **not** hold an active heap, parse source, execute
//! instructions, or define admission. Interpreter and JIT share this IR.

mod plans;

pub use plans::{REL_EQUAL, RULE_EQUAL_TRANSITIVITY, equal_transitivity_join_plan};

use metis_types::NodeId;

/// Dense register index within a plan frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Reg(pub u16);

/// Opaque relation identity referenced by bytecode (Kernel-owned payload).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RelationId(pub u32);

/// Opaque derivation-rule identity for premise checks / evidence build.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RuleId(pub u32);

/// Opaque M-Link / W-Link handle for transport / view switches.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LinkId(pub u32);

/// What a register is allowed to hold at plan validate time.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegKind {
    Node,
    Relation,
    Evidence,
    Iterator,
    Tuple,
    Status,
    Value,
    Bool,
}

/// Side effects a plan may declare. Kernel admission is never an IR effect.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Effect {
    /// Read-only graph / world queries.
    Query,
    /// Produce candidate evidence for later Kernel admission.
    EmitCandidate,
    /// Observe through a registered world morphism (no mint of trusted π_T).
    TransportView,
}

/// First-generation bytecode opcodes (Living `13`).
///
/// `Admit` is intentionally absent: only Kernel admission casts results.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    LoadNode {
        dst: Reg,
        node: NodeId,
    },
    LoadRelation {
        dst: Reg,
        relation: RelationId,
    },
    /// Load a host-table evidence handle into a register (index from prior `alloc_gen` / search).
    LoadEvidence {
        dst: Reg,
        evidence: u64,
    },
    /// `gen(edge)` from a Value register holding an [`EdgeId`] raw (`Next` yield).
    GenFromEdge {
        dst: Reg,
        edge: Reg,
    },
    /// Target endpoint of an edge Value → Node register.
    EdgeTarget {
        dst: Reg,
        edge: Reg,
    },
    /// Unconditional jump to instruction index (within the same function).
    Jump {
        target: u32,
    },
    /// If `cond` holds an empty slot (iterator exhausted after `Next`), jump; else fall through.
    BranchIfEmpty {
        cond: Reg,
        target: u32,
    },
    /// If boolean `cond` is false, jump; else fall through.
    BranchIfFalse {
        cond: Reg,
        target: u32,
    },
    /// Compare two Node registers → Bool.
    NodesEqual {
        dst: Reg,
        left: Reg,
        right: Reg,
    },
    ScanOut {
        iter: Reg,
        node: Reg,
        relation_filter: Option<RelationId>,
    },
    ScanIn {
        iter: Reg,
        node: Reg,
        relation_filter: Option<RelationId>,
    },
    Next {
        dst: Reg,
        iter: Reg,
    },
    Match {
        dst: Reg,
        /// Pattern table index resolved by the host / compile unit.
        pattern: u32,
        tuple: Reg,
    },
    CheckPremises {
        rule: RuleId,
        tuple: Reg,
        evidence_regs: Vec<Reg>,
    },
    BuildEvidence {
        dst: Reg,
        rule: RuleId,
        evidence_regs: Vec<Reg>,
    },
    EmitCandidate {
        relation: RelationId,
        evidence: Reg,
    },
    TransportView {
        dst: Reg,
        m_link: LinkId,
        source: Reg,
    },
    SwitchView {
        dst: Reg,
        w_link: LinkId,
        observation: Reg,
    },
    GuardWorld {
        /// Host-resolved world fingerprint expected at entry.
        world_fingerprint: u64,
    },
    ReturnStatus {
        status: Reg,
    },
}

/// One validated function body: register file layout + instruction stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub regs: Vec<RegKind>,
    pub ops: Vec<Op>,
    pub effects: Vec<Effect>,
}

/// Top-level plan module shared by VM and JIT.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Module {
    pub functions: Vec<Function>,
    /// Entry function index into [`Module::functions`].
    pub entry: u32,
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum IrError {
    #[error("empty module")]
    EmptyModule,
    #[error("entry index out of range")]
    BadEntry,
    #[error("register index out of range")]
    BadReg,
    #[error("register kind mismatch")]
    RegKindMismatch,
    #[error("effect not declared")]
    UndeclaredEffect,
    #[error("jump target out of range")]
    BadJump,
    #[error("function has no return")]
    MissingReturn,
}

impl Module {
    /// Structural validation only: bounds, kinds, declared effects, return.
    pub fn validate(&self) -> Result<(), IrError> {
        if self.functions.is_empty() {
            return Err(IrError::EmptyModule);
        }
        let entry = self.entry as usize;
        if entry >= self.functions.len() {
            return Err(IrError::BadEntry);
        }
        for f in &self.functions {
            validate_function(f)?;
        }
        Ok(())
    }

    pub fn entry_function(&self) -> Result<&Function, IrError> {
        self.functions.get(self.entry as usize).ok_or(IrError::BadEntry)
    }
}

fn validate_function(f: &Function) -> Result<(), IrError> {
    let n = f.regs.len();
    let has = |r: Reg| (r.0 as usize) < n;
    let kind = |r: Reg| -> Result<RegKind, IrError> { f.regs.get(r.0 as usize).copied().ok_or(IrError::BadReg) };
    let expect = |r: Reg, want: RegKind| -> Result<(), IrError> {
        if kind(r)? != want {
            return Err(IrError::RegKindMismatch);
        }
        Ok(())
    };
    let need_effect =
        |e: Effect| -> Result<(), IrError> { if f.effects.contains(&e) { Ok(()) } else { Err(IrError::UndeclaredEffect) } };

    let mut saw_return = false;
    for op in &f.ops {
        match op {
            Op::LoadNode { dst, .. } => {
                if !has(*dst) {
                    return Err(IrError::BadReg);
                }
                expect(*dst, RegKind::Node)?;
            }
            Op::LoadRelation { dst, .. } => {
                if !has(*dst) {
                    return Err(IrError::BadReg);
                }
                expect(*dst, RegKind::Relation)?;
            }
            Op::LoadEvidence { dst, .. } => {
                if !has(*dst) {
                    return Err(IrError::BadReg);
                }
                expect(*dst, RegKind::Evidence)?;
            }
            Op::GenFromEdge { dst, edge } => {
                expect(*dst, RegKind::Evidence)?;
                expect(*edge, RegKind::Value)?;
            }
            Op::EdgeTarget { dst, edge } => {
                expect(*dst, RegKind::Node)?;
                expect(*edge, RegKind::Value)?;
            }
            Op::Jump { target } => {
                if (*target as usize) >= f.ops.len() {
                    return Err(IrError::BadJump);
                }
            }
            Op::BranchIfEmpty { cond, target } => {
                expect(*cond, RegKind::Value)?;
                if (*target as usize) >= f.ops.len() {
                    return Err(IrError::BadJump);
                }
            }
            Op::BranchIfFalse { cond, target } => {
                expect(*cond, RegKind::Bool)?;
                if (*target as usize) >= f.ops.len() {
                    return Err(IrError::BadJump);
                }
            }
            Op::NodesEqual { dst, left, right } => {
                expect(*dst, RegKind::Bool)?;
                expect(*left, RegKind::Node)?;
                expect(*right, RegKind::Node)?;
            }
            Op::ScanOut { iter, node, .. } | Op::ScanIn { iter, node, .. } => {
                need_effect(Effect::Query)?;
                expect(*iter, RegKind::Iterator)?;
                expect(*node, RegKind::Node)?;
            }
            Op::Next { dst, iter } => {
                need_effect(Effect::Query)?;
                expect(*dst, RegKind::Value)?;
                expect(*iter, RegKind::Iterator)?;
            }
            Op::Match { dst, tuple, .. } => {
                expect(*dst, RegKind::Bool)?;
                expect(*tuple, RegKind::Tuple)?;
            }
            Op::CheckPremises { tuple, evidence_regs, .. } => {
                expect(*tuple, RegKind::Tuple)?;
                for r in evidence_regs {
                    expect(*r, RegKind::Evidence)?;
                }
            }
            Op::BuildEvidence { dst, evidence_regs, .. } => {
                expect(*dst, RegKind::Evidence)?;
                for r in evidence_regs {
                    expect(*r, RegKind::Evidence)?;
                }
            }
            Op::EmitCandidate { evidence, .. } => {
                need_effect(Effect::EmitCandidate)?;
                expect(*evidence, RegKind::Evidence)?;
            }
            Op::TransportView { dst, source, .. } => {
                need_effect(Effect::TransportView)?;
                expect(*dst, RegKind::Value)?;
                expect(*source, RegKind::Value)?;
            }
            Op::SwitchView { dst, observation, .. } => {
                need_effect(Effect::TransportView)?;
                expect(*dst, RegKind::Value)?;
                expect(*observation, RegKind::Value)?;
            }
            Op::GuardWorld { .. } => {}
            Op::ReturnStatus { status } => {
                expect(*status, RegKind::Status)?;
                saw_return = true;
            }
        }
    }
    if !saw_return {
        return Err(IrError::MissingReturn);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn status_only() -> Module {
        Module {
            entry: 0,
            functions: vec![Function {
                name: "status".into(),
                regs: vec![RegKind::Status],
                effects: vec![],
                ops: vec![Op::ReturnStatus { status: Reg(0) }],
            }],
        }
    }

    #[test]
    fn validates_minimal_return() {
        status_only().validate().unwrap();
    }

    #[test]
    fn rejects_undeclared_emit() {
        let m = Module {
            entry: 0,
            functions: vec![Function {
                name: "bad".into(),
                regs: vec![RegKind::Evidence, RegKind::Status],
                effects: vec![],
                ops: vec![Op::EmitCandidate { relation: RelationId(1), evidence: Reg(0) }, Op::ReturnStatus { status: Reg(1) }],
            }],
        };
        assert_eq!(m.validate(), Err(IrError::UndeclaredEffect));
    }

    #[test]
    fn rejects_missing_return() {
        let m = Module {
            entry: 0,
            functions: vec![Function {
                name: "bad".into(),
                regs: vec![RegKind::Node],
                effects: vec![],
                ops: vec![Op::LoadNode { dst: Reg(0), node: NodeId(1) }],
            }],
        };
        assert_eq!(m.validate(), Err(IrError::MissingReturn));
    }
}
