//! Register interpreter for Metis bytecode.
//!
//! Owns execution lifecycle: frames, fuel, cancel, safepoint hooks, and GC root
//! orchestration contracts. Does **not** mint admitted tokens, mutate sealed
//! worlds, or depend on JIT. Kernel interaction goes through [`KernelView`].

use athena_gc::GcMode;
use metis_graph::Graph;
use metis_ir::{Effect, Function, IrError, Module, Op, Reg, RegKind, RelationId, RuleId};
use metis_types::{MetisError, NodeId};

/// Query / plan outcome surface aligned with Metis four-state answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmStatus {
    Proven,
    Refuted,
    Unknown,
    Inconsistent,
    /// Plan finished without writing a status register (should not happen
    /// after IR validation).
    Halted,
}

/// Fuel and cancel knobs for one interpreter batch.
#[derive(Clone, Debug)]
pub struct Budget {
    pub fuel: u64,
    pub cancelled: bool,
}

impl Budget {
    pub fn new(fuel: u64) -> Self {
        Self {
            fuel,
            cancelled: false,
        }
    }

    pub fn tick(&mut self) -> Result<(), VmError> {
        if self.cancelled {
            return Err(VmError::Cancelled);
        }
        if self.fuel == 0 {
            return Err(VmError::OutOfFuel);
        }
        self.fuel -= 1;
        Ok(())
    }
}

/// Runtime register payload. Persistent objects stay Kernel / GC owned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Slot {
    Empty,
    Node(NodeId),
    Relation(RelationId),
    Evidence(u64),
    Iterator(u32),
    Tuple(u32),
    Status(VmStatus),
    Value(u64),
    Bool(bool),
}

/// One activation record.
#[derive(Clone, Debug)]
pub struct Frame {
    pub regs: Vec<Slot>,
    pub ip: usize,
}

impl Frame {
    pub fn for_function(f: &Function) -> Self {
        Self {
            regs: f.regs.iter().map(|_| Slot::Empty).collect(),
            ip: 0,
        }
    }

    fn get(&self, r: Reg) -> Result<&Slot, VmError> {
        self.regs
            .get(r.0 as usize)
            .ok_or(VmError::BadReg)
    }

    fn set(&mut self, r: Reg, v: Slot) -> Result<(), VmError> {
        let slot = self.regs.get_mut(r.0 as usize).ok_or(VmError::BadReg)?;
        *slot = v;
        Ok(())
    }
}

/// Host callbacks into Kernel-owned storage. Admission is never exposed here.
pub trait KernelView {
    fn load_node(&self, node: NodeId) -> Result<NodeId, VmError>;
    fn scan_out(
        &mut self,
        node: NodeId,
        relation_filter: Option<RelationId>,
    ) -> Result<u32, VmError>;
    fn scan_in(
        &mut self,
        node: NodeId,
        relation_filter: Option<RelationId>,
    ) -> Result<u32, VmError>;
    fn next(&mut self, iter: u32) -> Result<Option<u64>, VmError>;
    fn check_premises(
        &self,
        rule: RuleId,
        tuple: u32,
        evidence: &[u64],
    ) -> Result<bool, VmError>;
    fn build_evidence(
        &mut self,
        rule: RuleId,
        evidence: &[u64],
    ) -> Result<u64, VmError>;
    fn emit_candidate(&mut self, relation: RelationId, evidence: u64) -> Result<(), VmError>;
    fn world_fingerprint(&self) -> u64;
}

/// Minimal Kernel adapter over an in-memory [`Graph`].
///
/// Scan / evidence paths stay stubs until GC-backed World wiring lands.
pub struct GraphKernel<'a> {
    pub graph: &'a Graph,
    pub world_fingerprint: u64,
}

impl<'a> KernelView for GraphKernel<'a> {
    fn load_node(&self, node: NodeId) -> Result<NodeId, VmError> {
        let _ = self.graph;
        Ok(node)
    }

    fn scan_out(
        &mut self,
        _node: NodeId,
        _relation_filter: Option<RelationId>,
    ) -> Result<u32, VmError> {
        Err(VmError::Unimplemented("ScanOut"))
    }

    fn scan_in(
        &mut self,
        _node: NodeId,
        _relation_filter: Option<RelationId>,
    ) -> Result<u32, VmError> {
        Err(VmError::Unimplemented("ScanIn"))
    }

    fn next(&mut self, _iter: u32) -> Result<Option<u64>, VmError> {
        Err(VmError::Unimplemented("Next"))
    }

    fn check_premises(
        &self,
        _rule: RuleId,
        _tuple: u32,
        _evidence: &[u64],
    ) -> Result<bool, VmError> {
        Err(VmError::Unimplemented("CheckPremises"))
    }

    fn build_evidence(
        &mut self,
        _rule: RuleId,
        _evidence: &[u64],
    ) -> Result<u64, VmError> {
        Err(VmError::Unimplemented("BuildEvidence"))
    }

    fn emit_candidate(
        &mut self,
        _relation: RelationId,
        _evidence: u64,
    ) -> Result<(), VmError> {
        Err(VmError::Unimplemented("EmitCandidate"))
    }

    fn world_fingerprint(&self) -> u64 {
        self.world_fingerprint
    }
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum VmError {
    #[error(transparent)]
    Ir(#[from] IrError),
    #[error("register out of range")]
    BadReg,
    #[error("empty register")]
    EmptyReg,
    #[error("slot kind mismatch")]
    SlotMismatch,
    #[error("out of fuel")]
    OutOfFuel,
    #[error("cancelled")]
    Cancelled,
    #[error("world guard failed")]
    WorldGuard,
    #[error("effect not allowed at runtime")]
    EffectDenied,
    #[error("unimplemented opcode host path: {0}")]
    Unimplemented(&'static str),
    #[error("metis error: {0}")]
    Metis(#[from] MetisError),
}

/// Interpreter batch state. GC mode is recorded for future root orchestration.
pub struct Vm {
    pub budget: Budget,
    pub gc_mode: GcMode,
    /// Placeholder for InFlight root tokens once plans live on `athena-gc`.
    pub in_flight_roots: u32,
}

impl Vm {
    pub fn new(fuel: u64) -> Self {
        Self {
            budget: Budget::new(fuel),
            gc_mode: GcMode::default(),
            in_flight_roots: 0,
        }
    }

    /// Enter a kernel batch: register InFlight roots (count stub for now).
    pub fn enter_batch(&mut self) {
        self.in_flight_roots = self.in_flight_roots.saturating_add(1);
    }

    /// Leave a kernel batch and drop temporary roots.
    pub fn leave_batch(&mut self) {
        self.in_flight_roots = self.in_flight_roots.saturating_sub(1);
    }

    /// Cooperative safepoint: fuel tick + cancel check.
    pub fn safepoint(&mut self) -> Result<(), VmError> {
        self.budget.tick()
    }

    /// Validate then run the module entry function against `kernel`.
    pub fn run(
        &mut self,
        module: &Module,
        kernel: &mut dyn KernelView,
    ) -> Result<VmStatus, VmError> {
        module.validate()?;
        let f = module.entry_function()?;
        self.enter_batch();
        let status = self.run_function(f, kernel);
        self.leave_batch();
        status
    }

    fn run_function(
        &mut self,
        f: &Function,
        kernel: &mut dyn KernelView,
    ) -> Result<VmStatus, VmError> {
        let mut frame = Frame::for_function(f);
        // Default status register to Unknown when present.
        for (i, kind) in f.regs.iter().enumerate() {
            if *kind == RegKind::Status {
                frame.regs[i] = Slot::Status(VmStatus::Unknown);
            }
        }

        while frame.ip < f.ops.len() {
            self.safepoint()?;
            let op = &f.ops[frame.ip];
            frame.ip += 1;
            match op {
                Op::LoadNode { dst, node } => {
                    let n = kernel.load_node(*node)?;
                    frame.set(*dst, Slot::Node(n))?;
                }
                Op::LoadRelation { dst, relation } => {
                    frame.set(*dst, Slot::Relation(*relation))?;
                }
                Op::ScanOut {
                    iter,
                    node,
                    relation_filter,
                } => {
                    require_effect(f, Effect::Query)?;
                    let n = expect_node(frame.get(*node)?)?;
                    let id = kernel.scan_out(n, *relation_filter)?;
                    frame.set(*iter, Slot::Iterator(id))?;
                }
                Op::ScanIn {
                    iter,
                    node,
                    relation_filter,
                } => {
                    require_effect(f, Effect::Query)?;
                    let n = expect_node(frame.get(*node)?)?;
                    let id = kernel.scan_in(n, *relation_filter)?;
                    frame.set(*iter, Slot::Iterator(id))?;
                }
                Op::Next { dst, iter } => {
                    require_effect(f, Effect::Query)?;
                    let id = expect_iter(frame.get(*iter)?)?;
                    match kernel.next(id)? {
                        Some(v) => frame.set(*dst, Slot::Value(v))?,
                        None => frame.set(*dst, Slot::Empty)?,
                    }
                }
                Op::Match { dst, .. } => {
                    // Pattern tables arrive with compile units later.
                    frame.set(*dst, Slot::Bool(false))?;
                }
                Op::CheckPremises {
                    rule,
                    tuple,
                    evidence_regs,
                } => {
                    let t = expect_tuple(frame.get(*tuple)?)?;
                    let ev = read_evidence(&frame, evidence_regs)?;
                    let _ok = kernel.check_premises(*rule, t, &ev)?;
                }
                Op::BuildEvidence {
                    dst,
                    rule,
                    evidence_regs,
                } => {
                    let ev = read_evidence(&frame, evidence_regs)?;
                    let id = kernel.build_evidence(*rule, &ev)?;
                    frame.set(*dst, Slot::Evidence(id))?;
                }
                Op::EmitCandidate {
                    relation,
                    evidence,
                } => {
                    require_effect(f, Effect::EmitCandidate)?;
                    let ev = expect_evidence(frame.get(*evidence)?)?;
                    kernel.emit_candidate(*relation, ev)?;
                }
                Op::TransportView { dst, .. } => {
                    require_effect(f, Effect::TransportView)?;
                    frame.set(*dst, Slot::Value(0))?;
                }
                Op::SwitchView { dst, .. } => {
                    require_effect(f, Effect::TransportView)?;
                    frame.set(*dst, Slot::Value(0))?;
                }
                Op::GuardWorld { world_fingerprint } => {
                    if kernel.world_fingerprint() != *world_fingerprint {
                        return Err(VmError::WorldGuard);
                    }
                }
                Op::ReturnStatus { status } => {
                    return Ok(expect_status(frame.get(*status)?)?);
                }
            }
        }
        Ok(VmStatus::Halted)
    }
}

fn require_effect(f: &Function, e: Effect) -> Result<(), VmError> {
    if f.effects.contains(&e) {
        Ok(())
    } else {
        Err(VmError::EffectDenied)
    }
}

fn expect_node(s: &Slot) -> Result<NodeId, VmError> {
    match s {
        Slot::Node(n) => Ok(*n),
        Slot::Empty => Err(VmError::EmptyReg),
        _ => Err(VmError::SlotMismatch),
    }
}

fn expect_iter(s: &Slot) -> Result<u32, VmError> {
    match s {
        Slot::Iterator(i) => Ok(*i),
        Slot::Empty => Err(VmError::EmptyReg),
        _ => Err(VmError::SlotMismatch),
    }
}

fn expect_tuple(s: &Slot) -> Result<u32, VmError> {
    match s {
        Slot::Tuple(t) => Ok(*t),
        Slot::Empty => Err(VmError::EmptyReg),
        _ => Err(VmError::SlotMismatch),
    }
}

fn expect_evidence(s: &Slot) -> Result<u64, VmError> {
    match s {
        Slot::Evidence(e) => Ok(*e),
        Slot::Empty => Err(VmError::EmptyReg),
        _ => Err(VmError::SlotMismatch),
    }
}

fn expect_status(s: &Slot) -> Result<VmStatus, VmError> {
    match s {
        Slot::Status(st) => Ok(*st),
        Slot::Empty => Err(VmError::EmptyReg),
        _ => Err(VmError::SlotMismatch),
    }
}

fn read_evidence(frame: &Frame, regs: &[Reg]) -> Result<Vec<u64>, VmError> {
    let mut out = Vec::with_capacity(regs.len());
    for r in regs {
        out.push(expect_evidence(frame.get(*r)?)?);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use metis_ir::{Function, Module, Op, Reg, RegKind};

    #[test]
    fn runs_status_return() {
        let module = Module {
            entry: 0,
            functions: vec![Function {
                name: "status".into(),
                regs: vec![RegKind::Status],
                effects: vec![],
                ops: vec![Op::ReturnStatus { status: Reg(0) }],
            }],
        };
        let graph = Graph::default();
        let mut kernel = GraphKernel {
            graph: &graph,
            world_fingerprint: 1,
        };
        let mut vm = Vm::new(32);
        assert_eq!(vm.run(&module, &mut kernel).unwrap(), VmStatus::Unknown);
        assert_eq!(vm.in_flight_roots, 0);
    }

    #[test]
    fn world_guard_rejects_mismatch() {
        let module = Module {
            entry: 0,
            functions: vec![Function {
                name: "guard".into(),
                regs: vec![RegKind::Status],
                effects: vec![],
                ops: vec![
                    Op::GuardWorld {
                        world_fingerprint: 99,
                    },
                    Op::ReturnStatus { status: Reg(0) },
                ],
            }],
        };
        let graph = Graph::default();
        let mut kernel = GraphKernel {
            graph: &graph,
            world_fingerprint: 1,
        };
        let mut vm = Vm::new(32);
        assert_eq!(vm.run(&module, &mut kernel), Err(VmError::WorldGuard));
    }

    #[test]
    fn fuel_exhaustion_stops() {
        let module = Module {
            entry: 0,
            functions: vec![Function {
                name: "status".into(),
                regs: vec![RegKind::Status],
                effects: vec![],
                ops: vec![Op::ReturnStatus { status: Reg(0) }],
            }],
        };
        let graph = Graph::default();
        let mut kernel = GraphKernel {
            graph: &graph,
            world_fingerprint: 1,
        };
        let mut vm = Vm::new(0);
        assert_eq!(vm.run(&module, &mut kernel), Err(VmError::OutOfFuel));
    }
}
