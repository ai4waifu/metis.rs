//! Register interpreter for Metis bytecode.
//!
//! Owns execution lifecycle: frames, fuel, cancel, safepoint hooks, and GC root
//! orchestration contracts. Does **not** mint admitted tokens, mutate sealed
//! worlds, or depend on JIT. Kernel interaction goes through [`KernelView`].

use athena_gc::GcMode;
use metis_graph::{
    Graph,
    admission::WorldId,
    derivation_rules::EQUAL_TRANSITIVITY,
    evidence::{Evidence, JudgmentAtom, concluded_judgment},
};
use metis_ir::{Effect, Function, IrError, Module, Op, Reg, RegKind, RelationId, RuleId};
use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

pub use metis_ir::{REL_EQUAL, RULE_EQUAL_TRANSITIVITY, equal_transitivity_join_plan};

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
        Self { fuel, cancelled: false }
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
        Self { regs: f.regs.iter().map(|_| Slot::Empty).collect(), ip: 0 }
    }

    fn get(&self, r: Reg) -> Result<&Slot, VmError> {
        self.regs.get(r.0 as usize).ok_or(VmError::BadReg)
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
    fn load_evidence(&self, evidence: u64) -> Result<u64, VmError>;
    fn gen_from_edge(&mut self, edge: u64) -> Result<u64, VmError>;
    fn edge_target(&self, edge: u64) -> Result<NodeId, VmError>;
    fn scan_out(&mut self, node: NodeId, relation_filter: Option<RelationId>) -> Result<u32, VmError>;
    fn scan_in(&mut self, node: NodeId, relation_filter: Option<RelationId>) -> Result<u32, VmError>;
    fn next(&mut self, iter: u32) -> Result<Option<u64>, VmError>;
    fn check_premises(&self, rule: RuleId, tuple: u32, evidence: &[u64]) -> Result<bool, VmError>;
    fn build_evidence(&mut self, rule: RuleId, evidence: &[u64]) -> Result<u64, VmError>;
    fn emit_candidate(&mut self, relation: RelationId, evidence: u64) -> Result<(), VmError>;
    fn world_fingerprint(&self) -> u64;
}

#[derive(Clone, Debug)]
struct ScanCursor {
    /// Packed edge ids still to yield.
    edges: Vec<EdgeId>,
    cursor: usize,
}

/// Candidate evidence emitted by the VM for later Kernel replay / admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmittedCandidate {
    pub relation: RelationId,
    pub evidence: Evidence,
}

/// Minimal Kernel adapter over an in-memory [`Graph`].
///
/// Owns scan iterators and a scratch evidence table. Does **not** mint admitted tokens.
pub struct GraphKernel<'a> {
    pub graph: &'a Graph,
    pub world: WorldId,
    pub world_fingerprint: u64,
    relation_kinds: Vec<Option<EdgeKind>>,
    rule_names: Vec<Option<String>>,
    iterators: Vec<ScanCursor>,
    evidence: Vec<Evidence>,
    candidates: Vec<EmittedCandidate>,
}

impl<'a> GraphKernel<'a> {
    pub fn new(graph: &'a Graph, world: WorldId, world_fingerprint: u64) -> Self {
        let mut relation_kinds = vec![None; 8];
        relation_kinds[REL_EQUAL.0 as usize] = Some(EdgeKind::Equal);
        let mut rule_names = vec![None; 8];
        rule_names[RULE_EQUAL_TRANSITIVITY.0 as usize] = Some(EQUAL_TRANSITIVITY.into());
        Self {
            graph,
            world,
            world_fingerprint,
            relation_kinds,
            rule_names,
            iterators: Vec::new(),
            evidence: Vec::new(),
            candidates: Vec::new(),
        }
    }

    /// Insert `gen(edge)` into the scratch evidence table. Returns the handle.
    pub fn alloc_gen(&mut self, edge: EdgeId) -> Result<u64, VmError> {
        if !self.graph.is_judgment(edge)? {
            return Err(VmError::Metis(MetisError::ProofInvalid));
        }
        let id = self.evidence.len() as u64;
        self.evidence.push(Evidence::Gen { edge });
        Ok(id)
    }

    pub fn evidence(&self, id: u64) -> Option<&Evidence> {
        self.evidence.get(id as usize)
    }

    pub fn candidates(&self) -> &[EmittedCandidate] {
        &self.candidates
    }

    pub fn take_candidates(&mut self) -> Vec<EmittedCandidate> {
        std::mem::take(&mut self.candidates)
    }

    fn relation_kind(&self, id: RelationId) -> Result<EdgeKind, VmError> {
        self.relation_kinds.get(id.0 as usize).copied().flatten().ok_or(VmError::UnknownRelation)
    }

    fn rule_name(&self, id: RuleId) -> Result<&str, VmError> {
        self.rule_names.get(id.0 as usize).and_then(|s| s.as_deref()).ok_or(VmError::UnknownRule)
    }

    fn push_scan(&mut self, edges: Vec<EdgeId>) -> u32 {
        let id = self.iterators.len() as u32;
        self.iterators.push(ScanCursor { edges, cursor: 0 });
        id
    }

    fn filter_kind(&self, filter: Option<RelationId>) -> Result<Option<EdgeKind>, VmError> {
        match filter {
            None => Ok(None),
            Some(rel) => Ok(Some(self.relation_kind(rel)?)),
        }
    }

    /// Host-side Living `14` search: find `Equal(a,b)` and `Equal(b,c)`, build
    /// `app(equal_transitivity, …)`, emit a candidate. Does not admit.
    pub fn search_equal_transitivity(&mut self, a: NodeId, c: NodeId) -> Result<Option<u64>, VmError> {
        let outs = self.graph.judgment_outgoing_of_kind(a, EdgeKind::Equal)?;
        for (e_ab, b) in outs {
            let seconds = self.graph.judgment_outgoing_of_kind(b, EdgeKind::Equal)?;
            for (e_bc, nxt) in seconds {
                if nxt != c {
                    continue;
                }
                let g0 = self.alloc_gen(e_ab)?;
                let g1 = self.alloc_gen(e_bc)?;
                let ev = self.build_evidence(RULE_EQUAL_TRANSITIVITY, &[g0, g1])?;
                self.emit_candidate(REL_EQUAL, ev)?;
                return Ok(Some(ev));
            }
        }
        Ok(None)
    }
}

impl<'a> KernelView for GraphKernel<'a> {
    fn load_node(&self, node: NodeId) -> Result<NodeId, VmError> {
        if node.0 >= self.graph.node_count() as u64 {
            return Err(VmError::Metis(MetisError::NodeNotFound));
        }
        Ok(node)
    }

    fn load_evidence(&self, evidence: u64) -> Result<u64, VmError> {
        if (evidence as usize) >= self.evidence.len() {
            return Err(VmError::BadEvidence);
        }
        Ok(evidence)
    }

    fn gen_from_edge(&mut self, edge: u64) -> Result<u64, VmError> {
        self.alloc_gen(EdgeId(edge))
    }

    fn edge_target(&self, edge: u64) -> Result<NodeId, VmError> {
        let (_from, _kind, to) = self.graph.edge(EdgeId(edge))?;
        Ok(to)
    }

    fn scan_out(&mut self, node: NodeId, relation_filter: Option<RelationId>) -> Result<u32, VmError> {
        let want = self.filter_kind(relation_filter)?;
        let mut edges = Vec::new();
        for (edge, kind, _to) in self.graph.judgment_outgoing(node)? {
            if want.is_none_or(|k| k == kind) {
                edges.push(edge);
            }
        }
        Ok(self.push_scan(edges))
    }

    fn scan_in(&mut self, node: NodeId, relation_filter: Option<RelationId>) -> Result<u32, VmError> {
        let want = self.filter_kind(relation_filter)?;
        let mut edges = Vec::new();
        for (edge, kind, _from) in self.graph.judgment_incoming(node)? {
            if want.is_none_or(|k| k == kind) {
                edges.push(edge);
            }
        }
        Ok(self.push_scan(edges))
    }

    fn next(&mut self, iter: u32) -> Result<Option<u64>, VmError> {
        let cursor = self.iterators.get_mut(iter as usize).ok_or(VmError::BadIterator)?;
        if cursor.cursor >= cursor.edges.len() {
            return Ok(None);
        }
        let edge = cursor.edges[cursor.cursor];
        cursor.cursor += 1;
        Ok(Some(edge.0))
    }

    fn check_premises(&self, rule: RuleId, _tuple: u32, evidence: &[u64]) -> Result<bool, VmError> {
        let name = self.rule_name(rule)?;
        if name != EQUAL_TRANSITIVITY || evidence.len() != 2 {
            return Ok(false);
        }
        let e0 = self.evidence.get(evidence[0] as usize).ok_or(VmError::BadEvidence)?;
        let e1 = self.evidence.get(evidence[1] as usize).ok_or(VmError::BadEvidence)?;
        let j0 = concluded_judgment(self.graph, e0)?;
        let j1 = concluded_judgment(self.graph, e1)?;
        Ok(j0.kind == EdgeKind::Equal && j1.kind == EdgeKind::Equal && j0.endpoints.1 == j1.endpoints.0)
    }

    fn build_evidence(&mut self, rule: RuleId, evidence: &[u64]) -> Result<u64, VmError> {
        let name = self.rule_name(rule)?.to_string();
        if name != EQUAL_TRANSITIVITY {
            return Err(VmError::Unimplemented("BuildEvidence: non-EQ rule"));
        }
        if evidence.len() != 2 {
            return Err(VmError::Metis(MetisError::ProofInvalid));
        }
        let p0 = self.evidence.get(evidence[0] as usize).cloned().ok_or(VmError::BadEvidence)?;
        let p1 = self.evidence.get(evidence[1] as usize).cloned().ok_or(VmError::BadEvidence)?;
        let j0 = concluded_judgment(self.graph, &p0)?;
        let j1 = concluded_judgment(self.graph, &p1)?;
        if j0.kind != EdgeKind::Equal || j1.kind != EdgeKind::Equal || j0.endpoints.1 != j1.endpoints.0 {
            return Err(VmError::Metis(MetisError::ProofInvalid));
        }
        let conclusion = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (j0.endpoints.0, j1.endpoints.1) };
        let id = self.evidence.len() as u64;
        self.evidence.push(Evidence::App { rule: name, premises: vec![p0, p1], conclusion });
        Ok(id)
    }

    fn emit_candidate(&mut self, relation: RelationId, evidence: u64) -> Result<(), VmError> {
        let ev = self.evidence.get(evidence as usize).cloned().ok_or(VmError::BadEvidence)?;
        self.candidates.push(EmittedCandidate { relation, evidence: ev });
        Ok(())
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
    #[error("unknown relation id")]
    UnknownRelation,
    #[error("unknown rule id")]
    UnknownRule,
    #[error("bad iterator")]
    BadIterator,
    #[error("bad evidence handle")]
    BadEvidence,
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
        Self { budget: Budget::new(fuel), gc_mode: GcMode::default(), in_flight_roots: 0 }
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
    pub fn run(&mut self, module: &Module, kernel: &mut dyn KernelView) -> Result<VmStatus, VmError> {
        module.validate()?;
        let f = module.entry_function()?;
        self.enter_batch();
        let status = self.run_function(f, kernel);
        self.leave_batch();
        status
    }

    fn run_function(&mut self, f: &Function, kernel: &mut dyn KernelView) -> Result<VmStatus, VmError> {
        let mut frame = Frame::for_function(f);
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
                Op::LoadEvidence { dst, evidence } => {
                    let id = kernel.load_evidence(*evidence)?;
                    frame.set(*dst, Slot::Evidence(id))?;
                }
                Op::GenFromEdge { dst, edge } => {
                    let e = expect_value(frame.get(*edge)?)?;
                    let id = kernel.gen_from_edge(e)?;
                    frame.set(*dst, Slot::Evidence(id))?;
                }
                Op::EdgeTarget { dst, edge } => {
                    let e = expect_value(frame.get(*edge)?)?;
                    let n = kernel.edge_target(e)?;
                    frame.set(*dst, Slot::Node(n))?;
                }
                Op::Jump { target } => {
                    frame.ip = *target as usize;
                }
                Op::BranchIfEmpty { cond, target } => {
                    if matches!(frame.get(*cond)?, Slot::Empty) {
                        frame.ip = *target as usize;
                    }
                }
                Op::BranchIfFalse { cond, target } => {
                    if !expect_bool(frame.get(*cond)?)? {
                        frame.ip = *target as usize;
                    }
                }
                Op::NodesEqual { dst, left, right } => {
                    let a = expect_node(frame.get(*left)?)?;
                    let b = expect_node(frame.get(*right)?)?;
                    frame.set(*dst, Slot::Bool(a == b))?;
                }
                Op::ScanOut { iter, node, relation_filter } => {
                    require_effect(f, Effect::Query)?;
                    let n = expect_node(frame.get(*node)?)?;
                    let id = kernel.scan_out(n, *relation_filter)?;
                    frame.set(*iter, Slot::Iterator(id))?;
                }
                Op::ScanIn { iter, node, relation_filter } => {
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
                    frame.set(*dst, Slot::Bool(false))?;
                }
                Op::CheckPremises { rule, tuple, evidence_regs } => {
                    let t = expect_tuple(frame.get(*tuple)?)?;
                    let ev = read_evidence(&frame, evidence_regs)?;
                    let _ok = kernel.check_premises(*rule, t, &ev)?;
                }
                Op::BuildEvidence { dst, rule, evidence_regs } => {
                    let ev = read_evidence(&frame, evidence_regs)?;
                    let id = kernel.build_evidence(*rule, &ev)?;
                    frame.set(*dst, Slot::Evidence(id))?;
                }
                Op::EmitCandidate { relation, evidence } => {
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
    if f.effects.contains(&e) { Ok(()) } else { Err(VmError::EffectDenied) }
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

fn expect_value(s: &Slot) -> Result<u64, VmError> {
    match s {
        Slot::Value(v) => Ok(*v),
        Slot::Empty => Err(VmError::EmptyReg),
        _ => Err(VmError::SlotMismatch),
    }
}

fn expect_bool(s: &Slot) -> Result<bool, VmError> {
    match s {
        Slot::Bool(b) => Ok(*b),
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
    use core::num::NonZeroU32;
    use metis_graph::evidence::replay_evidence;
    use metis_ir::{Effect, Function, Module, Op, Reg, RegKind};
    use metis_types::{EdgeKind, IslandId};

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    fn equal_chain() -> (Graph, NodeId, NodeId, NodeId, EdgeId, EdgeId) {
        let mut g = Graph::new();
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        let e_ab = g.assert(a, EdgeKind::Equal, b).unwrap();
        let e_bc = g.assert(b, EdgeKind::Equal, c).unwrap();
        (g, a, b, c, e_ab, e_bc)
    }

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
        let mut kernel = GraphKernel::new(&graph, world(), 1);
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
                ops: vec![Op::GuardWorld { world_fingerprint: 99 }, Op::ReturnStatus { status: Reg(0) }],
            }],
        };
        let graph = Graph::default();
        let mut kernel = GraphKernel::new(&graph, world(), 1);
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
        let mut kernel = GraphKernel::new(&graph, world(), 1);
        let mut vm = Vm::new(0);
        assert_eq!(vm.run(&module, &mut kernel), Err(VmError::OutOfFuel));
    }

    #[test]
    fn scan_out_yields_equal_edges() {
        let (g, a, _b, _c, e_ab, _) = equal_chain();
        let mut kernel = GraphKernel::new(&g, world(), 1);
        let iter = kernel.scan_out(a, Some(REL_EQUAL)).unwrap();
        assert_eq!(kernel.next(iter).unwrap(), Some(e_ab.0));
        assert_eq!(kernel.next(iter).unwrap(), None);
    }

    #[test]
    fn search_equal_transitivity_emits_candidate_then_kernel_admits() {
        let (g, a, _b, c, _, _) = equal_chain();
        let mut kernel = GraphKernel::new(&g, world(), 1);
        let ev_id = kernel.search_equal_transitivity(a, c).unwrap().unwrap();
        let candidates = kernel.take_candidates();
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].relation, REL_EQUAL);
        let adm = replay_evidence(&g, world(), &candidates[0].evidence, &[]).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
        assert_eq!(kernel.evidence(ev_id).unwrap(), &candidates[0].evidence);
    }

    #[test]
    fn ir_build_evidence_emits_candidate_for_kernel_replay() {
        let (g, a, _b, c, e_ab, e_bc) = equal_chain();
        let mut kernel = GraphKernel::new(&g, world(), 1);
        let g0 = kernel.alloc_gen(e_ab).unwrap();
        let g1 = kernel.alloc_gen(e_bc).unwrap();

        // regs: e0, e1, app, status
        let module = Module {
            entry: 0,
            functions: vec![Function {
                name: "trans_app".into(),
                regs: vec![RegKind::Evidence, RegKind::Evidence, RegKind::Evidence, RegKind::Status],
                effects: vec![Effect::EmitCandidate],
                ops: vec![
                    Op::LoadEvidence { dst: Reg(0), evidence: g0 },
                    Op::LoadEvidence { dst: Reg(1), evidence: g1 },
                    Op::BuildEvidence { dst: Reg(2), rule: RULE_EQUAL_TRANSITIVITY, evidence_regs: vec![Reg(0), Reg(1)] },
                    Op::EmitCandidate { relation: REL_EQUAL, evidence: Reg(2) },
                    Op::ReturnStatus { status: Reg(3) },
                ],
            }],
        };

        let mut vm = Vm::new(64);
        assert_eq!(vm.run(&module, &mut kernel).unwrap(), VmStatus::Unknown);
        let candidates = kernel.take_candidates();
        assert_eq!(candidates.len(), 1);
        let adm = replay_evidence(&g, world(), &candidates[0].evidence, &[]).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
    }

    #[test]
    fn gen_from_edge_and_edge_target_from_scan() {
        let (g, a, b, _c, e_ab, _) = equal_chain();
        let mut kernel = GraphKernel::new(&g, world(), 1);
        // regs: node_a, iter, edge_val, mid, gen0, status
        let module = Module {
            entry: 0,
            functions: vec![Function {
                name: "scan_gen".into(),
                regs: vec![RegKind::Node, RegKind::Iterator, RegKind::Value, RegKind::Node, RegKind::Evidence, RegKind::Status],
                effects: vec![Effect::Query],
                ops: vec![
                    Op::LoadNode { dst: Reg(0), node: a },
                    Op::ScanOut { iter: Reg(1), node: Reg(0), relation_filter: Some(REL_EQUAL) },
                    Op::Next { dst: Reg(2), iter: Reg(1) },
                    Op::EdgeTarget { dst: Reg(3), edge: Reg(2) },
                    Op::GenFromEdge { dst: Reg(4), edge: Reg(2) },
                    Op::ReturnStatus { status: Reg(5) },
                ],
            }],
        };
        let mut vm = Vm::new(64);
        assert_eq!(vm.run(&module, &mut kernel).unwrap(), VmStatus::Unknown);
        let ev = kernel.evidence(0).unwrap();
        assert_eq!(ev, &Evidence::Gen { edge: e_ab });
        let (_f, _k, to) = g.edge(e_ab).unwrap();
        assert_eq!(to, b);
    }

    #[test]
    fn ir_nested_scan_proves_equal_transitivity_candidate() {
        let (g, a, _b, c, _, _) = equal_chain();
        let mut kernel = GraphKernel::new(&g, world(), 1);
        let module = equal_transitivity_join_plan(a, c);
        module.validate().unwrap();
        let mut vm = Vm::new(256);
        assert_eq!(vm.run(&module, &mut kernel).unwrap(), VmStatus::Unknown);
        let candidates = kernel.take_candidates();
        assert_eq!(candidates.len(), 1);
        let adm = replay_evidence(&g, world(), &candidates[0].evidence, &[]).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
    }
}
