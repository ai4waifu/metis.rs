//! Stable Metis facade.

pub use athena_gc::{GcHeap, HeapBudget};
pub use metis_compile::{LoweringResult, compile_declarations, lower_module, parse_source};
pub use metis_graph::{
    EdgePayload, Graph, NodePayload, Step,
    admission::{
        AdmittedRelation, AdmittedWorld, CandidateRelation, ConflictReport, JudgmentLane, ObservationBoundary, QueryStatus,
        WorldId, query_status_of_admitted, unknown_if_missing,
    },
    closure::{
        phi_equal_step, phi_rule_table_step, saturate_equal_inner, saturate_rule_table_inner, seed_declared_generators,
        seed_equal_generators,
    },
    conflict::{Incompatibility, detect_judgment_conflict, query_under_incompatibility},
    connection::{
        AdmittedConnection, CandidateConnection, ConnectionClass, RegisteredMLink, TransportWitness, admit_connection,
        bidirectional_skeleton, bootstrap_transport_relation, bootstrap_transport_relation_asserting, compose_connections,
        identity_morphism, refuse_galois_without_proof, transport_query_status, transport_relation,
        transport_relation_asserting, transport_relation_trusted, validate_candidate,
    },
    derivation::{
        DerivationDiagram, replay_equal_derivation, replay_equal_derivation_checked, search_and_admit_equal,
        search_and_admit_equal_checked,
    },
    derivation_rules::{
        ChainRule, DerivationRegistry, EQUAL_REFL, EQUAL_SYMMETRY, EQUAL_TRANSITIVITY, apply_builtin_rule, builtin_rule_names,
        is_builtin_rule, registry_from_rule_table,
    },
    eval::{
        EvalAttachment, EvalCertificateKind, eval_is_not_equal, eval_query_status, form_eval_attachment, form_eval_candidate,
        may_request_admission, refuse_eval_as_equal,
    },
    evidence::{
        CheckedDerivation, Evidence, JudgmentAtom, concluded_judgment, evidence_from_equal_steps, height,
        replay_checked_derivation, replay_evidence, replay_evidence_with, validate_finite,
    },
    evidence_dag::{EvidenceDag, EvidenceId},
    inner::InnerTable,
    relation::{admit_equal_relation, compose_equal_relations, form_relation},
    rules::{RelationSignature, RuleTable},
    transform::{
        PremisePattern, TransformationInstance, TransformationSchema, evidence_from_two_premise, replay_two_premise,
        replay_two_premise_checked, replay_two_premise_checked_with,
    },
};
pub use metis_ir::{
    Effect, Function as IrFunction, Module as IrModule, Op, REL_EQUAL, RULE_EQUAL_TRANSITIVITY, Reg, RegKind,
    equal_transitivity_join_plan,
};
pub use metis_vm::{Budget, EmittedCandidate, GraphKernel, KernelView, Slot, Vm, VmError, VmStatus};

pub use metis_island::{Island, IslandStore};
pub use metis_jit::{Artifact, ArtifactKind, CompileUnitId, compile_reach};
pub use metis_types::{EdgeId, EdgeKind, IslandId, MetisError, NodeId};
pub use metis_verify::{Goal, Justification, Proof, prove, query_equal, query_member, verify, zfc};
pub use oak_metis::{MetisLanguage, MetisTokenType, lex_stub, parse_module};

/// Facade version string for smoke probes.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
