//! Stable Metis facade.

pub use athena_gc::{GcHeap, HeapBudget};
pub use metis_compile::{LoweringResult, compile_declarations, lower_module, parse_source};
pub use metis_graph::{
    EdgePayload, Graph, NodePayload, Step,
    admission::{
        AdmittedRelation, AdmittedWorld, CandidateRelation, ConflictReport, ObservationBoundary, QueryStatus, WorldId,
        unknown_if_missing,
    },
    conflict::{Incompatibility, detect_judgment_conflict, query_under_incompatibility},
    connection::{
        AdmittedConnection, CandidateConnection, ConnectionClass, admit_connection, bidirectional_skeleton,
        refuse_galois_without_proof, transport_relation, transport_relation_asserting, validate_candidate,
    },
    derivation::{DerivationDiagram, replay_equal_derivation, search_and_admit_equal},
    eval::{
        EvalAttachment, EvalCertificateKind, eval_is_not_equal, eval_query_status, form_eval_attachment,
        form_eval_candidate, may_request_admission, refuse_eval_as_equal,
    },
    relation::{admit_equal_relation, compose_equal_relations, form_relation},
    rules::{RelationSignature, RuleTable},
    transform::{PremisePattern, TransformationInstance, TransformationSchema, replay_two_premise},
};

pub use metis_island::{Island, IslandStore};
pub use metis_jit::{Artifact, ArtifactKind, CompileUnitId, compile_reach};
pub use metis_types::{EdgeId, EdgeKind, IslandId, MetisError, NodeId};
pub use metis_verify::{Goal, Justification, Proof, prove, query_equal, query_member, verify, zfc};
pub use oak_metis::{MetisLanguage, MetisTokenType, lex_stub, parse_module};

/// Facade version string for smoke probes.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
