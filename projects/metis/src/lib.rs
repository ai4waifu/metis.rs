//! Stable Metis facade.

pub use athena_gc::{GcHeap, HeapBudget};
pub use metis_compile::parse_source;
pub use metis_graph::{
    Graph, Step,
    admission::{AdmittedRelation, CandidateRelation, ConflictReport, QueryStatus, WorldId, unknown_if_missing},
    connection::{
        AdmittedConnection, CandidateConnection, ConnectionClass, bidirectional_skeleton, refuse_galois_without_proof,
        validate_candidate,
    },
};

pub use metis_island::{Island, IslandStore};
pub use metis_jit::{Artifact, ArtifactKind, CompileUnitId, compile_reach};
pub use metis_types::{EdgeId, EdgeKind, IslandId, MetisError, NodeId};
pub use metis_verify::{Goal, Justification, Proof, prove, query_equal, query_member, verify, zfc};
pub use oak_metis::{MetisLanguage, MetisTokenType, lex_stub, parse_module};

/// Facade version string for smoke probes.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
