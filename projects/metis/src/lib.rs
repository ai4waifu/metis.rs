//! Stable Metis facade.
//!
//! Re-exports foundation crates. Island language CST comes from `oak-metis`.
//! Object heap protocol is `athena-gc` (no parallel `metis-gc`).

pub use athena_gc::{GcHeap, HeapBudget};
pub use metis_graph::Graph;
pub use metis_island::{Island, IslandStore};
pub use metis_jit::{compile_reach, Artifact, ArtifactKind, CompileUnitId};
pub use metis_types::{EdgeId, EdgeKind, IslandId, MetisError, NodeId};
pub use oak_metis::{lex_stub, MetisLanguage, MetisTokenType};

/// Facade version string for smoke probes.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
