//! Stable Metis facade.
//!
//! Theorems and proofs are authored in island language (`oak-metis` + `metis-compile`).
//! Object heap protocol is `athena-gc` (no parallel `metis-gc`).

pub use athena_gc::{GcHeap, HeapBudget};
pub use metis_compile::{run_module, run_source, TheoremReport};
pub use metis_graph::{Graph, Step};
pub use metis_island::{Island, IslandStore};
pub use metis_jit::{compile_reach, Artifact, ArtifactKind, CompileUnitId};
pub use metis_types::{EdgeId, EdgeKind, IslandId, MetisError, NodeId};
pub use metis_verify::zfc;
pub use metis_verify::{prove, verify, Goal, Justification, Proof};
pub use oak_metis::{lex_stub, parse_module, MetisLanguage, MetisTokenType};

/// Facade version string for smoke probes.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
