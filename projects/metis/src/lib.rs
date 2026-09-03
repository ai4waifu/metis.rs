//! Stable Metis facade.
//!
//! Re-exports foundation crates. Callers should depend on `metis` rather than
//! reaching into internal crates unless they are extending the workspace itself.

pub use metis_graph::Graph;
pub use metis_island::{Island, IslandStore};
pub use metis_lang::{parse_stub, ParseStub, SourceFile};
pub use metis_types::{EdgeId, EdgeKind, IslandId, MetisError, NodeId};

/// Facade version string for smoke probes.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
