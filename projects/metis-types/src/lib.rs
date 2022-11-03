//! Stable handles and diagnostics for the Metis relation graph.

use core::{fmt, num::NonZeroU32};

/// Island namespace id (stable within a loaded graph store).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IslandId(NonZeroU32);

impl IslandId {
    pub const fn from_raw(raw: NonZeroU32) -> Self {
        Self(raw)
    }

    pub const fn get(self) -> u32 {
        self.0.get()
    }
}

impl fmt::Debug for IslandId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IslandId({})", self.get())
    }
}

/// Node handle. Identity is defined by outgoing edges (extensional).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NodeId(NonZeroU32);

impl NodeId {
    pub const fn from_raw(raw: NonZeroU32) -> Self {
        Self(raw)
    }

    pub const fn get(self) -> u32 {
        self.0.get()
    }
}

impl fmt::Debug for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NodeId({})", self.get())
    }
}

/// Edge (morphism) handle.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EdgeId(NonZeroU32);

impl EdgeId {
    pub const fn from_raw(raw: NonZeroU32) -> Self {
        Self(raw)
    }

    pub const fn get(self) -> u32 {
        self.0.get()
    }
}

impl fmt::Debug for EdgeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EdgeId({})", self.get())
    }
}

/// Built-in relation kinds for the foundation layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(u16)]
pub enum EdgeKind {
    /// Structural equality / identified shortcut.
    Equal = 1,
    /// Membership / incidence placeholder (island-specific meaning).
    In = 2,
    /// Evaluation / numeric shadow attachment point.
    Eval = 3,
    /// User-declared custom kind index (island vocabulary).
    Custom(u16),
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum MetisError {
    #[error("island not found")]
    IslandNotFound,
    #[error("node not found")]
    NodeNotFound,
    #[error("edge not found")]
    EdgeNotFound,
    #[error("path not found")]
    PathNotFound,
    #[error("proof invalid")]
    ProofInvalid,
    #[error("capacity exhausted")]
    Capacity,
    #[error("invalid handle")]
    InvalidHandle,
}
