//! Payload types carried on the ordinary [`athena_graph::GraphBuilder`] base.
//!
//! Metis still keeps hash-cons / label sidecars. Payloads make structural vs judgment
//! and labels visible on the athena graph itself (Living / plan ID contract).

use metis_types::EdgeKind;

/// Node payload on the ordinary discrete graph.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NodePayload {
    /// Present for `intern_label` atoms. Structural cons nodes use `None`.
    pub label: Option<Vec<u8>>,
}

impl NodePayload {
    pub fn unlabeled() -> Self {
        Self { label: None }
    }

    pub fn labeled(name: impl AsRef<[u8]>) -> Self {
        Self { label: Some(name.as_ref().to_vec()) }
    }
}

/// Edge payload on the ordinary discrete graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EdgePayload {
    pub kind: EdgeKind,
    /// `true` = structural (hash-cons identity). `false` = judgment.
    pub structural: bool,
}

impl EdgePayload {
    pub const fn structural(kind: EdgeKind) -> Self {
        Self { kind, structural: true }
    }

    pub const fn judgment(kind: EdgeKind) -> Self {
        Self { kind, structural: false }
    }
}
