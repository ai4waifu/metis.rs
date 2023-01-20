//! Metis Core admission contract stubs (Living constitution).
//!
//! These are **contract stubs**, not a finished trusted kernel.
//! Only Core may eventually mint opaque admitted values. Search / CAS / JIT
//! produce candidates only.

use metis_types::{EdgeId, EdgeKind, IslandId, NodeId};

/// Four-valued query outcome. Missing a path is [`Unknown`], not negation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum QueryStatus {
    /// Target relation has a trusted derivation.
    Proven,
    /// An Island-declared incompatible relation has a trusted derivation.
    Refuted,
    /// Neither side has a trusted derivation.
    Unknown,
    /// Both a relation and an incompatible counterpart are trusted, or the world is quarantined.
    Inconsistent,
}

/// Relative world handle (Island version / staging context). Not a global universe object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WorldId {
    pub island: IslandId,
    pub version: u64,
}

/// Whether further outer-world admissions may enter this world version.
///
/// Distinct from [`crate::Graph::seal`]: Metis judgment / hash-cons state stays queryable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub enum ObservationBoundary {
    /// Outer candidates may still be proposed for admission into this world version.
    #[default]
    Open,
    /// Observation closed: no further transport / morphism admission *into* this version.
    Sealed,
}

/// Candidate relation awaiting admission (outer world).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CandidateRelation {
    pub world: WorldId,
    pub kind_edge: Option<EdgeId>,
    pub endpoints: (NodeId, NodeId),
}

/// Provenance lane for an opaque relation token (Living `10` trusted-path gate).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JudgmentLane {
    /// Minted by single-world derivation replay. Bootstrap candidate for the trusted path.
    SingleWorldReplay,
    /// Minted by connection transport without a transport-preservation witness.
    /// Outer only. Must not be treated as `QueryStatus::Proven` for CVO.
    BootstrapOuterTransport,
    /// Conflict-report scaffolding. Not a positive Inner membership witness.
    BootstrapConflictReport,
}

/// Opaque admitted relation. Only Core mint paths may create it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AdmittedRelation {
    world: WorldId,
    kind: EdgeKind,
    endpoints: (NodeId, NodeId),
    evidence_tag: u64,
    lane: JudgmentLane,
}

impl AdmittedRelation {
    /// Core-internal mint. External crates must go through replay, not this constructor.
    pub(crate) fn mint(
        world: WorldId,
        kind: EdgeKind,
        endpoints: (NodeId, NodeId),
        evidence_tag: u64,
        lane: JudgmentLane,
    ) -> Self {
        Self { world, kind, endpoints, evidence_tag, lane }
    }

    pub const fn world(self) -> WorldId {
        self.world
    }

    pub const fn kind(self) -> EdgeKind {
        self.kind
    }

    pub const fn endpoints(self) -> (NodeId, NodeId) {
        self.endpoints
    }

    pub const fn evidence_tag(self) -> u64 {
        self.evidence_tag
    }

    pub const fn lane(self) -> JudgmentLane {
        self.lane
    }

    /// True only for single-world replay tokens. Transport / conflict lanes stay Outer.
    pub const fn is_trusted_path_candidate(self) -> bool {
        matches!(self.lane, JudgmentLane::SingleWorldReplay)
    }
}

/// Map an opaque token to query status for CVO / facade consumers.
///
/// Only [`JudgmentLane::SingleWorldReplay`] may surface as [`QueryStatus::Proven`].
/// Bootstrap transport / conflict tokens stay [`QueryStatus::Unknown`].
pub const fn query_status_of_admitted(rel: AdmittedRelation) -> QueryStatus {
    if rel.is_trusted_path_candidate() { QueryStatus::Proven } else { QueryStatus::Unknown }
}

/// Opaque admitted world (accepted island version). Only Core mint paths may create it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AdmittedWorld {
    world: WorldId,
    evidence_tag: u64,
}

impl AdmittedWorld {
    pub(crate) fn mint(world: WorldId, evidence_tag: u64) -> Self {
        Self { world, evidence_tag }
    }

    /// Mint after a world is accepted / sealed into the inner table.
    pub fn admit(world: WorldId) -> Self {
        let tag = world.version.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(u64::from(world.island.get()));
        Self::mint(world, tag)
    }

    pub const fn world(self) -> WorldId {
        self.world
    }

    pub const fn evidence_tag(self) -> u64 {
        self.evidence_tag
    }
}

/// Explicit conflict report. Does not explode into arbitrary relations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConflictReport {
    pub world: WorldId,
    pub left: AdmittedRelation,
    pub right: AdmittedRelation,
}

/// Map absence of a directed proof to [`QueryStatus::Unknown`] (never automatic negation).
pub const fn unknown_if_missing(found: bool) -> QueryStatus {
    if found { QueryStatus::Proven } else { QueryStatus::Unknown }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::EdgeKind;

    #[test]
    fn missing_is_unknown_not_refuted() {
        assert_eq!(unknown_if_missing(false), QueryStatus::Unknown);
        assert_eq!(unknown_if_missing(true), QueryStatus::Proven);
    }

    #[test]
    fn admitted_is_opaque_but_readable() {
        let w = WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 0 };
        let a = AdmittedRelation::mint(w, EdgeKind::Equal, (NodeId(0), NodeId(1)), 7, JudgmentLane::SingleWorldReplay);
        assert_eq!(a.world(), w);
        assert_eq!(a.kind(), EdgeKind::Equal);
        assert_eq!(a.evidence_tag(), 7);
        assert!(a.is_trusted_path_candidate());
    }

    #[test]
    fn equal_and_in_tokens_are_distinct() {
        let w = WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 0 };
        let eq = AdmittedRelation::mint(w, EdgeKind::Equal, (NodeId(0), NodeId(1)), 1, JudgmentLane::SingleWorldReplay);
        let mem = AdmittedRelation::mint(w, EdgeKind::In, (NodeId(0), NodeId(1)), 1, JudgmentLane::SingleWorldReplay);
        assert_ne!(eq, mem);
        assert_eq!(eq.endpoints(), mem.endpoints());
    }

    #[test]
    fn transport_lane_is_not_trusted_path_candidate() {
        let w = WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 0 };
        let t = AdmittedRelation::mint(w, EdgeKind::Equal, (NodeId(0), NodeId(1)), 1, JudgmentLane::BootstrapOuterTransport);
        assert!(!t.is_trusted_path_candidate());
        assert_eq!(query_status_of_admitted(t), QueryStatus::Unknown);
    }

    #[test]
    fn replay_lane_maps_to_proven() {
        let w = WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 0 };
        let r = AdmittedRelation::mint(w, EdgeKind::Equal, (NodeId(0), NodeId(1)), 1, JudgmentLane::SingleWorldReplay);
        assert_eq!(query_status_of_admitted(r), QueryStatus::Proven);
    }

    #[test]
    fn admitted_world_is_deterministic_for_same_id() {
        let w = WorldId { island: IslandId::from_raw(NonZeroU32::new(2).unwrap()), version: 3 };
        let a = AdmittedWorld::admit(w);
        let b = AdmittedWorld::admit(w);
        assert_eq!(a, b);
        assert_eq!(a.world(), w);
    }

    #[test]
    fn observation_defaults_open() {
        assert_eq!(ObservationBoundary::default(), ObservationBoundary::Open);
    }
}
