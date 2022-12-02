//! Metis Core admission contract stubs (Living constitution).
//!
//! These are **contract stubs**, not a finished trusted kernel.
//! Only Core may eventually mint opaque admitted values. Search / CAS / JIT
//! produce candidates only.

use metis_types::{EdgeId, IslandId, NodeId};

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

/// Opaque admitted relation. Construction is private — only Core mint paths may create it later.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AdmittedRelation {
    world: WorldId,
    endpoints: (NodeId, NodeId),
    evidence_tag: u64,
}

impl AdmittedRelation {
    /// Test / bootstrap helper. Production minting will go through admission replay.
    #[doc(hidden)]
    pub fn bootstrap_unchecked(world: WorldId, endpoints: (NodeId, NodeId), evidence_tag: u64) -> Self {
        Self { world, endpoints, evidence_tag }
    }

    pub const fn world(self) -> WorldId {
        self.world
    }

    pub const fn endpoints(self) -> (NodeId, NodeId) {
        self.endpoints
    }

    pub const fn evidence_tag(self) -> u64 {
        self.evidence_tag
    }
}

/// Opaque admitted world (accepted island version). Only Core mint paths may create it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AdmittedWorld {
    world: WorldId,
    evidence_tag: u64,
}

impl AdmittedWorld {
    #[doc(hidden)]
    pub fn bootstrap_unchecked(world: WorldId, evidence_tag: u64) -> Self {
        Self { world, evidence_tag }
    }

    /// Mint after a world is accepted / sealed into the inner table.
    pub fn admit(world: WorldId) -> Self {
        let tag = world
            .version
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(u64::from(world.island.get()));
        Self { world, evidence_tag: tag }
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
    if found {
        QueryStatus::Proven
    }
    else {
        QueryStatus::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;

    #[test]
    fn missing_is_unknown_not_refuted() {
        assert_eq!(unknown_if_missing(false), QueryStatus::Unknown);
        assert_eq!(unknown_if_missing(true), QueryStatus::Proven);
    }

    #[test]
    fn admitted_is_opaque_but_readable() {
        let w = WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 0 };
        let a = AdmittedRelation::bootstrap_unchecked(w, (NodeId(0), NodeId(1)), 7);
        assert_eq!(a.world(), w);
        assert_eq!(a.evidence_tag(), 7);
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
