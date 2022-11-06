//! Island / world connection contracts (Living constitution).
//!
//! A connection is first a **theory / world morphism**. Surface `A <-> B` only yields a
//! bidirectional skeleton. Galois / isomorphism / adjunction require extra evidence and
//! must not be inferred from the bidirectional keyword alone.

use std::collections::HashMap;

use metis_types::{EdgeKind, MetisError, NodeId};

use super::admission::WorldId;

/// Declared strength of a connection candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConnectionClass {
    /// Minimal legal connection: world morphism skeleton.
    WorldMorphism,
    /// Pair of opposite morphisms from `connection A <-> B` surface syntax.
    BidirectionalSkeleton,
    /// User *claimed* Galois; not yet admitted as such.
    GaloisClaimed,
}

/// Candidate connection (outer world). Cannot mint trusted transport by itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateConnection {
    pub source: WorldId,
    pub target: WorldId,
    pub class: ConnectionClass,
    /// Partial object / position map (source node → target node).
    pub object_map: HashMap<NodeId, NodeId>,
    /// Relation-kind map (source kind → target kind).
    pub relation_map: HashMap<EdgeKind, EdgeKind>,
    /// True when the map is declared lossy (must not be treated as isomorphism).
    pub lossy: bool,
}

/// Opaque admitted connection. Only Core mint paths may create it later.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmittedConnection {
    source: WorldId,
    target: WorldId,
    class: ConnectionClass,
    evidence_tag: u64,
}

impl AdmittedConnection {
    #[doc(hidden)]
    pub fn bootstrap_unchecked(source: WorldId, target: WorldId, class: ConnectionClass, evidence_tag: u64) -> Self {
        Self { source, target, class, evidence_tag }
    }

    pub const fn source(&self) -> WorldId {
        self.source
    }

    pub const fn target(&self) -> WorldId {
        self.target
    }

    pub const fn class(&self) -> ConnectionClass {
        self.class
    }

    pub const fn evidence_tag(&self) -> u64 {
        self.evidence_tag
    }
}

/// Structural checks for a candidate. Does **not** prove Galois or transport theorems.
pub fn validate_candidate(c: &CandidateConnection) -> Result<(), MetisError> {
    if c.source == c.target {
        return Err(MetisError::ConnectionInvalid);
    }
    if c.class == ConnectionClass::GaloisClaimed && c.lossy {
        // Lossy maps cannot even claim Galois.
        return Err(MetisError::ConnectionInvalid);
    }
    Ok(())
}

/// Lowering for surface `connection A <-> B`: two opposite world-morphism skeletons.
///
/// Neither direction is a Galois connection by default.
pub fn bidirectional_skeleton(
    left: WorldId,
    right: WorldId,
    forward_objects: HashMap<NodeId, NodeId>,
    forward_relations: HashMap<EdgeKind, EdgeKind>,
) -> Result<(CandidateConnection, CandidateConnection), MetisError> {
    if left == right {
        return Err(MetisError::ConnectionInvalid);
    }
    let forward = CandidateConnection {
        source: left,
        target: right,
        class: ConnectionClass::BidirectionalSkeleton,
        object_map: forward_objects,
        relation_map: forward_relations,
        lossy: false,
    };
    // Reverse maps are left empty until elaborator fills them — still a legal skeleton.
    let backward = CandidateConnection {
        source: right,
        target: left,
        class: ConnectionClass::BidirectionalSkeleton,
        object_map: HashMap::new(),
        relation_map: HashMap::new(),
        lossy: false,
    };
    validate_candidate(&forward)?;
    validate_candidate(&backward)?;
    Ok((forward, backward))
}

/// Refuse treating a bidirectional skeleton as an admitted Galois connection.
pub fn refuse_galois_without_proof(c: &CandidateConnection) -> Result<(), MetisError> {
    match c.class {
        ConnectionClass::GaloisClaimed | ConnectionClass::BidirectionalSkeleton => Err(MetisError::ConnectionInvalid),
        ConnectionClass::WorldMorphism => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    fn world(n: u32, v: u64) -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(n).unwrap()), version: v }
    }

    #[test]
    fn bidirectional_is_not_galois() {
        let a = world(1, 1);
        let b = world(2, 1);
        let (fwd, back) = bidirectional_skeleton(a, b, HashMap::new(), HashMap::new()).unwrap();
        assert_eq!(fwd.class, ConnectionClass::BidirectionalSkeleton);
        assert_eq!(back.source, b);
        assert!(refuse_galois_without_proof(&fwd).is_err());
    }

    #[test]
    fn same_world_rejected() {
        let a = world(1, 1);
        assert_eq!(
            bidirectional_skeleton(a, a, HashMap::new(), HashMap::new()).unwrap_err(),
            MetisError::ConnectionInvalid
        );
    }

    #[test]
    fn lossy_galois_claim_rejected() {
        let c = CandidateConnection {
            source: world(1, 1),
            target: world(2, 1),
            class: ConnectionClass::GaloisClaimed,
            object_map: HashMap::new(),
            relation_map: HashMap::new(),
            lossy: true,
        };
        assert_eq!(validate_candidate(&c).unwrap_err(), MetisError::ConnectionInvalid);
    }
}
