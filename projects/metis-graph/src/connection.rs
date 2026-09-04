//! Island / world connection contracts (Living constitution).
//!
//! A connection is first a **theory / world morphism**. Surface `A <-> B` only yields a
//! bidirectional skeleton. Galois / isomorphism / adjunction require extra evidence and
//! must not be inferred from the bidirectional keyword alone.

use std::collections::HashMap;

use metis_types::{EdgeKind, MetisError, NodeId};

use super::admission::{AdmittedRelation, WorldId};

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

/// Opaque admitted connection. Only Core mint paths may create it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmittedConnection {
    source: WorldId,
    target: WorldId,
    class: ConnectionClass,
    evidence_tag: u64,
    object_map: HashMap<NodeId, NodeId>,
    relation_map: HashMap<EdgeKind, EdgeKind>,
    lossy: bool,
}

impl AdmittedConnection {
    #[doc(hidden)]
    pub fn bootstrap_unchecked(
        source: WorldId,
        target: WorldId,
        class: ConnectionClass,
        evidence_tag: u64,
        object_map: HashMap<NodeId, NodeId>,
        relation_map: HashMap<EdgeKind, EdgeKind>,
        lossy: bool,
    ) -> Self {
        Self { source, target, class, evidence_tag, object_map, relation_map, lossy }
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

    pub const fn lossy(&self) -> bool {
        self.lossy
    }

    pub fn object_map(&self) -> &HashMap<NodeId, NodeId> {
        &self.object_map
    }

    pub fn relation_map(&self) -> &HashMap<EdgeKind, EdgeKind> {
        &self.relation_map
    }
}

fn connection_evidence_tag(c: &CandidateConnection) -> u64 {
    let mut tag = c.source.version
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
        .wrapping_add(c.target.version);
    tag ^= match c.class {
        ConnectionClass::WorldMorphism => 1,
        ConnectionClass::BidirectionalSkeleton => 2,
        ConnectionClass::GaloisClaimed => 3,
    };
    tag ^= (c.object_map.len() as u64).wrapping_mul(0xC2B2_AE3D_27D4_EB4F);
    tag ^= (c.relation_map.len() as u64).wrapping_mul(0x1656_67B1_9E37_79B9);
    if c.lossy {
        tag ^= 0xDEAD_BEEF_CAFE_BABE;
    }
    for (k, v) in &c.object_map {
        tag = tag.wrapping_mul(31).wrapping_add(k.0).wrapping_mul(31).wrapping_add(v.0);
    }
    for (k, v) in &c.relation_map {
        tag = tag.wrapping_mul(31).wrapping_add(kind_tag(*k)).wrapping_mul(31).wrapping_add(kind_tag(*v));
    }
    tag
}

fn kind_tag(k: EdgeKind) -> u64 {
    match k {
        EdgeKind::Equal => 1,
        EdgeKind::In => 2,
        EdgeKind::Eval => 3,
        EdgeKind::Custom(v) => 4u64.wrapping_add(u64::from(v)),
    }
}

/// Admit a candidate as a trusted world morphism.
///
/// Only [`ConnectionClass::WorldMorphism`] may be admitted here.
/// Bidirectional skeletons and Galois claims stay outer-world until separately proved.
pub fn admit_connection(c: &CandidateConnection) -> Result<AdmittedConnection, MetisError> {
    validate_candidate(c)?;
    match c.class {
        ConnectionClass::WorldMorphism => Ok(AdmittedConnection {
            source: c.source,
            target: c.target,
            class: ConnectionClass::WorldMorphism,
            evidence_tag: connection_evidence_tag(c),
            object_map: c.object_map.clone(),
            relation_map: c.relation_map.clone(),
            lossy: c.lossy,
        }),
        ConnectionClass::BidirectionalSkeleton | ConnectionClass::GaloisClaimed => {
            Err(MetisError::ConnectionInvalid)
        }
    }
}

/// Transport an admitted relation along an admitted connection.
///
/// Requires the relation's world to match the connection source, both endpoints in
/// `object_map`, and `kind` present in `relation_map`. Does **not** write judgment edges
/// into the target graph — it only mints a transported opaque relation.
pub fn transport_relation(
    conn: &AdmittedConnection,
    relation: AdmittedRelation,
    kind: EdgeKind,
) -> Result<AdmittedRelation, MetisError> {
    if relation.world() != conn.source {
        return Err(MetisError::ConnectionInvalid);
    }
    if !conn.relation_map.contains_key(&kind) {
        return Err(MetisError::ConnectionInvalid);
    }
    let (left, right) = relation.endpoints();
    let left_t = *conn.object_map.get(&left).ok_or(MetisError::ConnectionInvalid)?;
    let right_t = *conn.object_map.get(&right).ok_or(MetisError::ConnectionInvalid)?;
    let tag = conn
        .evidence_tag
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
        .wrapping_add(relation.evidence_tag())
        .wrapping_add(kind_tag(kind));
    Ok(AdmittedRelation::bootstrap_unchecked(conn.target, (left_t, right_t), tag))
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

    #[test]
    fn only_world_morphism_admits() {
        let a = world(1, 1);
        let b = world(2, 1);
        let (fwd, _) = bidirectional_skeleton(a, b, HashMap::new(), HashMap::new()).unwrap();
        assert_eq!(admit_connection(&fwd).unwrap_err(), MetisError::ConnectionInvalid);

        let morph = CandidateConnection {
            source: a,
            target: b,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(0), NodeId(10))]),
            relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
            lossy: false,
        };
        let adm = admit_connection(&morph).unwrap();
        assert_eq!(adm.class(), ConnectionClass::WorldMorphism);
        assert_eq!(adm.source(), a);
        assert_eq!(adm.target(), b);
        assert_eq!(adm.object_map().get(&NodeId(0)), Some(&NodeId(10)));
    }

    #[test]
    fn transport_requires_maps_and_source_world() {
        let a = world(1, 1);
        let b = world(2, 1);
        let morph = CandidateConnection {
            source: a,
            target: b,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(0), NodeId(10)), (NodeId(1), NodeId(11))]),
            relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
            lossy: false,
        };
        let conn = admit_connection(&morph).unwrap();
        let rel = AdmittedRelation::bootstrap_unchecked(a, (NodeId(0), NodeId(1)), 42);
        let moved = transport_relation(&conn, rel, EdgeKind::Equal).unwrap();
        assert_eq!(moved.world(), b);
        assert_eq!(moved.endpoints(), (NodeId(10), NodeId(11)));

        let wrong_world = AdmittedRelation::bootstrap_unchecked(b, (NodeId(0), NodeId(1)), 1);
        assert_eq!(
            transport_relation(&conn, wrong_world, EdgeKind::Equal).unwrap_err(),
            MetisError::ConnectionInvalid
        );
        assert_eq!(
            transport_relation(&conn, rel, EdgeKind::In).unwrap_err(),
            MetisError::ConnectionInvalid
        );
    }
}
