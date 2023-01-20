//! Island / world connection contracts (Living constitution · Living `12` / `13`).
//!
//! Three statuses must stay distinct:
//! 1. [`CandidateConnection`] — outer proposal only
//! 2. [`AdmittedConnection`] / registered M-Link structure \(C_m\) — maps objects/kinds
//! 3. [`TransportWitness`] `π_T` — required for trusted transport into Inner
//!
//! Surface `A <-> B` only yields a bidirectional skeleton. Galois / isomorphism /
//! adjunction require extra evidence and must not be inferred from the keyword alone.
//! Bootstrap transport APIs mint [`JudgmentLane::BootstrapOuterTransport`] only.

use std::collections::HashMap;

use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

use super::admission::{AdmittedRelation, JudgmentLane, QueryStatus, WorldId, query_status_of_admitted};

/// Living `12` transport-preservation witness `π_T`.
///
/// Opaque and currently uninhabited from public API: bootstrap cannot mint a witness.
/// Trusted transport requires this token; without it only Outer bootstrap transport exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TransportWitness {
    _private: (),
}

impl TransportWitness {
    /// Bootstrap cannot construct `π_T`. Always fails until a preservation theorem is available.
    pub fn try_mint_bootstrap() -> Result<Self, MetisError> {
        Err(MetisError::ProofInvalid)
    }
}

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

/// Registered M-Link structure \(C_m\) (Living `12`).
///
/// This is **not** a transport-preservation theorem. Bootstrap Outer transport may use the
/// maps; trusted Inner transport still requires [`TransportWitness`].
///
/// Alias: [`RegisteredMLink`].
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

/// Clearer name for [`AdmittedConnection`]: registered structure, not trusted transport.
pub type RegisteredMLink = AdmittedConnection;

impl AdmittedConnection {
    pub(crate) fn mint(
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
    let mut tag = c.source.version.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(c.target.version);
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
        ConnectionClass::WorldMorphism => Ok(AdmittedConnection::mint(
            c.source,
            c.target,
            ConnectionClass::WorldMorphism,
            connection_evidence_tag(c),
            c.object_map.clone(),
            c.relation_map.clone(),
            c.lossy,
        )),
        ConnectionClass::BidirectionalSkeleton | ConnectionClass::GaloisClaimed => Err(MetisError::ConnectionInvalid),
    }
}

/// Bootstrap Outer transport of an opaque relation along an admitted connection.
///
/// Not part of the Living `10` trusted path. Does **not** establish
/// `W; empty ⊢ e : J` in the target world and does **not** write a judgment edge
/// into the target graph — it only mints a transported Outer token.
pub fn transport_relation(
    conn: &AdmittedConnection,
    relation: AdmittedRelation,
    kind: EdgeKind,
) -> Result<AdmittedRelation, MetisError> {
    bootstrap_transport_relation(conn, relation, kind)
}

/// Explicit bootstrap alias for [`transport_relation`].
pub fn bootstrap_transport_relation(
    conn: &AdmittedConnection,
    relation: AdmittedRelation,
    kind: EdgeKind,
) -> Result<AdmittedRelation, MetisError> {
    let (_tgt_kind, adm) = transport_mapped(conn, relation, kind)?;
    Ok(adm)
}

/// Trusted-path transport under a Living `12` `π_T` witness.
///
/// Unreachable in bootstrap because [`TransportWitness::try_mint_bootstrap`] always fails.
/// When a witness exists, this remints the mapped token on the SingleWorldReplay lane.
pub fn transport_relation_trusted(
    conn: &AdmittedConnection,
    relation: AdmittedRelation,
    kind: EdgeKind,
    witness: TransportWitness,
) -> Result<AdmittedRelation, MetisError> {
    let _ = witness;
    let (_tgt_kind, outer) = transport_mapped(conn, relation, kind)?;
    Ok(AdmittedRelation::mint(
        outer.world(),
        outer.kind(),
        outer.endpoints(),
        outer.evidence_tag(),
        JudgmentLane::SingleWorldReplay,
    ))
}

/// Query status for a transport result. Bootstrap Outer tokens stay non-Proven.
pub fn transport_query_status(rel: AdmittedRelation) -> QueryStatus {
    query_status_of_admitted(rel)
}

/// Bootstrap Outer transport that also asserts a mapped judgment edge into `target`.
///
/// Demo / staging helper only. The written edge is **not** Inner membership under
/// Living `10` until a transport-preservation theorem is available.
pub fn transport_relation_asserting(
    target: &mut super::Graph,
    conn: &AdmittedConnection,
    relation: AdmittedRelation,
    kind: EdgeKind,
) -> Result<(AdmittedRelation, EdgeId), MetisError> {
    bootstrap_transport_relation_asserting(target, conn, relation, kind)
}

/// Explicit bootstrap alias for [`transport_relation_asserting`].
pub fn bootstrap_transport_relation_asserting(
    target: &mut super::Graph,
    conn: &AdmittedConnection,
    relation: AdmittedRelation,
    kind: EdgeKind,
) -> Result<(AdmittedRelation, EdgeId), MetisError> {
    let (tgt_kind, adm) = transport_mapped(conn, relation, kind)?;
    let (left_t, right_t) = adm.endpoints();
    let edge = target.assert(left_t, tgt_kind, right_t)?;
    Ok((adm, edge))
}

fn transport_mapped(
    conn: &AdmittedConnection,
    relation: AdmittedRelation,
    kind: EdgeKind,
) -> Result<(EdgeKind, AdmittedRelation), MetisError> {
    if relation.world() != conn.source {
        return Err(MetisError::ConnectionInvalid);
    }
    // Abstract identity: empty maps leave endpoints and kind unchanged.
    if conn.source == conn.target && conn.object_map.is_empty() && conn.relation_map.is_empty() {
        let tag = conn
            .evidence_tag
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(relation.evidence_tag())
            .wrapping_add(kind_tag(kind));
        let adm = AdmittedRelation::mint(conn.target, kind, relation.endpoints(), tag, JudgmentLane::BootstrapOuterTransport);
        return Ok((kind, adm));
    }
    let tgt_kind = *conn.relation_map.get(&kind).ok_or(MetisError::ConnectionInvalid)?;
    let (left, right) = relation.endpoints();
    let left_t = *conn.object_map.get(&left).ok_or(MetisError::ConnectionInvalid)?;
    let right_t = *conn.object_map.get(&right).ok_or(MetisError::ConnectionInvalid)?;
    let tag = conn
        .evidence_tag
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
        .wrapping_add(relation.evidence_tag())
        .wrapping_add(kind_tag(kind));
    let adm = AdmittedRelation::mint(conn.target, tgt_kind, (left_t, right_t), tag, JudgmentLane::BootstrapOuterTransport);
    Ok((tgt_kind, adm))
}

/// Structural checks for a candidate. Does **not** prove Galois or transport theorems.
pub fn validate_candidate(c: &CandidateConnection) -> Result<(), MetisError> {
    if c.class == ConnectionClass::GaloisClaimed && c.lossy {
        return Err(MetisError::ConnectionInvalid);
    }
    if c.source == c.target {
        // Identity world morphism: maps must be id-like (or empty = abstract identity).
        if c.class != ConnectionClass::WorldMorphism || c.lossy {
            return Err(MetisError::ConnectionInvalid);
        }
        for (k, v) in &c.object_map {
            if k != v {
                return Err(MetisError::ConnectionInvalid);
            }
        }
        for (k, v) in &c.relation_map {
            if k != v {
                return Err(MetisError::ConnectionInvalid);
            }
        }
        return Ok(());
    }
    Ok(())
}

/// Identity world morphism on `world` (Living connection coherence).
///
/// Empty maps denote an abstract identity. Non-empty maps must be pointwise id.
pub fn identity_morphism(world: WorldId) -> CandidateConnection {
    CandidateConnection {
        source: world,
        target: world,
        class: ConnectionClass::WorldMorphism,
        object_map: HashMap::new(),
        relation_map: HashMap::new(),
        lossy: false,
    }
}

/// Compose admitted morphisms `second ∘ first` (apply `first`, then `second`).
///
/// Yields an outer [`CandidateConnection`] — still needs [`admit_connection`].
pub fn compose_connections(first: &AdmittedConnection, second: &AdmittedConnection) -> Result<CandidateConnection, MetisError> {
    if first.target() != second.source() {
        return Err(MetisError::ConnectionInvalid);
    }
    if first.class() != ConnectionClass::WorldMorphism || second.class() != ConnectionClass::WorldMorphism {
        return Err(MetisError::ConnectionInvalid);
    }
    let mut object_map = HashMap::new();
    for (a, b) in first.object_map() {
        if let Some(c) = second.object_map().get(b) {
            object_map.insert(*a, *c);
        }
    }
    let mut relation_map = HashMap::new();
    for (k, m) in first.relation_map() {
        if let Some(n) = second.relation_map().get(m) {
            relation_map.insert(*k, *n);
        }
    }
    let candidate = CandidateConnection {
        source: first.source(),
        target: second.target(),
        class: ConnectionClass::WorldMorphism,
        object_map,
        relation_map,
        lossy: first.lossy() || second.lossy(),
    };
    validate_candidate(&candidate)?;
    Ok(candidate)
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
        assert_eq!(bidirectional_skeleton(a, a, HashMap::new(), HashMap::new()).unwrap_err(), MetisError::ConnectionInvalid);
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
        let rel = AdmittedRelation::mint(a, EdgeKind::Equal, (NodeId(0), NodeId(1)), 42, JudgmentLane::SingleWorldReplay);
        let moved = transport_relation(&conn, rel, EdgeKind::Equal).unwrap();
        assert_eq!(moved.world(), b);
        assert_eq!(moved.endpoints(), (NodeId(10), NodeId(11)));
        assert!(!moved.is_trusted_path_candidate());
        assert_eq!(moved.lane(), JudgmentLane::BootstrapOuterTransport);

        let wrong_world =
            AdmittedRelation::mint(b, EdgeKind::Equal, (NodeId(0), NodeId(1)), 1, JudgmentLane::SingleWorldReplay);
        assert_eq!(transport_relation(&conn, wrong_world, EdgeKind::Equal).unwrap_err(), MetisError::ConnectionInvalid);
        assert_eq!(transport_relation(&conn, rel, EdgeKind::In).unwrap_err(), MetisError::ConnectionInvalid);
    }

    #[test]
    fn transport_asserting_writes_target_judgment() {
        use crate::Graph;
        let a = world(1, 1);
        let b = world(2, 1);
        let mut tgt = Graph::new();
        let t0 = tgt.intern_label(b"T0").unwrap();
        let t1 = tgt.intern_label(b"T1").unwrap();
        let morph = CandidateConnection {
            source: a,
            target: b,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(0), t0), (NodeId(1), t1)]),
            relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
            lossy: false,
        };
        let conn = admit_connection(&morph).unwrap();
        let rel = AdmittedRelation::mint(a, EdgeKind::Equal, (NodeId(0), NodeId(1)), 3, JudgmentLane::SingleWorldReplay);
        let (moved, edge) = transport_relation_asserting(&mut tgt, &conn, rel, EdgeKind::Equal).unwrap();
        assert_eq!(moved.endpoints(), (t0, t1));
        let (from, kind, to) = tgt.edge(edge).unwrap();
        assert_eq!((from, kind, to), (t0, EdgeKind::Equal, t1));
        assert!(tgt.is_judgment(edge).unwrap());
    }

    #[test]
    fn identity_morphism_admits_and_transports() {
        let w = world(1, 1);
        let id = admit_connection(&identity_morphism(w)).unwrap();
        assert_eq!(id.source(), w);
        assert_eq!(id.target(), w);
        let rel = AdmittedRelation::mint(w, EdgeKind::Equal, (NodeId(3), NodeId(4)), 1, JudgmentLane::SingleWorldReplay);
        let moved = transport_relation(&id, rel, EdgeKind::Equal).unwrap();
        assert_eq!(moved.endpoints(), (NodeId(3), NodeId(4)));
        assert_eq!(moved.world(), w);

        let bad = CandidateConnection {
            source: w,
            target: w,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(0), NodeId(1))]),
            relation_map: HashMap::new(),
            lossy: false,
        };
        assert_eq!(validate_candidate(&bad).unwrap_err(), MetisError::ConnectionInvalid);
    }

    #[test]
    fn compose_connections_chains_maps() {
        let a = world(1, 1);
        let b = world(2, 1);
        let c = world(3, 1);
        let ab = admit_connection(&CandidateConnection {
            source: a,
            target: b,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(0), NodeId(1))]),
            relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::In)]),
            lossy: false,
        })
        .unwrap();
        let bc = admit_connection(&CandidateConnection {
            source: b,
            target: c,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(1), NodeId(2))]),
            relation_map: HashMap::from([(EdgeKind::In, EdgeKind::Eval)]),
            lossy: false,
        })
        .unwrap();
        let ac = compose_connections(&ab, &bc).unwrap();
        assert_eq!(ac.source, a);
        assert_eq!(ac.target, c);
        assert_eq!(ac.object_map.get(&NodeId(0)), Some(&NodeId(2)));
        assert_eq!(ac.relation_map.get(&EdgeKind::Equal), Some(&EdgeKind::Eval));
        let admitted = admit_connection(&ac).unwrap();
        assert_eq!(admitted.target(), c);
    }

    #[test]
    fn compose_connections_associativity_on_maps() {
        let a = world(1, 1);
        let b = world(2, 1);
        let c = world(3, 1);
        let d = world(4, 1);
        let ab = admit_connection(&CandidateConnection {
            source: a,
            target: b,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(0), NodeId(1))]),
            relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::In)]),
            lossy: false,
        })
        .unwrap();
        let bc = admit_connection(&CandidateConnection {
            source: b,
            target: c,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(1), NodeId(2))]),
            relation_map: HashMap::from([(EdgeKind::In, EdgeKind::Eval)]),
            lossy: false,
        })
        .unwrap();
        let cd = admit_connection(&CandidateConnection {
            source: c,
            target: d,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(2), NodeId(3))]),
            relation_map: HashMap::from([(EdgeKind::Eval, EdgeKind::Custom(9))]),
            lossy: false,
        })
        .unwrap();
        let left = {
            let bc_cd = admit_connection(&compose_connections(&bc, &cd).unwrap()).unwrap();
            compose_connections(&ab, &bc_cd).unwrap()
        };
        let right = {
            let ab_bc = admit_connection(&compose_connections(&ab, &bc).unwrap()).unwrap();
            compose_connections(&ab_bc, &cd).unwrap()
        };
        assert_eq!(left.source, right.source);
        assert_eq!(left.target, right.target);
        assert_eq!(left.object_map, right.object_map);
        assert_eq!(left.relation_map, right.relation_map);
        assert_eq!(left.object_map.get(&NodeId(0)), Some(&NodeId(3)));
        assert_eq!(left.relation_map.get(&EdgeKind::Equal), Some(&EdgeKind::Custom(9)));
    }

    #[test]
    fn bootstrap_cannot_mint_transport_witness() {
        assert_eq!(TransportWitness::try_mint_bootstrap().unwrap_err(), MetisError::ProofInvalid);
    }

    #[test]
    fn bootstrap_transport_token_is_not_proven() {
        let src = world(1, 1);
        let tgt = world(2, 1);
        let conn = admit_connection(&CandidateConnection {
            source: src,
            target: tgt,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(NodeId(0), NodeId(10)), (NodeId(1), NodeId(11))]),
            relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
            lossy: false,
        })
        .unwrap();
        let rel = AdmittedRelation::mint(src, EdgeKind::Equal, (NodeId(0), NodeId(1)), 7, JudgmentLane::SingleWorldReplay);
        let moved = bootstrap_transport_relation(&conn, rel, EdgeKind::Equal).unwrap();
        assert_eq!(moved.lane(), JudgmentLane::BootstrapOuterTransport);
        assert_eq!(transport_query_status(moved), QueryStatus::Unknown);
        assert!(!moved.is_trusted_path_candidate());
    }
}
