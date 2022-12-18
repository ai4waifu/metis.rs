//! Bootstrap `Inner(W)` registry (Living `10` opaque checked judgment slice).
//!
//! Stores judgments that have been minted by single-world replay. This is **not** yet
//! a proven least fixed point `μΦ_W`; it is the runtime table CVO may consult for
//! `QueryStatus::Proven` membership under a fixed [`WorldId`] snapshot.

use std::collections::HashMap;

use metis_types::{EdgeKind, MetisError, NodeId};

use super::admission::{AdmittedRelation, QueryStatus, WorldId, query_status_of_admitted};
use super::evidence::JudgmentAtom;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct JudgmentKey {
    kind: EdgeKind,
    left: NodeId,
    right: NodeId,
}

impl From<JudgmentAtom> for JudgmentKey {
    fn from(j: JudgmentAtom) -> Self {
        Self { kind: j.kind, left: j.endpoints.0, right: j.endpoints.1 }
    }
}

impl From<AdmittedRelation> for JudgmentKey {
    fn from(rel: AdmittedRelation) -> Self {
        let (left, right) = rel.endpoints();
        Self { kind: rel.kind(), left, right }
    }
}

/// Per-world table of opaque checked judgments (bootstrap Inner projection).
#[derive(Clone, Debug, Default)]
pub struct InnerTable {
    by_world: HashMap<WorldId, HashMap<JudgmentKey, AdmittedRelation>>,
}

impl InnerTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a SingleWorldReplay token. Transport / conflict lanes are rejected.
    pub fn insert(&mut self, rel: AdmittedRelation) -> Result<(), MetisError> {
        if !rel.is_trusted_path_candidate() {
            return Err(MetisError::ProofInvalid);
        }
        let world = rel.world();
        let key = JudgmentKey::from(rel);
        self.by_world.entry(world).or_default().insert(key, rel);
        Ok(())
    }

    pub fn contains_atom(&self, world: WorldId, atom: JudgmentAtom) -> bool {
        self.by_world.get(&world).is_some_and(|m| m.contains_key(&JudgmentKey::from(atom)))
    }

    pub fn get(&self, world: WorldId, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> Option<AdmittedRelation> {
        let key = JudgmentKey { kind, left: endpoints.0, right: endpoints.1 };
        self.by_world.get(&world)?.get(&key).copied()
    }

    /// Proven iff the judgment is registered for this world snapshot.
    pub fn query(&self, world: WorldId, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> QueryStatus {
        match self.get(world, kind, endpoints) {
            Some(rel) => query_status_of_admitted(rel),
            None => QueryStatus::Unknown,
        }
    }

    pub fn len_world(&self, world: WorldId) -> usize {
        self.by_world.get(&world).map(|m| m.len()).unwrap_or(0)
    }

    pub fn is_empty(&self) -> bool {
        self.by_world.values().all(|m| m.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::JudgmentLane;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn insert_replay_and_query_proven() {
        let mut inner = InnerTable::new();
        let rel = AdmittedRelation::mint(
            world(),
            EdgeKind::Equal,
            (NodeId(0), NodeId(1)),
            9,
            JudgmentLane::SingleWorldReplay,
        );
        inner.insert(rel).unwrap();
        assert_eq!(inner.query(world(), EdgeKind::Equal, (NodeId(0), NodeId(1))), QueryStatus::Proven);
        assert_eq!(inner.len_world(world()), 1);
    }

    #[test]
    fn reject_transport_lane() {
        let mut inner = InnerTable::new();
        let rel = AdmittedRelation::mint(
            world(),
            EdgeKind::Equal,
            (NodeId(0), NodeId(1)),
            9,
            JudgmentLane::BootstrapOuterTransport,
        );
        assert_eq!(inner.insert(rel).unwrap_err(), MetisError::ProofInvalid);
        assert!(inner.is_empty());
    }
}
