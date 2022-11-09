//! Island registry: accepted graphs plus disposable staging arenas.
//!
//! Accepted islands are frozen for mutation. Staging can be discarded or
//! promoted into the accepted table. Each island carries a monotonic
//! [`WorldId::version`] for Core-relative world context.

use std::{collections::HashMap, num::NonZeroU32};

use metis_graph::admission::WorldId;
use metis_graph::connection::{
    CandidateConnection, bidirectional_skeleton, refuse_galois_without_proof, validate_candidate,
};
use metis_graph::Graph;
use metis_types::{IslandId, MetisError};

/// Named island entry.
pub struct Island {
    pub name: String,
    pub graph: Graph,
    pub accepted: bool,
    /// Monotonic world version (bumped when staging is accepted).
    pub version: u64,
}

impl Island {
    /// Relative world handle for Core admission context.
    pub fn world_id(&self, id: IslandId) -> WorldId {
        WorldId { island: id, version: self.version }
    }
}

/// Store of islands plus one optional staging workspace.
#[derive(Default)]
pub struct IslandStore {
    islands: HashMap<IslandId, Island>,
    by_name: HashMap<String, IslandId>,
    next_id: u32,
    staging: Option<(IslandId, Island)>,
    /// Candidate connections only — never auto-admitted as Galois.
    connections: Vec<CandidateConnection>,
}

impl IslandStore {
    pub fn new() -> Self {
        Self::default()
    }

    fn alloc_id(&mut self) -> Result<IslandId, MetisError> {
        self.next_id = self.next_id.checked_add(1).ok_or(MetisError::Capacity)?;
        let raw = NonZeroU32::new(self.next_id).ok_or(MetisError::Capacity)?;
        Ok(IslandId::from_raw(raw))
    }

    /// Register an accepted island loaded from compiled sources (foundation: empty graph ok).
    pub fn register_accepted(&mut self, name: impl Into<String>) -> Result<IslandId, MetisError> {
        let name = name.into();
        if self.by_name.contains_key(&name) {
            return Err(MetisError::InvalidHandle);
        }
        let id = self.alloc_id()?;
        self.by_name.insert(name.clone(), id);
        self.islands.insert(
            id,
            Island { name, graph: Graph::new(), accepted: true, version: 1 },
        );
        Ok(id)
    }

    pub fn get(&self, id: IslandId) -> Result<&Island, MetisError> {
        self.islands.get(&id).ok_or(MetisError::IslandNotFound)
    }

    pub fn get_mut(&mut self, id: IslandId) -> Result<&mut Island, MetisError> {
        let island = self.islands.get_mut(&id).ok_or(MetisError::IslandNotFound)?;
        if island.accepted {
            return Err(MetisError::InvalidHandle);
        }
        Ok(island)
    }

    pub fn lookup(&self, name: &str) -> Option<IslandId> {
        self.by_name.get(name).copied()
    }

    /// Open a disposable staging island. Replaces any previous staging.
    pub fn open_staging(&mut self, name: impl Into<String>) -> Result<IslandId, MetisError> {
        let id = self.alloc_id()?;
        self.staging = Some((
            id,
            Island { name: name.into(), graph: Graph::new(), accepted: false, version: 0 },
        ));
        Ok(id)
    }

    pub fn staging_mut(&mut self) -> Result<&mut Island, MetisError> {
        self.staging.as_mut().map(|(_, island)| island).ok_or(MetisError::IslandNotFound)
    }

    pub fn staging_id(&self) -> Option<IslandId> {
        self.staging.as_ref().map(|(id, _)| *id)
    }

    /// Discard the staging arena entirely.
    pub fn discard_staging(&mut self) {
        self.staging = None;
    }

    /// Promote current staging into the accepted table under `as_name`.
    ///
    /// Keeps the staging [`IslandId`]. Bumps [`Island::version`]. Does **not** call
    /// [`Graph::seal`] — Metis judgment / hash-cons state must remain for verify.
    pub fn accept_staging(&mut self, as_name: impl Into<String>) -> Result<IslandId, MetisError> {
        let name = as_name.into();
        if self.by_name.contains_key(&name) {
            return Err(MetisError::InvalidHandle);
        }
        let (id, mut island) = self.staging.take().ok_or(MetisError::IslandNotFound)?;
        island.name = name.clone();
        island.accepted = true;
        island.version = island.version.saturating_add(1);
        self.by_name.insert(name, id);
        self.islands.insert(id, island);
        Ok(id)
    }

    fn require_known_world(&self, world: WorldId) -> Result<(), MetisError> {
        let island = self.get(world.island)?;
        if island.version != world.version {
            return Err(MetisError::ConnectionInvalid);
        }
        Ok(())
    }

    /// Register a validated candidate connection (still outer-world / unverified transport).
    ///
    /// Bidirectional skeletons are allowed as candidates. They are **not** admitted Galois links.
    pub fn register_connection(&mut self, candidate: CandidateConnection) -> Result<(), MetisError> {
        validate_candidate(&candidate)?;
        self.require_known_world(candidate.source)?;
        self.require_known_world(candidate.target)?;
        self.connections.push(candidate);
        Ok(())
    }

    /// Declare surface `A <-> B` skeletons between two accepted islands' current worlds.
    pub fn declare_bidirectional(
        &mut self,
        left: IslandId,
        right: IslandId,
    ) -> Result<(usize, usize), MetisError> {
        let lw = self.get(left)?.world_id(left);
        let rw = self.get(right)?.world_id(right);
        let (fwd, back) = bidirectional_skeleton(lw, rw, HashMap::new(), HashMap::new())?;
        self.register_connection(fwd)?;
        self.register_connection(back)?;
        let n = self.connections.len();
        Ok((n - 2, n - 1))
    }

    pub fn connections(&self) -> &[CandidateConnection] {
        &self.connections
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use metis_types::EdgeKind;

    #[test]
    fn accepted_is_frozen_staging_is_mutable() {
        let mut store = IslandStore::new();
        let zfc = store.register_accepted("ZFC").unwrap();
        assert!(store.get_mut(zfc).is_err());

        let sid = store.open_staging("explore").unwrap();
        assert_eq!(store.staging_id(), Some(sid));
        {
            let st = store.staging_mut().unwrap();
            let leaf = st.graph.intern_empty().unwrap();
            let _ = st.graph.intern(&[(EdgeKind::In, leaf)]).unwrap();
            assert_eq!(st.graph.node_count(), 2);
        }
        store.discard_staging();
        assert!(store.staging_mut().is_err());
    }

    #[test]
    fn accept_staging_freezes_and_versions() {
        let mut store = IslandStore::new();
        let sid = store.open_staging("draft").unwrap();
        {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            st.graph.assert(a, EdgeKind::Equal, b).unwrap();
            assert_eq!(st.version, 0);
        }
        let id = store.accept_staging("Group").unwrap();
        assert_eq!(id, sid);
        assert!(store.staging_id().is_none());
        let island = store.get(id).unwrap();
        assert!(island.accepted);
        assert_eq!(island.version, 1);
        assert_eq!(island.name, "Group");
        assert_eq!(island.graph.node_count(), 2);
        let w = island.world_id(id);
        assert_eq!(w.island, id);
        assert_eq!(w.version, 1);
        assert!(store.get_mut(id).is_err());
    }

    #[test]
    fn accept_staging_rejects_name_clash() {
        let mut store = IslandStore::new();
        store.register_accepted("Group").unwrap();
        store.open_staging("draft").unwrap();
        assert_eq!(store.accept_staging("Group").unwrap_err(), MetisError::InvalidHandle);
        assert!(store.staging_id().is_some());
    }

    #[test]
    fn bidirectional_connection_between_accepted_islands() {
        use metis_graph::connection::ConnectionClass;
        let mut store = IslandStore::new();
        let a = store.register_accepted("ZFC").unwrap();
        let b = store.register_accepted("HoTT").unwrap();
        let (i, j) = store.declare_bidirectional(a, b).unwrap();
        assert_eq!(store.connections().len(), 2);
        assert_eq!(store.connections()[i].class, ConnectionClass::BidirectionalSkeleton);
        assert_eq!(store.connections()[j].source.island, b);
        assert!(refuse_galois_without_proof(&store.connections()[i]).is_err());
    }
}
