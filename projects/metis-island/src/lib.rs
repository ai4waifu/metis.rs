//! Island registry: accepted graphs plus disposable staging arenas.

use std::collections::HashMap;
use std::num::NonZeroU32;

use metis_graph::Graph;
use metis_types::{IslandId, MetisError};

/// Named island entry. Accepted islands are treated as read-mostly for now.
pub struct Island {
    pub name: String,
    pub graph: Graph,
    pub accepted: bool,
}

/// Store of islands plus one optional staging workspace.
#[derive(Default)]
pub struct IslandStore {
    islands: HashMap<IslandId, Island>,
    by_name: HashMap<String, IslandId>,
    next_id: u32,
    staging: Option<(IslandId, Island)>,
}

impl IslandStore {
    pub fn new() -> Self {
        Self::default()
    }

    fn alloc_id(&mut self) -> Result<IslandId, MetisError> {
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or(MetisError::Capacity)?;
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
            Island {
                name,
                graph: Graph::new(),
                accepted: true,
            },
        );
        Ok(id)
    }

    pub fn get(&self, id: IslandId) -> Result<&Island, MetisError> {
        self.islands.get(&id).ok_or(MetisError::IslandNotFound)
    }

    pub fn get_mut(&mut self, id: IslandId) -> Result<&mut Island, MetisError> {
        let island = self.islands.get_mut(&id).ok_or(MetisError::IslandNotFound)?;
        if island.accepted {
            // Foundation: accepted islands stay structurally frozen.
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
            Island {
                name: name.into(),
                graph: Graph::new(),
                accepted: false,
            },
        ));
        Ok(id)
    }

    pub fn staging_mut(&mut self) -> Result<&mut Island, MetisError> {
        self.staging
            .as_mut()
            .map(|(_, island)| island)
            .ok_or(MetisError::IslandNotFound)
    }

    pub fn staging_id(&self) -> Option<IslandId> {
        self.staging.as_ref().map(|(id, _)| *id)
    }

    /// Discard the staging arena entirely.
    pub fn discard_staging(&mut self) {
        self.staging = None;
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
}
