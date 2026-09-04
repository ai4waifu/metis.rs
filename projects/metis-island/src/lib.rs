//! Island registry: accepted graphs plus disposable staging arenas.
//!
//! Accepted islands are frozen for mutation. Staging can be discarded or
//! promoted into the accepted table. Each island carries a monotonic
//! [`WorldId::version`] for Core-relative world context.

use std::{
    collections::{HashMap, HashSet},
    num::NonZeroU32,
};

use metis_graph::admission::WorldId;
use metis_graph::conflict::{Incompatibility, detect_judgment_conflict};
use metis_graph::connection::{CandidateConnection, bidirectional_skeleton, validate_candidate};
use metis_graph::rules::RuleTable;
use metis_graph::transform::TransformationSchema;
use metis_graph::Graph;
use metis_types::{EdgeId, EdgeKind, IslandId, MetisError, NodeId};

/// Named island entry.
pub struct Island {
    pub name: String,
    pub graph: Graph,
    pub accepted: bool,
    /// Monotonic world version (bumped when staging is accepted).
    pub version: u64,
    /// Declared generating kinds + transformation schemas for this world.
    pub rules: RuleTable,
}

impl Island {
    fn new(name: impl Into<String>, accepted: bool, version: u64) -> Self {
        Self {
            name: name.into(),
            graph: Graph::new(),
            accepted,
            version,
            rules: RuleTable::default(),
        }
    }

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
    /// Islands quarantined after an explicit local conflict (does not cascade).
    quarantined: HashSet<IslandId>,
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
        self.islands.insert(id, Island::new(name, true, 1));
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
        self.staging = Some((id, Island::new(name, false, 0)));
        Ok(id)
    }

    pub fn staging_mut(&mut self) -> Result<&mut Island, MetisError> {
        self.staging.as_mut().map(|(_, island)| island).ok_or(MetisError::IslandNotFound)
    }

    /// Declare a generating relation kind on the current staging island.
    pub fn declare_generating_kind(&mut self, kind: EdgeKind) -> Result<(), MetisError> {
        self.staging_mut()?.rules.declare_kind(kind);
        Ok(())
    }

    /// Declare a transformation schema on the current staging island.
    pub fn declare_transform(&mut self, schema: TransformationSchema) -> Result<(), MetisError> {
        self.staging_mut()?.rules.add_transform(schema);
        Ok(())
    }

    /// Assert a generating judgment only if the kind was declared in the staging rule table.
    pub fn assert_generating(
        &mut self,
        from: NodeId,
        kind: EdgeKind,
        to: NodeId,
    ) -> Result<EdgeId, MetisError> {
        let st = self.staging_mut()?;
        if !st.rules.signature.allows(kind) {
            return Err(MetisError::ProofInvalid);
        }
        st.graph.assert(from, kind, to)
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

    /// Admit an EQ derivation only if `diagram.world` matches the island's current version.
    pub fn admit_equal(
        &self,
        island: IslandId,
        diagram: &metis_graph::derivation::DerivationDiagram,
    ) -> Result<metis_graph::admission::AdmittedRelation, MetisError> {
        let entry = self.get(island)?;
        let current = entry.world_id(island);
        if diagram.world != current {
            return Err(MetisError::ProofInvalid);
        }
        metis_graph::derivation::replay_equal_derivation(&entry.graph, diagram)
    }

    /// Search-and-admit EQ under the island's current [`WorldId`].
    pub fn search_admit_equal(
        &self,
        island: IslandId,
        left: metis_types::NodeId,
        right: metis_types::NodeId,
    ) -> Result<(metis_graph::admission::QueryStatus, Option<metis_graph::admission::AdmittedRelation>), MetisError> {
        let entry = self.get(island)?;
        let world = entry.world_id(island);
        metis_graph::derivation::search_and_admit_equal(&entry.graph, world, left, right)
    }

    pub fn is_quarantined(&self, island: IslandId) -> bool {
        self.quarantined.contains(&island)
    }

    /// Detect an endpoint conflict under `policy`. On hit, quarantine **only** that island.
    pub fn report_conflict(
        &mut self,
        island: IslandId,
        endpoints: (NodeId, NodeId),
        policy: Incompatibility,
    ) -> Result<Option<metis_graph::admission::ConflictReport>, MetisError> {
        let report = {
            let entry = self.get(island)?;
            let world = entry.world_id(island);
            detect_judgment_conflict(&entry.graph, world, endpoints, policy)?
        };
        if report.is_some() {
            self.quarantined.insert(island);
        }
        Ok(report)
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
        use metis_graph::connection::{ConnectionClass, refuse_galois_without_proof};
        let mut store = IslandStore::new();
        let a = store.register_accepted("ZFC").unwrap();
        let b = store.register_accepted("HoTT").unwrap();
        let (i, j) = store.declare_bidirectional(a, b).unwrap();
        assert_eq!(store.connections().len(), 2);
        assert_eq!(store.connections()[i].class, ConnectionClass::BidirectionalSkeleton);
        assert_eq!(store.connections()[j].source.island, b);
        assert!(refuse_galois_without_proof(&store.connections()[i]).is_err());
    }

    #[test]
    fn conflict_quarantines_only_that_island() {
        use metis_graph::conflict::Incompatibility;
        const NOT_EQ: u16 = 7;
        let mut store = IslandStore::new();
        let a = store.register_accepted("A").unwrap();
        let b = store.register_accepted("B").unwrap();
        // Put conflict only in A via staging→accept would freeze empty; mutate before accept:
        let sid = store.open_staging("draft").unwrap();
        let (x, y) = {
            let st = store.staging_mut().unwrap();
            let x = st.graph.intern_label(b"x").unwrap();
            let y = st.graph.intern_label(b"y").unwrap();
            st.graph.assert(x, EdgeKind::Equal, y).unwrap();
            st.graph.assert(x, EdgeKind::Custom(NOT_EQ), y).unwrap();
            (x, y)
        };
        let a2 = store.accept_staging("A2").unwrap();
        assert_eq!(a2, sid);
        let policy = Incompatibility::equal_vs_custom_not_equal(NOT_EQ);
        let report = store.report_conflict(a2, (x, y), policy).unwrap();
        assert!(report.is_some());
        assert!(store.is_quarantined(a2));
        assert!(!store.is_quarantined(a));
        assert!(!store.is_quarantined(b));
    }

    #[test]
    fn admit_equal_rejects_stale_world_version() {
        use metis_graph::derivation::DerivationDiagram;
        let mut store = IslandStore::new();
        let sid = store.open_staging("draft").unwrap();
        let (a, b) = {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            st.graph.assert(a, EdgeKind::Equal, b).unwrap();
            (a, b)
        };
        let id = store.accept_staging("G").unwrap();
        assert_eq!(id, sid);
        let stale = DerivationDiagram {
            world: WorldId { island: id, version: 0 },
            conclusion: (a, b),
            steps: store.get(id).unwrap().graph.find_equal_path(a, b).unwrap().unwrap(),
        };
        assert_eq!(store.admit_equal(id, &stale).unwrap_err(), MetisError::ProofInvalid);
        let (st, adm) = store.search_admit_equal(id, a, b).unwrap();
        assert_eq!(st, metis_graph::admission::QueryStatus::Proven);
        assert!(adm.is_some());
    }

    #[test]
    fn generating_kind_must_be_declared_before_assert() {
        let mut store = IslandStore::new();
        store.open_staging("draft").unwrap();
        let (a, b) = {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            (a, b)
        };
        assert_eq!(
            store.assert_generating(a, EdgeKind::Equal, b).unwrap_err(),
            MetisError::ProofInvalid
        );
        store.declare_generating_kind(EdgeKind::Equal).unwrap();
        store.assert_generating(a, EdgeKind::Equal, b).unwrap();
    }

    /// Living Core first-slice acceptance checklist (smoke).
    #[test]
    fn core_acceptance_smoke_eight_points() {
        use metis_graph::admission::QueryStatus;
        use metis_graph::conflict::Incompatibility;
        use metis_graph::transform::{TransformationInstance, TransformationSchema, replay_two_premise};

        const NOT_EQ: u16 = 9;
        let mut store = IslandStore::new();
        // 1. declare generating kinds
        store.open_staging("eq").unwrap();
        store.declare_generating_kind(EdgeKind::Equal).unwrap();
        store.declare_generating_kind(EdgeKind::Custom(NOT_EQ)).unwrap();
        // 2. declare two-premise transform
        store.declare_transform(TransformationSchema::equal_transitivity()).unwrap();
        let (a, b, c) = {
            let st = store.staging_mut().unwrap();
            assert!(st.rules.has_transform("equal_transitivity"));
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            let c = st.graph.intern_label(b"c").unwrap();
            (a, b, c)
        };
        store.assert_generating(a, EdgeKind::Equal, b).unwrap();
        store.assert_generating(b, EdgeKind::Equal, c).unwrap();
        let id = store.accept_staging("EQ").unwrap();
        let island = store.get(id).unwrap();
        let world = island.world_id(id);
        // 3–4. searcher proposes instance; kernel replays and admits
        let schema = TransformationSchema::equal_transitivity();
        let inst = TransformationInstance {
            premise_a: (a, b),
            premise_b: (b, c),
            conclusion: (a, c),
        };
        let adm = replay_two_premise(&island.graph, world, &schema, &inst).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
        // 5. tamper conclusion → reject
        let bad = TransformationInstance { conclusion: (a, b), ..inst };
        assert!(replay_two_premise(&island.graph, world, &schema, &bad).is_err());
        // 6. missing path → Unknown
        store.open_staging("u").unwrap();
        store.declare_generating_kind(EdgeKind::Equal).unwrap();
        let (x, y) = {
            let st = store.staging_mut().unwrap();
            (st.graph.intern_label(b"x").unwrap(), st.graph.intern_label(b"y").unwrap())
        };
        let uid = store.accept_staging("U").unwrap();
        let (st, none) = store.search_admit_equal(uid, x, y).unwrap();
        assert_eq!(st, QueryStatus::Unknown);
        assert!(none.is_none());
        // 7. conflict isolates only that island
        store.open_staging("c").unwrap();
        store.declare_generating_kind(EdgeKind::Equal).unwrap();
        store.declare_generating_kind(EdgeKind::Custom(NOT_EQ)).unwrap();
        let (p, q) = {
            let st = store.staging_mut().unwrap();
            let p = st.graph.intern_label(b"p").unwrap();
            let q = st.graph.intern_label(b"q").unwrap();
            (p, q)
        };
        store.assert_generating(p, EdgeKind::Equal, q).unwrap();
        store.assert_generating(p, EdgeKind::Custom(NOT_EQ), q).unwrap();
        let cid = store.accept_staging("C").unwrap();
        let policy = Incompatibility::equal_vs_custom_not_equal(NOT_EQ);
        assert!(store.report_conflict(cid, (p, q), policy).unwrap().is_some());
        assert!(store.is_quarantined(cid));
        assert!(!store.is_quarantined(id));
        // 8. same evidence → same tag
        let adm2 = replay_two_premise(&store.get(id).unwrap().graph, world, &schema, &inst).unwrap();
        assert_eq!(adm.evidence_tag(), adm2.evidence_tag());
    }
}
