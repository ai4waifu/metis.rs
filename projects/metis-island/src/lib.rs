//! Island registry: accepted graphs plus disposable staging arenas.
//!
//! Accepted islands are frozen for mutation. Staging can be discarded or
//! promoted into the accepted table. Each island carries a monotonic
//! [`WorldId::version`] for Core-relative world context.

use std::{
    collections::{HashMap, HashSet},
    num::NonZeroU32,
};

use metis_graph::{
    Graph,
    admission::{AdmittedRelation, AdmittedWorld, ObservationBoundary, QueryStatus, WorldId},
    conflict::{Incompatibility, detect_judgment_conflict},
    connection::{
        AdmittedConnection, CandidateConnection, admit_connection, bidirectional_skeleton, transport_relation,
        transport_relation_asserting, validate_candidate,
    },
    eval::{EvalAttachment, eval_query_status},
    inner::InnerTable,
    rules::RuleTable,
    transform::TransformationSchema,
};
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
    /// Whether further admissions may enter this accepted world version.
    pub observation: ObservationBoundary,
    /// Optional parent / source worlds from `use` (not automatic import of judgments).
    pub parents: Vec<WorldId>,
}

impl Island {
    fn new(name: impl Into<String>, accepted: bool, version: u64) -> Self {
        Self {
            name: name.into(),
            graph: Graph::new(),
            accepted,
            version,
            rules: RuleTable::default(),
            observation: ObservationBoundary::Open,
            parents: Vec::new(),
        }
    }

    /// Relative world handle for Core admission context.
    pub fn world_id(&self, id: IslandId) -> WorldId {
        WorldId { island: id, version: self.version }
    }

    pub const fn is_sealed(&self) -> bool {
        matches!(self.observation, ObservationBoundary::Sealed)
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
    /// Registered M-Link structures \(C_m\). Not transport theorems (`π_T` still absent).
    admitted_connections: Vec<AdmittedConnection>,
    /// Core-admitted worlds minted when staging is accepted or an island is registered.
    admitted_worlds: Vec<AdmittedWorld>,
    /// Outer Eval attachments (Living `08`) — never auto-written as Equal judgments.
    eval_attachments: Vec<EvalAttachment>,
    /// Islands quarantined after an explicit local conflict (does not cascade).
    quarantined: HashSet<IslandId>,
    /// Bootstrap `Inner(W)` projection: SingleWorldReplay judgments only.
    inner: InnerTable,
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
        let world = self.islands.get(&id).unwrap().world_id(id);
        self.admitted_worlds.push(AdmittedWorld::admit(world));
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
    ///
    /// Alias of the Living Core `open_world` role for relative outer/staging contexts.
    pub fn open_staging(&mut self, name: impl Into<String>) -> Result<IslandId, MetisError> {
        let id = self.alloc_id()?;
        self.staging = Some((id, Island::new(name, false, 0)));
        Ok(id)
    }

    /// Living Core name for opening a relative world (staging).
    pub fn open_world(&mut self, name: impl Into<String>) -> Result<IslandId, MetisError> {
        self.open_staging(name)
    }

    pub fn staging_mut(&mut self) -> Result<&mut Island, MetisError> {
        self.staging.as_mut().map(|(_, island)| island).ok_or(MetisError::IslandNotFound)
    }

    /// Record a parent / source world on the current staging island (`use` elaborator).
    ///
    /// Does **not** import judgments. Cross-world facts still require connections.
    pub fn add_staging_parent(&mut self, parent: WorldId) -> Result<(), MetisError> {
        self.require_known_world(parent)?;
        let st = self.staging_mut()?;
        if !st.parents.iter().any(|p| *p == parent) {
            st.parents.push(parent);
        }
        Ok(())
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
    pub fn assert_generating(&mut self, from: NodeId, kind: EdgeKind, to: NodeId) -> Result<EdgeId, MetisError> {
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
        let world = self.islands.get(&id).unwrap().world_id(id);
        self.admitted_worlds.push(AdmittedWorld::admit(world));
        Ok(id)
    }

    pub fn admitted_worlds(&self) -> &[AdmittedWorld] {
        &self.admitted_worlds
    }

    /// Return the admitted world for `island` if its current version was minted.
    pub fn admitted_world_of(&self, island: IslandId) -> Option<AdmittedWorld> {
        let entry = self.islands.get(&island)?;
        let current = entry.world_id(island);
        self.admitted_worlds.iter().copied().find(|w| w.world() == current)
    }

    /// Close the observation boundary for an accepted world version.
    ///
    /// Also freezes the island graph snapshot (`Graph::freeze_snapshot`) so Core
    /// mutation paths cannot write judgment edges. Does **not** call [`Graph::seal`],
    /// which would drop Metis cons tables. Idempotent. Version is unchanged.
    pub fn seal_world(&mut self, island: IslandId) -> Result<AdmittedWorld, MetisError> {
        let entry = self.islands.get_mut(&island).ok_or(MetisError::IslandNotFound)?;
        if !entry.accepted {
            return Err(MetisError::InvalidHandle);
        }
        entry.observation = ObservationBoundary::Sealed;
        entry.graph.freeze_snapshot();
        self.admitted_world_of(island).ok_or(MetisError::InvalidHandle)
    }

    pub fn is_sealed(&self, island: IslandId) -> Result<bool, MetisError> {
        Ok(self.get(island)?.is_sealed())
    }

    fn require_open_target(&self, world: WorldId) -> Result<(), MetisError> {
        self.require_known_world(world)?;
        if self.get(world.island)?.is_sealed() {
            return Err(MetisError::ConnectionInvalid);
        }
        Ok(())
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
    pub fn declare_bidirectional(&mut self, left: IslandId, right: IslandId) -> Result<(usize, usize), MetisError> {
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

    pub fn admitted_connections(&self) -> &[AdmittedConnection] {
        &self.admitted_connections
    }

    /// Alias for [`Self::admitted_connections`]: registered M-Link structures only.
    pub fn registered_m_links(&self) -> &[AdmittedConnection] {
        self.admitted_connections()
    }

    /// Promote a candidate into a registered M-Link structure \(C_m\).
    ///
    /// Rejects bidirectional skeletons and Galois claims. Does **not** mint `π_T` or
    /// authorize trusted Inner transport — only structure maps for Outer bootstrap use.
    pub fn register_m_link(&mut self, index: usize) -> Result<usize, MetisError> {
        let candidate = self.connections.get(index).cloned().ok_or(MetisError::InvalidHandle)?;
        self.require_known_world(candidate.source)?;
        self.require_open_target(candidate.target)?;
        let admitted = admit_connection(&candidate)?;
        self.admitted_connections.push(admitted);
        Ok(self.admitted_connections.len() - 1)
    }

    /// Legacy name for [`Self::register_m_link`].
    pub fn admit_registered_connection(&mut self, index: usize) -> Result<usize, MetisError> {
        self.register_m_link(index)
    }

    /// Register a world-morphism candidate as an M-Link structure (not a transport theorem).
    pub fn register_world_morphism(&mut self, candidate: CandidateConnection) -> Result<usize, MetisError> {
        self.register_connection(candidate.clone())?;
        let idx = self.connections.len() - 1;
        self.register_m_link(idx)
    }

    /// Legacy name for [`Self::register_world_morphism`].
    pub fn admit_world_morphism(&mut self, candidate: CandidateConnection) -> Result<usize, MetisError> {
        self.register_world_morphism(candidate)
    }

    /// Register the identity M-Link for an accepted island's current version.
    pub fn admit_identity(&mut self, island: IslandId) -> Result<usize, MetisError> {
        let world = self.get(island)?.world_id(island);
        self.register_world_morphism(metis_graph::connection::identity_morphism(world))
    }

    /// Compose two registered M-Links and register the composite structure.
    pub fn admit_composed_connection(&mut self, first_index: usize, second_index: usize) -> Result<usize, MetisError> {
        let first = self.admitted_connections.get(first_index).cloned().ok_or(MetisError::InvalidHandle)?;
        let second = self.admitted_connections.get(second_index).cloned().ok_or(MetisError::InvalidHandle)?;
        let candidate = metis_graph::connection::compose_connections(&first, &second)?;
        self.register_world_morphism(candidate)
    }

    /// Bootstrap Outer transport along a registered M-Link index.
    ///
    /// Not Living `10` trusted path. Target world must not be sealed.
    pub fn transport_along(
        &self,
        connection_index: usize,
        relation: AdmittedRelation,
        kind: EdgeKind,
    ) -> Result<AdmittedRelation, MetisError> {
        self.bootstrap_transport_along(connection_index, relation, kind)
    }

    /// Explicit bootstrap alias for [`Self::transport_along`].
    pub fn bootstrap_transport_along(
        &self,
        connection_index: usize,
        relation: AdmittedRelation,
        kind: EdgeKind,
    ) -> Result<AdmittedRelation, MetisError> {
        let conn = self.admitted_connections.get(connection_index).ok_or(MetisError::InvalidHandle)?;
        self.require_known_world(conn.source())?;
        self.require_open_target(conn.target())?;
        transport_relation(conn, relation, kind)
    }

    /// Bootstrap Outer transport that writes a mapped judgment into the target graph.
    ///
    /// Demo helper only. Does **not** establish Inner membership for CVO.
    pub fn transport_and_assert(
        &mut self,
        connection_index: usize,
        relation: AdmittedRelation,
        kind: EdgeKind,
    ) -> Result<(AdmittedRelation, EdgeId), MetisError> {
        self.bootstrap_transport_and_assert(connection_index, relation, kind)
    }

    /// Explicit bootstrap alias for [`Self::transport_and_assert`].
    pub fn bootstrap_transport_and_assert(
        &mut self,
        connection_index: usize,
        relation: AdmittedRelation,
        kind: EdgeKind,
    ) -> Result<(AdmittedRelation, EdgeId), MetisError> {
        let conn = self.admitted_connections.get(connection_index).cloned().ok_or(MetisError::InvalidHandle)?;
        self.require_known_world(conn.source())?;
        self.require_open_target(conn.target())?;
        let target_id = conn.target().island;
        let graph = &mut self.islands.get_mut(&target_id).ok_or(MetisError::IslandNotFound)?.graph;
        transport_relation_asserting(graph, &conn, relation, kind)
    }

    /// Record an Outer Eval attachment. Does **not** assert Equal or mutate the graph.
    pub fn record_eval_attachment(&mut self, attachment: EvalAttachment) -> Result<usize, MetisError> {
        self.require_known_world(attachment.world)?;
        self.eval_attachments.push(attachment);
        Ok(self.eval_attachments.len() - 1)
    }

    pub fn eval_attachments(&self) -> &[EvalAttachment] {
        &self.eval_attachments
    }

    /// Query whether an Outer Eval attachment exists. Always [`QueryStatus::Unknown`] for math.
    pub fn query_eval_at(&self, world: WorldId, position: NodeId) -> Result<QueryStatus, MetisError> {
        self.require_known_world(world)?;
        let found = self.eval_attachments.iter().any(|a| a.world == world && a.position == position);
        Ok(eval_query_status(found))
    }

    /// Refuse promoting a recorded Eval attachment into an Equal judgment.
    pub fn refuse_eval_attachment_as_equal(&self, index: usize) -> Result<(), MetisError> {
        let att = self.eval_attachments.get(index).ok_or(MetisError::InvalidHandle)?;
        metis_graph::eval::refuse_eval_as_equal(att)
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
        &mut self,
        island: IslandId,
        left: metis_types::NodeId,
        right: metis_types::NodeId,
    ) -> Result<(metis_graph::admission::QueryStatus, Option<metis_graph::admission::AdmittedRelation>), MetisError> {
        let entry = self.get(island)?;
        let world = entry.world_id(island);
        let (status, admitted) = metis_graph::derivation::search_and_admit_equal_checked(&entry.graph, world, left, right)?;
        if let Some((rel, evidence)) = admitted {
            self.inner.insert_checked(rel, evidence)?;
            Ok((status, Some(rel)))
        }
        else {
            Ok((status, None))
        }
    }

    /// Query bootstrap `Inner(W)` membership for `Equal(left, right)` under the island world.
    pub fn query_inner_equal(
        &self,
        island: IslandId,
        left: metis_types::NodeId,
        right: metis_types::NodeId,
    ) -> Result<QueryStatus, MetisError> {
        let entry = self.get(island)?;
        let world = entry.world_id(island);
        Ok(self.inner.query(world, EdgeKind::Equal, (left, right)))
    }

    pub fn inner(&self) -> &InnerTable {
        &self.inner
    }

    /// Seed generating Equal edges into bootstrap `Inner(W)` as `gen` evidence (`Φ_W⁰`).
    pub fn seed_inner_equal_generators(&mut self, island: IslandId) -> Result<usize, MetisError> {
        let world = self.get(island)?.world_id(island);
        // Split borrows: graph lives in the island map, Inner is a sibling field.
        let graph = &self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.graph;
        metis_graph::closure::seed_equal_generators(graph, world, &mut self.inner)
    }

    /// Seed all signature-declared generating kinds into bootstrap `Inner(W)`.
    pub fn seed_inner_declared_generators(&mut self, island: IslandId) -> Result<usize, MetisError> {
        let world = self.get(island)?.world_id(island);
        let sig = self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.rules.signature.clone();
        let graph = &self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.graph;
        metis_graph::closure::seed_declared_generators(graph, world, &sig, &mut self.inner)
    }

    /// One Equal `Φ_W` step (symmetry + transitivity) on bootstrap `Inner(W)`.
    pub fn phi_inner_equal_step(&mut self, island: IslandId) -> Result<usize, MetisError> {
        let world = self.get(island)?.world_id(island);
        let graph = &self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.graph;
        metis_graph::closure::phi_equal_step(graph, world, &mut self.inner)
    }

    /// Seed then iterate Equal `Φ_W` steps until fixed point or `max_steps`.
    pub fn saturate_inner_equal(&mut self, island: IslandId, max_steps: u32) -> Result<usize, MetisError> {
        let world = self.get(island)?.world_id(island);
        let graph = &self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.graph;
        metis_graph::closure::saturate_equal_inner(graph, world, &mut self.inner, max_steps)
    }

    /// One rule-table `Φ_W` step using declared transforms with builtin replay support.
    pub fn phi_inner_rule_table_step(&mut self, island: IslandId) -> Result<usize, MetisError> {
        let world = self.get(island)?.world_id(island);
        let rules = self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.rules.clone();
        let graph = &self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.graph;
        metis_graph::closure::phi_rule_table_step(graph, world, &rules, &mut self.inner)
    }

    /// Seed declared generators then alternate Equal / rule-table phi until fixed or capped.
    pub fn saturate_inner_rule_table(&mut self, island: IslandId, max_steps: u32) -> Result<usize, MetisError> {
        let world = self.get(island)?.world_id(island);
        let rules = self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.rules.clone();
        let graph = &self.islands.get(&island).ok_or(MetisError::IslandNotFound)?.graph;
        metis_graph::closure::saturate_rule_table_inner(graph, world, &rules, &mut self.inner, max_steps)
    }

    /// Replay a declared two-premise transform and register it in bootstrap `Inner(W)`.
    pub fn admit_two_premise(
        &mut self,
        island: IslandId,
        schema: &metis_graph::transform::TransformationSchema,
        inst: &metis_graph::transform::TransformationInstance,
    ) -> Result<metis_graph::admission::AdmittedRelation, MetisError> {
        let entry = self.get(island)?;
        let world = entry.world_id(island);
        let registry = metis_graph::derivation_rules::registry_from_rule_table(&entry.rules);
        let (rel, evidence) =
            metis_graph::transform::replay_two_premise_checked_with(&entry.graph, world, schema, inst, &registry)?;
        self.inner.insert_checked(rel, evidence)?;
        Ok(rel)
    }

    /// Admit an EQ [`CandidateRelation`] under the island's current world (Living `admit_relation`).
    pub fn admit_equal_candidate(
        &mut self,
        island: IslandId,
        candidate: metis_graph::admission::CandidateRelation,
    ) -> Result<metis_graph::admission::AdmittedRelation, MetisError> {
        let entry = self.get(island)?;
        let world = entry.world_id(island);
        if candidate.world != world {
            return Err(MetisError::ProofInvalid);
        }
        let (status, pair) = metis_graph::derivation::search_and_admit_equal_checked(
            &entry.graph,
            world,
            candidate.endpoints.0,
            candidate.endpoints.1,
        )?;
        match (status, pair) {
            (QueryStatus::Proven, Some((rel, evidence))) => {
                self.inner.insert_checked(rel, evidence)?;
                Ok(rel)
            }
            _ => Err(MetisError::ProofInvalid),
        }
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
        let adm = store.admitted_world_of(id).expect("admitted world");
        assert_eq!(adm.world(), w);
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
        // Bidirectional skeletons cannot be Core-admitted as morphisms.
        assert_eq!(store.admit_registered_connection(i).unwrap_err(), MetisError::ConnectionInvalid);
        assert!(store.admitted_connections().is_empty());
    }

    #[test]
    fn admit_morphism_and_transport_equal() {
        use metis_graph::connection::ConnectionClass;
        let mut store = IslandStore::new();
        store.open_staging("L").unwrap();
        let (a, b) = {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            st.graph.assert(a, EdgeKind::Equal, b).unwrap();
            (a, b)
        };
        let left = store.accept_staging("Left").unwrap();

        store.open_staging("R").unwrap();
        let (a2, b2) = {
            let st = store.staging_mut().unwrap();
            let a2 = st.graph.intern_label(b"A").unwrap();
            let b2 = st.graph.intern_label(b"B").unwrap();
            (a2, b2)
        };
        let right = store.accept_staging("Right").unwrap();

        let lw = store.get(left).unwrap().world_id(left);
        let rw = store.get(right).unwrap().world_id(right);
        let candidate = CandidateConnection {
            source: lw,
            target: rw,
            class: ConnectionClass::WorldMorphism,
            object_map: HashMap::from([(a, a2), (b, b2)]),
            relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
            lossy: false,
        };
        let cidx = store.admit_world_morphism(candidate).unwrap();
        assert_eq!(store.admitted_connections().len(), 1);

        let rel = store.search_admit_equal(left, a, b).unwrap().1.expect("replay Equal");
        let moved = store.transport_along(cidx, rel, EdgeKind::Equal).unwrap();
        assert_eq!(moved.world(), rw);
        assert_eq!(moved.endpoints(), (a2, b2));
    }

    #[test]
    fn transport_and_assert_writes_accepted_target() {
        use metis_graph::connection::ConnectionClass;
        let mut store = IslandStore::new();
        store.open_staging("L").unwrap();
        let (a, b) = {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            st.graph.assert(a, EdgeKind::Equal, b).unwrap();
            (a, b)
        };
        let left = store.accept_staging("Left").unwrap();
        store.open_staging("R").unwrap();
        let (a2, b2) = {
            let st = store.staging_mut().unwrap();
            (st.graph.intern_label(b"A").unwrap(), st.graph.intern_label(b"B").unwrap())
        };
        let right = store.accept_staging("Right").unwrap();
        let lw = store.get(left).unwrap().world_id(left);
        let rw = store.get(right).unwrap().world_id(right);
        let cidx = store
            .admit_world_morphism(CandidateConnection {
                source: lw,
                target: rw,
                class: ConnectionClass::WorldMorphism,
                object_map: HashMap::from([(a, a2), (b, b2)]),
                relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
                lossy: false,
            })
            .unwrap();
        assert!(store.get_mut(right).is_err());
        let rel = store.search_admit_equal(left, a, b).unwrap().1.expect("replay Equal");
        let (moved, edge) = store.transport_and_assert(cidx, rel, EdgeKind::Equal).unwrap();
        assert_eq!(moved.endpoints(), (a2, b2));
        let (from, kind, to) = store.get(right).unwrap().graph.edge(edge).unwrap();
        assert_eq!((from, kind, to), (a2, EdgeKind::Equal, b2));
        let (st, adm) = store.search_admit_equal(right, a2, b2).unwrap();
        assert_eq!(st, metis_graph::admission::QueryStatus::Proven);
        assert!(adm.is_some());
        // Outer transport token itself must not be a trusted-path candidate.
        assert_eq!(moved.lane(), metis_graph::admission::JudgmentLane::BootstrapOuterTransport);
        assert!(!moved.is_trusted_path_candidate());
        assert_eq!(metis_graph::connection::transport_query_status(moved), metis_graph::admission::QueryStatus::Unknown);
    }

    #[test]
    fn saturate_inner_equal_closes_path() {
        let mut store = IslandStore::new();
        store.open_staging("eq").unwrap();
        store.declare_generating_kind(EdgeKind::Equal).unwrap();
        let (a, b, c) = {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            let c = st.graph.intern_label(b"c").unwrap();
            (a, b, c)
        };
        store.assert_generating(a, EdgeKind::Equal, b).unwrap();
        store.assert_generating(b, EdgeKind::Equal, c).unwrap();
        let id = store.accept_staging("Path").unwrap();
        let n = store.saturate_inner_equal(id, 8).unwrap();
        assert!(n >= 2);
        assert_eq!(store.query_inner_equal(id, a, c).unwrap(), metis_graph::admission::QueryStatus::Proven);
        assert_eq!(store.query_inner_equal(id, c, a).unwrap(), metis_graph::admission::QueryStatus::Proven);
    }

    #[test]
    fn seal_world_blocks_transport_into_target() {
        use metis_graph::connection::ConnectionClass;
        let mut store = IslandStore::new();
        store.open_staging("L").unwrap();
        let (a, b) = {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            st.graph.assert(a, EdgeKind::Equal, b).unwrap();
            (a, b)
        };
        let left = store.accept_staging("Left").unwrap();
        store.open_staging("R").unwrap();
        let (a2, b2) = {
            let st = store.staging_mut().unwrap();
            (st.graph.intern_label(b"A").unwrap(), st.graph.intern_label(b"B").unwrap())
        };
        let right = store.accept_staging("Right").unwrap();
        let lw = store.get(left).unwrap().world_id(left);
        let rw = store.get(right).unwrap().world_id(right);
        let cidx = store
            .admit_world_morphism(CandidateConnection {
                source: lw,
                target: rw,
                class: ConnectionClass::WorldMorphism,
                object_map: HashMap::from([(a, a2), (b, b2)]),
                relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
                lossy: false,
            })
            .unwrap();
        let adm = store.seal_world(right).unwrap();
        assert_eq!(adm.world().version, 1);
        assert!(store.is_sealed(right).unwrap());
        assert!(store.get(right).unwrap().graph.is_snapshot_frozen());
        let rel = store.search_admit_equal(left, a, b).unwrap().1.expect("replay Equal");
        assert_eq!(store.transport_along(cidx, rel, EdgeKind::Equal).unwrap_err(), MetisError::ConnectionInvalid);
        // Sealing source still allows reading it as transport origin once target is open again —
        // here target stays sealed, so only assert source seal is allowed.
        store.seal_world(left).unwrap();
        assert!(store.is_sealed(left).unwrap());
    }

    #[test]
    fn seal_world_blocks_new_morphism_into_target() {
        use metis_graph::connection::ConnectionClass;
        let mut store = IslandStore::new();
        let left = store.register_accepted("L").unwrap();
        let right = store.register_accepted("R").unwrap();
        store.seal_world(right).unwrap();
        let lw = store.get(left).unwrap().world_id(left);
        let rw = store.get(right).unwrap().world_id(right);
        assert_eq!(
            store
                .admit_world_morphism(CandidateConnection {
                    source: lw,
                    target: rw,
                    class: ConnectionClass::WorldMorphism,
                    object_map: HashMap::new(),
                    relation_map: HashMap::new(),
                    lossy: false,
                })
                .unwrap_err(),
            MetisError::ConnectionInvalid
        );
    }

    #[test]
    fn form_compose_and_admit_equal_candidate() {
        use metis_graph::relation::{compose_equal_relations, form_relation};
        let mut store = IslandStore::new();
        let sid = store.open_world("draft").unwrap();
        let (a, b, c) = {
            let st = store.staging_mut().unwrap();
            let a = st.graph.intern_label(b"a").unwrap();
            let b = st.graph.intern_label(b"b").unwrap();
            let c = st.graph.intern_label(b"c").unwrap();
            st.graph.assert(a, EdgeKind::Equal, b).unwrap();
            st.graph.assert(b, EdgeKind::Equal, c).unwrap();
            (a, b, c)
        };
        let id = store.accept_staging("EQ").unwrap();
        assert_eq!(id, sid);
        let world = store.get(id).unwrap().world_id(id);
        let ab = store.admit_equal_candidate(id, form_relation(world, (a, b), None)).unwrap();
        let bc = store.admit_equal_candidate(id, form_relation(world, (b, c), None)).unwrap();
        let cand = compose_equal_relations(ab, bc).unwrap();
        let ac = store.admit_equal_candidate(id, cand).unwrap();
        assert_eq!(ac.endpoints(), (a, c));
    }

    #[test]
    fn staging_parent_does_not_import_judgments() {
        let mut store = IslandStore::new();
        let base = store.register_accepted("Base").unwrap();
        let bw = store.get(base).unwrap().world_id(base);
        store.open_world("ext").unwrap();
        store.add_staging_parent(bw).unwrap();
        let ext = store.accept_staging("Ext").unwrap();
        assert_eq!(store.get(ext).unwrap().parents, vec![bw]);
        // Parent link is metadata only — no automatic EQ path across islands.
        assert!(store.get(ext).unwrap().graph.node_count() == 0);
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
        assert_eq!(store.query_inner_equal(id, a, b).unwrap(), metis_graph::admission::QueryStatus::Proven);
        assert!(store.inner().evidence_of(adm.unwrap().world(), EdgeKind::Equal, (a, b)).is_some());
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
        assert_eq!(store.assert_generating(a, EdgeKind::Equal, b).unwrap_err(), MetisError::ProofInvalid);
        store.declare_generating_kind(EdgeKind::Equal).unwrap();
        store.assert_generating(a, EdgeKind::Equal, b).unwrap();
    }

    /// Living Core first-slice acceptance checklist (smoke).
    #[test]
    fn core_acceptance_smoke_eight_points() {
        use metis_graph::{
            admission::QueryStatus,
            conflict::Incompatibility,
            transform::{TransformationInstance, TransformationSchema},
        };

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
        let world = store.get(id).unwrap().world_id(id);
        // 3–4. searcher proposes instance; kernel replays and admits into Inner
        let schema = TransformationSchema::equal_transitivity();
        let inst = TransformationInstance { premise_a: (a, b), premise_b: (b, c), conclusion: (a, c) };
        let adm = store.admit_two_premise(id, &schema, &inst).unwrap();
        assert_eq!(adm.endpoints(), (a, c));
        assert!(store.inner().evidence_of(world, EdgeKind::Equal, (a, c)).is_some());
        // 5. tamper conclusion → reject
        let bad = TransformationInstance { conclusion: (a, b), ..inst };
        assert!(store.admit_two_premise(id, &schema, &bad).is_err());
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
        let adm2 = store.admit_two_premise(id, &schema, &inst).unwrap();
        assert_eq!(adm.evidence_tag(), adm2.evidence_tag());
    }

    #[test]
    fn eval_attachment_stays_outer_never_equal() {
        use metis_graph::eval::{EvalCertificateKind, form_eval_attachment};
        let mut store = IslandStore::new();
        let id = store.register_accepted("Num").unwrap();
        let world = store.get(id).unwrap().world_id(id);
        let nodes_before = store.get(id).unwrap().graph.node_count();
        let att = form_eval_attachment(world, NodeId(0), 99, EvalCertificateKind::Approximate);
        let idx = store.record_eval_attachment(att).unwrap();
        assert_eq!(store.eval_attachments().len(), 1);
        assert_eq!(store.query_eval_at(world, NodeId(0)).unwrap(), QueryStatus::Unknown);
        assert_eq!(store.refuse_eval_attachment_as_equal(idx).unwrap_err(), MetisError::ProofInvalid);
        assert_eq!(store.get(id).unwrap().graph.node_count(), nodes_before);
    }

    #[test]
    fn admit_identity_and_compose_morphisms() {
        use metis_graph::connection::ConnectionClass;
        let mut store = IslandStore::new();
        let a = store.register_accepted("A").unwrap();
        let b = store.register_accepted("B").unwrap();
        let c = store.register_accepted("C").unwrap();
        let id_a = store.admit_identity(a).unwrap();
        assert_eq!(store.admitted_connections()[id_a].source(), store.get(a).unwrap().world_id(a));
        assert_eq!(store.admitted_connections()[id_a].target(), store.get(a).unwrap().world_id(a));

        let aw = store.get(a).unwrap().world_id(a);
        let bw = store.get(b).unwrap().world_id(b);
        let cw = store.get(c).unwrap().world_id(c);
        let ab = store
            .admit_world_morphism(CandidateConnection {
                source: aw,
                target: bw,
                class: ConnectionClass::WorldMorphism,
                object_map: HashMap::from([(NodeId(0), NodeId(1))]),
                relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::Equal)]),
                lossy: false,
            })
            .unwrap();
        let bc = store
            .admit_world_morphism(CandidateConnection {
                source: bw,
                target: cw,
                class: ConnectionClass::WorldMorphism,
                object_map: HashMap::from([(NodeId(1), NodeId(2))]),
                relation_map: HashMap::from([(EdgeKind::Equal, EdgeKind::In)]),
                lossy: false,
            })
            .unwrap();
        let ac = store.admit_composed_connection(ab, bc).unwrap();
        let comp = &store.admitted_connections()[ac];
        assert_eq!(comp.source(), aw);
        assert_eq!(comp.target(), cw);
        assert_eq!(comp.object_map().get(&NodeId(0)), Some(&NodeId(2)));
        assert_eq!(comp.relation_map().get(&EdgeKind::Equal), Some(&EdgeKind::In));
    }
}
