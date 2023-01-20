//! Bootstrap `Inner(W)` registry (Living `10` opaque checked judgment slice).
//!
//! Stores judgments that have been minted by single-world replay. This is **not** yet
//! a proven least fixed point `μΦ_W`; it is the runtime table CVO may consult for
//! `QueryStatus::Proven` membership under a fixed [`WorldId`] snapshot.
//!
//! Checked evidence is hash-consed into an [`EvidenceDag`] so repeated subterms share nodes.

use std::collections::HashMap;

use metis_types::{EdgeKind, MetisError, NodeId};

use super::{
    admission::{AdmittedRelation, QueryStatus, WorldId, query_status_of_admitted},
    evidence::{Evidence, JudgmentAtom},
    evidence_dag::{EvidenceDag, EvidenceId},
};

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
    by_world: HashMap<WorldId, HashMap<JudgmentKey, InnerEntry>>,
    /// Shared derivation DAG for all checked evidence in this table.
    dag: EvidenceDag,
}

#[derive(Clone, Copy, Debug)]
struct InnerEntry {
    admitted: AdmittedRelation,
    /// Living `10` evidence node when minted via checked replay. Absent for bare bootstrap mints.
    evidence: Option<EvidenceId>,
}

impl InnerTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn evidence_dag(&self) -> &EvidenceDag {
        &self.dag
    }

    /// Insert a SingleWorldReplay token without storing an evidence AST (bootstrap / tests).
    pub fn insert(&mut self, rel: AdmittedRelation) -> Result<(), MetisError> {
        self.insert_entry(rel, None)
    }

    /// Insert a SingleWorldReplay token with its checked evidence (`W;∅ ⊢ e : J`).
    pub fn insert_checked(&mut self, rel: AdmittedRelation, evidence: Evidence) -> Result<(), MetisError> {
        let id = self.dag.intern(&evidence)?;
        self.insert_entry(rel, Some(id))
    }

    fn insert_entry(&mut self, rel: AdmittedRelation, evidence: Option<EvidenceId>) -> Result<(), MetisError> {
        if !rel.is_trusted_path_candidate() {
            return Err(MetisError::ProofInvalid);
        }
        let world = rel.world();
        let key = JudgmentKey::from(rel);
        self.by_world.entry(world).or_default().insert(key, InnerEntry { admitted: rel, evidence });
        Ok(())
    }

    pub fn contains_atom(&self, world: WorldId, atom: JudgmentAtom) -> bool {
        self.by_world.get(&world).is_some_and(|m| m.contains_key(&JudgmentKey::from(atom)))
    }

    pub fn get(&self, world: WorldId, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> Option<AdmittedRelation> {
        let key = JudgmentKey { kind, left: endpoints.0, right: endpoints.1 };
        self.by_world.get(&world)?.get(&key).map(|e| e.admitted)
    }

    /// Shared DAG handle for a checked Inner membership, if any.
    pub fn evidence_id_of(&self, world: WorldId, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> Option<EvidenceId> {
        let key = JudgmentKey { kind, left: endpoints.0, right: endpoints.1 };
        self.by_world.get(&world)?.get(&key)?.evidence
    }

    /// Expand persisted evidence for a checked Inner membership, if any.
    pub fn evidence_of(&self, world: WorldId, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> Option<Evidence> {
        let id = self.evidence_id_of(world, kind, endpoints)?;
        self.dag.expand(id).ok()
    }

    /// Proven iff a checked evidence node is registered for this world snapshot.
    pub fn query(&self, world: WorldId, kind: EdgeKind, endpoints: (NodeId, NodeId)) -> QueryStatus {
        let key = JudgmentKey { kind, left: endpoints.0, right: endpoints.1 };
        match self.by_world.get(&world).and_then(|m| m.get(&key)) {
            Some(entry) if entry.evidence.is_some() => query_status_of_admitted(entry.admitted),
            _ => QueryStatus::Unknown,
        }
    }

    pub fn len_world(&self, world: WorldId) -> usize {
        self.by_world.get(&world).map(|m| m.len()).unwrap_or(0)
    }

    /// Snapshot Equal atoms currently in Inner for `world`, with expanded evidence.
    pub fn equal_memberships(&self, world: WorldId) -> Vec<(JudgmentAtom, Evidence)> {
        self.memberships_of(world, EdgeKind::Equal)
    }

    /// Snapshot checked atoms of `kind` in Inner for `world`.
    pub fn memberships_of(&self, world: WorldId, kind: EdgeKind) -> Vec<(JudgmentAtom, Evidence)> {
        let Some(map) = self.by_world.get(&world)
        else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for (key, entry) in map {
            if key.kind != kind {
                continue;
            }
            let Some(eid) = entry.evidence
            else {
                continue;
            };
            let Ok(evidence) = self.dag.expand(eid)
            else {
                continue;
            };
            out.push((JudgmentAtom { kind, endpoints: (key.left, key.right) }, evidence));
        }
        out
    }

    /// Snapshot all checked atoms in Inner for `world`.
    pub fn memberships(&self, world: WorldId) -> Vec<(JudgmentAtom, Evidence)> {
        let Some(map) = self.by_world.get(&world)
        else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for (key, entry) in map {
            let Some(eid) = entry.evidence
            else {
                continue;
            };
            let Ok(evidence) = self.dag.expand(eid)
            else {
                continue;
            };
            out.push((JudgmentAtom { kind: key.kind, endpoints: (key.left, key.right) }, evidence));
        }
        out
    }

    pub fn is_empty(&self) -> bool {
        self.by_world.values().all(|m| m.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{admission::JudgmentLane, derivation_rules::EQUAL_TRANSITIVITY};
    use core::num::NonZeroU32;
    use metis_types::{EdgeId, IslandId};

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn insert_replay_and_query_proven() {
        let mut inner = InnerTable::new();
        let evidence = Evidence::App {
            rule: "equal_refl".into(),
            premises: Vec::new(),
            conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(0), NodeId(0)) },
        };
        let rel = AdmittedRelation::mint(world(), EdgeKind::Equal, (NodeId(0), NodeId(0)), 9, JudgmentLane::SingleWorldReplay);
        inner.insert_checked(rel, evidence).unwrap();
        assert_eq!(inner.query(world(), EdgeKind::Equal, (NodeId(0), NodeId(0))), QueryStatus::Proven);
        assert_eq!(inner.len_world(world()), 1);
    }

    #[test]
    fn bare_insert_without_evidence_is_not_proven() {
        let mut inner = InnerTable::new();
        let rel = AdmittedRelation::mint(world(), EdgeKind::Equal, (NodeId(0), NodeId(1)), 9, JudgmentLane::SingleWorldReplay);
        inner.insert(rel).unwrap();
        assert_eq!(inner.query(world(), EdgeKind::Equal, (NodeId(0), NodeId(1))), QueryStatus::Unknown);
        assert!(inner.get(world(), EdgeKind::Equal, (NodeId(0), NodeId(1))).is_some());
    }

    #[test]
    fn reject_transport_lane() {
        let mut inner = InnerTable::new();
        let rel =
            AdmittedRelation::mint(world(), EdgeKind::Equal, (NodeId(0), NodeId(1)), 9, JudgmentLane::BootstrapOuterTransport);
        assert_eq!(inner.insert(rel).unwrap_err(), MetisError::ProofInvalid);
        assert!(inner.is_empty());
    }

    #[test]
    fn insert_checked_persists_evidence_ast() {
        let mut inner = InnerTable::new();
        let evidence = Evidence::App {
            rule: "equal_refl".into(),
            premises: Vec::new(),
            conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(0), NodeId(0)) },
        };
        let rel = AdmittedRelation::mint(world(), EdgeKind::Equal, (NodeId(0), NodeId(0)), 1, JudgmentLane::SingleWorldReplay);
        inner.insert_checked(rel, evidence.clone()).unwrap();
        assert_eq!(inner.evidence_of(world(), EdgeKind::Equal, (NodeId(0), NodeId(0))), Some(evidence));
    }

    #[test]
    fn repeated_checked_inserts_share_dag_nodes() {
        let mut inner = InnerTable::new();
        let leaf = Evidence::Gen { edge: EdgeId(3) };
        let shared = Evidence::App {
            rule: EQUAL_TRANSITIVITY.into(),
            premises: vec![leaf.clone(), leaf],
            conclusion: JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(0), NodeId(2)) },
        };
        let w1 = world();
        let w2 = WorldId { island: w1.island, version: 2 };
        let r1 = AdmittedRelation::mint(w1, EdgeKind::Equal, (NodeId(0), NodeId(2)), 1, JudgmentLane::SingleWorldReplay);
        let r2 = AdmittedRelation::mint(w2, EdgeKind::Equal, (NodeId(0), NodeId(2)), 2, JudgmentLane::SingleWorldReplay);
        inner.insert_checked(r1, shared.clone()).unwrap();
        let before = inner.evidence_dag().len();
        inner.insert_checked(r2, shared).unwrap();
        // Second insert reuses Gen + App nodes — DAG length must not grow.
        assert_eq!(inner.evidence_dag().len(), before);
        assert_eq!(
            inner.evidence_id_of(w1, EdgeKind::Equal, (NodeId(0), NodeId(2))),
            inner.evidence_id_of(w2, EdgeKind::Equal, (NodeId(0), NodeId(2)))
        );
    }
}
