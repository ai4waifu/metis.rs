//! Shared evidence DAG (Living `10` compression slice).
//!
//! Owned [`super::evidence::Evidence`] trees remain the surface form. This store
//! hash-conses structurally equal subterms so repeated premises share nodes.
//! Sharing is only compression — replay still expands to a finite well-founded term.

use std::collections::HashMap;

use metis_types::{EdgeId, MetisError};

use super::evidence::{Evidence, JudgmentAtom, height, validate_finite};

/// Stable handle into an [`EvidenceDag`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EvidenceId(u32);

impl EvidenceId {
    pub const fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NodeKey {
    Gen { edge: EdgeId },
    Hyp { judgment: JudgmentAtom },
    App { rule: String, premises: Vec<EvidenceId>, conclusion: JudgmentAtom },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Node {
    Gen { edge: EdgeId },
    Hyp { judgment: JudgmentAtom },
    App { rule: String, premises: Vec<EvidenceId>, conclusion: JudgmentAtom },
}

/// Hash-consed evidence DAG for one elaborator / world session.
#[derive(Clone, Debug, Default)]
pub struct EvidenceDag {
    nodes: Vec<Node>,
    cons: HashMap<NodeKey, EvidenceId>,
}

impl EvidenceDag {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Intern an owned evidence tree. Equal subtrees reuse the same [`EvidenceId`].
    pub fn intern(&mut self, evidence: &Evidence) -> Result<EvidenceId, MetisError> {
        validate_finite(evidence)?;
        self.intern_unchecked(evidence)
    }

    fn intern_unchecked(&mut self, evidence: &Evidence) -> Result<EvidenceId, MetisError> {
        match evidence {
            Evidence::Gen { edge } => self.intern_key(NodeKey::Gen { edge: *edge }),
            Evidence::Hyp { judgment } => self.intern_key(NodeKey::Hyp { judgment: *judgment }),
            Evidence::App { rule, premises, conclusion } => {
                let mut prem_ids = Vec::with_capacity(premises.len());
                for p in premises {
                    prem_ids.push(self.intern_unchecked(p)?);
                }
                self.intern_key(NodeKey::App { rule: rule.clone(), premises: prem_ids, conclusion: *conclusion })
            }
        }
    }

    fn intern_key(&mut self, key: NodeKey) -> Result<EvidenceId, MetisError> {
        if let Some(id) = self.cons.get(&key) {
            return Ok(*id);
        }
        if self.nodes.len() >= u32::MAX as usize {
            return Err(MetisError::Capacity);
        }
        let id = EvidenceId(self.nodes.len() as u32);
        let node = match &key {
            NodeKey::Gen { edge } => Node::Gen { edge: *edge },
            NodeKey::Hyp { judgment } => Node::Hyp { judgment: *judgment },
            NodeKey::App { rule, premises, conclusion } => {
                Node::App { rule: rule.clone(), premises: premises.clone(), conclusion: *conclusion }
            }
        };
        self.nodes.push(node);
        self.cons.insert(key, id);
        Ok(id)
    }

    /// Expand a shared node back into an owned tree (sharing is lost on expand).
    pub fn expand(&self, id: EvidenceId) -> Result<Evidence, MetisError> {
        let node = self.nodes.get(id.0 as usize).ok_or(MetisError::InvalidHandle)?;
        Ok(match node {
            Node::Gen { edge } => Evidence::Gen { edge: *edge },
            Node::Hyp { judgment } => Evidence::Hyp { judgment: *judgment },
            Node::App { rule, premises, conclusion } => {
                let mut prem = Vec::with_capacity(premises.len());
                for p in premises {
                    prem.push(self.expand(*p)?);
                }
                Evidence::App { rule: rule.clone(), premises: prem, conclusion: *conclusion }
            }
        })
    }

    /// Living height on the DAG (same measure as the expanded tree).
    pub fn height_of(&self, id: EvidenceId) -> Result<u32, MetisError> {
        let evidence = self.expand(id)?;
        Ok(height(&evidence))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use metis_types::{EdgeKind, NodeId};

    use crate::derivation_rules::EQUAL_TRANSITIVITY;

    fn eq(a: u64, b: u64) -> JudgmentAtom {
        JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(a), NodeId(b)) }
    }

    #[test]
    fn identical_subtrees_share_one_node() {
        let mut dag = EvidenceDag::new();
        let leaf = Evidence::Gen { edge: EdgeId(7) };
        let left =
            Evidence::App { rule: EQUAL_TRANSITIVITY.into(), premises: vec![leaf.clone(), leaf.clone()], conclusion: eq(0, 2) };
        let id = dag.intern(&left).unwrap();
        // Gen once + App once = 2 nodes (not 3).
        assert_eq!(dag.len(), 2);
        let again = dag.intern(&left).unwrap();
        assert_eq!(id, again);
        assert_eq!(dag.len(), 2);
        assert_eq!(dag.expand(id).unwrap(), left);
    }

    #[test]
    fn distinct_gens_are_not_shared() {
        let mut dag = EvidenceDag::new();
        let a = Evidence::Gen { edge: EdgeId(1) };
        let b = Evidence::Gen { edge: EdgeId(2) };
        let ia = dag.intern(&a).unwrap();
        let ib = dag.intern(&b).unwrap();
        assert_ne!(ia, ib);
        assert_eq!(dag.len(), 2);
    }
}
