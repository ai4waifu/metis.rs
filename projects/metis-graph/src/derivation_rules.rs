//! Derivation rule registry for evidence replay (Living `10` finite DAG slice).
//!
//! Search proposes `app(ρ, …)` by name. Replay looks up `ρ` in builtins first, then in
//! registered two-premise chain rules (shared middle endpoint, optional fixed ends).

use std::collections::HashMap;

use metis_types::{EdgeKind, MetisError};

use super::evidence::JudgmentAtom;
use super::transform::{PremisePattern, TransformationSchema};

/// Reflexivity: `Equal(x, x)` with zero premises.
pub const EQUAL_REFL: &str = "equal_refl";
/// Symmetry: `Equal(x, y)` ⇒ `Equal(y, x)`.
pub const EQUAL_SYMMETRY: &str = "equal_symmetry";
/// Transitivity: `Equal(x, y)` and `Equal(y, z)` ⇒ `Equal(x, z)`.
pub const EQUAL_TRANSITIVITY: &str = "equal_transitivity";

/// Names registered in the bootstrap derivation rule table.
pub fn builtin_rule_names() -> &'static [&'static str] {
    &[EQUAL_REFL, EQUAL_SYMMETRY, EQUAL_TRANSITIVITY]
}

pub fn is_builtin_rule(name: &str) -> bool {
    builtin_rule_names().contains(&name)
}

/// Two-premise chain rule: `R(x,y)` and `S(y,z)` ⇒ `T(x,z)`, with optional fixed ends.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainRule {
    pub name: String,
    pub premise_a: PremisePattern,
    pub premise_b: PremisePattern,
    pub conclusion: EdgeKind,
}

impl ChainRule {
    /// Build a chain rule from a two-premise schema (fixed endpoints preserved).
    pub fn from_schema(schema: &TransformationSchema) -> Result<Self, MetisError> {
        if schema.name.is_empty() {
            return Err(MetisError::ProofInvalid);
        }
        Ok(Self {
            name: schema.name.clone(),
            premise_a: schema.premise_a,
            premise_b: schema.premise_b,
            conclusion: schema.conclusion_kind,
        })
    }

    /// Unconstrained chain over a single kind (compat helper for tests / simple declares).
    pub fn unconstrained(name: impl Into<String>, kind: EdgeKind, conclusion: EdgeKind) -> Self {
        Self {
            name: name.into(),
            premise_a: PremisePattern { kind, from: None, to: None },
            premise_b: PremisePattern { kind, from: None, to: None },
            conclusion,
        }
    }
}

/// Builtin EQ rules plus island-declared chain rules.
#[derive(Clone, Debug, Default)]
pub struct DerivationRegistry {
    chains: HashMap<String, ChainRule>,
}

impl DerivationRegistry {
    pub fn builtins() -> Self {
        Self::default()
    }

    /// Register a custom chain rule. Builtin names and duplicates are rejected.
    pub fn register_chain(&mut self, rule: ChainRule) -> Result<(), MetisError> {
        if rule.name.is_empty() || is_builtin_rule(&rule.name) {
            return Err(MetisError::InvalidHandle);
        }
        if self.chains.contains_key(&rule.name) {
            return Err(MetisError::InvalidHandle);
        }
        self.chains.insert(rule.name.clone(), rule);
        Ok(())
    }

    pub fn has_rule(&self, name: &str) -> bool {
        is_builtin_rule(name) || self.chains.contains_key(name)
    }

    pub fn chain(&self, name: &str) -> Option<&ChainRule> {
        self.chains.get(name)
    }

    /// Apply builtin or registered chain rule to already-replayed premises.
    pub fn apply(
        &self,
        name: &str,
        premises: &[JudgmentAtom],
        conclusion: JudgmentAtom,
    ) -> Result<JudgmentAtom, MetisError> {
        if is_builtin_rule(name) {
            return apply_builtin_rule(name, premises, conclusion);
        }
        let rule = self.chains.get(name).ok_or(MetisError::ProofInvalid)?;
        if premises.len() != 2 {
            return Err(MetisError::ProofInvalid);
        }
        let j0 = premises[0];
        let j1 = premises[1];
        if !rule.premise_a.matches_atom(j0) || !rule.premise_b.matches_atom(j1) {
            return Err(MetisError::ProofInvalid);
        }
        let (x, y1) = j0.endpoints;
        let (y2, z) = j1.endpoints;
        if y1 != y2 {
            return Err(MetisError::ProofInvalid);
        }
        if conclusion.kind != rule.conclusion || conclusion.endpoints != (x, z) {
            return Err(MetisError::ProofInvalid);
        }
        Ok(conclusion)
    }
}

/// Check that `premises` (already replayed) justify `conclusion` under builtin rule `name`.
pub fn apply_builtin_rule(
    name: &str,
    premises: &[JudgmentAtom],
    conclusion: JudgmentAtom,
) -> Result<JudgmentAtom, MetisError> {
    match name {
        EQUAL_REFL => {
            if !premises.is_empty() {
                return Err(MetisError::ProofInvalid);
            }
            let (a, b) = conclusion.endpoints;
            if conclusion.kind != EdgeKind::Equal || a != b {
                return Err(MetisError::ProofInvalid);
            }
            Ok(conclusion)
        }
        EQUAL_SYMMETRY => {
            if premises.len() != 1 {
                return Err(MetisError::ProofInvalid);
            }
            let j0 = premises[0];
            if j0.kind != EdgeKind::Equal || conclusion.kind != EdgeKind::Equal {
                return Err(MetisError::ProofInvalid);
            }
            let (x, y) = j0.endpoints;
            if conclusion.endpoints != (y, x) {
                return Err(MetisError::ProofInvalid);
            }
            Ok(conclusion)
        }
        EQUAL_TRANSITIVITY => {
            if premises.len() != 2 {
                return Err(MetisError::ProofInvalid);
            }
            let j0 = premises[0];
            let j1 = premises[1];
            if j0.kind != EdgeKind::Equal || j1.kind != EdgeKind::Equal {
                return Err(MetisError::ProofInvalid);
            }
            let (x, y1) = j0.endpoints;
            let (y2, z) = j1.endpoints;
            if y1 != y2 {
                return Err(MetisError::ProofInvalid);
            }
            if conclusion.kind != EdgeKind::Equal || conclusion.endpoints != (x, z) {
                return Err(MetisError::ProofInvalid);
            }
            Ok(conclusion)
        }
        _ => Err(MetisError::ProofInvalid),
    }
}

/// Build a registry from a [`super::rules::RuleTable`]: builtins + auto chain rules for transforms.
pub fn registry_from_rule_table(rules: &super::rules::RuleTable) -> DerivationRegistry {
    let mut reg = DerivationRegistry::builtins();
    for schema in &rules.transforms {
        if is_builtin_rule(&schema.name) {
            continue;
        }
        if let Ok(chain) = ChainRule::from_schema(schema) {
            let _ = reg.register_chain(chain);
        }
    }
    reg
}

#[cfg(test)]
mod tests {
    use super::*;
    use metis_types::NodeId;

    #[test]
    fn symmetry_flips_endpoints() {
        let prem = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(1), NodeId(2)) };
        let conc = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(2), NodeId(1)) };
        assert_eq!(apply_builtin_rule(EQUAL_SYMMETRY, &[prem], conc).unwrap(), conc);
        let bad = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(1), NodeId(2)) };
        assert!(apply_builtin_rule(EQUAL_SYMMETRY, &[prem], bad).is_err());
    }

    #[test]
    fn unknown_rule_rejected() {
        let j = JudgmentAtom { kind: EdgeKind::Equal, endpoints: (NodeId(0), NodeId(0)) };
        assert!(apply_builtin_rule("nope", &[], j).is_err());
        assert!(DerivationRegistry::builtins().apply("nope", &[], j).is_err());
    }

    #[test]
    fn custom_chain_rule_replays() {
        let mut reg = DerivationRegistry::builtins();
        reg.register_chain(ChainRule::unconstrained("in_compose", EdgeKind::In, EdgeKind::In))
            .unwrap();
        let p0 = JudgmentAtom { kind: EdgeKind::In, endpoints: (NodeId(0), NodeId(1)) };
        let p1 = JudgmentAtom { kind: EdgeKind::In, endpoints: (NodeId(1), NodeId(2)) };
        let conc = JudgmentAtom { kind: EdgeKind::In, endpoints: (NodeId(0), NodeId(2)) };
        assert_eq!(reg.apply("in_compose", &[p0, p1], conc).unwrap(), conc);
        assert!(reg.has_rule("in_compose"));
        assert_eq!(
            reg.register_chain(ChainRule::unconstrained("in_compose", EdgeKind::In, EdgeKind::In))
                .unwrap_err(),
            MetisError::InvalidHandle
        );
    }

    #[test]
    fn fixed_endpoint_chain_rejects_wrong_source() {
        let mut reg = DerivationRegistry::builtins();
        reg.register_chain(ChainRule {
            name: "from_root".into(),
            premise_a: PremisePattern { kind: EdgeKind::In, from: Some(NodeId(0)), to: None },
            premise_b: PremisePattern { kind: EdgeKind::In, from: None, to: None },
            conclusion: EdgeKind::In,
        })
        .unwrap();
        let ok0 = JudgmentAtom { kind: EdgeKind::In, endpoints: (NodeId(0), NodeId(1)) };
        let ok1 = JudgmentAtom { kind: EdgeKind::In, endpoints: (NodeId(1), NodeId(2)) };
        let conc = JudgmentAtom { kind: EdgeKind::In, endpoints: (NodeId(0), NodeId(2)) };
        assert_eq!(reg.apply("from_root", &[ok0, ok1], conc).unwrap(), conc);
        let bad0 = JudgmentAtom { kind: EdgeKind::In, endpoints: (NodeId(3), NodeId(1)) };
        assert!(reg.apply("from_root", &[bad0, ok1], conc).is_err());
    }
}
