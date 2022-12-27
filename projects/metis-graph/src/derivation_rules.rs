//! Builtin derivation rule table for evidence replay (Living `10` finite DAG slice).
//!
//! Search proposes `app(ρ, …)` by name. Replay looks up `ρ` here instead of an open-ended
//! match — the first general rule table for trusted-path EQ scaffolding.

use metis_types::{EdgeKind, MetisError};

use super::evidence::JudgmentAtom;

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
    }
}
