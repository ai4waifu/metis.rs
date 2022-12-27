//! Generating relations and island rule tables (Living Core constitution).
//!
//! Axioms are **generating relations** for closure, not `proved=true` flags on proposition nodes.
//! Transformations are declared rule shapes; search only proposes instances.

use std::collections::HashSet;

use metis_types::EdgeKind;

use super::derivation_rules::is_builtin_rule;
use super::transform::TransformationSchema;

/// Declared relation kinds that may appear as generators (axioms) in a world.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RelationSignature {
    kinds: HashSet<EdgeKindKey>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum EdgeKindKey {
    Equal,
    In,
    Eval,
    Custom(u16),
}

impl From<EdgeKind> for EdgeKindKey {
    fn from(k: EdgeKind) -> Self {
        match k {
            EdgeKind::Equal => Self::Equal,
            EdgeKind::In => Self::In,
            EdgeKind::Eval => Self::Eval,
            EdgeKind::Custom(v) => Self::Custom(v),
        }
    }
}

impl RelationSignature {
    pub fn new() -> Self {
        Self::default()
    }

    /// Declare that `kind` may be used as a generating / axiom relation.
    pub fn declare_kind(&mut self, kind: EdgeKind) {
        self.kinds.insert(EdgeKindKey::from(kind));
    }

    pub fn allows(&self, kind: EdgeKind) -> bool {
        self.kinds.contains(&EdgeKindKey::from(kind))
    }

    pub fn kind_count(&self) -> usize {
        self.kinds.len()
    }
}

/// Island-local rule table: signature + declared transformations.
#[derive(Clone, Debug, Default)]
pub struct RuleTable {
    pub signature: RelationSignature,
    pub transforms: Vec<TransformationSchema>,
}

impl RuleTable {
    pub fn declare_kind(&mut self, kind: EdgeKind) {
        self.signature.declare_kind(kind);
    }

    pub fn add_transform(&mut self, schema: TransformationSchema) {
        self.transforms.push(schema);
    }

    pub fn has_transform(&self, name: &str) -> bool {
        self.transforms.iter().any(|t| t.name == name)
    }

    /// True if `name` is a builtin EQ derivation rule or a declared transform schema.
    pub fn has_derivation_rule(&self, name: &str) -> bool {
        is_builtin_rule(name) || self.has_transform(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signature_gates_kinds() {
        let mut sig = RelationSignature::new();
        assert!(!sig.allows(EdgeKind::Equal));
        sig.declare_kind(EdgeKind::Equal);
        assert!(sig.allows(EdgeKind::Equal));
        assert!(!sig.allows(EdgeKind::In));
    }

    #[test]
    fn rule_table_holds_transitivity() {
        use super::super::derivation_rules::{EQUAL_REFL, EQUAL_SYMMETRY, EQUAL_TRANSITIVITY};
        let mut rules = RuleTable::default();
        rules.declare_kind(EdgeKind::Equal);
        rules.add_transform(TransformationSchema::equal_transitivity());
        assert!(rules.has_transform(EQUAL_TRANSITIVITY));
        assert!(rules.has_derivation_rule(EQUAL_REFL));
        assert!(rules.has_derivation_rule(EQUAL_SYMMETRY));
        assert!(rules.has_derivation_rule(EQUAL_TRANSITIVITY));
        assert_eq!(rules.signature.kind_count(), 1);
    }
}
