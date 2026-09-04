//! First-slice elaborator: declare islands / nodes / relation kinds into [`IslandStore`].
//!
//! Does **not** prove axioms or theorems. Surface `connection A <-> B` only registers
//! bidirectional candidate skeletons (not Galois, not admitted morphisms).

use std::collections::HashMap;

use metis_island::IslandStore;
use metis_types::{EdgeKind, IslandId, MetisError, NodeId};
use oak_metis::{Item, Module};

/// Result of lowering a parsed module into a Core-facing store.
#[derive(Default)]
pub struct LoweringResult {
    /// Populated island store (accepted worlds).
    pub store: IslandStore,
    /// `(island, node_name) →` interned label node.
    pub nodes: HashMap<(IslandId, String), NodeId>,
    /// `(island, relation_name) →` declared generating kind.
    pub relations: HashMap<(IslandId, String), EdgeKind>,
    /// Axiom names recorded per island (formulas not executed).
    pub axioms: Vec<(IslandId, String)>,
    /// Theorem names recorded per island (formulas not proved).
    pub theorems: Vec<(IslandId, String)>,
}

/// Lower a typed module AST into an [`IslandStore`].
pub fn lower_module(module: &Module) -> Result<LoweringResult, MetisError> {
    let mut out = LoweringResult::default();
    let mut next_custom: u16 = 1;
    let mut pending_connections: Vec<(String, String)> = Vec::new();

    for island in &module.islands {
        if island.name == "_" {
            for item in &island.items {
                if let Item::Connection(c) = item {
                    pending_connections.push((c.left.clone(), c.right.clone()));
                }
            }
            continue;
        }

        out.store.open_staging(&island.name)?;
        out.store.declare_generating_kind(EdgeKind::Equal)?;
        out.store.declare_generating_kind(EdgeKind::In)?;

        let mut local_nodes: HashMap<String, NodeId> = HashMap::new();
        let mut local_relations: HashMap<String, EdgeKind> = HashMap::new();
        let mut local_axioms: Vec<String> = Vec::new();
        let mut local_theorems: Vec<String> = Vec::new();
        let mut uses: Vec<String> = Vec::new();

        for item in &island.items {
            match item {
                Item::Node(name) => {
                    let nid = {
                        let st = out.store.staging_mut()?;
                        st.graph.intern_label(name.as_bytes())?
                    };
                    local_nodes.insert(name.clone(), nid);
                }
                Item::Relation(rel) => {
                    if next_custom == u16::MAX {
                        return Err(MetisError::Capacity);
                    }
                    let kind = EdgeKind::Custom(next_custom);
                    next_custom = next_custom.saturating_add(1);
                    out.store.declare_generating_kind(kind)?;
                    local_relations.insert(rel.name.clone(), kind);
                }
                Item::Axiom(ax) => local_axioms.push(ax.name.clone()),
                Item::Theorem(th) => local_theorems.push(th.name.clone()),
                Item::Connection(c) => {
                    pending_connections.push((c.left.clone(), c.right.clone()));
                }
                Item::Use(name) => uses.push(name.clone()),
                Item::Rewrites(_) => {}
            }
        }

        // `use` must name an already-accepted island (declaration order matters).
        for name in &uses {
            let pid = out.store.lookup(name).ok_or(MetisError::IslandNotFound)?;
            let parent = out.store.get(pid)?.world_id(pid);
            out.store.add_staging_parent(parent)?;
        }

        let id = out.store.accept_staging(island.name.clone())?;
        for (name, nid) in local_nodes {
            out.nodes.insert((id, name), nid);
        }
        for (name, kind) in local_relations {
            out.relations.insert((id, name), kind);
        }
        for name in local_axioms {
            out.axioms.push((id, name));
        }
        for name in local_theorems {
            out.theorems.push((id, name));
        }
    }

    for (left, right) in pending_connections {
        let lid = out.store.lookup(&left).ok_or(MetisError::IslandNotFound)?;
        let rid = out.store.lookup(&right).ok_or(MetisError::IslandNotFound)?;
        out.store.declare_bidirectional(lid, rid)?;
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use metis_graph::connection::ConnectionClass;
    use oak_metis::parse_module;

    #[test]
    fn lowers_group_theory_declarations() {
        let src = include_str!("../fixtures/group_theory_min.metis");
        let module = parse_module(src).expect("parse");
        let low = lower_module(&module).expect("lower");
        let id = low.store.lookup("GroupTheory").expect("island");
        assert!(low.nodes.contains_key(&(id, "Group".into())));
        assert!(low.nodes.contains_key(&(id, "Element".into())));
        assert!(low.relations.contains_key(&(id, "Mul".into())));
        assert!(low.relations.contains_key(&(id, "Inv".into())));
        assert!(low.axioms.iter().any(|(i, n)| *i == id && n == "Associativity"));
        assert!(low.theorems.iter().any(|(i, n)| *i == id && n == "FirstIsomorphismTheorem"));
        let island = low.store.get(id).unwrap();
        assert!(island.rules.signature.allows(EdgeKind::Equal));
        assert!(island.rules.signature.allows(EdgeKind::In));
        assert!(island.rules.signature.allows(*low.relations.get(&(id, "Mul".into())).unwrap()));
    }

    #[test]
    fn connection_registers_bidirectional_candidates_only() {
        let src = r#"
island ZFC { node Set }
island HoTT { node Type }
connection ZFC <-> HoTT { }
"#;
        let module = parse_module(src).expect("parse");
        let low = lower_module(&module).expect("lower");
        assert_eq!(low.store.connections().len(), 2);
        assert!(low.store.admitted_connections().is_empty());
        assert_eq!(low.store.connections()[0].class, ConnectionClass::BidirectionalSkeleton);
    }

    #[test]
    fn use_requires_prior_accepted_island() {
        let ok = parse_module(
            r#"
island Base { node X }
island Ext {
    use Base
    node Y
}
"#,
        )
        .expect("parse");
        let low = lower_module(&ok).expect("lower");
        let ext = low.store.lookup("Ext").unwrap();
        let base = low.store.lookup("Base").unwrap();
        let parents = &low.store.get(ext).unwrap().parents;
        assert_eq!(parents.len(), 1);
        assert_eq!(parents[0], low.store.get(base).unwrap().world_id(base));

        let bad = parse_module(
            r#"
island Ext {
    use Missing
    node Y
}
"#,
        )
        .expect("parse");
        assert!(matches!(lower_module(&bad), Err(MetisError::IslandNotFound)));
    }
}
