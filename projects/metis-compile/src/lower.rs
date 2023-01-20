//! First-slice elaborator: declare islands / nodes / relation kinds into [`IslandStore`].
//!
//! Does **not** prove axioms or theorems. Surface `connection A <-> B` only registers
//! bidirectional candidate skeletons (not Galois, not admitted morphisms).
//! Top-level `using` is Living `09` name resolution only — never imports judgments.

use std::collections::HashMap;

use metis_island::IslandStore;
use metis_types::{EdgeKind, IslandId, MetisError, NodeId};
use oak_metis::{Item, Module};

/// Result of lowering a parsed module into a Core-facing store.
#[derive(Default)]
pub struct LoweringResult {
    /// Populated island store (accepted worlds).
    pub store: IslandStore,
    /// Top-level `using Path` entries (name resolution only; no math import).
    pub usings: Vec<String>,
    /// Short-name → full `using` path (last path segment). Duplicate shorts are rejected.
    pub using_aliases: HashMap<String, String>,
    /// Same-module short island name → store registration key (`namespace::name` or bare).
    pub local_aliases: HashMap<String, String>,
    /// `(island, node_name) →` interned label node.
    pub nodes: HashMap<(IslandId, String), NodeId>,
    /// `(island, relation_name) →` declared generating kind.
    pub relations: HashMap<(IslandId, String), EdgeKind>,
    /// Axiom names recorded per island (formulas not executed).
    pub axioms: Vec<(IslandId, String)>,
    /// Theorem names recorded per island (formulas not proved).
    pub theorems: Vec<(IslandId, String)>,
    /// Top-level `action` names (bodies not executed).
    pub actions: Vec<String>,
    /// `rewrites` rule-set names (rules not applied).
    pub rewrites: Vec<(IslandId, String)>,
}

fn path_short_name(path: &str) -> &str {
    path.rsplit("::").next().unwrap_or(path)
}

fn island_register_name(island: &oak_metis::Island) -> String {
    match &island.namespace {
        Some(ns) if !ns.is_empty() => format!("{ns}::{}", island.name),
        _ => island.name.clone(),
    }
}

fn build_using_aliases(usings: &[String]) -> Result<HashMap<String, String>, MetisError> {
    let mut aliases = HashMap::new();
    for path in usings {
        let short = path_short_name(path).to_string();
        if short.is_empty() {
            return Err(MetisError::InvalidHandle);
        }
        if let Some(prev) = aliases.insert(short.clone(), path.clone()) {
            if prev != *path {
                return Err(MetisError::InvalidHandle);
            }
        }
    }
    Ok(aliases)
}

/// Resolve an island reference for `:`, legacy `use`, or `connection` endpoints.
///
/// Order:
/// 1. Exact store lookup of `name`
/// 2. If `name` is a full path listed in `using`, lookup its terminal short name
///    (islands registered without a namespace)
/// 3. If `name` is a short alias from `using`, lookup the full path registration
/// 4. Same-module short name → qualified registration key
fn resolve_island_ref(
    store: &IslandStore,
    usings: &[String],
    local_aliases: &HashMap<String, String>,
    name: &str,
) -> Result<IslandId, MetisError> {
    if let Some(id) = store.lookup(name) {
        return Ok(id);
    }
    if name.contains("::") && usings.iter().any(|u| u == name) {
        let short = path_short_name(name);
        if let Some(id) = store.lookup(short) {
            return Ok(id);
        }
    }
    if !name.contains("::") {
        for path in usings {
            if path_short_name(path) == name {
                if let Some(id) = store.lookup(path) {
                    return Ok(id);
                }
            }
        }
        if let Some(qualified) = local_aliases.get(name) {
            if let Some(id) = store.lookup(qualified) {
                return Ok(id);
            }
        }
    }
    Err(MetisError::IslandNotFound)
}

/// Lower a typed module AST into an [`IslandStore`].
pub fn lower_module(module: &Module) -> Result<LoweringResult, MetisError> {
    let mut out = LoweringResult::default();
    // Living `09`: `using` is elaborator name material only — record paths, import no judgments.
    out.usings = module.usings.clone();
    out.using_aliases = build_using_aliases(&out.usings)?;
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
        let mut local_rewrites: Vec<String> = Vec::new();
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
                Item::Rewrites(rw) => local_rewrites.push(rw.name.clone()),
            }
        }

        // Canonical single-base extension `island C : B` (Living `09`).
        // Legacy island-body `use` remains as migration compatibility.
        if let Some(base) = &island.extends {
            if !uses.is_empty() {
                // Single direct base only — do not mix `:` with body `use`.
                return Err(MetisError::InvalidHandle);
            }
            let pid = resolve_island_ref(&out.store, &out.usings, &out.local_aliases, base)?;
            let parent = out.store.get(pid)?.world_id(pid);
            out.store.add_staging_parent(parent)?;
        }
        else {
            // `use` must name an already-accepted island (declaration order matters).
            for name in &uses {
                let pid = resolve_island_ref(&out.store, &out.usings, &out.local_aliases, name)?;
                let parent = out.store.get(pid)?.world_id(pid);
                out.store.add_staging_parent(parent)?;
            }
        }

        let register_as = island_register_name(island);
        out.local_aliases.insert(island.name.clone(), register_as.clone());
        let id = out.store.accept_staging(register_as)?;
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
        for name in local_rewrites {
            out.rewrites.push((id, name));
        }
    }

    for (left, right) in pending_connections {
        let lid = resolve_island_ref(&out.store, &out.usings, &out.local_aliases, &left)?;
        let rid = resolve_island_ref(&out.store, &out.usings, &out.local_aliases, &right)?;
        out.store.declare_bidirectional(lid, rid)?;
    }

    for action in &module.actions {
        out.actions.push(action.name.clone());
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
        let id = low.store.lookup("std::algebra::GroupTheory").expect("island");
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
    fn records_action_names_without_running_body() {
        let src = r#"
island Nat { node Nat }
action SearchPath {
    let start = Nat
}
"#;
        let module = parse_module(src).expect("parse");
        let low = lower_module(&module).expect("lower");
        assert_eq!(low.actions, vec!["SearchPath".to_string()]);
        assert!(low.store.lookup("Nat").is_some());
    }

    #[test]
    fn records_rewrites_names_without_applying() {
        let src = r#"
island Nat {
    node Nat
    rewrites AddComm {
        forall (a: Nat, b: Nat) -> a + b == b + a
    }
}
"#;
        let module = parse_module(src).expect("parse");
        let low = lower_module(&module).expect("lower");
        let id = low.store.lookup("Nat").unwrap();
        assert!(low.rewrites.iter().any(|(i, n)| *i == id && n == "AddComm"));
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

    #[test]
    fn extends_sets_staging_parent() {
        let ok = parse_module(
            r#"
island Base { node X }
island Ext : Base { node Y }
"#,
        )
        .expect("parse");
        let low = lower_module(&ok).expect("lower");
        let ext = low.store.lookup("Ext").unwrap();
        let base = low.store.lookup("Base").unwrap();
        let parents = &low.store.get(ext).unwrap().parents;
        assert_eq!(parents.len(), 1);
        assert_eq!(parents[0], low.store.get(base).unwrap().world_id(base));

        let missing = parse_module(
            r#"
island Ext : Missing { node Y }
"#,
        )
        .expect("parse");
        assert!(matches!(lower_module(&missing), Err(MetisError::IslandNotFound)));

        let mixed = parse_module(
            r#"
island Base { node X }
island Ext : Base {
    use Base
    node Y
}
"#,
        )
        .expect("parse");
        assert!(matches!(lower_module(&mixed), Err(MetisError::InvalidHandle)));
    }

    #[test]
    fn records_top_level_using_without_importing_math() {
        let module = parse_module(
            r#"
using std::algebra::GroupTheory
island GroupTheory { node Element }
island AbelianGroup : GroupTheory { node Element }
"#,
        )
        .expect("parse");
        let low = lower_module(&module).expect("lower");
        assert_eq!(low.usings, vec!["std::algebra::GroupTheory".to_string()]);
        assert_eq!(low.using_aliases.get("GroupTheory").map(String::as_str), Some("std::algebra::GroupTheory"));
        let ab = low.store.lookup("AbelianGroup").unwrap();
        let gt = low.store.lookup("GroupTheory").unwrap();
        assert_eq!(low.store.get(ab).unwrap().parents.len(), 1);
        assert_eq!(low.store.get(ab).unwrap().parents[0], low.store.get(gt).unwrap().world_id(gt));
        // `using` must not invent Extra islands or judgment edges.
        assert_eq!(low.store.lookup("std::algebra::GroupTheory"), None);
    }

    #[test]
    fn using_resolves_qualified_extends_to_short_island() {
        let module = parse_module(
            r#"
using std::algebra::GroupTheory
island GroupTheory { node Element }
island AbelianGroup : std::algebra::GroupTheory { node Element }
"#,
        )
        .expect("parse");
        let low = lower_module(&module).expect("lower");
        let ab = low.store.lookup("AbelianGroup").unwrap();
        let gt = low.store.lookup("GroupTheory").unwrap();
        assert_eq!(low.store.get(ab).unwrap().parents[0], low.store.get(gt).unwrap().world_id(gt));

        let no_using = parse_module(
            r#"
island GroupTheory { node Element }
island AbelianGroup : std::algebra::GroupTheory { node Element }
"#,
        )
        .expect("parse");
        assert!(matches!(lower_module(&no_using), Err(MetisError::IslandNotFound)));
    }

    #[test]
    fn duplicate_using_short_names_rejected() {
        let module = parse_module(
            r#"
using a::Foo
using b::Foo
island Foo { node X }
"#,
        )
        .expect("parse");
        assert!(matches!(lower_module(&module), Err(MetisError::InvalidHandle)));
    }

    #[test]
    fn namespace_registers_qualified_name_resolvable_via_using() {
        let module = parse_module(
            r#"
namespace std::algebra
using std::algebra::GroupTheory
island GroupTheory { node Element }
island AbelianGroup : GroupTheory { node Element }
"#,
        )
        .expect("parse");
        let low = lower_module(&module).expect("lower");
        assert!(low.store.lookup("std::algebra::GroupTheory").is_some());
        assert!(low.store.lookup("std::algebra::AbelianGroup").is_some());
        // Bare short name is not a store key when namespace is set.
        assert_eq!(low.store.lookup("GroupTheory"), None);
        let via_using = resolve_island_ref(&low.store, &low.usings, &low.local_aliases, "GroupTheory").unwrap();
        let gt = low.store.lookup("std::algebra::GroupTheory").unwrap();
        assert_eq!(via_using, gt);
        let via_local = resolve_island_ref(&low.store, &low.usings, &low.local_aliases, "AbelianGroup").unwrap();
        let ab_id = low.store.lookup("std::algebra::AbelianGroup").unwrap();
        assert_eq!(via_local, ab_id);
        assert_eq!(low.local_aliases.get("GroupTheory").map(String::as_str), Some("std::algebra::GroupTheory"));
        assert_eq!(low.store.get(ab_id).unwrap().parents[0], low.store.get(gt).unwrap().world_id(gt));
    }

    #[test]
    fn same_module_namespace_short_name_extends_without_using() {
        let module = parse_module(
            r#"
namespace std::algebra
island GroupTheory { node Element }
island AbelianGroup : GroupTheory { node Element }
"#,
        )
        .expect("parse");
        let low = lower_module(&module).expect("lower");
        let gt = low.store.lookup("std::algebra::GroupTheory").unwrap();
        let ab = low.store.lookup("std::algebra::AbelianGroup").unwrap();
        assert_eq!(low.store.get(ab).unwrap().parents[0], low.store.get(gt).unwrap().world_id(gt));
    }
}
