//! Lowering / execution entry (Living grammar).
//!
//! Current foundation: **parse** `.metis` via `oak-metis`. FOL prove and `action` verify
//! are not yet implemented — do not revive the retired `Island::check` script dialect.

use oak_metis::{parse_module, Module};

/// Parse Metis source into a typed module AST.
pub fn parse_source(source: &str) -> Result<Module, String> {
    parse_module(source)
}

#[cfg(test)]
mod tests {
    use super::*;
    use oak_metis::{BinOp, Formula, Item};

    const GROUP: &str = include_str!("../fixtures/group_theory_min.metis");
    const IFF: &str = include_str!("../fixtures/iff_samples.metis");
    const GRAPH: &str = include_str!("../fixtures/graph_bfs_min.metis");

    #[test]
    fn parse_group_theory_fixture() {
        let m = parse_source(GROUP).expect("group_theory_min.metis");
        assert_eq!(m.islands[0].name, "GroupTheory");
        assert_eq!(m.islands[0].namespace.as_deref(), Some("std::algebra"));
    }

    #[test]
    fn parse_iff_fixture() {
        let m = parse_source(IFF).expect("iff_samples.metis");
        let has_iff = m.islands.iter().any(|isl| {
            isl.items.iter().any(|it| match it {
                Item::Rewrites(rw) => rw
                    .rules
                    .iter()
                    .any(|r| matches!(r, Formula::BinOp { op: BinOp::Iff, .. })),
                Item::Connection(_) => true,
                Item::Theorem(th) => {
                    matches!(th.formula, Formula::BinOp { op: BinOp::Iff, .. })
                        || formula_has_iff(&th.formula)
                }
                _ => false,
            })
        });
        assert!(has_iff);
    }

    #[test]
    fn parse_graph_bfs_fixture() {
        let m = parse_source(GRAPH).expect("graph_bfs_min.metis");
        assert!(m.islands.iter().any(|i| i.name == "GraphTheory"));
        assert!(m.islands.iter().any(|i| i.name == "BFS"));
    }
}

fn formula_has_iff(f: &oak_metis::Formula) -> bool {
    use oak_metis::Formula::*;
    match f {
        BinOp { op: oak_metis::BinOp::Iff, .. } => true,
        BinOp { left, right, .. } => formula_has_iff(left) || formula_has_iff(right),
        Forall { body, .. } | Exists { body, .. } | UnaryOp { expr: body, .. } | Group(body) => {
            formula_has_iff(body)
        }
        Call { args, .. } => args.iter().any(formula_has_iff),
        SetComp { head, pred } => formula_has_iff(head) || formula_has_iff(pred),
        TypedName { .. } | Name(_) | String(_) => false,
    }
}
