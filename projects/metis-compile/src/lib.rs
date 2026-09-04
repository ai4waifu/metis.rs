//! Compile / execute Metis island theorem scripts.
//!
//! Source of truth is island language text (`oak-metis`). This crate lowers and runs
//! `Island::check` goals against `metis-verify`.

use std::collections::HashMap;

use metis_graph::Graph;
use metis_types::{MetisError, NodeId};
use metis_verify::{prove, zfc, Goal, Proof};
use oak_metis::{parse_module, Expr, Item, Module, Stmt, Theorem};

/// Result of running one theorem script.
#[derive(Clone, Debug)]
pub struct TheoremReport {
    pub island: String,
    pub theorem: String,
    pub proofs: Vec<Proof>,
}

/// Parse island source and execute every theorem body.
pub fn run_source(source: &str) -> Result<Vec<TheoremReport>, MetisError> {
    let module = parse_module(source).map_err(|_| MetisError::ProofInvalid)?;
    run_module(&module)
}

/// Execute an already-parsed module.
pub fn run_module(module: &Module) -> Result<Vec<TheoremReport>, MetisError> {
    let mut out = Vec::new();
    for island in &module.islands {
        for item in &island.items {
            match item {
                Item::Theorem(th) => {
                    out.push(run_theorem(&island.name, th)?);
                }
            }
        }
    }
    Ok(out)
}

fn run_theorem(island: &str, th: &Theorem) -> Result<TheoremReport, MetisError> {
    let mut g = Graph::new();
    let mut env: HashMap<String, NodeId> = HashMap::new();
    let mut proofs = Vec::new();

    for stmt in &th.body {
        match stmt {
            Stmt::Let { name, value } => {
                let v = eval_value(island, &mut g, &env, value)?;
                env.insert(name.clone(), v);
            }
            Stmt::Expr(expr) => match expect_check(island, expr)? {
                Some(goal_expr) => {
                    let goal = eval_goal(&mut g, &env, &goal_expr)?;
                    proofs.push(prove(&g, goal)?);
                }
                None => {
                    let _ = eval_value(island, &mut g, &env, expr)?;
                }
            },
        }
    }

    Ok(TheoremReport {
        island: island.to_string(),
        theorem: th.name.clone(),
        proofs,
    })
}

fn expect_check(island: &str, expr: &Expr) -> Result<Option<Expr>, MetisError> {
    match expr {
        Expr::Call { path, args } if path.len() == 2 && path[0] == island && path[1] == "check" => {
            if args.len() != 1 {
                return Err(MetisError::ProofInvalid);
            }
            Ok(Some(args[0].clone()))
        }
        _ => Ok(None),
    }
}

fn eval_goal(
    graph: &mut Graph,
    env: &HashMap<String, NodeId>,
    expr: &Expr,
) -> Result<Goal, MetisError> {
    let Expr::Call { path, args } = expr else {
        return Err(MetisError::ProofInvalid);
    };
    if path.len() != 1 {
        return Err(MetisError::ProofInvalid);
    }
    match path[0].as_str() {
        "Member" => {
            let (a, b) = two_nodes(graph, env, args)?;
            Ok(Goal::Member(a, b))
        }
        "NotMember" => {
            let (a, b) = two_nodes(graph, env, args)?;
            Ok(Goal::NotMember(a, b))
        }
        "Equal" => {
            let (a, b) = two_nodes(graph, env, args)?;
            Ok(Goal::Equal(a, b))
        }
        "NotEqual" => {
            let (a, b) = two_nodes(graph, env, args)?;
            Ok(Goal::NotEqual(a, b))
        }
        _ => Err(MetisError::ProofInvalid),
    }
}

fn two_nodes(
    graph: &mut Graph,
    env: &HashMap<String, NodeId>,
    args: &[Expr],
) -> Result<(NodeId, NodeId), MetisError> {
    if args.len() != 2 {
        return Err(MetisError::ProofInvalid);
    }
    // island name unused for goal ctors
    let a = eval_value("_", graph, env, &args[0])?;
    let b = eval_value("_", graph, env, &args[1])?;
    Ok((a, b))
}

fn eval_value(
    island: &str,
    graph: &mut Graph,
    env: &HashMap<String, NodeId>,
    expr: &Expr,
) -> Result<NodeId, MetisError> {
    match expr {
        Expr::Name(n) => env.get(n).copied().ok_or(MetisError::NodeNotFound),
        Expr::String(s) => zfc::atom(graph, s.as_bytes()),
        Expr::Call { path, args } => eval_call(island, graph, env, path, args),
    }
}

fn eval_call(
    island: &str,
    graph: &mut Graph,
    env: &HashMap<String, NodeId>,
    path: &[String],
    args: &[Expr],
) -> Result<NodeId, MetisError> {
    if path.len() == 2 && path[0] == island {
        match path[1].as_str() {
            "empty" => {
                if !args.is_empty() {
                    return Err(MetisError::ProofInvalid);
                }
                zfc::empty_set(graph)
            }
            "atom" => {
                if args.len() != 1 {
                    return Err(MetisError::ProofInvalid);
                }
                match &args[0] {
                    Expr::String(s) => zfc::atom(graph, s.as_bytes()),
                    _ => Err(MetisError::ProofInvalid),
                }
            }
            "finite_set" => {
                let mut members = Vec::with_capacity(args.len());
                for a in args {
                    members.push(eval_value(island, graph, env, a)?);
                }
                zfc::finite_set(graph, &members)
            }
            _ => Err(MetisError::ProofInvalid),
        }
    } else {
        Err(MetisError::ProofInvalid)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ZFC_BASIC: &str = include_str!("../fixtures/zfc_basic.metis");

    #[test]
    fn zfc_basic_theorems_from_island_source() {
        let reports = run_source(ZFC_BASIC).expect("run zfc_basic.metis");
        assert!(reports.len() >= 5);
        for r in &reports {
            assert!(
                !r.proofs.is_empty(),
                "theorem {} produced no checks",
                r.theorem
            );
        }
    }

    #[test]
    fn rejects_member_of_empty_from_island() {
        let src = r#"
island ZFC {
  theorem bad {
    let a = ZFC::atom("a")
    let empty = ZFC::empty()
    ZFC::check(Member(a, empty))
  }
}
"#;
        assert!(run_source(src).is_err());
    }
}
