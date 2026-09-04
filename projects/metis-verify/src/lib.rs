//! Path search and proof verification for Metis islands.
//!
//! - **EQ**: reflexivity, symmetry, transitivity of `Equal` judgment edges.
//! - **ZFC-lite**: finite sets — see [`zfc`].

use metis_graph::{Graph, Step};
use metis_types::{EdgeId, EdgeKind, MetisError, NodeId};

pub mod zfc;

/// A goal that can be proved or verified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Goal {
    /// Propositional equality under EQ rules (and definitional identity).
    Equal(NodeId, NodeId),
    /// Weak inequality: distinct handles and no `Equal` path.
    NotEqual(NodeId, NodeId),
    /// Membership `x ∈ S` via judgment `In`.
    Member(NodeId, NodeId),
    /// `x ∉ S` when no justifying `In` exists.
    NotMember(NodeId, NodeId),
}

/// How a goal was justified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Justification {
    /// EQ path (empty = reflexivity or definitional same node).
    EqualSteps(Vec<Step>),
    /// Witness `In` edge for membership.
    MemberIn(EdgeId),
    /// Negative goals.
    Negation,
}

/// Certificate that `goal` holds under the island rules used to build it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    /// Goal proved.
    pub goal: Goal,
    /// Justification payload.
    pub justification: Justification,
}

/// Search a proof of `goal`.
pub fn prove(graph: &Graph, goal: Goal) -> Result<Proof, MetisError> {
    let proof = match goal {
        Goal::Equal(a, b) => {
            if a == b {
                Proof {
                    goal,
                    justification: Justification::EqualSteps(Vec::new()),
                }
            } else {
                let steps = graph
                    .find_equal_path(a, b)?
                    .ok_or(MetisError::PathNotFound)?;
                Proof {
                    goal,
                    justification: Justification::EqualSteps(steps),
                }
            }
        }
        Goal::NotEqual(a, b) => {
            if a == b {
                return Err(MetisError::ProofInvalid);
            }
            if graph.find_equal_path(a, b)?.is_some() {
                return Err(MetisError::ProofInvalid);
            }
            Proof {
                goal,
                justification: Justification::Negation,
            }
        }
        Goal::Member(x, s) => {
            let eid = find_member_edge(graph, x, s)?.ok_or(MetisError::PathNotFound)?;
            Proof {
                goal,
                justification: Justification::MemberIn(eid),
            }
        }
        Goal::NotMember(x, s) => {
            if find_member_edge(graph, x, s)?.is_some() {
                return Err(MetisError::ProofInvalid);
            }
            Proof {
                goal,
                justification: Justification::Negation,
            }
        }
    };
    verify(graph, &proof)?;
    Ok(proof)
}

/// Recheck a proof against the graph. Does not invent edges.
pub fn verify(graph: &Graph, proof: &Proof) -> Result<(), MetisError> {
    match (&proof.goal, &proof.justification) {
        (Goal::Equal(a, b), Justification::EqualSteps(steps)) => {
            verify_equal(graph, *a, *b, steps)
        }
        (Goal::NotEqual(a, b), Justification::Negation) => {
            if a == b || graph.find_equal_path(*a, *b)?.is_some() {
                Err(MetisError::ProofInvalid)
            } else {
                Ok(())
            }
        }
        (Goal::Member(x, s), Justification::MemberIn(eid)) => {
            let (from, kind, to) = graph.edge(*eid)?;
            if kind != EdgeKind::In || !graph.is_judgment(*eid)? || from != *x || to != *s {
                return Err(MetisError::ProofInvalid);
            }
            Ok(())
        }
        (Goal::NotMember(x, s), Justification::Negation) => {
            if find_member_edge(graph, *x, *s)?.is_some() {
                Err(MetisError::ProofInvalid)
            } else {
                Ok(())
            }
        }
        _ => Err(MetisError::ProofInvalid),
    }
}

fn find_member_edge(
    graph: &Graph,
    elem: NodeId,
    set: NodeId,
) -> Result<Option<EdgeId>, MetisError> {
    for (eid, kind, to) in graph.judgment_outgoing(elem)? {
        if kind == EdgeKind::In && to == set {
            return Ok(Some(eid));
        }
    }
    Ok(None)
}

fn verify_equal(
    graph: &Graph,
    start: NodeId,
    end: NodeId,
    steps: &[Step],
) -> Result<(), MetisError> {
    if steps.is_empty() {
        return if start == end {
            Ok(())
        } else {
            Err(MetisError::ProofInvalid)
        };
    }

    let mut cur = start;
    for step in steps {
        let (from, kind, to) = graph.edge(step.edge)?;
        if kind != EdgeKind::Equal {
            return Err(MetisError::ProofInvalid);
        }
        if !graph.is_judgment(step.edge)? {
            return Err(MetisError::ProofInvalid);
        }
        let (expected_from, nxt) = if step.forward {
            (from, to)
        } else {
            (to, from)
        };
        if cur != expected_from {
            return Err(MetisError::ProofInvalid);
        }
        cur = nxt;
    }
    if cur == end {
        Ok(())
    } else {
        Err(MetisError::ProofInvalid)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn labels(g: &mut Graph) -> (NodeId, NodeId, NodeId, NodeId) {
        let a = g.intern_label(b"a").unwrap();
        let b = g.intern_label(b"b").unwrap();
        let c = g.intern_label(b"c").unwrap();
        let d = g.intern_label(b"d").unwrap();
        (a, b, c, d)
    }

    #[test]
    fn prove_reflexivity() {
        let mut g = Graph::new();
        let (a, _, _, _) = labels(&mut g);
        let proof = prove(&g, Goal::Equal(a, a)).unwrap();
        assert!(matches!(
            proof.justification,
            Justification::EqualSteps(ref s) if s.is_empty()
        ));
        verify(&g, &proof).unwrap();
    }

    #[test]
    fn prove_symmetry() {
        let mut g = Graph::new();
        let (a, b, _, _) = labels(&mut g);
        g.assert(a, EdgeKind::Equal, b).unwrap();
        let proof = prove(&g, Goal::Equal(b, a)).unwrap();
        match &proof.justification {
            Justification::EqualSteps(steps) => {
                assert_eq!(steps.len(), 1);
                assert!(!steps[0].forward);
            }
            _ => panic!("expected equal steps"),
        }
        verify(&g, &proof).unwrap();
    }

    #[test]
    fn prove_transitivity() {
        let mut g = Graph::new();
        let (a, b, c, _) = labels(&mut g);
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let proof = prove(&g, Goal::Equal(a, c)).unwrap();
        match &proof.justification {
            Justification::EqualSteps(steps) => assert_eq!(steps.len(), 2),
            _ => panic!("expected equal steps"),
        }
        verify(&g, &proof).unwrap();
    }

    #[test]
    fn prove_rejects_unrelated() {
        let mut g = Graph::new();
        let (a, _, _, d) = labels(&mut g);
        let err = prove(&g, Goal::Equal(a, d)).unwrap_err();
        assert_eq!(err, MetisError::PathNotFound);
    }

    #[test]
    fn verify_rejects_tampered_path() {
        let mut g = Graph::new();
        let (a, b, c, _) = labels(&mut g);
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(b, EdgeKind::Equal, c).unwrap();
        let mut proof = prove(&g, Goal::Equal(a, c)).unwrap();
        proof.goal = Goal::Equal(a, b);
        assert_eq!(verify(&g, &proof).unwrap_err(), MetisError::ProofInvalid);
    }

    #[test]
    fn longer_chain_a_to_d() {
        let mut g = Graph::new();
        let (a, b, c, d) = labels(&mut g);
        g.assert(a, EdgeKind::Equal, b).unwrap();
        g.assert(c, EdgeKind::Equal, b).unwrap();
        g.assert(c, EdgeKind::Equal, d).unwrap();
        let proof = prove(&g, Goal::Equal(a, d)).unwrap();
        verify(&g, &proof).unwrap();
        match &proof.justification {
            Justification::EqualSteps(steps) => assert!(steps.len() >= 3),
            _ => panic!("expected equal steps"),
        }
    }
}
