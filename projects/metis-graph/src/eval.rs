//! Outer-world Eval attachments (Living `08` numeric boundary).
//!
//! Numeric routines may form these candidates. They do **not** mint inner-world
//! [`EdgeKind::Equal`] judgments and must not call graph `assert` themselves.

use metis_types::{EdgeKind, MetisError, NodeId};

use super::admission::{CandidateRelation, QueryStatus, WorldId};
use super::relation::form_relation;

/// How a numeric routine classified its Outer result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EvalCertificateKind {
    /// Exact rational (or integer) with a replayable certificate handle.
    ExactBounded,
    /// Interval enclosure — Outer only, never Equal.
    Interval,
    /// Floating / approximate — Outer only, never Equal.
    Approximate,
    /// Timeout / diverge / NaN — Outer failure record, not Refuted.
    Failed,
}

/// Outer numeric attachment at a symbolic position (sidecar, not an admitted fact).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EvalAttachment {
    pub world: WorldId,
    pub position: NodeId,
    /// Opaque certificate / numeric shadow handle (no numeric library required).
    pub certificate_tag: u64,
    pub kind: EvalCertificateKind,
}

/// Form an Outer Eval candidate relation (position → shadow node) without admission.
pub fn form_eval_candidate(
    world: WorldId,
    position: NodeId,
    shadow: NodeId,
) -> CandidateRelation {
    form_relation(world, (position, shadow), None)
}

/// Record an Outer Eval attachment sidecar.
pub fn form_eval_attachment(
    world: WorldId,
    position: NodeId,
    certificate_tag: u64,
    kind: EvalCertificateKind,
) -> EvalAttachment {
    EvalAttachment { world, position, certificate_tag, kind }
}

/// Refuse treating any Eval attachment as an Equal judgment.
pub fn refuse_eval_as_equal(att: &EvalAttachment) -> Result<(), MetisError> {
    let _ = att;
    Err(MetisError::ProofInvalid)
}

/// Only exact bounded certificates may *apply* for admission later.
///
/// Interval / approximate / failed stay Outer forever under this first-slice policy.
pub fn may_request_admission(att: &EvalAttachment) -> bool {
    matches!(att.kind, EvalCertificateKind::ExactBounded)
}

/// Missing Eval attachment → [`QueryStatus::Unknown`] (never automatic Refuted).
pub const fn eval_query_status(found: bool) -> QueryStatus {
    if found {
        // Presence of an Outer attachment is not Proven mathematics.
        QueryStatus::Unknown
    } else {
        QueryStatus::Unknown
    }
}

/// Document that Eval kind is not Equal.
pub const fn eval_is_not_equal() -> bool {
    !matches!(EdgeKind::Eval, EdgeKind::Equal)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use metis_types::IslandId;

    fn world() -> WorldId {
        WorldId { island: IslandId::from_raw(NonZeroU32::new(1).unwrap()), version: 1 }
    }

    #[test]
    fn eval_never_counts_as_equal_or_proven() {
        assert!(eval_is_not_equal());
        let att = form_eval_attachment(world(), NodeId(0), 42, EvalCertificateKind::Approximate);
        assert_eq!(refuse_eval_as_equal(&att).unwrap_err(), MetisError::ProofInvalid);
        assert!(!may_request_admission(&att));
        assert_eq!(eval_query_status(false), QueryStatus::Unknown);
        assert_eq!(eval_query_status(true), QueryStatus::Unknown);
    }

    #[test]
    fn exact_bounded_may_request_admission_only() {
        let ok = form_eval_attachment(world(), NodeId(1), 7, EvalCertificateKind::ExactBounded);
        assert!(may_request_admission(&ok));
        assert_eq!(refuse_eval_as_equal(&ok).unwrap_err(), MetisError::ProofInvalid);
        let fail = form_eval_attachment(world(), NodeId(1), 8, EvalCertificateKind::Failed);
        assert!(!may_request_admission(&fail));
    }

    #[test]
    fn form_eval_candidate_is_outer() {
        let c = form_eval_candidate(world(), NodeId(0), NodeId(1));
        assert_eq!(c.endpoints, (NodeId(0), NodeId(1)));
    }
}
