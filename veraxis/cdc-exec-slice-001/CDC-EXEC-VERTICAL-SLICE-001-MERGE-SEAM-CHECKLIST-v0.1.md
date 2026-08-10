# CDC-EXEC-VERTICAL-SLICE-001 — MERGE-SEAM CHECKLIST v0.1

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-10. Status: **preregistered now, applied later** — frozen
before any merge of the Codex core branch and the Claude integration
branch; no implementation code seen at authoring.

Purpose: the semantic checks that MUST pass when the two implementation
branches are combined. Each item is checked at the merge seam — i.e. on
the combined state, not on either branch alone, because seams are exactly
where each branch's discipline can silently cancel the other's. An item
that cannot be evaluated on the combined state is reported as unevaluated,
never assumed from per-branch results (conformance is not inherited —
NON_HEREDITARY_CONFORMANCE).

## Checklist (all items required; each returns PASS / FAIL / NOT_EVALUABLE)

1. **Candidate ≠ admitted meaning.** Across the seam, no code path treats
   a candidate representation as institutionally admitted meaning; the
   admission record reference remains the only bridge.
2. **T/F/Z discipline unchanged.** The kernel's atom statuses and claim
   dispositions cross the seam unmodified: no wrapper re-derives, renames,
   or defaults them; unverified remains Z, never a defaulted T or F.
3. **Fallback ≠ ZTL warrant (N-1).** A fallback artifact keeps its own
   artifact class through the seam; `ZTL_warrant_digest` is never
   populated by a fallback on either side of the merge or in glue code.
4. **CANNOT never rewritten as REFUTED.** No adapter, serializer, enum
   mapping or storage schema at the seam collapses CANNOT (or any
   unresolved state) into a refutation value.
5. **Gate decision ≠ epistemic state (N-2).** ALLOW/DENY/ESCALATE values
   never flow into any field typed or read as an epistemic state; where a
   CANNOT is operationally mapped to DENY, the epistemic state survives in
   the reason-code/event record after the merge.
6. **Reviewer-authority failure carries no truth implication.** The
   combined path from authority check to record never touches candidate or
   warrant truth values on authority failure.
7. **No implicit ALLOW.** The merged gate has a single explicit ALLOW
   path; no default branch, exception handler, or fall-through in either
   branch's code (or the glue) can yield ALLOW.
8. **No new disposition vocabulary.** The combined system emits only
   {ACCEPT_CANDIDATE, QUALIFY, DISMISS, REQUEST_EVIDENCE, ESCALATE,
   DEFER} as institutional dispositions and only {ALLOW, DENY, ESCALATE}
   as gate decisions; no merged enum introduces or aliases new values.
9. **Correction preserves predecessor.** The merged correction path
   creates successors with bidirectional supersession links; no combined
   write path can mutate, delete or de-address a predecessor object.
10. **No runtime result can modify the oracle.** No merged component
    reads, writes, or parameterizes itself from the oracle file; the
    oracle remains outside the runtime dependency graph entirely.
11. **FO-1/FO-2/FO-3 provenance remains reachable.** The recorded
    first-observation records designated by the owner program record
    (including both branches' original blocker records preserved per
    Corrective Directive 001) remain addressable and byte-intact from the
    merged state; the merge introduces no history rewrite that orphans
    them. (Identity binding of FO-1/FO-2/FO-3 is owner-side; this item
    verifies reachability and byte-integrity, not content.)
12. **FAILURE-PRESERVING AVAILABILITY stays a candidate invariant.** No
    merged artifact, docstring, README, log line or report represents it
    as a proven global property; slice results are represented only as
    behavior consistent/inconsistent with the candidate invariant.

## Application rule

The checklist is applied once at merge time on the combined head, and its
per-item results are recorded with the merged commit/tree identities. Any
FAIL blocks the merge from being represented as semantically accepted;
NOT_EVALUABLE items are carried as open, never counted as PASS. Later
changes to this checklist are versioned addenda; v0.1 stays byte-frozen.
