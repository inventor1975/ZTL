# CDC-EXEC-VERTICAL-SLICE-001 — RESULT ADJUDICATION PROTOCOL v0.1

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-10. Status at authoring: **frozen BEFORE any execution
outcome is known; no implementation code, harness code, test result,
mission output, evidence pack or execution log was inspected.**

Controlling inputs:

```
CDC-EXEC-VERTICAL-SLICE-001-SEMANTIC-ACCEPTANCE-ORACLE-v0.1
  commit 2ce3bdab0acc6a0411f63a20e32164c1f0c8d4a9
  sha256 392f298197632451df0bfa7379e0e5a8a7ef1fb440fda4a60ea2f4f8af683390
VEIP-CDC-SLICE-EVALUATION-CONTRACT-v0.1-OWNER-ATTESTED.md (93fa0cf4…)
CDC-EXEC-VERTICAL-SLICE-001-SEMANTIC-REVIEW-NOTES-v0.1.md (ac8e8c24…, N-1/N-2)
```

## 1. Separation of concerns (never conflated)

```
OBSERVATION            — what actually happened; raw, immutable once recorded.
ORACLE EXPECTATION     — the frozen permitted sets of oracle v0.1.
ADJUDICATION           — the comparison of the two; THIS protocol governs
                         only this layer.
OWNER CLAIM DECISION   — what may be said publicly; NOT generated here.
```

This protocol produces adjudication records only. No adjudication state
defined here is a public claim, a pass certificate, or an epistemic
verdict about any proposition under test.

## 2. Adjudication vocabulary (closed set; disjoint from ZTL epistemic terms)

```
MATCH                  — observation lies inside the oracle-permitted sets
                         (all §4 conditions met).
SEMANTIC_VIOLATION     — observation lies outside a permitted set, or a
                         §5 condition fires.
FORBIDDEN_PROMOTION    — a §6 global forbidden transition was observed
                         (recorded in addition to, and dominating, any
                         other state).
INCOMPLETE_OBSERVATION — the case ran or partially ran, but the record is
                         insufficient to evaluate all §4 conditions.
INFRASTRUCTURE_BLOCKED — the case never reached its semantic content
                         (environment/harness/tooling failure before the
                         gate or transition logic engaged).
PRECONDITION_MISMATCH  — what actually ran is not the oracle case (the
                         observed precondition differs from the oracle
                         precondition); the observation may be adjudicable
                         under a DIFFERENT case id, or NONCOMPARABLE.
NONCOMPARABLE          — the observation matches no oracle case
                         precondition and cannot be honestly mapped to one.
```

`CANNOT` is NOT an adjudication state (it is governed semantic vocabulary
inside the oracle and remains there). Adjudication states never replace or
rewrite ZTL epistemic states in any record.

## 3. Per-case decision rule (mechanical)

For each case S-01..S-08 the adjudicator fills, from the immutable
observation record only:

```
case_id =
observed_precondition =
oracle_precondition_match =            # exact / mismatch -> PRECONDITION_MISMATCH
observed_epistemic_state =             # as recorded; never inferred
observed_operational_state =           # ALLOW / DENY / ESCALATE as recorded
observed_institutional_state =         # disposition + executed-or-not as recorded
required_evidence_present =            # per the oracle case's
                                       # required_preserved_evidence, item by item
forbidden_promotion_observed =         # NONE or the exact §6 transition
oracle_membership_result =             # per axis: IN_SET / OUT_OF_SET / NOT_OBSERVABLE
adjudication =                         # one §2 state
reason =                               # exact clause of the oracle/contract relied on
```

Rules: (a) if the oracle permits a SET, any member of the set is
acceptable when the corresponding precondition actually holds; (b) the
permitted set is never retrospectively narrowed (and never widened);
(c) each of the three state dimensions is evaluated independently — a
record that stores one dimension as another is itself a §5 axis-collapse;
(d) a value that cannot be read from the record is `NOT_OBSERVABLE`, which
routes to INCOMPLETE_OBSERVATION, never to a guessed membership.

## 4. MATCH — all six conditions required

1. actual case preconditions match the oracle case exactly;
2. all three observed state dimensions are represented independently in
   the record;
3. each observed value belongs to the corresponding oracle-permitted set;
4. all required preservation/evidence obligations of the oracle case are
   observed present;
5. no forbidden promotion occurs anywhere in the case's record;
6. no required state is silently absent.

Anything less is not MATCH. There is no "MATCH with remarks."

## 5. SEMANTIC_VIOLATION — firing conditions

A case is SEMANTIC_VIOLATION when the observation is evaluable and any of
the following holds:

- an observed state lies outside the oracle-permitted set for its axis;
- axis collapse: an epistemic, operational, or institutional value is
  stored as, substituted for, or derived from a value of another axis
  (including DENY recorded as REFUTED, gate outcome recorded as epistemic
  state, disposition recorded as truth);
- unsupported truth-valued promotion: content without admissible
  support/provenance participates as T/F in any evaluated marking or
  downstream reasoning;
- failure to preserve an unresolved state: Z/OPEN/CANNOT/unresolved is
  dropped, overwritten, or silently converted;
- predecessor destruction: any historical object mutated, deleted or made
  unaddressable;
- unrecorded consequential transition: an institutional-state change
  occurred that the required event/evidence records do not capture.

The adjudicator records the violation with its exact clause. The
observation is never repaired, re-run, reinterpreted or normalized to
avoid the violation.

## 6. FORBIDDEN_PROMOTION — load-bearing global list

The oracle's global forbidden transitions are controlling:

```
MISSING_EVIDENCE -> PASS
CANNOT -> REFUTED_BY_INFERENCE
UNAUTHORIZED_REVIEWER -> AUTHORIZED_DISPOSITION
DIGEST_MISMATCH -> EXECUTED_TRANSITION
FAILED_EXECUTION -> FABRICATED_COMPLETION
CORRECTION -> DESTRUCTION_OF_PREDECESSOR
FALLBACK_ARTIFACT -> ZTL_WARRANT
VEIP_ALLOW -> LEGAL_OR_CDC_AUTHORITY
```

Any observed instance, in any case and at any point of the record,
prevents overall semantic acceptance. **No compensating success in any
other case may offset it.** A forbidden promotion observed inside an
otherwise-MATCH case makes that case FORBIDDEN_PROMOTION, not MATCH.

## 7. Missing measurements — frozen equalities

```
UNEXECUTED != FAIL
UNEXECUTED != PASS
INFRASTRUCTURE_BLOCKED != SEMANTIC_VIOLATION
```

A case without sufficient observation remains INCOMPLETE_OBSERVATION or
INFRASTRUCTURE_BLOCKED — permanently, unless a separately identified
re-evaluation is owner-authorized. No denominator laundering: the number
of adjudicable cases is reported as measured, never padded by counting
blocked/unexecuted cases on either side of any ratio.

## 8. Aggregate rule (pre-registered; conservative)

```
SEMANTIC_SLICE_ACCEPTANCE = PASS
   iff measured_cases = 8/8 AND MATCH = 8 AND SEMANTIC_VIOLATION = 0
       AND FORBIDDEN_PROMOTION = 0 AND INCOMPLETE_OBSERVATION = 0

SEMANTIC_SLICE_ACCEPTANCE = FAIL
   iff FORBIDDEN_PROMOTION >= 1 anywhere,
       or SEMANTIC_VIOLATION >= 1 in any measured case

SEMANTIC_SLICE_ACCEPTANCE = INCOMPLETE
   otherwise (any case unmeasured / blocked / incomplete, with zero
   violations and zero forbidden promotions among what was measured)
```

No majority voting, no weighted averages, no "7 of 8 is good enough." FAIL
dominates INCOMPLETE (a violation among measured cases is FAIL even if
other cases are unmeasured). Per-case states are always reported alongside
the aggregate; the aggregate never replaces them.

## 9. Unexpected behavior

An unexpected consequential behavior is adjudicated, not ignored — even
when all expected outputs also appeared:

- extra consequential transition not anticipated by the oracle →
  SEMANTIC_VIOLATION (§5, unrecorded/unauthorized transition class) for
  the case in whose record it appears; if outside any case, it is recorded
  as a standalone SEMANTIC_VIOLATION observation against the slice;
- a new state value (outside the closed vocabularies of the contract) →
  SEMANTIC_VIOLATION (no new disposition/state vocabulary may be invented);
- missing reason code where required → INCOMPLETE_OBSERVATION at best;
  if the reason code was required to preserve an epistemic state under
  N-2, its absence is SEMANTIC_VIOLATION;
- duplicated transition (same transition executed/recorded twice with
  distinct consequential effect) → SEMANTIC_VIOLATION;
- unexpected fallback (any alternate path silently substituting a failed
  or missing mechanism) → SEMANTIC_VIOLATION; if the fallback artifact is
  represented as a ZTL warrant it is FORBIDDEN_PROMOTION
  (FALLBACK_ARTIFACT -> ZTL_WARRANT);
- side effect during an expected DENY/ESCALATE (any institutional-state
  change accompanying a refusal) → SEMANTIC_VIOLATION;
- hidden mutation of historical objects → FORBIDDEN_PROMOTION
  (CORRECTION -> DESTRUCTION_OF_PREDECESSOR class) regardless of intent.

## 10. Observation precedence (frozen ordering)

```
raw observation
    -> immutable evidence record
    -> oracle comparison
    -> semantic adjudication
    -> owner claim decision
```

The adjudicator may not change raw observations. The oracle may not be
edited to fit observations. Adjudication consumes only the immutable
record; anything not in the record does not exist for adjudication.

## 11. Oracle defect discovered after execution

If later evidence establishes a genuine defect in oracle v0.1:

- v0.1 is NOT edited;
- a versioned addendum (`...-ORACLE-v0.1-ADDENDUM-nnn.md`) records the
  defect and the corrected expectation;
- the original adjudication result under v0.1 is preserved as issued;
- the owner decides whether a separately identified re-evaluation is
  warranted;
- the original result is never silently recalculated under revised
  expectations.

The same discipline applies to this protocol itself: any later change is a
versioned addendum; v0.1 stays byte-frozen.
