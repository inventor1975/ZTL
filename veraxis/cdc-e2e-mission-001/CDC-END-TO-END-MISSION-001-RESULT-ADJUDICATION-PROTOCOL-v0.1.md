# CDC-END-TO-END-MISSION-001 — RESULT ADJUDICATION PROTOCOL v0.1

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-11. **Frozen BEFORE any result-bearing mission execution.**
Same discipline as Slice 001; controlling oracle:
`CDC-END-TO-END-MISSION-001-SEMANTIC-ACCEPTANCE-ORACLE-v0.1`.

## 1. Separation of concerns

```
OBSERVATION          — what actually happened; raw, immutable once recorded.
ORACLE EXPECTATION   — the frozen M01–M12 requirements and forbidden list.
ADJUDICATION         — the comparison; THIS protocol governs only this.
OWNER CLAIM DECISION — public claims; NOT generated here.
```

## 2. Adjudication vocabulary (closed; identical to Slice 001)

```
MATCH · SEMANTIC_VIOLATION · FORBIDDEN_PROMOTION ·
INCOMPLETE_OBSERVATION · INFRASTRUCTURE_BLOCKED ·
PRECONDITION_MISMATCH · NONCOMPARABLE
```

`CANNOT` is not an adjudication state. No eighth state; no
"MATCH with remarks".

## 3. Per-case decision rule (mechanical; M01–M12)

```
case_id =
observation_record_id =
observation_digest =
observed_precondition =
oracle_precondition_match =
observed_epistemic_state =
observed_operational_state =
observed_institutional_state =
required_evidence_present =
forbidden_promotion_observed =
oracle_membership_epistemic =     IN_SET / OUT_OF_SET / NOT_OBSERVABLE
oracle_membership_operational =
oracle_membership_institutional =
adjudication =
reason =                          exact clause relied on
```

Rules as frozen for Slice 001: any member of a permitted set is
acceptable when its precondition holds; no retrospective narrowing or
widening; three axes evaluated independently (storage of one axis as
another is itself a violation); `NOT_OBSERVABLE` routes to
INCOMPLETE_OBSERVATION, never to guessed membership.

## 4. MATCH — all six conditions (unchanged)

(1) preconditions match exactly; (2) three axes independently
represented; (3) each observed value in its permitted set; (4) all
preservation/evidence obligations observed; (5) no forbidden promotion;
(6) no required state silently absent.

## 5. SEMANTIC_VIOLATION — firing conditions (unchanged, plus path-stage forms)

Out-of-set values; axis collapse (including evaluation-verdict fields
consumed as dispositions or warrant states — the M05 object-level form);
unsupported truth-valued promotion; unresolved state dropped;
predecessor destruction; unrecorded consequential transition; a
deliverable statement above its recorded state (M11 form). Observations
are never repaired.

## 6. FORBIDDEN_PROMOTION — the frozen 14

The oracle's final list (8 carried + 6 path-mechanical) is load-bearing.
Any observed instance, at any stage, dominates: the containing case is
FORBIDDEN_PROMOTION and the aggregate is FAIL. No cross-stage
compensation; final-document quality never offsets an upstream
promotion.

## 7. Missing measurements (frozen equalities)

```
UNEXECUTED != FAIL
UNEXECUTED != PASS
INFRASTRUCTURE_BLOCKED != SEMANTIC_VIOLATION
```

An unmeasured oracle case stays unmeasured; re-evaluation only as a
separately identified, owner-authorized successor measurement (the §7
path exercised in Slice 001 RUN-003); the original record is never
recalculated.

## 8. Aggregate rule (pre-registered; identical shape)

```
PASS        iff measured 12/12, MATCH = 12, zero violations, zero
            forbidden promotions, zero incomplete
FAIL        iff any forbidden promotion anywhere, or any semantic
            violation among measured cases
INCOMPLETE  otherwise
```

FAIL dominates INCOMPLETE. Per-case states always reported alongside the
aggregate. No voting, weighting, or percentages.

## 9. Unexpected behavior

As frozen for Slice 001: extra consequential transitions, new state
vocabulary, missing required reason codes, duplicated transitions,
silent fallbacks, side effects during refusals, hidden mutation of
historical objects — each adjudicated (violation or forbidden promotion
per its class), never ignored because expected outputs also appeared.

## 10. Observation precedence (frozen ordering)

```
raw observation → immutable evidence record → oracle comparison →
semantic adjudication → owner claim decision
```

The adjudicator may not change raw observations; the oracle may not be
edited to fit them; stale or mislabelled fixture metadata is disposed
under this precedence exactly as in RUN-003 (operative facts control;
discrepancies recorded, not normalized).

## 11. Instrument defect discovered after execution

No edits to v0.1 instruments; versioned addendum; original results
preserved; owner decides any separately identified re-evaluation; no
silent recalculation.
