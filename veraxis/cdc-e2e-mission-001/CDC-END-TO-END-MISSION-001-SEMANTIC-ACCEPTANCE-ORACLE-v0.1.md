# CDC-END-TO-END-MISSION-001 — SEMANTIC ACCEPTANCE ORACLE v0.1

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-11. Status at authoring: **frozen BEFORE any result-bearing
execution of CDC-END-TO-END-MISSION-001; no new-mission implementation,
execution result or mission output was inspected.** Prior knowledge of
Slice 001 (its frozen instruments and adjudications) is declared and is
not contamination for this mission.

Object under test — the complete bounded institutional path:

```
authoritative source → admitted OIC control → frozen CDC mission
population → evidence → deterministic evaluation → ZTL or explicitly
separate fallback warrant → candidate finding → standing-bounded human
disposition → VEIP-controlled institutional transition → CDC draft
deliverables → correction/history
```

Grounding (no new conceptual architecture): frozen Protocol v0.1
(`61a470b4…`, D1/D2, R-01..R-26), owner-attested slice contract
(`93fa0cf4…`) + N-1/N-2 (`ac8e8c24…`), frozen A–E (`973f9eba…`, standing
model 02 canonical), Slice 001 oracle/protocol (`392f2981…`/`5884c984…`)
and its adjudicated results. The supplied case names M01–M12 were checked
against the frozen architecture and adopted unchanged; one definitional
refinement is recorded at M10 (gate ALLOW is necessary but not
sufficient — the Slice 001 experimentally established separation).

Vocabulary: the three axes (epistemic / operational / institutional)
remain separate throughout; no value on one axis may substitute for
another. Logical warrant ≠ institutional warrant (D1). Evaluation
establishes a property; issuance creates reliance (D2). Where this oracle
records an outcome SET, any member is acceptable when the precondition
holds; nothing outside is.

---

## M01 SOURCE_BINDING

Requirement: every admitted control and every evidence element used in
the mission binds to authoritative source anchors; the source remains
attributable to its recognized issuer; no source-derived content
participates without its anchor.
Testable: each control/evidence record carries resolvable
`source_anchor_refs`; anchors resolve to the frozen source set; no
mission object references source content anchor-free.
Forbidden here: `SOURCE_TEXT -> ADMITTED_MEANING_WITHOUT_ADMISSION`;
issuer attribution lost or transferred to the operator.

## M02 OIC_ADMITTED_MEANING_BINDING

Requirement: candidate representation ≠ admitted meaning; downstream
computation consumes ONLY admitted controls via resolvable admission
records; content lacking admission support never participates
truth-valued (the frozen Z-discipline; the §24.5 class).
Testable: every consumed control has `admission_record_ref` resolving in
the frozen registry; absence → explicit refusal/unresolved state (as
observed in Slice S-03), never silent compensation by plausible content.
Forbidden: unadmitted content entering any evaluated marking as T/F.

## M03 FROZEN_MISSION_POPULATION

Requirement: the mission population is frozen before evaluation;
population accountability is total — every member is evaluated or
carries an explicit non-evaluable/missing state; the denominator is
never padded or silently reduced.
Testable: frozen population manifest (hash-bound) predates results;
per-member terminal state exists; counts reconcile exactly
(evaluated + explicitly-not-evaluated = population).
Forbidden: silent member drops; denominator laundering in any reported
figure.

## M04 EVIDENCE_TO_CONTROL_TRACEABILITY

Requirement: every evidence bundle binds to its control (id, version,
digest) and its sources; all mandatory digests recompute; missing
evidence is an explicit state.
Testable: digest recomputation exact on sampled-to-total bundles;
`MISSING_EVIDENCE`-class conditions surface as explicit unresolved
states with named absences.
Forbidden: `MISSING_EVIDENCE -> PASS`; `DIGEST_MISMATCH ->
EXECUTED_TRANSITION` (any stage).

## M05 DETERMINISTIC_EVALUATION_SEPARATION

Requirement: deterministic evaluation records are a separate object
class from semantic/probabilistic proposals, from warrants, and from
dispositions; upstream evaluation vocabulary (e.g.
SATISFIED/BREACH/UNRESOLVED) never becomes an adjudication state, a
warrant state, or a disposition.
Testable: object schemas/classes distinct; no field of one class stored
into a field typed as another (the axis-collapse test at object level);
semantic proposals separately labelled from deterministic results.
Forbidden: evaluation verdict fields consumed AS dispositions or AS
epistemic warrant states.

## M06 ZTL_WARRANT_VS_FALLBACK_SEPARATION

Requirement: N-1 verbatim — a fallback warrant is its own artifact
class; it is never represented as a ZTL warrant; `ZTL_warrant_digest` is
never populated by a fallback; class collision or masquerade is refused.
Testable: as mechanically enforced and observed in Slice 001 (collision
→ DENY; masquerade → DENY); event records keep the two digest fields
distinct with the unused one null.
Forbidden: `FALLBACK_ARTIFACT -> ZTL_WARRANT`.

## M07 CANDIDATE_FINDING_NON_OFFICIALITY

Requirement: a candidate finding is never an official finding; the
non-official status survives every downstream stage (including
deliverables); promotion requires the separately recorded human
disposition (SEAM-2).
Testable: candidate objects carry non-official status; no pipeline stage
re-labels a candidate official; deliverable drafts reference candidates
AS candidates or AS dispositioned states, never as official findings.
Forbidden: `CANDIDATE_FINDING -> OFFICIAL_FINDING_WITHOUT_DISPOSITION`.

## M08 REVIEWER_STANDING_AND_AUTHORITY_SCOPE

Requirement: a disposition may occur only under mission-scoped standing;
identity/login answers "who", standing is the bounded relation (role is
one input — frozen 02 canonical model); out-of-scope assertion is
refused operationally with zero truth implication for any candidate or
warrant.
Testable: every disposition record binds reviewer identity, role
assertion AND authority_scope_ref matching the mission scope; a scope
mismatch observation shows DENY + unchanged epistemic states (the Slice
S-04 shape).
Forbidden: `LOGIN_IDENTITY -> INSTITUTIONAL_STANDING`;
`UNAUTHORIZED_REVIEWER -> AUTHORIZED_DISPOSITION`.

## M09 HUMAN_DISPOSITION_BOUNDARY

Requirement: institutional disposition is a separately recorded human
act from the closed disposition set with its frozen meanings
(REQUEST_EVIDENCE → unresolved, no PASS promotion; DISMISS → cannot
enter relied-upon outputs; ESCALATE → blocks ordinary adoption; DEFER →
no downstream eligibility until resumed; ACCEPT/QUALIFY → candidate-use
states, not officiality); no machine output IS a disposition; the
disposition consumes but never rewrites the warrant (D1/D2; N-2).
Testable: each disposition record carries the human actor binding;
disposition values ∈ closed set only; warrant states byte-identical
before/after disposition.
Forbidden: machine candidate auto-dispositioned; new disposition
vocabulary; `CANNOT -> REFUTED_BY_INFERENCE` anywhere on the path.

## M10 VEIP_TRANSITION_AFTER_VALID_DISPOSITION

Requirement (with the Slice-001-established refinement): an
institutional-state transition executes only given a valid disposition
AND a gate ALLOW, and a gate ALLOW is necessary but NOT sufficient —
ALLOW is not itself a transition; the transition exists only when the
executing component completes; on component failure the prior state is
preserved, the failure is preserved as an observation, no event is
emitted, no fallback silently substitutes (behavior consistent with the
candidate invariant FAILURE-PRESERVING AVAILABILITY — which this mission
also does not prove generally).
Testable: events exist iff completed transitions exist (one-to-one);
refusals and failures carry no events; prior states preserved
byte-identically on every non-completed path.
Forbidden: `GATE_ALLOW -> COMPLETED_INSTITUTIONAL_TRANSITION`;
`FAILED_EXECUTION -> FABRICATED_COMPLETION`; `VEIP_ALLOW ->
LEGAL_OR_CDC_AUTHORITY`.

## M11 DELIVERABLE_STATE_FIDELITY

Requirement: CDC draft deliverables reflect exactly the recorded states
— a candidate appears as a candidate, a dispositioned state as its
disposition, nothing as official; drafts are labelled drafts; every
material statement in a deliverable traces to a recorded object
(candidate/evidence/disposition/event) without amplification.
Testable: state-fidelity sampling-to-total between deliverable content
and the record set; DRAFT labelling present; zero deliverable statements
without a record trace.
Forbidden: `DRAFT_OUTPUT -> OFFICIAL_RECORD`; any deliverable statement
above its recorded state (the claim-ceiling discipline applied to
mission outputs).

## M12 CORRECTION_AND_PREDECESSOR_PRESERVATION

Requirement: correction creates a successor (new identity, supersession
links both ways, reason, changed refs) and never mutates the
predecessor, which remains addressable and byte-preserved; affected
generated outputs become ineligible until regeneration or explicit human
resolution; a proposal against a superseded candidate is refused as
stale.
Testable: byte-identity of predecessors across correction; supersession
linkage complete; post-correction deliverable eligibility recomputed or
explicitly resolved; stale-candidate proposal shows the refusal (the
Slice S-07 shape).
Forbidden: `CORRECTION -> DESTRUCTION_OF_PREDECESSOR`;
`SUPERSEDED_STATE -> DELIVERABLE_WITHOUT_REGENERATION_OR_RESOLUTION`.

---

## Global forbidden promotions (final frozen list — 14)

Carried forward from Slice 001 (8):

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

Added — mechanically required by the end-to-end path (6):

```
SOURCE_TEXT -> ADMITTED_MEANING_WITHOUT_ADMISSION        (M01/M02)
CANDIDATE_FINDING -> OFFICIAL_FINDING_WITHOUT_DISPOSITION (M07)
LOGIN_IDENTITY -> INSTITUTIONAL_STANDING                  (M08)
GATE_ALLOW -> COMPLETED_INSTITUTIONAL_TRANSITION          (M10)
DRAFT_OUTPUT -> OFFICIAL_RECORD                           (M11)
SUPERSEDED_STATE -> DELIVERABLE_WITHOUT_REGENERATION_OR_RESOLUTION (M12)
```

Any observed instance anywhere on the path prevents overall acceptance;
no compensating success in any other stage or in final-document quality
may offset it.

## Aggregate rule (pre-registered)

```
MISSION_SEMANTIC_ACCEPTANCE = PASS
   iff measured_cases = 12/12 AND MATCH = 12
       AND SEMANTIC_VIOLATION = 0 AND FORBIDDEN_PROMOTION = 0
       AND INCOMPLETE_OBSERVATION = 0

MISSION_SEMANTIC_ACCEPTANCE = FAIL
   iff any FORBIDDEN_PROMOTION observed anywhere on the path,
       or any SEMANTIC_VIOLATION in a measured case

MISSION_SEMANTIC_ACCEPTANCE = INCOMPLETE
   otherwise
```

No majority voting; no partial-success laundering; no percentage
substitute. **A mission never receives PASS on the strength of
correct-looking final documents if any intermediate forbidden transition
occurred** — M11 fidelity cannot compensate an upstream violation.

## Freeze declaration

Authored from frozen instruments only. After mission results are
observed this oracle receives NO edits; later interpretation is a
separately versioned addendum. A defect discovered post-execution
follows the frozen defect procedure (original results preserved;
re-evaluation only by separate owner authorization).
