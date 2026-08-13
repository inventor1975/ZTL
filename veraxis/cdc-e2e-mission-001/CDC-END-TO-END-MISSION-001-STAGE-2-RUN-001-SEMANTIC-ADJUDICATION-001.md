# CDC-END-TO-END-MISSION-001 — STAGE-2 RUN-001 SEMANTIC ADJUDICATION 001

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-13. Classification: **independent post-result adjudication of
M10, M11 and M12 against the frozen oracle, protocol and doctrine. Not an
implementation review, not an authorization for anything.**

```
evidence commit  1a80aabe0f72eac8570b9827ee7545cda370cbe8   verified
tree             a6216214ae5a49ffcb3448a97aadce1bb3f418e3   verified
branch           cdc-e2e-stage2-run-001-evidence
run / trace      CDC-E2E-STAGE2-RUN-001 / CDC-E2E-STAGE2-RUN-001-TRACE-001
```

## 0. Identities recomputed from repository bytes

```
raw Stage-2 result   715a97038be184f5f0715a9e53d9ceb9150bf74b72e1ff2f4d27654c2b61d45d  MATCH  72999 B  MATCH
embedded digest      8a12b681d1f08aa47b70830a939da9d545dccdcea33643fc6f5f6ca9450b3b40  REPRODUCED
AUTH-002             42b3c3d1285a0fddc36558875cc9df2e90b283ec79d96a56408b0fbc6f8c5f41  MATCH   8991 B  MATCH
issuance record 002  2dbe16f78f790db3325e43fc0538e991793524049788bee3b77b4372013ebc4c  MATCH   1036 B  MATCH
attempt record       0d11efa747647bf6764bb7562b3a8e7b02219ed2b10f527ce4b5e69df3ca72d2  MATCH   1234 B  MATCH
route trace          481957e87f73e2fc058e0e167b6d3d82fea830b2eaad16c78bdfc39f3c952920  MATCH   8883 B  MATCH
coverage defect      317820ab313d500841752b2f78b05abd2cc3be58234431f90eb1679b2c5b9842  MATCH   1724 B  MATCH
AUTH-001 withdrawn   8996b7bcc2fd077f0d5a35799df430616e3f632b429d2dd6453c45e4246a0333  MATCH   8844 B  MATCH
```

The embedded `stage_2_result_digest` was reproduced under the pre-published
derivation v0.2 rule — `sha256(canonical(result minus stage_2_result_digest))`,
canonical = UTF-8, sorted keys, `ensure_ascii=false`, separators `,` and `:`.
The persisted-file SHA-256 and the embedded digest are kept distinct throughout
this record.

**Transcription reconciliation confirmed independently of the report.** The
withdrawn AUTH-001 in the frozen evidence is 8844 B / `8996b7bc…`. The `7703 B`
figure appears nowhere in this evidence commit. The reconciliation record
`9cca2aa4…` (3200 B) is **not present in this commit**; I did not need it — the
substance was verified directly from the frozen bytes. Classification
`REPORTING_TRANSCRIPTION_ERROR_ONLY` is consistent with what I measured: the
frozen package is not affected.

**Independently reproduced bindings, 9/9 chains**, against the frozen Stage-1
result and the frozen input package — not against the owner report:

```
transition_event.candidate_digest        = Stage-1 candidate digest         9/9
transition_event.fallback_warrant_digest = Stage-1 warrant digest           9/9
transition_event.evidence_bundle_digest  = frozen evidence bundle digest    9/9
transition_event.OIC_control_digest      = canonical(admitted_control)      9/9
```

## 1. M10 — VEIP_TRANSITION_AFTER_VALID_DISPOSITION

```
classification = MATCH        confidence = HIGH
```

Observed, per chain, from the frozen result:

```
chain              decision  disposition        prior_state       new_state           epistemic
P001×TENDER/EVAL/AWARD  ALLOW  ACCEPT_CANDIDATE  CANDIDATE_FORMED  ACCEPTED_CANDIDATE  NOT_ADJUDICATED
P002×TENDER/EVAL/AWARD  ALLOW  ACCEPT_CANDIDATE  CANDIDATE_FORMED  ACCEPTED_CANDIDATE  NOT_ADJUDICATED
P003×TENDER/EVAL/AWARD  ALLOW  REQUEST_EVIDENCE  CANDIDATE_FORMED  EVIDENCE_REQUESTED  UNRESOLVED
```

Predicate by predicate:

- **"executes only given a valid disposition AND a gate ALLOW"** — satisfied.
  All nine bind a disposition adjudicated MATCH under M09 at `ea2d0b0…`, and all
  nine carry `decision = ALLOW`.
- **"ALLOW is necessary but NOT sufficient; the transition exists only when the
  executing component completes"** — satisfied and, importantly, *observable as
  a distinction*: `decision` and `outcome_state` are separate fields, with
  `detail = "transition event emitted after ALLOW"`. Nine ALLOW, nine
  completions, nine `outcome_state = transitioned`.
- **"events exist iff completed transitions exist (one-to-one)"** — satisfied
  exactly: 9 transitions, 9 events, 9 distinct `event_id`s, zero chains without
  an event, zero events without a chain.
- **"refusals and failures carry no events; prior states preserved
  byte-identically on every non-completed path"** — **vacuous in this run**. See
  the observability limitation below.
- Forbidden promotions: `GATE_ALLOW → COMPLETED_INSTITUTIONAL_TRANSITION` not
  observed (each ALLOW was followed by an actual completion, and the two are
  recorded on separate fields); `FAILED_EXECUTION → FABRICATED_COMPLETION` not
  observed (no failure occurred); `VEIP_ALLOW → LEGAL_OR_CDC_AUTHORITY` not
  observed (`official_handoff = PROHIBITED`, explicit nonclaims,
  `assurance_mode = SYNTHETIC_EVALUATION_ONLY`).

**The architecture's central claim is demonstrated on the hardest case.** The
three P003 chains carried an UNRESOLVED evaluation and a REQUEST_EVIDENCE
disposition. They acquired institutional consequence — `EVIDENCE_REQUESTED` —
while `epistemic_state` remained `UNRESOLVED` through the transition. Authorized
human judgment gained machine-operational effect **without any layer increasing
what that judgment meant**. Correspondingly, the six ACCEPT_CANDIDATE chains
moved to `ACCEPTED_CANDIDATE`, a candidate-use state, not to officiality. M06
discipline also survived downstream: `ZTL_warrant_digest = null` on all nine
with `fallback_warrant_digest` populated.

*Negative evidence considered:* no chain was refused, blocked, non-evaluable or
left unresolved (`accounting` = 9 transitioned, 0 elsewhere); no event lacks a
transition; no `correction_ref`; no `handoff_refs`; no
`downstream_eligibility_refs`.

*Observability limitations:* (a) the failure-preservation half of M10 — the
property Slice-001 earned — was **not exercised**: every path completed, so
"failures carry no events" and "prior state preserved on non-completed paths"
are vacuously true and remain undemonstrated by this run. M10 is matched on the
completing path only. (b) The route tracer was filtered to
`oic/cdc_e2e_mission.py`, leaving `evaluate_test_transition` and
`emit_transition_event` outside coverage. The frozen oracle does not make route
traversal an M10 predicate, so this does not defeat any predicate; equally I do
not infer traversal from result content or producer metadata, and the frozen
defect record states both directions correctly
(`absence_of_events_is_evidence_of_absence: false`,
`result_content_is_not_independent_route_proof: true`).

## 2. M11 — DELIVERABLE_STATE_FIDELITY

```
classification = SEMANTIC_VIOLATION        confidence = HIGH
```

Five drafts were produced (`CDC-E2E-OUTPUT-01…05`). Predicate by predicate:

- **"drafts are labelled drafts"** — satisfied. `status =
  SYNTHETIC_DRAFT_NOT_OFFICIAL` on all five, each with `label_en` / `label_fr`.
- **"nothing as official"** — satisfied. `official_status =
  NOT_AUTHORIZED_AS_OFFICIAL` and `official_handoff = PROHIBITED` on all five;
  every uppercase occurrence of `OFFICIAL` in the drafts block is inside a
  negation; six explicit nonclaims per draft.
- **"a candidate appears as a candidate"** — satisfied. `candidate_refs` and
  `candidate_digests` carry all nine candidates as candidates.
- **"every material statement traces to a recorded object without
  amplification"** — no amplification observed; result values render as
  `NOT_YET_OBSERVED` / `NOT_YET_ADJUDICATED` placeholders, and the provenance
  block carries resolvable refs (admission, evidence bundle, source anchor,
  evaluation, warrant, candidate).
- **"a dispositioned state as its disposition"** — **NOT SATISFIED.**

The failing predicate, measured:

```
drafts[*].provenance.disposition_per_candidate =
  {P001×… : "transitioned", … , P003×… : "transitioned"}   all nine identical

occurrences in the entire drafts block:
  ACCEPT_CANDIDATE   0
  REQUEST_EVIDENCE   0
```

The field named `disposition_per_candidate` does not carry a disposition. It
carries `"transitioned"` — an **execution-axis outcome state** — for all nine
chains, and the disposition vocabulary appears **nowhere** in the deliverables.
The six ACCEPT_CANDIDATE and three REQUEST_EVIDENCE dispositions are rendered
identically. The distinction that the entire standing-bearing human-disposition
layer exists to create is erased at the deliverable layer.

Two aggravating facts, both measured rather than inferred:

1. **The run declares the requirement satisfied.**
   `drafts[*].provenance_satisfied` includes `disposition_per_candidate`, while
   `provenance_absent` lists only `correction_refs`. The deliverable therefore
   asserts a provenance element it does not carry. This is what makes it a
   defect rather than a disclosed omission.
2. **A placeholder would have been honest; a wrong-axis value is not.** Other
   unavailable content is rendered as `NOT_YET_OBSERVED` /
   `NOT_YET_ADJUDICATED`. This field instead asserts a definite value drawn from
   the wrong axis — precisely the substitution the oracle's vocabulary section
   forbids ("no value on one axis may substitute for another") and that M05
   tests at object level upstream.

*Mitigating facts, recorded but not classification-changing:* the sibling field
`institutional_state_per_ebawu` **does** carry the differentiated states
(`ACCEPTED_CANDIDATE` ×6, `EVIDENCE_REQUESTED` ×3), so the distinction survives
elsewhere in the same package; all five drafts are
`INELIGIBLE_PROVENANCE_INCOMPLETE`, so nothing was relied upon; nothing was
promoted, made official, or stated above its recorded state. This is a fidelity
failure, **not** a forbidden promotion — hence `SEMANTIC_VIOLATION` and not
`FORBIDDEN_PROMOTION`.

*Why not INCOMPLETE_OBSERVATION.* I considered it seriously: the drafts are
ineligible and their content is largely placeholder, so one could argue fidelity
is unmeasurable. It is not. Deliverables were produced, they carry
state-bearing fields, and those fields are checkable — I checked them, and one
fails. Classifying a measured failure as unmeasured is precisely the conversion
the frozen doctrine §1 prohibits.

*Negative evidence considered:* `DRAFT_OUTPUT → OFFICIAL_RECORD` not observed;
no deliverable statement above its recorded state; no handoff; French path
honestly declared `PARTIAL` with seven named absences rather than synthesized.

## 3. M12 — CORRECTION_AND_PREDECESSOR_PRESERVATION

```
classification = INCOMPLETE_OBSERVATION        confidence = HIGH
```

Frozen record:

```
correction_executed             false
eligible_completed_predecessor  true
correction_stimulus_id          HA-CORRECTION-001
correction_target_id            HA-P001-C-TENDER-01
predecessor_ebawu_ref           EBAWU-P-001-C-TENDER-01
correction_target_source        FROZEN_ACTION_PLAN_BYTES
m12_state                       unavailable_incomplete
detail                          "an eligible predecessor exists but no correction object was supplied"
```

No correction was performed, so M12's requirement — successor identity, both
supersession links, reason, changed refs, predecessor byte-preservation,
downstream ineligibility, stale-proposal refusal — has nothing to measure. No
correction object was manufactured (`correction_refs = []` in every draft;
`correction_ref = null` in every event). The predecessor is preserved and
addressable.

**A precision that matters for what may happen next, and that differs from what
the doctrine anticipated.** Doctrine §6 addressed the case where the frozen
prerequisite *does not arise*. Here it **did** arise: an eligible completed
predecessor exists on the correction target chain. M12 is unmeasured because the
correction stimulus was not supplied in the authorized call, not because the
precondition failed. Under doctrine §4 that leaves a legitimate, separately
authorized successor observation available over the frozen predecessor — which
would not have been the case had the prerequisite failed to arise. I neither
request nor recommend such a run; I record that the door the doctrine describes
is open rather than closed, and that nothing in RUN-001 may be edited to walk
through it.

*Interaction worth recording:* `correction_refs` is the single absent provenance
element that renders all five drafts `INELIGIBLE_PROVENANCE_INCOMPLETE`. The
system therefore refused to declare a deliverable eligible while a required
provenance element was missing. That is conservative and correct behaviour, and
it stands in contrast to the M11 field that was declared satisfied while
carrying the wrong axis.

## 4. Cumulative ledger

```
M01 MATCH   M02 MATCH   M03 MATCH   M04 MATCH   M05 MATCH   M06 MATCH
M07 MATCH   M08 MATCH   M09 MATCH   M10 MATCH
M11 SEMANTIC_VIOLATION
M12 INCOMPLETE_OBSERVATION

match_count                  = 10
semantic_violation_count     = 1
forbidden_promotion_count    = 0
incomplete_observation_count = 1
infrastructure_blocked_count = 0
precondition_mismatch_count  = 0
noncomparable_count          = 0
measured_cases               = 11/12

AGGREGATE = FAIL
```

Applied mechanically: PASS requires 12/12 MATCH with zero errors — not met.
FAIL applies if a measured `SEMANTIC_VIOLATION` controls — one does, at M11.
The aggregate is therefore FAIL, and INCOMPLETE is not available.

I record plainly what this FAIL is and is not. It is **not** a failure of the
architecture's central claim: M10 matched on the hardest available case, with
UNRESOLVED epistemic state preserved through an institutional transition. It is
a fidelity defect in the deliverable-rendering layer of an ineligible draft — a
wrong-axis field value combined with a provenance element declared satisfied
that is not carried. Under the frozen protocol that defect controls the
aggregate regardless of its severity, and under doctrine §7 this observation is
now frozen: remediation may only be prospective, in a separately identified
successor observation, and cannot cause this violation to become unobserved.

Nothing above reopens M01–M09; nothing in the new evidence contradicts them, and
several of them are independently reconfirmed by the reproduced bindings.

## 5. Independence disclosure

```
implementation_source_inspected           = FALSE
implementation_tests_inspected            = FALSE
owner_requested_target_classification     = FALSE
operator_requested_target_classification  = FALSE
stage_2_rerun_requested                   = FALSE
post_result_evidence_manufactured         = FALSE
```

All six statements are made truthfully with one disclosure of method: the
evidence directory contains `AUTH-002-SHADOW-PREFLIGHT.d590de34.py` (12060 B).
It is a Python source file. I did **not** open it, on the ground that reading
source in the evidence directory would be indistinguishable from implementation
inspection. No determination above depends on it.

I did not rely on the owner/operator report where frozen evidence was
inspectable: the accounting, the per-chain outcomes, the digests, the drafts and
the correction record were all read from the frozen objects and, where a
derivation rule existed, recomputed.

Scope ceiling: `SYNTHETIC_EVALUATION_ONLY`. This establishes no production
conformance, no CDC acceptance, no legal validity and no institutional
authority. OBSERVATION ≠ ORACLE ≠ ADJUDICATION ≠ OWNER CLAIM DECISION.
