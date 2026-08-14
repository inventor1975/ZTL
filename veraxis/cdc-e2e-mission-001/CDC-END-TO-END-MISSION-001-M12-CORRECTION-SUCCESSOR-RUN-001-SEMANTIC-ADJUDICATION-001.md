# CDC-END-TO-END-MISSION-001 — M12 CORRECTION-SUCCESSOR RUN-001 SEMANTIC ADJUDICATION 001

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-14. Classification: **independent adjudication of the completed
M12 correction-successor attempt against the frozen oracle and protocol. Not an
implementation review, not a repair, not an authorization for any recovery.**

```
evidence commit  b6dca9153cb8496b8147019e8f6074bf73cb14f7   verified
evidence tree    c77b8901f064a3598f2340fb26fac925d79f8cc0   verified
parent           f9afeea6f820391de18e9182f2eda763038ea94e   verified (= execution-gate acceptance)
```

## 0. A boundary I am declaring before anything else

Every prior adjudication in this mission was performed implementation-blind, and
the independence of the whole chain rests on that. **This handoff asks me, for
the first time, to inspect the accepted implementation** in order to establish
the cause of the failure, and it omits the implementation-blind clauses that
governed every earlier task.

I did **not** open implementation source or tests. I did not need to: the
causal proposition is fully established by the frozen failure observation's own
bytes, which contain the traceback. Reading an archived traceback that is part
of the evidence is not implementation inspection. The finding in §3 below is
therefore reached without spending the blindness that gives this chain its
value. If the owner wants a code-level confirmation beyond what the evidence
carries, that must be a separately identified act by someone else, or by me at
the explicit cost of blindness for all subsequent adjudications — a cost I am
not authorized to incur silently.

## 1. Authority chain — verified from repository bytes

```
execution decision   7589fc6f7557e538da6eb467d0d35257ec7058e6f555f9bcebadce47bec43e03  MATCH  1357 B
  decision           EXECUTE_AUTHORIZED_CORRECTION_ONCE                                  confirmed
  authority_scope    ONE_CORRECTION_SUCCESSOR_CONSTRUCTION   single_use true
  automatic_retry_authorized  false
AUTH-003             ee8b80921c704b165ab6482187cbbb1eab4fa315d7e89b468b98b83ac86f34ff  MATCH  3631 B
  located at veraxis/cdc-e2e-mission-001/authorizations/…-M12-AUTH-003.json
correction instr.    b8b4cfcb73df1db0f1fc057f2a445355f34d3bd02cd6b28a6136a27cadc53dfd  MATCH  1042 B
attempt record       7a5ff7eabaa103e1b0d682683a6bba478fa279908cf47e649d2b4edee2ce1472  MATCH   823 B
```

The decision binds the authorization, the instruction, the environment manifest
and the successor id; the attempt filename is keyed to the AUTH-003 digest. The
authorized successor `EBAWU-P-001-C-TENDER-01-CORR-001` and authorized
predecessor `EBAWU-P-001-C-TENDER-01` with digest `07db4673…` appear identically
in decision, attempt and observations.

## 2. Execution facts — verified from the archived bytes

```
attempt records in the directory        exactly 1
attempt_state                           CONSUMED_AFTER_FIRST_SUCCESSOR_CONSTRUCTION
successor_construction_invoked          true
successor_constructed                   true
successor_id                            EBAWU-P-001-C-TENDER-01-CORR-001
execution_invocation_count              1
automatic_retry                         false
attempt_record_deleted_or_rewritten     false
converted_to_no_attempt_record          false
direct_core_invocation                  false
post-issuance preflight                 18/18 passed, execution_allowed true, refusals []
```

One claim, one invocation, one consumption, no retry, no second result-bearing
invocation, and the ledger was neither deleted nor renamed. The attempt was
consumed **at first successor construction**, which is what the single-use
semantics specify — consumption is not contingent on the run completing.

## 3. The failure — established independently, not inherited

The frozen failure observation carries the traceback. Its frames, in order:

```
execute_authorized_correction_successor          cdc_e2e_mission.py:5356
  → verify_frozen_stage_2_archive_identity(authorization, locations)
      → find_repo_root(locations.root)           cdc_e2e_mission.py:4862
          → ConfigurationError [OIC-1001]        paths.py:62
            "no BOOTSTRAP_MANIFEST.json found at or above
             /private/tmp/cdc-e2e-stage2-run-001"
  → wrapped as PostConstructionIntegrityError    cdc_e2e_mission.py:5362
```

That `locations.root` is the **authorized runtime evidence root** is established
independently of any narrative: the execution decision's
`canonical_execution_decision_path`, the attempt record path, the AUTH-003 path,
the correction-instruction path and the environment-manifest path all resolve
inside `/private/tmp/cdc-e2e-stage2-run-001`.

**Independent finding.** Archive-identity verification resolves repository
identity by walking upward from the bound evidence root in search of
`BOOTSTRAP_MANIFEST.json`. The authorized evidence root is a runtime run
directory outside any repository checkout. The proposition put to me in the
handoff is therefore **confirmed on the evidence** — and confirmed without
adopting the producer's `failure_cause` string, which says the same thing.

**A consequence the label "infrastructure" tends to hide, and which I record
because it changes what remediation means.** This is not a transient or
environmental accident. Two requirements of the authorized run procedure are
mutually unsatisfiable by construction: archive-identity verification demands a
repository root, while the governed harness is required to run from a temp
evidence root that is not one. Any correction-successor execution under this
run procedure fails identically. "Infrastructure" here means *reproducible
design seam*, not *flaky, retry will clear it*. Recovery therefore requires a
governed change, not a rerun — which is also why §7 of the handoff is right that
no retry may occur under the consumed authority.

I do **not** adopt `failure_is_infrastructure_not_semantic: true` as the
adjudicative conclusion. I reach the classification in §6 myself, by testing
each M12 predicate and each frozen forbidden promotion.

## 4. What was observed and what was not

Observed, with evidence:

```
successor construction            OBSERVED   attempt + execution observation, successor_constructed true
successor id                      EBAWU-P-001-C-TENDER-01-CORR-001
predecessor before digest         07db4673eed5a124ee5eec96f4d149e59654632a12ad2632db72c19cc6efc311
predecessor after  digest         07db4673eed5a124ee5eec96f4d149e59654632a12ad2632db72c19cc6efc311
predecessor state                 ACCEPTED_CANDIDATE (unchanged from Stage-2)
predecessor_digest_unchanged_across_correction   true
single-use authority consumption  OBSERVED
automatic retry                   FALSE
```

Not produced as completed result observations — each explicitly recorded as
absent, not silently missing:

```
affected-output determinations    "NOT_PRODUCED: execution failed before result assembly"
stale-predecessor refusal         "NOT_PRODUCED: execution failed before result assembly"
final immutability observation    "NOT_PRODUCED_IN_RESULT; predecessor digests preserved in the failure context"
archive-identity verification     "NOT_OBSERVABLE: repository root could not be resolved from the bound evidence root"
CorrectionSuccessorResult         correction_successor_result_persisted false; raw_successor_result_exists false
correction-successor result digest  absent (no result to digest)
```

I infer none of these from the v0.4 pre-execution derivations or from
implementation intent, and I treat `NOT_OBSERVABLE` as the frozen protocol
requires — routed to unmeasured, never to guessed membership.

**The single most important negative check.** A successor was constructed but
**not persisted** (`correction_successor_result_persisted: false`,
`raw_successor_result_exists: false`). Had a successor object been written while
its supersession linkage, reason and changed-refs remained unassembled, the run
would have left a half-formed successor in the record — and that *would* have
been a semantic violation, not an infrastructure block. It did not. The failure
was contained on the safe side of the seam.

## 5. M12 predicate by predicate

| frozen predicate | state | evidence |
|---|---|---|
| correction creates a successor with new identity | **partially established** — construction observed, identity `…-CORR-001` recorded; the successor object itself was never assembled or persisted | attempt record, execution observation |
| supersession links both ways, reason, changed refs | **NOT ESTABLISHED** | no `CorrectionSuccessorResult` exists |
| predecessor never mutated; remains addressable and byte-preserved | **ESTABLISHED** | before = after = `07db4673…`; `predecessor_digest_unchanged_across_correction: true`; predecessor state unchanged |
| affected generated outputs become ineligible until regeneration or explicit human resolution | **NOT ESTABLISHED** | `affected_output_observations = NOT_PRODUCED`. (Stage-2 drafts remain `INELIGIBLE_PROVENANCE_INCOMPLETE`, but that is RUN-001 evidence, not an observation of this predicate) |
| a proposal against a superseded candidate is refused as stale | **NOT ESTABLISHED** | `stale_refusal_observation = NOT_PRODUCED` |
| *testable:* byte-identity of predecessors across correction | **ESTABLISHED** | as above |
| *testable:* supersession linkage complete | **NOT ESTABLISHED** | — |
| *testable:* post-correction deliverable eligibility recomputed or explicitly resolved | **NOT ESTABLISHED** | — |
| *testable:* stale-candidate proposal shows refusal (S-07 shape) | **NOT ESTABLISHED** | — |
| forbidden `CORRECTION → DESTRUCTION_OF_PREDECESSOR` | **not observed** | predecessor byte-identical, attempt ledger intact |
| forbidden `SUPERSEDED_STATE → DELIVERABLE_WITHOUT_REGENERATION_OR_RESOLUTION` | **not observed** | no deliverable regenerated or re-declared eligible |

Against the protocol's six MATCH conditions: (1) preconditions matched exactly
and (5) no forbidden promotion occurred, but (4) "all preservation/evidence
obligations observed" fails and (6) is only satisfied in the sense that the
absent states are absent **explicitly** rather than silently. MATCH is therefore
unavailable.

## 6. Classification

```
adjudication_state = INFRASTRUCTURE_BLOCKED
```

Reasoning, in the frozen vocabulary and not in the producer's:

- **Not SEMANTIC_VIOLATION.** No out-of-set value, no axis collapse, no
  unsupported truth-valued promotion, no unresolved state dropped, no
  predecessor destruction, no unrecorded consequential transition, no
  deliverable statement above its recorded state. The protocol freezes the
  equality `INFRASTRUCTURE_BLOCKED != SEMANTIC_VIOLATION`, and an exception
  alone never fires a violation.
- **Not FORBIDDEN_PROMOTION.** Neither M12 forbidden transition was observed;
  nothing was promoted anywhere.
- **Not PRECONDITION_MISMATCH.** Preconditions matched exactly: an eligible
  completed predecessor existed, all controlling identities verified, and the
  post-issuance preflight passed 18/18 with zero refusals.
- **Not NONCOMPARABLE.** The objects are comparable and were compared.
- **Why INFRASTRUCTURE_BLOCKED rather than INCOMPLETE_OBSERVATION.** Both leave
  M12 unmeasured, and the protocol routes `NOT_OBSERVABLE` to the unmeasured
  side either way. The distinction is the reason, and here it is specific: the
  authorized execution ran, was invoked once, and was stopped by a
  configuration/path-resolution failure inside a post-construction integrity
  step. That is infrastructure inability to complete a required observation, not
  the absence of a stimulus or of a precondition — which is what left M12
  incomplete in RUN-001. Recording it as INFRASTRUCTURE_BLOCKED preserves that
  difference; collapsing the two would lose the only fact that tells the owner
  what kind of remediation is even relevant.

```
M12_MATCH_ESTABLISHED = FALSE
```

M12 remains an unmeasured oracle case. Per protocol §7 an unmeasured case stays
unmeasured, and re-evaluation is available only as a separately identified,
owner-authorized successor measurement — the Slice-001 §7 path. This attempt is
not such a measurement; it is a blocked one.

**The cost, stated plainly.** The single-use authority AUTH-003 and its
execution decision are spent, and the attempt is consumed historical evidence.
That is correct behaviour, not a defect — but it means M12 now requires a new
governed authorization, and no recovery may reuse AUTH-003, the issued decision,
or the consumed attempt namespace. I neither recommend nor request such a
recovery.

## 7. RUN-001 history

```
raw result sha256      715a97038be184f5f0715a9e53d9ceb9150bf74b72e1ff2f4d27654c2b61d45d   unchanged
attempt record sha256  0d11efa747647bf6764bb7562b3a8e7b02219ed2b10f527ce4b5e69df3ca72d2   unchanged
route trace sha256     481957e87f73e2fc058e0e167b6d3d82fea830b2eaad16c78bdfc39f3c952920   unchanged
files touched in executions/STAGE-2-RUN-001 by this commit   0
```

The frozen RUN-001 record stands exactly as adjudicated at ZTL
`a682abc7e68a3fc98c3a131c10d9ec05457e5d9c`: historical M11 =
`SEMANTIC_VIOLATION`, historical M12 = `INCOMPLETE_OBSERVATION`, historical
aggregate = `FAIL`. Nothing in this attempt rewrites, reclassifies or improves
any of it, and this adjudication makes no such attempt.

## 8. Recorded observations

- **The controlling executable changed again.** This run executed under
  implementation `e01ab40c0ae63d5420248c8f950d3ca9fd8e618d` (tree `92780284…`),
  not the Stage-2 successor `50d9da82…`. Disclosed consistently in the decision,
  the attempt and the observation. Recorded for attribution: results from the
  three runs are not attributable to a single implementation.
- **Owner-decision verification is harness-enforced, not core-enforced.** The
  preflight discloses `production_hardening_question:
  MOVE_OWNER_EXECUTION_DECISION_VERIFICATION_INTO_CORE_RUNTIME_GATE` with status
  `OUT_OF_SCOPE_FOR_FROZEN_M12_SUCCESSOR`, and classifies a direct core call as
  `OUTSIDE_AUTHORIZED_RUN_PROCEDURE`. So "governed execution" here is a property
  of the harness, in the same class as the earlier
  `…_NOT_RUNTIME_VERIFIER_ENFORCED` bindings. Honestly disclosed; not adopted by
  me as a stronger claim.
- **The producer's own record keeps the right separation**:
  `m12_adjudication_in_this_record: "NONE_OBSERVATION_IS_NOT_ADJUDICATION"`.

## Return

```
M12_CORRECTION_SUCCESSOR_RUN_001_ADJUDICATION = COMPLETE

adjudication_state = INFRASTRUCTURE_BLOCKED
evidence_sufficiency = SUFFICIENT_TO_CLASSIFY_THE_ATTEMPT;
                       INSUFFICIENT_TO_MEASURE_M12

successor_construction_observed        = TRUE
predecessor_preservation_observed      = TRUE
affected_output_observation_complete   = FALSE
stale_refusal_observation_complete     = FALSE
archive_identity_observation_complete  = FALSE
correction_successor_result_exists     = FALSE
authority_consumed                     = TRUE
automatic_retry_occurred               = FALSE

failure_classification = POST-CONSTRUCTION ARCHIVE-IDENTITY VERIFICATION RESOLVED
  REPOSITORY IDENTITY FROM THE AUTHORIZED RUNTIME EVIDENCE ROOT, WHICH IS NOT A
  REPOSITORY. REPRODUCIBLE DESIGN SEAM UNDER THE AUTHORIZED RUN PROCEDURE, NOT A
  TRANSIENT ENVIRONMENT FAULT. NO SEMANTIC PREDICATE VIOLATED; NO SUCCESSOR
  PERSISTED.

M12_MATCH_ESTABLISHED   = FALSE
RUN_001_HISTORY_PRESERVED = TRUE

implementation_source_inspected = FALSE
implementation_tests_inspected  = FALSE
```

Scope ceiling: `SYNTHETIC_EVALUATION_ONLY`. This establishes no production
conformance, no CDC acceptance, no legal validity, no institutional authority,
and authorizes no recovery. OBSERVATION ≠ ORACLE ≠ ADJUDICATION ≠ OWNER CLAIM
DECISION.
