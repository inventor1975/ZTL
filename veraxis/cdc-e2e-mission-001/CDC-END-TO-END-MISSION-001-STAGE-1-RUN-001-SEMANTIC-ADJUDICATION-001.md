# CDC-END-TO-END-MISSION-001 — STAGE-1 RUN-001 SEMANTIC ADJUDICATION 001

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-12. Classification: **adjudication of a frozen, already-executed
Stage-1 run against the frozen oracle, using frozen protocol vocabulary only.
Not an implementation review, not a semantic design decision, not an
authorization for any further stage.**

Implementation blindness held: every object was read out of the object store by
exact path. No implementation source, no tests, no PR #24. The evidence index
present in the directory was treated as derived convenience metadata and carries
no weight in any determination below.

## 0. Identity verification (independently recomputed)

```
veraxis evidence commit  c44c9bf7d24b79990fb00274b871326f0d7617e9   verified
tree                     7ee4d2601e68c71bdf1f304b3e06750ec970aa15   verified
parent / implementation  2e15267194d320b54015f0c212a8041cedc22050   verified

raw result       aa32274f238d01bc9f6c6d1c67879acfb4765a34d0dc0b4ccf568f3c07353a70  MATCH  57970 B  MATCH
attempt record   b9977ea18e0a44b0213607aa9b8e512cac3aeebd4e1871aa6b80d9a2fca6478f  MATCH    416 B  MATCH
owner auth v0.2  47b97fadf9d44fdeec8359f7c582caf0269046d74cdd4b4353001b2ef7e3b240  MATCH   3306 B  MATCH
environment      7ace2de68d54c9ca2f3e1ee827e26fe11458c89854a0ed4d3552fce292876fe1  MATCH   3191 B  MATCH

stage_1_observation_digest  0c7c9aa770aee07b7c42f9bb48ec3b13058bbaf7559d5696bc59c6eb276510be
                            REPRODUCED = sha256(canonical(raw result minus the digest field))
```

Frozen semantic objects recomputed from my own repository, not read from the
evidence: oracle `72b554e6…`, protocol `0e2a9f72…`, plan `229a0c15…`. The
environment manifest binds these plus profile `03eb25ef…`, seam clarification
`a4a87ec5…`, owner interpretation `8242ccf9…` and package `b62f3966…` — all
identical to the frozen values. None was modified.

**Every digest in the run was reproduced from the frozen inputs, 9/9 chains:**

```
input_digest       sha256(canonical(frozen chain object minus chain_order,
                          object_digests, public_id))                  9/9 exact
evidence_bundle_digest  sha256(canonical(frozen evidence_bundle))      9/9 exact
evaluation_digest  sha256(canonical(evaluation minus its own digest))  9/9 exact
candidate_digest   sha256(canonical(candidate))                        9/9 exact
warrant_digest     sha256(canonical(warrant))                          9/9 exact
```

canonical = UTF-8 JSON, keys sorted, `ensure_ascii=false`, separators `,` `:`.

This matters for M01 and is stated because the raw result contains **zero**
occurrences of the strings `anchor`, `SRC-`, `admitted_control`, `source_hashes`
or `semantic_epoch`. Source binding is therefore not present as text — it is
present as a **cryptographic binding**: each chain's `input_digest` covers the
frozen chain object whose keys are `admission_record`, `admitted_control`,
`control_ref`, `ebawu`, `evidence_bundle`, `procedure_id`, `source_anchors`.
9/9 of those objects carry populated `source_anchors`. Binding by reproduced
digest is stronger than binding by restated text, not weaker.

## 1. Independent recomputation of the evaluation itself

I did not accept the recorded verdicts. For each of the nine chains I extracted
the observations from the **frozen input-v0.6 evidence bundles**, applied the
**frozen profile v0.2 ordered rules** myself, and compared:

```
chain               observed     recomputed   reason code observed / recomputed
P001×C-TENDER-01    SATISFIED    SATISFIED    ALL_REQUIRED_CONDITIONS_SATISFIED  (both)
P001×C-EVAL-01      SATISFIED    SATISFIED    ALL_REQUIRED_CONDITIONS_SATISFIED  (both)
P001×C-AWARD-01     SATISFIED    SATISFIED    ALL_REQUIRED_CONDITIONS_SATISFIED  (both)
P002×C-TENDER-01    BREACH       BREACH       REQUIRED_CONDITION_NOT_SATISFIED   (both)
P002×C-EVAL-01      BREACH       BREACH       REQUIRED_CONDITION_NOT_SATISFIED   (both)
P002×C-AWARD-01     BREACH       BREACH       REQUIRED_CONDITION_NOT_SATISFIED   (both)
P003×C-TENDER-01    UNRESOLVED   UNRESOLVED   MISSING_REQUIRED_EVIDENCE          (both)
P003×C-EVAL-01      UNRESOLVED   UNRESOLVED   MISSING_REQUIRED_EVIDENCE          (both)
P003×C-AWARD-01     UNRESOLVED   UNRESOLVED   MISSING_REQUIRED_EVIDENCE          (both)
```

0 divergences on verdicts, 0 on reason codes, and the consumed observations are
byte-identical to the frozen evidence bundles on every required fact — so the
runtime evidence source was the package, exactly as the seam clarification
requires, with no fallback to and no merge with the profile's constraint copy.

**P003 order behaviour, checked per chain rather than assumed.** Each P003 chain
carries *both* an absent fact and a conflicting fact simultaneously, and both
survive in the record:

```
P003×C-TENDER-01  absent: competition_notice_published []   conflicting: minimum_competition_period_met [true,false]
P003×C-EVAL-01    absent: scoring_record_complete []        conflicting: declared_criteria_only        [true,false]
P003×C-AWARD-01   absent: award_traceable_to_scoring []     conflicting: required_approvals_present    [true,false]
```

The reason code is `MISSING_REQUIRED_EVIDENCE` on all three because absence is
rule 1 and conflict is rule 2 in the frozen order. My recomputation, applying
that order independently, produced the same code. Nothing was discarded to reach
it: the conflicting observations remain visible in `observed_required_facts`. So
the record preserves *more* than the reason code reports, which is the correct
direction — the reason names the first ground, the evidence retains both.

## 2. Verdict per oracle case

| case | state | basis |
|---|---|---|
| **M01** SOURCE_BINDING | **MATCH** | `input_digest` reproduced 9/9 over frozen chain objects carrying populated `source_anchors`; no evaluated object participates anchor-free |
| **M02** OIC_ADMITTED_MEANING_BINDING | **MATCH** | `admission_record_ref` present 9/9 and resolving in the frozen registry; `admitted_control` inside the reproduced `input_digest`; profile bound by sha in every evaluation; unadmitted/absent content never became T or F — it became UNRESOLVED (the §24.5 discipline demonstrated, not asserted) |
| **M03** FROZEN_MISSION_POPULATION | **MATCH** | exactly 9 chains, 9 distinct chain ids, 3 procedures × 3 controls; accounting completed 9 / blocked 0 / refused 0 / non_evaluable 0 / unresolved 0, summing to 9 = population; no silent drop, no padded denominator |
| **M04** EVIDENCE_TO_CONTROL_TRACEABILITY | **MATCH** | `evidence_bundle_digest` recomputed exact on **total, not sample** (9/9); each bundle binds control and procedure; missing evidence surfaced as an explicit unresolved state with the absent fact named |
| **M05** DETERMINISTIC_EVALUATION_SEPARATION | **MATCH** | evaluation, candidate and warrant are distinct objects with distinct reproduced digests; evaluation vocabulary never occupies a disposition field; the warrant *consumes* the verdict as a labelled `evaluation_verdict` rather than becoming one; execution axis (`outcome_state`) kept separate from epistemic axis (`verdict`) |
| **M06** ZTL_WARRANT_VS_FALLBACK_SEPARATION | **MATCH** | 9/9 `FALLBACK_WARRANT`; `logical_warrant_status = NOT_ESTABLISHED`; `ztl_kernel_invoked = false`; `limitations = [NO_ZTL_DERIVATION]`; no ZTL warrant digest field exists in any warrant object |
| **M07** CANDIDATE_FINDING_NON_OFFICIALITY | **MATCH** | 9/9 `CANDIDATE_NOT_OFFICIAL` and `NOT_AUTHORIZED_AS_OFFICIAL`; `official_handoff = PROHIBITED`; `draft_eligibility = NONE`; zero occurrences of any official-finding token |
| **M08** REVIEWER_STANDING_AND_AUTHORITY_SCOPE | **INCOMPLETE_OBSERVATION** | no disposition occurred (`human_disposition = NOT_YET_SUPPLIED`), so no disposition record exists to carry identity, role assertion and authority scope. Nothing contradicts M08; it is not measurable from Stage-1 evidence |
| **M09** HUMAN_DISPOSITION_BOUNDARY | **INCOMPLETE_OBSERVATION** | the prohibition half is observably satisfied — `machine_disposition = null` 9/9 in both evaluation and candidate, no disposition-vocabulary token appears in any value position, `on_unknown` observed but not applied. The requirement's positive conjuncts (human actor binding, closed-set value, warrant byte-identity across disposition) need a disposition to exist. Grading MATCH here would be the artificial MATCH the protocol warns against |
| **M10** VEIP_TRANSITION_AFTER_VALID_DISPOSITION | **INCOMPLETE_OBSERVATION** | `institutional_transition = NONE`, zero events, zero transitions. The events-iff-transitions invariant holds vacuously at 0/0, which is not a measurement |
| **M11** DELIVERABLE_STATE_FIDELITY | **INCOMPLETE_OBSERVATION** | `draft_eligibility = NONE`; no deliverable was produced to check fidelity against |
| **M12** CORRECTION_AND_PREDECESSOR_PRESERVATION | **INCOMPLETE_OBSERVATION** | no correction issued — exactly the conditional observability pre-registered in review 001 and preserved by the owner interpretation |

```
measured_cases        7/12   (M01–M07)
MATCH                 7
SEMANTIC_VIOLATION    0
FORBIDDEN_PROMOTION   0
INCOMPLETE_OBSERVATION 5     (M08–M12)
INFRASTRUCTURE_BLOCKED 0
PRECONDITION_MISMATCH  0
NONCOMPARABLE          0

AGGREGATE = INCOMPLETE
```

Per the frozen rule, PASS requires 12/12 measured and 12 MATCH. Five cases are
downstream of Stage 1 and were not reachable by this run, so the aggregate is
INCOMPLETE. **This is the expected and correct shape of a Stage-1-only run and
must not be read as a failure**: zero violations and zero forbidden promotions
were observed, and every case Stage 1 could reach matched.

## 3. Authorization and single use

```
authorization scope   ONE_RESULT_BEARING_STAGE_1_EXECUTION      authorized_stage STAGE_1_ONLY
single_use            true      automatic_retry_authorized      false
stage_2_authorized    false     consume_on_first_governed_evaluator_invocation true
attempt record        exactly one, filename keyed to the authorization digest 47b97fad…
attempt_state         CONSUMED_AFTER_GOVERNED_EVALUATOR_INVOCATION
```

The ordering is coherent and checkable: the environment manifest was recorded at
15:53:44Z declaring `prospective_owner_authorization_exists: false` and
`stage_1_attempt_claim_created: false`, and creating no authority
(`authorizes_execution: false`, `consumes_attempt: false`); the authorization was
issued at 15:55:55Z; the attempt was then claimed and consumed once. One
authorization, one attempt, one run.

Stage 2, human disposition and correction were not performed: zero
disposition-vocabulary values, zero correction or supersession objects, zero
events, zero deliverables.

## 4. Recorded observations (none blocking)

- **`accounting.unresolved = 0` alongside three UNRESOLVED verdicts is not a
  contradiction, and should not be reported as one.** `accounting` counts
  execution outcome states; all nine chains completed. Three of them completed
  *with* an UNRESOLVED verdict. The two live on different axes, and keeping them
  apart is M05 working, not a discrepancy. Recorded because it is the single
  most likely thing for a later reader to misread.
- **Digest derivation rules for the run objects are not published.** The package
  rule was published and is reproducible. The five digests used inside this run
  (`input`, `evidence_bundle`, `evaluation`, `candidate`, `warrant`) and the
  `stage_1_observation_digest` are not. I reproduced all of them, but by
  inferring the rule — canonical JSON with sorted keys and compact separators,
  self-digest excluded, and for `input_digest` the frozen chain object minus
  `chain_order`, `object_digests`, `public_id`. An independent auditor without
  that guesswork is stuck. This is the third occurrence of the same class
  (A-OBS-2, then §0 of review 001). Publishing one derivation artifact, as was
  done for the package, closes it permanently.
- **The three-argument evaluator interface is not adjudicable from evidence.**
  The v0.1 profile recorded a defect — the Stage-1 path passing one object three
  times — and required `evaluator(admitted_control, evidence_bundle,
  admission_record)`. `input_digest` binds all three, but binding an input
  projection is not proof that the evaluator internally consumed three distinct
  arguments. That is an implementation fact, deliberately outside this review.
  Not adjudicated, and not counted for or against any case.
- **One reference outside the named frozen set.** The environment manifest cites
  `owner_semantic_preimplementation_freeze_sha256 = fa8f18cb…`, an object not
  supplied to me and not in the frozen list I was given. Unverified reference;
  no determination above depends on it.

## Return

```
CDC_E2E_MISSION_001_STAGE_1_RUN_001_SEMANTIC_ADJUDICATION = CONFORMANT

veraxis_evidence_commit             = c44c9bf7d24b79990fb00274b871326f0d7617e9
raw_result_sha256_verified          = TRUE
raw_result_bytes_verified           = 57970
stage_1_observation_digest_verified = TRUE
attempt_record_sha256_verified      = TRUE
attempt_state = CONSUMED_AFTER_GOVERNED_EVALUATOR_INVOCATION

M01 = MATCH                     M07 = MATCH
M02 = MATCH                     M08 = INCOMPLETE_OBSERVATION
M03 = MATCH                     M09 = INCOMPLETE_OBSERVATION
M04 = MATCH                     M10 = INCOMPLETE_OBSERVATION
M05 = MATCH                     M11 = INCOMPLETE_OBSERVATION
M06 = MATCH                     M12 = INCOMPLETE_OBSERVATION

measured_cases           = 7/12
match_cases              = 7
semantic_violations      = 0
forbidden_promotions     = 0
aggregate_protocol_state = INCOMPLETE

p003_missing_conflict_order  = MATCH
on_unknown_nonconsumption    = MATCH
fallback_warrant_separation  = MATCH
candidate_non_officiality    = MATCH
machine_disposition_boundary = MATCH

implementation_seen       = FALSE
human_disposition_applied = FALSE
stage_2_seen              = FALSE

blocking_issue = NONE
```

Scope ceiling: this adjudicates seven oracle cases against one frozen Stage-1
run under `SYNTHETIC_EVALUATION_ONLY`. It establishes no production conformance,
no CDC acceptance, no legal validity, no institutional authority, and no
authorization for Stage 2 or for any human disposition. OBSERVATION ≠ ORACLE ≠
ADJUDICATION ≠ OWNER CLAIM DECISION; this artifact is the third of those and
none of the others.
