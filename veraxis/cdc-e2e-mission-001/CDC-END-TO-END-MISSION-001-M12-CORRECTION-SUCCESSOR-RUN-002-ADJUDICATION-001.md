# CDC-END-TO-END-MISSION-001 — M12 CORRECTION-SUCCESSOR RUN-002 ADJUDICATION 001

```
adjudicator              Vitaliy Reznik
adjudication_class       PREREGISTERED_BOUNDED_TECHNICAL_ADJUDICATION
independent_review_claim FALSE
```

**Why the independence claim is false, stated in my own words rather than
inherited.** I am the author of the frozen semantic acceptance oracle and of the
frozen result-adjudication protocol — the very criteria applied below. Adjudicating
against criteria I wrote is not independent review, whatever discipline I bring
to it. What I can still offer, and did: the criteria were frozen before any
result-bearing execution, I recomputed every identity from repository bytes
rather than accepting the producer's report, and I inspected no implementation
source or tests. That is preregistered bounded technical adjudication. It is not
independence, and this record does not claim it.

No repair was performed or proposed. No new execution was requested. No criterion
was added, removed, weakened or strengthened after execution.

## 1. Adjudication frame — established before reading substantive result fields

```
FROZEN CRITERIA (authored by this adjudicator, frozen 2026-08-11 at ZTL commit
2e2282cb1bdeef972e2cf189030f24b011be2868, before any result-bearing execution)

  semantic acceptance oracle v0.1, §M12
    path    veraxis/cdc-e2e-mission-001/CDC-END-TO-END-MISSION-001-SEMANTIC-ACCEPTANCE-ORACLE-v0.1.md
    sha256  72b554e6c3ac25b8785805e57f2d0b3f0167a30d7fb9d62b61977b07a364d0d9   11585 B
  result adjudication protocol v0.1
    path    veraxis/cdc-e2e-mission-001/CDC-END-TO-END-MISSION-001-RESULT-ADJUDICATION-PROTOCOL-v0.1.md
    sha256  0e2a9f7202b2136b1edd76148da4f1c957ff86301c42ddf6f0dc1055ce20426b    4661 B

FROZEN OWNER INTERPRETATION (Institutional-Compiler, present at the evidence commit)
    path    veraxis/cdc-e2e-mission-001/preexecution/CDC-END-TO-END-MISSION-001-OWNER-PREEXECUTION-INTERPRETATION-v0.1.md
    sha256  8242ccf9612531dc7b3b1d648625a934c4f616d8b8565c61d958a6825d7f2f84    9311 B

FROZEN CORRECTION TARGET (frozen at IC commit 08649178be5, ancestor of the evidence commit)
    path    veraxis/cdc-e2e-mission-001/correction-instructions/CDC-END-TO-END-MISSION-001-M12-CORRECTION-INSTRUCTION-002.json
    sha256  e33e075c8364f96c999072f12e8dd1f396ba85ad6085c13f5c1e85923a8fd703    1042 B

FROZEN AUTHORITY
    AUTH-004  eb759b44a5c971ba711b7a2a335c35bb8b993fe4f319ddb0c5cc8c4c9bd90e5f  3624 B
    Decision 002  8dabd04971466a4235803118b499122b694ed7fe9e2e0cfc139b0563dee543e0  1375 B

interpretation_frozen_before_result_bearing_execution = TRUE
```

Ancestry checked, not assumed: Instruction 002 entered at `08649178be5`, AUTH-004
at `708f4e439ad`, Decision 002 review at `4af30ce584a`/`28330f89dae` — all
ancestors of the evidence commit `806490b6`. The oracle and protocol were frozen
in a separate repository three days before the first result-bearing execution of
any stage.

**Provenance observation, recorded rather than smoothed.** The Experimental
Integrity and Observability Doctrine v0.1 (`f612f358…`) is **not present in this
evidence lineage**: its commit `d2aea903…` is not an ancestor of `806490b6`. It
remains addressable and byte-verified on the `cdc-e2e-mission-001-preexecution-records`
branch, and I applied it, but a reader reconstructing this adjudication from the
evidence commit alone would not find it there.

## 2. Raw evidence identity — recomputed from repository bytes

```
evidence commit  806490b659520a351e81ccb4d1d3f3ab214af70d   verified
evidence tree    b8c365ac7dfc7d52965b1f34170bc8db10c3d48d   verified
delta            5 files, additions only, all inside executions/M12-CORRECTION-SUCCESSOR-RUN-002/

raw_execution_package   1135011c87cc96461d36b1fe8f7189210250ac618b51439fc95db5581bb7e140   MATCH   5979 B  MATCH
run_metadata            dcb89d261205a145678873f711703075645c9868569c9cb0f7fdd4ff1aad82b4   MATCH    377 B
attempt_record          a73b402e5612630e9ebce0248b2f475c1cd97b0ca57d7692e376169aa3c4dd40   MATCH    823 B
CORR-002 raw result     8b81e62a1a5e65f14e86ced9f7b3c1f506f4dd4ccaa1c4375e4fb76d41fee246   MATCH  15756 B
execute_return_digest   f5af7424bc58addba6bf1a12a78a6f7fb5979fd730d045ca7ca06f739b5cffc7   MATCH
```

`correction_successor_result_digest` was **reproduced** from the result body under
the pre-published canonical rule (UTF-8, sorted keys, `ensure_ascii=false`,
separators `,` `:`, self-digest excluded) and equals `execute_return_digest`.

Required execution facts, each read from the archived package:

```
semantic_adjudication_performed_by_execution_actor  FALSE   (semantic_adjudication_performed false)
execute_invocations                                 1
result_bearing_core_invocations                     1
automatic_retry_performed                           FALSE
second_execute_invocation                           FALSE
RUN_001_MODIFIED                                    FALSE
source_changed_during_execution                     FALSE
environment_changed_during_execution                FALSE
exception                                           NONE
```

`raw_evidence_verified = TRUE`.

## 3. Observation table — facts present in the frozen evidence

No pass/fail language appears in this table.

| field | observed value |
|---|---|
| successor_id | `EBAWU-P-001-C-TENDER-01-CORR-002` |
| successor.supersedes | `EBAWU-P-001-C-TENDER-01` |
| successor.new_state | `CANDIDATE_FORMED` |
| successor.prior_state | `ACCEPTED_CANDIDATE` |
| successor.new_candidate_digest | `d9fb749c59b3da5ddacfcf846fc89aaeb569fa3ada846150ee26f0ed7bac7eb1` |
| successor.superseded_by | `null` |
| successor.reliance_impact_refs | `[]` |
| successor.production_reliance_semantics | `OUT_OF_SCOPE` |
| predecessor_id | `EBAWU-P-001-C-TENDER-01` |
| predecessor_digest | `07db4673eed5a124ee5eec96f4d149e59654632a12ad2632db72c19cc6efc311` |
| predecessor.state | `ACCEPTED_CANDIDATE` |
| predecessor_byte_identity_preserved | `true`; level-1 in-memory before = after; level-2 expected = observed on RUN-001 raw result, attempt record and route trace; `mismatched: []` |
| supersession_record.superseded_by | `EBAWU-P-001-C-TENDER-01-CORR-002` |
| supersession_record.predecessor_mutated / _rewritten | `false` / `false` |
| affected_output_refs | 5 outputs, `CDC-E2E-OUTPUT-01…05` |
| affected_output_eligibility (each) | `post_correction_reliance_state = INELIGIBLE_PENDING_REGENERATION_OR_EXPLICIT_HUMAN_RESOLUTION`; `correction_impact = AFFECTED_BY_SUPERSESSION`; `frozen_draft_modified = false`; `pre_correction_frozen_eligibility = INELIGIBLE_PROVENANCE_INCOMPLETE` |
| stale predecessor decision | `DENY` |
| stale predecessor reason | `CANDIDATE_SUPERSEDED_OR_CORRECTED` |
| stale predecessor gate_invoked | `false` (rule source `oic.cdc_slice.refuse_stale_candidate_proposal`; `transition_event_emitted: false`; `stage_2_attempt_touched: false`) |
| archive_identity_verified | `true`; expected = observed commit `1a80aabe…`, tree `a6216214…`, branch `cdc-e2e-stage2-run-001-evidence`, `mismatched: []`, source `ORIGIN_LS_REMOTE` |
| correction_executed | `true` |
| successor_constructed | `true` |
| stage_2_reexecuted | `false` |
| run_001_modified | `false` |
| m11_repaired | `false` |
| official_handoff | `PROHIBITED` |
| attempt state | `CONSUMED_AFTER_FIRST_SUCCESSOR_CONSTRUCTION`, one record, keyed to AUTH-004 digest |
| authority state | AUTH-004 single-use, Decision 002 `EXECUTE_AUTHORIZED_CORRECTION_ONCE`, retry not authorized |

Additional observation of interest, since it is the seam that blocked RUN-001:
`repository_observation_root = /private/tmp/claude-501/cleanroom` with source
`LOADED_IMPLEMENTATION_LOCATION`, distinct from `runtime_evidence_root =
/private/tmp/cdc-e2e-stage2-run-001`, and
`runtime_evidence_root_equals_repository_observation_root: false`, with both
`caller_injectable: false` and `environment_override_used: false`.

## 4. Criterion matrix — frozen criteria only

Evidence reference for every row is the RUN-002 raw result
(`8b81e62a…`) unless stated otherwise.

| id | criterion (frozen) | required observation | observed | class |
|---|---|---|---|---|
| M12-R1 | correction creates a successor with new identity | distinct successor id | `…-CORR-002`, distinct from predecessor | SATISFIED |
| M12-R2 | supersession links both ways | successor→predecessor and predecessor→successor | `supersedes` + `supersession_record.superseded_by` | SATISFIED |
| M12-R3 | reason and changed refs recorded | both present | `correction_reason` verbatim; `changed_fact_or_control_refs: [C-TENDER-01]` | SATISFIED |
| M12-R4 | predecessor never mutated; addressable and byte-preserved | byte identity | two levels, `mismatched: []` | SATISFIED |
| M12-R5 | affected generated outputs become ineligible until regeneration or explicit human resolution | per-output determination | 5/5 `INELIGIBLE_PENDING_REGENERATION_OR_EXPLICIT_HUMAN_RESOLUTION` | SATISFIED |
| M12-R6 | proposal against a superseded candidate refused as stale | refusal with reason | `DENY` / `CANDIDATE_SUPERSEDED_OR_CORRECTED` | SATISFIED |
| M12-T1 | byte-identity of predecessors across correction | before = after | `07db4673…` = `07db4673…` | SATISFIED |
| M12-T2 | supersession linkage complete | both directions + event id | present, `CDC-E2E-M12-CORRECTION-EVT-002` | SATISFIED |
| M12-T3 | post-correction deliverable eligibility recomputed or explicitly resolved | explicit determination | recomputed for all 5, successor-side; frozen drafts unmodified | SATISFIED — see §5 boundary |
| M12-T4 | stale-candidate proposal shows the refusal (S-07 shape) | refusal observed | `DENY`, no transition event, gate not reached | SATISFIED |
| M12-F1 | forbidden: CORRECTION → DESTRUCTION_OF_PREDECESSOR | absent | predecessor intact at two levels | NOT OBSERVED |
| M12-F2 | forbidden: SUPERSEDED_STATE → DELIVERABLE_WITHOUT_REGENERATION_OR_RESOLUTION | absent | all 5 marked ineligible pending resolution | NOT OBSERVED |
| INSTR-1 | Instruction 002: successor id `…-CORR-002` | exact | exact | SATISFIED |
| INSTR-2 | Instruction 002: predecessor `EBAWU-P-001-C-TENDER-01`, digest `07db4673…` | exact | exact | SATISFIED |
| INSTR-3 | Instruction 002: `new_state = CANDIDATE_FORMED` | exact | exact; prior `ACCEPTED_CANDIDATE` recorded and not inherited | SATISFIED |
| INSTR-4 | Instruction 002: `new_candidate_digest = d9fb749c…` | exact | exact | SATISFIED |
| INSTR-5 | Instruction 002: changed refs `[C-TENDER-01]` | exact | exact | SATISFIED |
| INSTR-6 | Instruction 002: correction reason | verbatim | verbatim | SATISFIED |
| AUTH-1 | authority consumed exactly once | one attempt, consumed | one record, `CONSUMED_AFTER_FIRST_SUCCESSOR_CONSTRUCTION` | SATISFIED |
| AUTH-2 | one result-bearing invocation | 1 / 1, no second | `execute_invocations 1`, `result_bearing_core_invocations 1`, `second_execute_invocation false` | SATISFIED |
| AUTH-3 | no automatic retry | false | false | SATISFIED |
| AUTH-4 | execution actor performs no semantic adjudication | false | `semantic_adjudication_performed: false`; package states no verdict is recorded | SATISFIED |
| PRES-1 | RUN-001 unmodified | three identities preserved | raw result, attempt, route trace all unchanged | SATISFIED |
| PRES-2 | Stage 2 not re-executed | false | `stage_2_reexecuted: false` | SATISFIED |
| PRES-3 | M11 not repaired | false | `m11_repaired: false` | SATISFIED |
| PRES-4 | prior blocked/spent lineage not converted into success | separate run identity and namespace | run id `…RUN-002`, attempt keyed to AUTH-004, RUN-001 correction evidence untouched | SATISFIED |
| CEIL-1 | execution stays inside the authorized claim ceiling | `SYNTHETIC_EVALUATION_ONLY`, no official handoff | ceiling declared in result and package; `official_handoff: PROHIBITED` | SATISFIED |

```
criteria_total          27
criteria_satisfied      27   (M12-F1/F2 counted as satisfied by absence)
criteria_not_satisfied   0
criteria_not_observable  0
criteria_outside_scope   0
```

## 5. Boundary questions A–L

**A** yes — successor constructed under AUTH-004 / Decision 002, single-use, one
invocation. **B** yes — bound to `EBAWU-P-001-C-TENDER-01` with the digest named
in Instruction 002. **C** yes — byte identity preserved at two levels, including
the frozen RUN-001 files. **D** yes — supersession is an explicit record in both
directions with an event id; `predecessor_mutated: false`,
`predecessor_rewritten: false`. **E** yes as required by the frozen mission — see
the boundary below. **F** yes — `DENY` with `CANDIDATE_SUPERSEDED_OR_CORRECTED`;
`gate_invoked: false` means the refusal occurred at the rule layer *before* the
gate, which is stronger than a gate denial, and no transition event was emitted.
**G** yes — Stage 2 frozen, not rerun. **H** yes — RUN-001 unchanged. **I** yes —
M11 left unrepaired. **J** yes — consumed exactly once. **K** yes —
`SYNTHETIC_EVALUATION_ONLY` throughout. **L** no machine-observable result
established official handoff, institutional issuance, institutional reliance or
currentness; the frozen mission did not require them, so their absence is not a
failure and is not treated as one.

**The boundary material to interpreting this pass.** The post-correction
eligibility determination for all five outputs exists **on the successor side**.
The frozen RUN-001 drafts are byte-unchanged and carry no marker that they are
now affected by a supersession — correctly, since immutability forbids editing
them. So what is established is that the system *recorded* the affected outputs
as ineligible pending regeneration or explicit human resolution, not that
ineligibility *propagated into* the deliverables. A consumer reading the frozen
drafts alone would not learn it; the successor record must be consulted. This is
exactly the frozen architectural boundary — reliance and currentness propagation
remains an architectural requirement rather than an established executable
reliance claim — and it is stated here because "affected outputs became
ineligible" would otherwise be read as propagation.

## 6. Verdict

```
RUN_002_ADJUDICATION = PASS_WITH_BOUNDARY_LIMITATION
first_failed_criterion = NONE
```

All 27 frozen criteria are satisfied; the qualifier records the §5 boundary,
which is material to interpreting what the pass means, not a complaint that
broader architecture is unfinished.

```
ESTABLISHED
  Under a separately issued single-use authority, and without re-executing Stage 2,
  the system constructed one durable correction successor bound to the intended
  predecessor; recorded supersession explicitly in both directions with a correction
  event id, reason and changed control refs; preserved the predecessor byte-identically
  at two levels including the frozen RUN-001 evidence; verified frozen Stage-2 archive
  identity against origin after construction; recomputed post-correction eligibility for
  all five affected outputs as ineligible pending regeneration or explicit human
  resolution, on the successor side and without modifying the frozen drafts; and refused
  a stale pre-correction candidate proposal with an explicit reason, before the gate and
  without emitting a transition event. Bounded, synthetic, one execution.

NOT_ESTABLISHED
  Official finding, institutional issuance, official handoff, institutional reliance,
  institutional legitimacy, reliance or currentness propagation into the deliverables
  themselves, general CDC production readiness, universal institutional continuity,
  repair of the M11 semantic violation, and any re-measurement or improvement of the
  RUN-001 record.
```

## 7. Historical lineage preserved

RUN-001, AUTH-003, CORR-001, the spent and blocked attempt, Instruction 002,
AUTH-004, Decision 002 and RUN-002 retain their distinct historical meanings.
RUN-002 is a new, separately authorized correction-successor attempt; it does
**not** convert the earlier blocked attempt into a successful one, and that
attempt remains `INFRASTRUCTURE_BLOCKED` as adjudicated at ZTL `91910d0c…` with
corrigendum `76f2eafe…`. Stage-2 RUN-001 stands as adjudicated at ZTL
`a682abc7…`: M11 `SEMANTIC_VIOLATION`, M12 `INCOMPLETE_OBSERVATION`, aggregate
`FAIL`. No historical verdict is rewritten here.

Whether this successor observation is elected as the separately identified
successor **measurement** of oracle case M12 at mission level is not decided by
this adjudication and is not implied by it. That is a mission-final-disposition
question for the owner; the frozen protocol requires any such measurement to be
separately identified and to leave the predecessor record intact, which it does.

## 8. Limitations and declarations

- **Fourth distinct implementation in the mission.** RUN-002 executed under core
  `97f814e3d4ff40db6cdd55197a48e15c57b2ad49` (tree `ff6d864a…`), after Stage-2
  `50d9da82…` and correction RUN-001 `e01ab40c…`. Mission results are not
  attributable to a single implementation.
- `remote_commit_tree_source: LOCAL_OBJECT_FOR_ORIGIN_SUPPLIED_SHA` — the commit
  sha came from origin, the tree was read from a local object for that sha.
  Recorded for precision; the expected/observed pair matched with `mismatched: []`.
- Route trace not produced by this route (`route_trace_produced_by_this_route:
  false`); no transition event was emitted by this route, consistent with a
  correction-successor construction rather than an institutional transition.
- The evidence directory contains an execution harness `.py` (29929 B). I did not
  open it, for the same reason as in the RUN-001 adjudication.

```
implementation_source_inspected  FALSE
implementation_tests_inspected   FALSE
repair_performed                 FALSE
repair_proposed                  FALSE
new_execution_requested          FALSE
criteria_modified                FALSE
execution_evidence_modified      FALSE
run_001_evidence_modified        FALSE
git diff -- src tests            EMPTY (verified in the Institutional-Compiler working tree)
```

Scope ceiling: `SYNTHETIC_EVALUATION_ONLY`. OBSERVATION ≠ ORACLE ≠ ADJUDICATION ≠
OWNER CLAIM DECISION.
