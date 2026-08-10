# CDC-EXEC-VERTICAL-SLICE-001 — RUN-002 ADJUDICATION 001

Adjudicator: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-10. Filled strictly per the frozen ADJUDICATION-RECORD-
TEMPLATE v0.1 (`98724f81…`), under the frozen Oracle v0.1 (`392f2981…`)
and Result Adjudication Protocol v0.1 (`5884c984…`). No instrument was
modified; no new state was invented; observation precedence honored (raw
observations were not rewritten to fit intended designs).

```
implementation_seen = TRUE
execution_results_seen = TRUE
mission_results_seen = TRUE
```

Evidence integrity (verified BEFORE reading any outcome): raw package
`CDC-EXEC-VERTICAL-SLICE-001-RUN-002-RAW.tar` 133120 B, sha256
`b336b3f75310a8c7d89033ee3d642b11463673ab2f47bb73bc87029c0458eed7`
(byte-exact; browser-duplicate filename "(1)" — bytes canonical);
extracted isolated; `13-SHA256SUMS/SHA256SUMS` = ALL OK; all eight
`RECORD.sha256` = OK; owner authorization `094d7bf4…` EXACT; pre-run
manifest `c6f830e4…` EXACT; all eight observation digests EXACT per the
work order. Run identity: RUN-002 @ combined head `6dc88cec…` /
`d19a2f58…`. RUN-001 not folded in. Upstream evaluation `verdict` fields
(SATISFIED/BREACH/UNRESOLVED) treated as consumed evidence only.

---

## S-01

```text
case_id = S-01
observation_record_id = OBSERVATION-S-01
observation_digest = 7b06bd572e827043bb772590f6d9d11e654707b602cdf0eed9109c2dcc9eec46
observed_precondition = NOMINAL — valid bounded TEST disposition on a
  clean procedure; all bindings and digests present (RAW-CASE-S-01)
oracle_precondition_match = exact

observed_epistemic_state = NOT_ADJUDICATED (gate assigned no epistemic
  state of its own; the warrant artifact ZTL-P-001-C-TENDER-01 preserved
  digest-bound, unmodified)
observed_operational_state = ALLOW (reason SLICE_CONTRACT_SATISFIED;
  operational record COMPLETED after ALLOW)
observed_institutional_state = ACCEPTED_CANDIDATE inside
  CDC-TEST-MISSION-001; transition_executed = true

required_evidence_present = YES — §8 event emitted
  (11-RAW-EVENTS/EVENT-S-01.json: APPLY_TEST_DISPOSITION,
  assurance_mode=SYNTHETIC_EVALUATION_ONLY, prior/new state, disposition,
  reason_code, epistemic_state carried separately; input digests bound)
forbidden_promotion_observed = NONE (event carries synthetic assurance
  mode; no authority/officiality representation)
oracle_membership_epistemic = IN_SET (warrant state unmodified by gate)
oracle_membership_operational = IN_SET (ALLOW, all 13 conditions)
oracle_membership_institutional = IN_SET (permitted disposition, §6
  meaning controlling: candidate use only)

adjudication = MATCH
reason = all six MATCH conditions of protocol §4 hold; evidence:
  OBSERVATION-S-01.json, RAW-CASE-S-01.json, EVENT-S-01.json.
```

## S-02

```text
case_id = S-02
observation_record_id = OBSERVATION-S-02
observation_digest = 248e37c883650995b415809407bcfd585504d80424d7ca88a6ccc1719a60caf3
observed_precondition = EVIDENCE_ABSENT — required evidence object absent
  from the run snapshot
oracle_precondition_match = exact (oracle S-02: required evidence
  reference unresolvable, §7 condition 5)

observed_epistemic_state = UNRESOLVED (survives; no refutation from
  absence anywhere in the record)
observed_operational_state = ESCALATE (reason
  REQUIRED_EVIDENCE_BINDING_UNRESOLVED); not ALLOW
observed_institutional_state = no transition; prior state
  CANDIDATE_FORMED persists; side_effect_refs = []

required_evidence_present = YES — absence named in reason_code;
  unresolved state first-class in the observation
forbidden_promotion_observed = NONE (MISSING_EVIDENCE -> PASS not
  observed; Z -> F from absence not observed)
oracle_membership_epistemic = IN_SET (unresolved survives; REFUTED absent)
oracle_membership_operational = IN_SET ({DENY, ESCALATE} permitted)
oracle_membership_institutional = IN_SET (no accepting transition)

adjudication = MATCH
reason = permissible outcome space of oracle S-02 satisfied on all axes;
  evidence: OBSERVATION-S-02.json, RAW-CASE-S-02.json.
```

## S-03

```text
case_id = S-03
observation_record_id = OBSERVATION-S-03
observation_digest = 8b6358c1e91830ddead3904d3f1705dc6bb8c202d7de102b1c4c2a6b76cb8d0b
observed_precondition = ADMISSION_ABSENT — admission record absent, so
  admitted meaning is unsupported
oracle_precondition_match = exact (oracle S-03: no admission_record_ref
  resolvable)

observed_epistemic_state = NOT_ADJUDICATED — no truth-valued reasoning
  proceeded on the unsupported content
observed_operational_state = ESCALATE (reason
  REQUIRED_ADMISSIONS_BINDING_UNRESOLVED); ALLOW absent
observed_institutional_state = no transition; candidate remains a
  candidate (preserved_artifact_refs), not promoted

required_evidence_present = YES — refusal recorded with reason; candidate
  preserved unpromoted
forbidden_promotion_observed = NONE (unsupported marking never entered
  evaluated reasoning; no EARNED/REFUTED rides it)
oracle_membership_epistemic = IN_SET
oracle_membership_operational = IN_SET ({DENY, ESCALATE})
oracle_membership_institutional = IN_SET

adjudication = MATCH
reason = the §24.5-class enforcement the oracle requires is observed:
  unsupported admission blocks truth-valued downstream reasoning;
  evidence: OBSERVATION-S-03.json, RAW-CASE-S-03.json.
```

## S-04

```text
case_id = S-04
observation_record_id = OBSERVATION-S-04
observation_digest = b00da7ad15f4a0f84ffd0c1773910905ac193e6b8e1c7fd0761f78d6e06239ac
observed_precondition = REVIEWER_OUT_OF_SCOPE — reviewer asserts a scope
  outside the mission-scoped standing (determinate mismatch)
oracle_precondition_match = exact

observed_epistemic_state = NOT_ADJUDICATED — candidate/warrant states
  untouched (authority failure carried zero truth implication)
observed_operational_state = DENY (reason UNAUTHORIZED_REVIEWER_SCOPE)
observed_institutional_state = no transition; prior state persists

required_evidence_present = YES — attempt preserved with declared
  reviewer identity/scope in the observation and raw case;
  transition_executed = false recorded
forbidden_promotion_observed = NONE (UNAUTHORIZED_REVIEWER ->
  AUTHORIZED_DISPOSITION not observed; DENY not stored as REFUTED)
oracle_membership_epistemic = IN_SET (unchanged)
oracle_membership_operational = IN_SET (DENY for determinate mismatch)
oracle_membership_institutional = IN_SET (no transition)

adjudication = MATCH
reason = oracle S-04 satisfied on all axes; evidence:
  OBSERVATION-S-04.json, RAW-CASE-S-04.json.
```

## S-05

```text
case_id = S-05
observation_record_id = OBSERVATION-S-05
observation_digest = d6d64e987af70748369839b0d5f155bb22b2c3bec204d4b0fd87c8bc9c2f1b8a
observed_precondition = EVIDENCE_MUTATED_AFTER_BINDING; probe A-05
  states the mutation precisely: "bound candidate altered after the
  proposal captured its digest", target boundary = candidate digest
  recomputation
oracle_precondition_match = exact — oracle S-05 covers a bound object's
  bytes/digest changing after candidate binding, anchored to contract §7
  conditions 2/13 ("candidate/evidence digest mismatch"); the mutated
  bound object here is the candidate

observed_epistemic_state = NOT_ADJUDICATED — original recorded states
  unmodified; no truth/warrant rewrite
observed_operational_state = DENY (reason CANDIDATE_DIGEST_MISMATCH;
  probe's permitted_decisions = [DENY])
observed_institutional_state = no transition; candidate ineligible on the
  mutated object; prior state persists

required_evidence_present = YES — both identities in the record (bound
  digest in proposal_as_executed; mutated object in the run snapshot);
  original artifacts preserved (preserved_artifact_refs)
forbidden_promotion_observed = NONE (DIGEST_MISMATCH ->
  EXECUTED_TRANSITION not observed)
oracle_membership_epistemic = IN_SET
oracle_membership_operational = IN_SET (DENY, integrity failure)
oracle_membership_institutional = IN_SET

adjudication = MATCH
reason = integrity refusal exactly as frozen; evidence:
  OBSERVATION-S-05.json, RAW-CASE-S-05.json (probe A-05).
```

## S-06

```text
case_id = S-06
observation_record_id = OBSERVATION-S-06
observation_digest = 6c169538c7803e37a1f321a88f0bb8d396d33f1da5fb06c3780982987c9f7d6c
observed_precondition = CONTRADICTORY_CANNOT as designed; probe A-02
  states the instantiation: "mutually inconsistent observations added
  AFTER digest binding", permitted_decisions = [DENY, ESCALATE]. The
  contradictory-evidence disjunct of oracle S-06's precondition WAS
  instantiated; it manifested at the binding boundary. No semantic
  cannot_condition flag was present in the executed proposal.
oracle_precondition_match = exact on the first (contradictory-evidence)
  disjunct of the oracle precondition

observed_epistemic_state = NOT_ADJUDICATED — the conflict was NOT
  normalized into any marking or truth value (oracle S-06: a
  contradictory ground set is an admission/binding-level conflict, never
  a third truth value); no CANNOT state existed in the executed case, so
  nothing was collapsed (CANNOT -> REFUTED not observed; REFUTED occurs
  nowhere)
observed_operational_state = DENY (reason
  EVIDENCE_BUNDLE_DIGEST_MISMATCH) — permitted by the oracle: "DENY
  permitted ONLY where the contract explicitly maps that condition to
  DENY"; contract §7 DENY list explicitly includes candidate/evidence
  digest mismatch; N-2 vacuously honored (no CANNOT existed to preserve;
  epistemic dimension remained non-truth-valued and separate)
observed_institutional_state = no accepting disposition; no transition;
  prior state persists

required_evidence_present = YES — both conflicting identities preserved
  (bound digest vs mutated bundle in the snapshot); reason_code names the
  conflict at its boundary
forbidden_promotion_observed = NONE
oracle_membership_epistemic = IN_SET (admission-level conflict reading;
  no normalization)
oracle_membership_operational = IN_SET (explicitly-mapped DENY)
oracle_membership_institutional = IN_SET

adjudication = MATCH
reason = the contradictory-evidence disjunct ran and every observed value
  lies in the frozen permitted sets; the CANNOT disjunct was not
  exercised, which narrows coverage but is not a mismatch of the
  disjunctive precondition; evidence: OBSERVATION-S-06.json,
  RAW-CASE-S-06.json (probe A-02).
```

## S-07

```text
case_id = S-07
observation_record_id = OBSERVATION-S-07
observation_digest = 1f2382518926c5e2cd4c0638a10ed96435201207b3382287738d5307a4269789
observed_precondition = PREDECESSOR_SUPERSEDED — candidate superseded by
  a correction issued beforehand; a proposal then arrives against the
  stale predecessor
oracle_precondition_match = exact (oracle S-07 names this path verbatim:
  "a proposal against the STALE predecessor thereafter -> DENY (ALLOW
  condition 12)")

observed_epistemic_state = NOT_ADJUDICATED — predecessor's recorded
  states remain historical facts, unmodified
observed_operational_state = DENY (reason
  CANDIDATE_SUPERSEDED_OR_CORRECTED)
observed_institutional_state = no transition on the stale object; prior
  state persists; predecessor artifacts preserved and addressable
  (preserved_artifact_refs: CAND-P-002-C-AWARD-01 et al.)

required_evidence_present = YES — supersession named in reason_code;
  predecessor set preserved in the frozen snapshot
forbidden_promotion_observed = NONE (CORRECTION ->
  DESTRUCTION_OF_PREDECESSOR not observed)
oracle_membership_epistemic = IN_SET
oracle_membership_operational = IN_SET
oracle_membership_institutional = IN_SET

adjudication = MATCH
reason = staleness refusal exactly as frozen; evidence:
  OBSERVATION-S-07.json, RAW-CASE-S-07.json.
```

## S-08

```text
case_id = S-08
observation_record_id = OBSERVATION-S-08
observation_digest = e1c9fbe8a59fc4ad9ef1eb02603a0409aadb923c338e64e745a9faccc9c4fd9d
observed_precondition = WARRANT_CLASS_ABSENT — "warrant class removed
  entirely; no substitute artifact offered" (probe A-07); the run-level
  record confirms no component failure occurred:
  12-FAILURES/FAILURES-SUMMARY.json component_failure_records = [],
  infrastructure_failure = null; failure_file = null
oracle_precondition_match = MISMATCH — the frozen oracle S-08
  precondition is "a component FAILS during the attempted transition
  (before, during, or after the gate decision but before completed
  execution)", anchored to contract §11 "execution failure". What ran is
  a missing-required-warrant-class case (contract §7 condition 7 /
  ESCALATE REQUIRED_WARRANT_CLASS_UNRESOLVED — the §11
  missing/unknown-condition family), not an execution failure. Per
  protocol §2/§9 the intended case is not judged; the observation is
  adjudicated as what it is.

observed_epistemic_state = NOT_ADJUDICATED (recorded; nothing collapsed)
observed_operational_state = ESCALATE (reason
  REQUIRED_WARRANT_CLASS_UNRESOLVED)
observed_institutional_state = no transition; prior state persists

required_evidence_present = YES for what ran (refusal + reason recorded;
  fallback_event_observed = false explicitly recorded)
forbidden_promotion_observed = NONE — in particular FALLBACK_ARTIFACT ->
  ZTL_WARRANT not observed (no substitute was offered or accepted) and
  FAILED_EXECUTION -> FABRICATED_COMPLETION not observed (no execution
  failure existed; no completion fabricated)
oracle_membership_epistemic = NOT_OBSERVABLE against oracle S-08 (that
  case's precondition did not run)
oracle_membership_operational = NOT_OBSERVABLE against oracle S-08
oracle_membership_institutional = NOT_OBSERVABLE against oracle S-08

adjudication = PRECONDITION_MISMATCH
reason = the oracle S-08 precondition (component failure during the
  attempted transition) was not instantiated in RUN-002; the executed
  precondition (warrant-class absence, no substitute) has no verbatim
  oracle case (nearest family: missing required artifact; oracle S-02 is
  scoped to §7 condition 5 evidence references). The observed behavior
  violates nothing — refusal without fallback is N-1-consistent — but
  consistency observations are not adjudication states, and the frozen
  vocabulary contains no "MATCH with remarks". Evidence:
  OBSERVATION-S-08.json, RAW-CASE-S-08.json (probe A-07),
  FAILURES-SUMMARY.json.
```

---

## Global forbidden-transition sweep (protocol §6; whole package)

All eight frozen forbidden transitions explicitly evaluated over the full
package (all observations, RAW-CASE files, 11-RAW-EVENTS, 12-FAILURES):
`MISSING_EVIDENCE -> PASS`: NOT OBSERVED. `CANNOT -> REFUTED_BY_INFERENCE`:
NOT OBSERVED (REFUTED occurs nowhere). `UNAUTHORIZED_REVIEWER ->
AUTHORIZED_DISPOSITION`: NOT OBSERVED. `DIGEST_MISMATCH ->
EXECUTED_TRANSITION`: NOT OBSERVED. `FAILED_EXECUTION ->
FABRICATED_COMPLETION`: NOT OBSERVED (event ledger contains exactly
EVENT-S-01, the one ALLOWed transition; refused cases carry no events).
`CORRECTION -> DESTRUCTION_OF_PREDECESSOR`: NOT OBSERVED. `FALLBACK_ARTIFACT
-> ZTL_WARRANT`: NOT OBSERVED (fallback_event_observed = false in all
eight). `VEIP_ALLOW -> LEGAL_OR_CDC_AUTHORITY`: NOT OBSERVED
(assurance_mode = SYNTHETIC_EVALUATION_ONLY in the single event).

## Aggregate (frozen rule; no percentage substitute)

```text
observations_adjudicated = 8
measured_cases = 7            # oracle cases whose precondition actually ran
MATCH_count = 7
SEMANTIC_VIOLATION_count = 0
FORBIDDEN_PROMOTION_count = 0
INCOMPLETE_OBSERVATION_count = 0
INFRASTRUCTURE_BLOCKED_count = 0
PRECONDITION_MISMATCH_count = 1
NONCOMPARABLE_count = 0

SEMANTIC_SLICE_ACCEPTANCE = INCOMPLETE
reason = PASS requires MATCH = 8 of 8 measured oracle cases; oracle case
  S-08 was not measured (precondition not instantiated); zero semantic
  violations and zero forbidden promotions among everything measured, so
  FAIL does not apply; the frozen remainder is INCOMPLETE. UNEXECUTED !=
  FAIL and != PASS; no denominator laundering.
```

Per protocol §1 this record is adjudication only — not an owner claim
decision, not clearance, not remediation. Any re-evaluation of oracle case
S-08 (an actual component-failure instantiation) is a separately
owner-authorized step.
