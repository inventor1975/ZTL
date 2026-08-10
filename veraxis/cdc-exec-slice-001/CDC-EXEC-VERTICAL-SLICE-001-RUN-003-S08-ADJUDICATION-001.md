# CDC-EXEC-VERTICAL-SLICE-001 — RUN-003 S-08 ADJUDICATION 001

Adjudicator: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-11. Successor measurement to RUN-002; RUN-002 history
untouched (S-08 RUN-002 = PRECONDITION_MISMATCH; RUN-002 aggregate =
INCOMPLETE — both remain as issued). Instruments: frozen Oracle v0.1
(`392f2981…`) and Result Adjudication Protocol v0.1 (`5884c984…`),
unchanged. No cross-run aggregate is created here.

Evidence integrity (verified before reading any outcome): raw package
51200 B, sha256 `911019ee0abc38391800b5ad16e243264435d8e3c6581c4ff8741c93ea5d6557`
(byte-exact; browser-duplicate filename "(1)" — bytes canonical);
`08-SHA256SUMS/SHA256SUMS` ALL OK; `04-OBSERVATION-S-08/RECORD.sha256` OK;
authorization `f91e520b…` EXACT; pre-run manifest `5fe93428…` EXACT;
stimulus `70fd6f8f…` EXACT (precondition review: commit `ae197b7…`,
instantiated=YES, window=POST_GATE_PRE_COMMIT); `OBSERVATION-S-08.json`
file sha256 `5ff83cbe…` EXACT; `RAW-S08.json` file sha256 `1ff1f3a7…`
EXACT. The internal content-level `observation_digest = sha256:889e8b8e…`
noted and not confused with the file identity.

---

## Fixture-metadata discrepancy (mandatory review) — disposition A

`RAW-S08.json` fixture metadata carries a stale label
(`precondition_condition = WARRANT_CLASS_ABSENT`, "warrant class absent;
no substitute artifact offered"). **Disposition: A — the stale label is
non-operative metadata; the actual observed precondition is the bound-
component failure.** Basis, strictly under the frozen observation-
precedence rule (adjudication consumes only the immutable record; nothing
is resolved by intention or expected outcome) — the label is falsified by
four independent recorded execution facts:

1. `proposal_as_executed` carries `ZTL_warrant_ref = ZTL-P-001-C-TENDER-01`
   — the warrant class was present in the executed proposal;
2. the fixture object itself carries `warrant_ref = ZTL-P-001-C-TENDER-01`
   — the stale label contradicts its own enclosing object;
3. `gate_decision_if_reached = ALLOW` — under the frozen contract §7 an
   absent warrant class cannot reach ALLOW (condition 7 would ESCALATE);
4. component invocation (count 1, with event metadata) and the injected
   failure (`InjectedBoundComponentError … at POST_GATE_PRE_COMMIT`) are
   independently evidenced in 05-/06-.

Option B would require the label to have been operative or the executed
state ambiguous; the record shows neither. The discrepancy is **recorded,
not normalized**: the label remains in the frozen raw bytes and is named
here as stale metadata carried from the RUN-002-era fixture description.

## Adjudication against the unchanged oracle S-08

```text
case_id = S-08 (RUN-003)
observation_record_id = OBSERVATION-S-08 (RUN-003)
observation_digest = 5ff83cbe60fd71efc53b6df8b99e0c09db40615644d286d654f255b9416f6512
  (file identity; internal content digest sha256:889e8b8e…)
observed_precondition = fully conforming proposal and registry; gate
  reached ALLOW; bound emit_transition_event component invoked once
  (invocation evidence with event metadata — execution had begun);
  injected bound-component failure raised in the POST_GATE_PRE_COMMIT
  window; completed execution not reached
oracle_precondition_match = EXACT (a component fails during the attempted
  transition, after the gate decision and before completed execution)

observed_epistemic_state = NOT_ADJUDICATED — all epistemic states exactly
  as at the last completed record; nothing synthesized, advanced or lost
observed_operational_state = COMPONENT_FAILURE — the failure recorded AS
  a failure (06-FAILURE-EVIDENCE); the reached step (gate ALLOW) is a
  genuinely executed, recorded step, not a retroactive fabrication
observed_institutional_state = CANDIDATE_FORMED — prior state preserved;
  no transition (07-RAW-EVENTS: event_emitted = false,
  institutional_transition_observed = false,
  unexpected_additional_events = []); a gate ALLOW is not itself an
  institutional transition (contract §7 ALLOW meaning)

required_evidence_present = YES — prior institutional state intact;
  evidentiary artifacts intact (preserved_artifact_refs: candidate,
  control, admission, evidence bundle, warrant); the failure observation
  itself preserved as an event (06-); partial records preserved as
  partial (invocation evidence retained; no completed-looking event)
forbidden_promotion_observed = FALSE — explicitly: FAILED_EXECUTION ->
  FABRICATED_COMPLETION not observed (event_emitted = false,
  completed_execution_reached = false); FALLBACK_ARTIFACT -> ZTL_WARRANT
  not observed (fallback_attempted = false, fallback_observed = false);
  no institutional transition, no authority representation

oracle_membership_epistemic = IN_SET
oracle_membership_operational = IN_SET
oracle_membership_institutional = IN_SET

adjudication = MATCH
reason = all six MATCH conditions of protocol §4 hold on the RUN-003
  observation against the unchanged oracle S-08: exact precondition;
  three axes independently represented and in-set; all preservation
  obligations observed; no forbidden promotion; no required state
  silently absent. Per the oracle's own boundary: this is behavior
  CONSISTENT WITH the candidate invariant FAILURE-PRESERVING
  AVAILABILITY on a single instance; it does not prove the invariant
  generally.
```

## Scope ceiling — preserved

`CLAIMED_FAILURE_CLASS = BOUND_COMPONENT_FAILURE_AT_EXISTING_HARNESS_SEAM`
(the failure evidence itself names an injected bound-component error).
`INTERNAL_FAILURE_OF_PRODUCTION_emit_transition_event` is NOT established
and not claimed. No widening.

## Non-effects

This record does not modify the RUN-002 adjudication, does not create a
cross-run aggregate, does not authorize any merge, execution, production
or official use, and encodes no claim beyond the adjudication itself.
