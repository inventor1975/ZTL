# CDC-EXEC-VERTICAL-SLICE-001 — SEMANTIC ACCEPTANCE ORACLE v0.1

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-10. Status at authoring: **frozen BEFORE any result-bearing
execution; no implementation code, test code, harness or runtime result was
inspected.**

Controlling inputs (byte-verified before authoring):

```
VEIP-CDC-SLICE-EVALUATION-CONTRACT-v0.1-OWNER-ATTESTED.md
  sha256 93fa0cf467aa93df67079b24066bf3aeb40c70df768621ec6b8f6a8ace90300e
CDC-EXEC-VERTICAL-SLICE-001-SEMANTIC-REVIEW-NOTES-v0.1.md  (N-1, N-2)
  sha256 ac8e8c2488c35966508e824b665f0730d471835d15af5422ed5964729a138b41
Frozen Protocol v0.1 @ 61a470b41eccf8e57633d0abee7bbc795329a411
  (file byte-verified sha256 98bbb05b…)
Frozen A–E @ 973f9eba2dfe410efdadad132ce2348d3875e302
```

Vocabulary note (dimensions are separate and never collapse):
**epistemic** = kernel/warrant states: atom statuses T/F/Z; claim
dispositions EARNED / ON CREDIT / OPEN / REFUTED; CANNOT (protocol
representability/authority-refusal class). **operational** = VEIP gate:
ALLOW / DENY / ESCALATE. **institutional** = TEST disposition states from
the closed set {ACCEPT_CANDIDATE, QUALIFY, DISMISS, REQUEST_EVIDENCE,
ESCALATE, DEFER} plus whether the state transition executed. Per N-2 these
are distinct state dimensions; per contract §7 ALLOW is deterministic-
structural only.

---

## S-01 — Valid bounded TEST disposition

```text
case_id = S-01
precondition = all 13 ALLOW conditions of contract §7 hold (correct
  mission; exact candidate/evidence/control digests; admitted control;
  required warrant artifact present; valid TEST reviewer scope; permitted
  disposition; correct prior state; no stale/superseded conflict)
epistemic_state_allowed = exactly the disposition recorded in the
  referenced warrant artifact (EARNED / ON CREDIT / OPEN / REFUTED as
  recorded), UNMODIFIED by the gate; the gate neither upgrades nor
  downgrades any epistemic state
operational_state_allowed = ALLOW (and only ALLOW; DENY/ESCALATE would
  contradict the precondition)
institutional_state_allowed = the requested disposition from the permitted
  set takes effect as a TEST state inside CDC-TEST-MISSION-001; the §6
  meanings control (ACCEPT_CANDIDATE = candidate use only, not official;
  QUALIFY per its existing meaning; etc.)
required_preserved_evidence = full §8 execution event (immutable after
  emission) binding all input/output digests, prior_state, new_state,
  declared actor/role/scope, assurance_mode = SYNTHETIC_EVALUATION_ONLY;
  full §9 Evidence Pack (authority/policy/action/decision/execution/
  provenance)
forbidden_promotion = ALLOW -> legal authority, CDC approval, official
  adoption, institutional validity outside the synthetic evaluation
  (contract §7 ALLOW meaning + §12 nonclaims); ACCEPT_CANDIDATE ->
  official finding; VEIP verifier PASS -> legitimacy / evidence
  sufficiency (§9); warrant -> institutional warrant (Protocol D1);
  evaluation -> issuance (D2)
pass_condition = transition executed exactly as proposed; §8 event emitted
  with all mandatory fields; epistemic state of the warrant carried
  through unchanged
fail_condition = any silent alteration of the warrant's recorded epistemic
  state; any missing mandatory §8 field; any representation of the TEST
  disposition as official or authorized beyond the slice
cannot_condition = none in this case (precondition excludes it); if any
  condition is in fact indeterminate the case is not S-01
```

**What ALLOW does NOT establish (explicit):** legal authorization, CDC
approval, official adoption, institutional validity outside
CDC-TEST-MISSION-001, evidence sufficiency, real-world reviewer identity or
competence, production readiness, or any §12 nonclaim item.

## S-02 — Missing required evidence

```text
case_id = S-02
precondition = one or more required evidence references absent or
  unresolvable at proposal time (contract §7 condition 5 not satisfiable)
epistemic_state_allowed = affected atoms = Z (unverified); the claim over
  them = OPEN or ON CREDIT as the kernel computes; REFUTED is allowed ONLY
  if independently forced by verified grounds — NEVER solely because
  evidence is missing (kernel: an argument from absence never yields a
  hereditary F; default deny is operational, not a refutation)
operational_state_allowed = { DENY (structural failure of an ALLOW
  condition), ESCALATE (where absence itself is indeterminate) } ; ALLOW
  is forbidden
institutional_state_allowed = { REQUEST_EVIDENCE (its §6 meaning:
  unresolved, no PASS promotion), DEFER, ESCALATE } ; no transition to any
  accepted/qualified state
required_preserved_evidence = the proposal record with its explicit
  missing-reference identification; reason_code naming the absent
  evidence; unresolved state itself preserved as a first-class record
forbidden_promotion = MISSING_EVIDENCE -> PASS (any form of silent
  promotion); MISSING_EVIDENCE -> substantive refutation; Z -> F by
  inference from absence
pass_condition = the absence is named, the state remains explicitly
  unresolved, and re-proposal after evidence arrival is possible
fail_condition = any PASS/ACCEPT path taken; any refutation recorded with
  absence as its only ground; the unresolved state silently dropped
cannot_condition = if it cannot be determined WHETHER the evidence is
  required -> ESCALATE / CANNOT (never ALLOW), per §11 and N-1 logic
```

**Dimensional separation confirmed:** REQUEST_EVIDENCE (institutional
disposition) ≠ Z (atom status) ≠ CANNOT (representability/authority
refusal) ≠ ESCALATE (gate outcome). Each lives on its own axis; the slice
must not translate one into another implicitly.

## S-03 — Unsupported admission

```text
case_id = S-03
precondition = candidate proposition/control lacks sufficient source/
  provenance/admission support (no admission_record_ref resolvable, or
  claimed T/F without admissible witness)
epistemic_state_allowed = truth-valued reasoning MAY NOT proceed on the
  unsupported content: the unsupported marking is not admissible as T or F;
  it may exist only as Z / explicit-unknown (Protocol R-02; contract §11
  "unsupported admission -> no truth-valued downstream reasoning"; this is
  the enforcement of the frozen Z-discipline whose absence was the §24.5
  Phase-A defect)
operational_state_allowed = { DENY (ALLOW condition 4 unsatisfied),
  ESCALATE } ; ALLOW is forbidden
institutional_state_allowed = { REQUEST_EVIDENCE, ESCALATE } ; no
  disposition that consumes the unsupported content as established
required_preserved_evidence = the rejected/unadmitted candidate preserved
  as a candidate (not destroyed, not promoted); the admission refusal
  recorded with its reason
forbidden_promotion = unsupported marking -> evaluated marking; provenance-
  less T/F -> any EARNED/REFUTED conclusion riding it; admission gap ->
  silently bypassed via a downstream disposition
pass_condition = the unsupported content is identifiable in the record as
  never having entered truth-valued evaluation
fail_condition = any warrant or disposition whose carriers include the
  unsupported content admitted as T/F
cannot_condition = if support status itself is indeterminate -> ESCALATE /
  CANNOT
```

## S-04 — Unauthorized TEST reviewer

```text
case_id = S-04
precondition = candidate, digests and warrant otherwise valid; reviewer
  authority_scope_ref does not equal the mission-scoped test-reviewer
  scope for the proposed transition
epistemic_state_allowed = UNCHANGED — the warrant's recorded epistemic
  state (whatever it is) is preserved exactly; authority failure carries
  zero epistemic information about the candidate's truth (D1: logical
  warrant and institutional authority are different objects)
operational_state_allowed = DENY (contract §7 DENY list: unauthorized
  reviewer scope; §11) ; ALLOW and ESCALATE are forbidden when the scope
  mismatch is determinate; ESCALATE only if the authority STATE itself is
  unresolved (that is a different precondition — see cannot_condition)
institutional_state_allowed = NO institutional-state transition; prior
  state persists byte-identically
required_preserved_evidence = §9 Evidence Pack decision record (DENY +
  reason code + evaluation time) with the declared reviewer identity/scope
  preserved; execution section records that NO transition executed
forbidden_promotion = UNAUTHORIZED_REVIEWER -> AUTHORIZED_DISPOSITION (in
  any packaging); scope mismatch -> epistemic downgrade of the candidate;
  DENY -> REFUTED
pass_condition = DENY recorded, prior state intact, warrant untouched,
  the attempt itself preserved as evidence
fail_condition = any state transition executed; any epistemic mutation;
  the attempt not recorded
cannot_condition = required authority state UNRESOLVED (not mismatched but
  unknown) -> ESCALATE per §7 (this is the neighboring case, not S-04
  proper)
```

## S-05 — Bound evidence mutation

```text
case_id = S-05
precondition = evidence bytes or digest changed after candidate binding
  (recomputation does not match the bound digest)
epistemic_state_allowed = the ORIGINAL candidate/warrant epistemic states
  remain exactly as recorded against the original bytes; the mutated bytes
  constitute a NEW unadmitted object with no inherited status (Protocol
  R-08 CLWR immutability; R-25 marking succession: no in-place mutation)
operational_state_allowed = DENY (integrity failure; §7 conditions 2/13,
  §11 "candidate/evidence mutation -> DENY / integrity failure")
institutional_state_allowed = NO transition; candidate ineligible on the
  mutated evidence; eligibility restorable only via the §10 correction/
  supersession path (new successor identity), never by re-binding in place
required_preserved_evidence = the original bound object byte-preserved and
  addressable; the mismatch observation itself recorded (both digests);
  nothing overwritten
forbidden_promotion = DIGEST_MISMATCH -> EXECUTED_TRANSITION; mutated
  object -> inheritor of the original's admission/warrant/status; original
  -> destroyed or replaced
pass_condition = mismatch detected before any transition; both objects
  (original intact, mutation observed) in the record
fail_condition = transition executed on mismatched digests; original
  object lost; mutation silently adopted
cannot_condition = if digest recomputation is itself impossible (artifact
  unreachable) -> that is missing evidence (S-02) or ESCALATE, not a
  mismatch verdict
```

## S-06 — Contradictory / CANNOT condition

```text
case_id = S-06
precondition = contradictory evidence requiring governed review, or a
  CANNOT condition (representability/authority refusal) arises in
  determining the transition
epistemic_state_allowed = CANNOT remains CANNOT (Protocol R-18: CANNOT
  never decays into pass or fail); contradiction is expressed only as the
  kernel can express it — as a REFUTED compound over verified grounds or
  as an admission-level conflict routed to governed review; a contradictory
  ground SET is not silently normalized into a marking (a marking is a
  function; conflicting sources are an admission problem, not a third
  truth value)
operational_state_allowed = ESCALATE (default per §7: "any CANNOT
  condition not explicitly mapped to DENY"); DENY permitted ONLY where the
  contract explicitly maps that condition to DENY, and then N-2 applies in
  full
institutional_state_allowed = { ESCALATE, DEFER, REQUEST_EVIDENCE } ; no
  accepting disposition
required_preserved_evidence = the CANNOT/conflict condition preserved
  verbatim in reason_code and the §8/§9 records; both conflicting sources
  preserved (Protocol R-19: adverse evidence preserved)
forbidden_promotion = CANNOT -> REFUTED_BY_INFERENCE; CANNOT -> DENY-
  as-refutation; conflict -> silent selection of one side; N-2 explicitly:
  operational DENY, if used, must NOT become epistemic REFUTED — the
  epistemic dimension stays CANNOT/unresolved in the record
pass_condition = both dimensions independently recorded: epistemic
  (CANNOT/conflict, preserved) and operational (ESCALATE, or mapped DENY
  with epistemic state intact in reason_code)
fail_condition = any record in which the operational refusal is stored AS
  the epistemic state; loss of either conflicting source
cannot_condition = this IS the cannot case; its required handling is the
  content above
```

## S-07 — Correction / supersession

```text
case_id = S-07
precondition = a previously TEST-dispositioned candidate (e.g.
  ACCEPTED_CANDIDATE or QUALIFIED synthetic state) is corrected
epistemic_state_allowed = predecessor's recorded epistemic states remain
  historical facts, unmodified (records are immutable; correction opens a
  successor context — the epoch discipline: knowledge chronology vs
  validity chronology stay distinct); successor states are computed fresh
  against the successor's own grounds
operational_state_allowed = the correction itself follows §10; a proposal
  against the STALE predecessor thereafter -> DENY (ALLOW condition 12)
institutional_state_allowed = successor gets new identity
  (new_ebawu_or_successor_id, new_candidate_digest) with supersedes /
  superseded_by links; affected generated statements become INELIGIBLE
  until regeneration or explicit human resolution (§10); predecessor state
  history intact
required_preserved_evidence = predecessor byte-preserved AND addressable;
  correction_event with reason and changed refs; the full supersession
  linkage in both directions
forbidden_promotion = CORRECTION -> DESTRUCTION_OF_PREDECESSOR (any
  in-place mutation, deletion, or de-addressing); successor -> automatic
  inheritance of predecessor's dispositions; affected outputs -> continued
  eligibility without regeneration/resolution
pass_condition = both objects addressable; linkage complete; ineligibility
  of affected outputs actually in force until resolution
fail_condition = predecessor bytes changed or unreachable; affected output
  still eligible with no regeneration and no recorded human resolution
cannot_condition = none specific; indeterminate correction scope ->
  ESCALATE
```

**Explicit:** production `RELIED_UPON` is NOT required for this slice
(contract §10: `RELIED_UPON = NOT_REQUIRED_FOR_SLICE`,
`PRODUCTION_RELIANCE_SEMANTICS = OUT_OF_SCOPE`); the oracle imposes no
reliance/currentness requirement beyond the contract.

## S-08 — Runtime/component failure

```text
case_id = S-08
precondition = a component fails during the attempted transition (before,
  during, or after the gate decision but before completed execution)
epistemic_state_allowed = all epistemic states exactly as they were at the
  last completed record; no state is synthesized, advanced, or lost by the
  failure
operational_state_allowed = the failure is recorded as a failure; no
  retroactive ALLOW/DENY is fabricated for steps that did not run
institutional_state_allowed = PRIOR institutional state preserved
  byte-identically; no partial transition persists as if complete
required_preserved_evidence = prior institutional state; all evidentiary
  artifacts bound before the failure; the failure observation itself as a
  preserved event (§11 "failure event preserved"); whatever partial
  records exist, preserved as partial — not completed
forbidden_promotion = FAILED_EXECUTION -> FABRICATED_COMPLETION; failure
  -> implicit fallback path (no alternate mechanism silently substitutes);
  failure -> loss of evidentiary state; failure -> reconstruction of
  authority by assumption
pass_condition = after the failure: prior state intact, evidence intact,
  failure observable in the record, and the system able to refuse — this
  is behavior CONSISTENT WITH the candidate invariant
  FAILURE-PRESERVING AVAILABILITY; it does NOT prove the invariant
  generally (single-instance evidence only)
fail_condition = any completed-looking state or event that execution did
  not actually produce; any evidence or prior state lost; any silent
  fallback
cannot_condition = if it cannot be determined whether execution completed
  -> the record must say exactly that (unresolved completion state), and
  no completion may be assumed
```

---

## Global forbidden transitions — each confirmed PROHIBITED

| Transition | Prohibited | Controlling anchor |
|---|---|---|
| `MISSING_EVIDENCE -> PASS` | YES | contract §6 (REQUEST_EVIDENCE -> unresolved, no PASS promotion), §11; kernel default-deny |
| `CANNOT -> REFUTED_BY_INFERENCE` | YES | Protocol R-18 (CANNOT never decays); N-2 |
| `UNAUTHORIZED_REVIEWER -> AUTHORIZED_DISPOSITION` | YES | contract §7 DENY list, §11; Protocol D2; frozen SEAM-2 |
| `DIGEST_MISMATCH -> EXECUTED_TRANSITION` | YES | contract §7 conditions 2/13, §11 |
| `FAILED_EXECUTION -> FABRICATED_COMPLETION` | YES | contract §11 (no fabricated completion) |
| `CORRECTION -> DESTRUCTION_OF_PREDECESSOR` | YES | contract §10; Protocol R-08/R-25 |
| `FALLBACK_ARTIFACT -> ZTL_WARRANT` | YES | N-1 (own artifact class; ZTL_warrant_digest never populated by fallback) |
| `VEIP_ALLOW -> LEGAL_OR_CDC_AUTHORITY` | YES | contract §7 ALLOW meaning, §9 (PASS ≠ legitimacy), §12 nonclaims |

---

## Freeze declaration

This oracle was authored entirely from the hash-verified controlling
inputs and the frozen semantic surfaces. No implementation file, test
file, harness, or runtime result was opened. After Codex/Claude results
are observed, this file receives NO edits; any later interpretation
becomes a separately versioned addendum
(`...-ORACLE-v0.1-ADDENDUM-nnn.md`). Where this oracle records an outcome
SET, any member of the set is acceptance-conformant; anything outside the
set is a semantic acceptance failure to be reported, not repaired.
