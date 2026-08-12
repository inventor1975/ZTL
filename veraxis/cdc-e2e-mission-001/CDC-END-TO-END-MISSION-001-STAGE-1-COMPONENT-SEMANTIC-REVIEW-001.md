# CDC-END-TO-END-MISSION-001 — STAGE-1 COMPONENT SEMANTIC REVIEW 001

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-12. Classification: **implementation-blind pre-execution
semantic review of controlling inputs. NOT an adjudication, NOT an
authorization to implement.**

Controlling point reviewed:

```
branch  cdc-e2e-mission-001-preexecution-records
commit  bab17cd4781c407c640946915f52a869bd00712f    verified
tree    8e0f952d55360ecbff23623d42bcfecf0644561e    verified
```

Implementation blindness held: artifacts were read out of the object
store by exact path (`git show`), never by materialising the tree. No
implementation source, no tests, no PR #23, no historical v0.4 result
object was opened. Reference-only outputs played no part in this review.

---

## 0. Byte verification

```
profile v0.2   03eb25effa77af830faafdb49db8318c2adcb20619c6f580a853255334a30a57  MATCH   9015 B  MATCH
owner addendum b8a2174ff2f8306782547423c067826df260ec8a7553c7512757706703573ea8  MATCH   3631 B  MATCH
package manifest 8aad5e78635b691fa2fad0336e07d9b0738b61db7b12ded2ed22149a258bdb77  MATCH
physical bytes  57452                                                             MATCH  (15 files)
```

Frozen governance recomputed from my own repository, not read from these
artifacts: oracle `72b554e6…` (11585 B), protocol `0e2a9f72…` (4661 B),
plan `229a0c15…` (11374 B) — all three unchanged, matching what the
addendum asserts.

**Package aggregate digest — NOT independently reproducible.**
`b62f3966…` could not be reproduced by any published rule, because no
derivation rule for it is published in the artifacts I am authorised to
read. Ten derivations were tried and are recorded so the gap is
actionable: sha256 of `SHA256SUMS`; sha256 over member digests
(hex-concat, byte-concat, `digest␠␠path` lines) in `members[]` order;
concatenated member contents in `members[]` order; concatenated contents
in sorted-path order with and without the manifest; `sha256sum` listing
with and without the manifest; reproducible `tar`; `SHA256SUMS` +
manifest concatenation.

What *was* verified instead, and is stronger per member:

```
members verified 14/14 on sha256 AND sha512 AND byte count   0 mismatches
SHA256SUMS       13 lines, 0 disagreements with the manifest
byte reconciliation  47762 (members) + 9690 (manifest) = 57452 = declared
```

So the package content is fully verified member-by-member; only the
single aggregate number is unreproducible. This is the same class of gap
recorded as A-OBS-2 in review 001 (`01c3066a…`) and it has now recurred:
**publish the package-digest derivation rule, or stop asserting a package
digest.** An integrity number nobody outside can recompute is provenance
theatre, not provenance — it is the one figure in this package that
currently rests on trust.

---

## 1. Admission boundary — CONFORMANT

The boundary is drawn correctly and in three independent places:

- profile `claim_ceiling.relationship_to_admitted_meaning`: separately
  governed Stage-1 evaluation profile, does not retroactively become
  admitted OIC meaning, is not written into any admitted control; the
  `is_not` list explicitly excludes Moroccan law, CDC policy, legal
  interpretation, production OIC semantics, ZTL kernel semantics and
  admitted meaning;
- package manifest: `stage_1_component_profile_is_admitted_oic_meaning:
  false`, `component_evaluation_semantics_written_into_admitted_control:
  false`, `admitted_control_bytes_changed_vs_v0_4: false`,
  `admission_record_bytes_changed_vs_v0_4: false`,
  `control_identity_changed: false`;
- owner addendum: `component_profile_is_admitted_oic_meaning: false`.

The admitted control keeps its own identity and bytes; the synthetic
evaluation semantics sit beside it and are bound by digest
(`stage_1_component_profile_sha256`) with
`profile_change_after_authorization: INVALIDATES_CLEARANCE` and
verification from exact bytes required before Stage 1. That is the right
shape: the profile is *referenced* by the admitted layer, never *merged
into* it.

**Residue at this boundary — see §6.** Each admitted control carries
`on_unknown: "ESCALATE"`, and the component profile neither consumes that
field nor declines it.

## 2. Absence / conflict conservation — CONFORMANT

The ordered evaluator is correct, and the ordering is what makes it
correct:

```
1  any required fact absent      → UNRESOLVED  MISSING_REQUIRED_EVIDENCE
2  any required fact conflicting → UNRESOLVED  CONFLICTING_REQUIRED_EVIDENCE
3  all required facts true       → SATISFIED   ALL_REQUIRED_CONDITIONS_SATISFIED
4  otherwise                     → BREACH      REQUIRED_CONDITION_NOT_SATISFIED
```

Because absence and conflict are tested *before* rule 4, the catch-all
`otherwise` is reachable only when every required fact is present,
unconflicted, and at least one is false. An absent fact therefore cannot
reach BREACH by falling through, which is the exact failure this
requirement exists to prevent. Reinforced explicitly:
`absence_is_not_false: true`,
`conflict_is_not_resolved_by_precedence_or_recency: true`,
`unknown_may_become_breach: false`, `unknown_may_become_satisfied:
false`, `no_other_decision_route_exists: true`.

The representation choice is honest and is the reason this holds
mechanically: absence is the empty list, conflict is a list with more
than one distinct value, values are JSON booleans, and *no string
pseudo-values are used*. There is no `"UNKNOWN"` string that could be
compared, sorted or coerced into a truth value — absence has no
representation that could accidentally behave like `false`. This is the
frozen Z-discipline expressed in data rather than in prose, and it is the
strongest part of the profile.

Recorded observation (non-blocking): `observation_value_domain` is
`[true, false]`, but behaviour on an out-of-domain observation value is
unspecified. The successor implementation must refuse or record it, never
coerce it — a non-boolean silently read as falsy would reintroduce
exactly the promotion rules 1–2 forbid.

## 3. Warrant boundary — CONFORMANT

`FALLBACK_WARRANT ≠ ZTL_WARRANT` is enforced by construction, not by
convention:

```
permitted_warrant_class   [FALLBACK_WARRANT]        (closed, single member)
ZTL_WARRANT               PROHIBITED
establishes_logical_warrant  false
fixed_field_values        warrant_class = FALLBACK_WARRANT
                          logical_warrant_status = NOT_ESTABLISHED
                          ztl_kernel_invoked = false
                          fallback_basis = DETERMINISTIC_EVALUATION_RECORD
required_limitations      [NO_ZTL_DERIVATION]
```

Three properties make this stricter than a naming rule. The values are
*fixed*, so no code path can compute them into something else. There is
no `ztl_warrant_digest` field in `required_fields` at all — the field an
evaluation result could be written into does not exist, which is stronger
than requiring it be null. And the prohibition lifts only on a separately
governed owner-designated kernel adapter, so "we already invoke ZTL"
cannot arrive by drift. `semantics` states the ceiling plainly: the
fallback artifact is provenance around an evaluation and does not
establish a logical warrant.

`unresolved_evaluation_handling: preserve UNRESOLVED verbatim; promotion
to SATISFIED or BREACH is prohibited` closes the remaining leak — the
warrant builder cannot launder an unresolved evaluation on the way out.

A deterministic evaluation cannot, under this profile, be mistaken for a
ZTL warrant. This matches frozen M06 and the N-1 reading verbatim.

## 4. Pre-result input integrity — CONFORMANT

No hidden semantic promotion, no result leakage, no representation choice
that predetermines Stage 1 beyond frozen determinism.

Measured, not read off the declarations: I extracted every admitted
observation from `02-POPULATION/P001–P003.json` and compared it against
the profile's `preregistered_population_assignments`, per member, per
control, per required fact — **18 of 18 identical, 0 divergences**,
including the two representations that matter (`[]` for absence,
`[true,false]` for conflict). The profile therefore *restates* the
package evidence; it does not override it and is not a second, richer
source of truth.

Declarations that hold up: `precomputed_candidate_objects_present`,
`precomputed_evaluation_objects_present`,
`precomputed_verdict_objects_present`,
`precomputed_warrant_objects_present` all false; `candidate_count: 0`;
`stage_1_input_state: PRE_CANDIDATE`;
`derived_results_supplied_as_runtime_inputs: false`;
`reference_only_results_used_as_computational_input: false`. Design
metadata was removed from the controlling runtime projection
(`mission_population[*].shape`) with the reason stated correctly — it
must not be inspected by the evaluator — and retained addressably in the
immutable v0.4, so removal is not destruction.

The profile's own `result_language` note is right and worth endorsing:
that the answers follow from the frozen rules and the frozen inputs is a
property of determinism, not an encoded expectation; the prohibited thing
is a derived result handed back to the computation that is supposed to
produce it, and no such object is present.

Recorded observation (non-blocking): the evidence values now exist in two
places — the package payload and the profile's preregistered assignments
— and no artifact publishes a precedence rule between them. Today they
agree exactly, so nothing is wrong. But the v0.1 clarification *did*
publish such a rule for manifest-vs-`binding.json`, and the same
discipline should apply here before any correction touches one copy
without the other. One sentence in a successor artifact settles it.

## 5. Compatibility with frozen mission governance — CONFORMANT

Oracle `72b554e6…`, protocol `0e2a9f72…` and plan `229a0c15…` are
unchanged, confirmed by my own recomputation. The addendum asserts
`m09_interpretation_modified: false`,
`m12_no_rerun_interpretation_modified: false`, and keeps the v0.1
interpretation controlling for the M09 crosswalk, M12 conditional
observability and the no-rerun rule.

**My own open item from review 001 is now closed by measurement.**
B-OBS-1 flagged that the plan writes `ACCEPT_CANDIDATE` where the
oracle's M09 prose names `ACCEPT`, and I recorded that I could not settle
it without inspecting the frozen vocabulary. `01-MISSION-MANIFEST.json`
in this package carries `permitted_disposition_vocabulary` =
`[ACCEPT_CANDIDATE, DEFER, DISMISS, ESCALATE, QUALIFY, REQUEST_EVIDENCE]`
— identical to the human action plan's set. So the mission's frozen
closed set contains `ACCEPT_CANDIDATE` verbatim, the oracle's prose was
shorthand, and **M09's "no new disposition vocabulary" is satisfied**.
This required no instrument change, which is the correct outcome: the
freeze holds.

Human actions remain stimuli, not predictions: the plan is unchanged, the
profile encodes no expected disposition, `expected_results_encoded:
false` in both package manifest and mission manifest, and nothing in
these artifacts binds a chain to a machine outcome.

M12 conditional observability and the no-rerun rule are untouched. The
consequence I recorded before still stands and still needs to be known in
advance: if no eligible completed transition occurs, M12 yields no
observation and the aggregate is INCOMPLETE, not FAIL.

`semantic_oracle_change_required = FALSE`
`human_action_plan_change_required = FALSE`

## 6. The one thing to settle before the evaluator is written

**`on_unknown: "ESCALATE"` is present on all nine admitted controls, and
nothing says who consumes it.**

Measured: every chain (P001/P002/P003 × C-TENDER-01/C-EVAL-01/C-AWARD-01)
carries `admitted_control.on_unknown = "ESCALATE"` with
`decision_mode = "DETERMINISTIC"`. The component profile's decision
procedure never mentions the field and declares
`no_other_decision_route_exists: true`; its verdict vocabulary is
`SATISFIED / BREACH / UNRESOLVED`. So the field sits inside admitted
meaning, unaddressed by the semantics that will be implemented against
it.

`ESCALATE` is not a neutral token. It is a member of the mission's
`permitted_disposition_vocabulary`. Two branches follow, and the choice
between them is currently an implementation decision — which is exactly
what this review exists to prevent:

- **If the evaluator or warrant builder acts on it**, a machine emits a
  disposition-vocabulary value on an unresolved chain. That collides with
  frozen M09 (*no machine output IS a disposition*; machine candidate
  auto-dispositioned is forbidden) and with the human action plan, whose
  P003 chains — the three that evaluate UNRESOLVED — are preregistered
  `REQUEST_EVIDENCE` stimuli. Two disposition-shaped values would then
  exist on the same chain, one of them machine-made.
- **If nothing consumes it**, a field of the admitted control is silently
  dropped. Not automatically a violation, but silence is the wrong form:
  non-consumption of admitted meaning must be recorded explicitly, or the
  admission boundary is being honoured in one direction only.

The frozen instruments already forbid the bad branch — no oracle change
is required. What is missing is a settled, published reading. One
sentence from the owner does it, and it should exist before the evaluator
and warrant builder are written, not be discovered in a result.

Suggested shape, offered as a **proposed interpretation, not a finding**:
`on_unknown` is institutional routing guidance addressed to the human
disposition layer, is not consumed by the deterministic evaluator, and
its non-consumption at Stage 1 is recorded explicitly in the evaluation
record.

---

## Return

```
CDC_E2E_MISSION_001_STAGE_1_COMPONENT_SEMANTIC_REVIEW = CONFORMANT

profile_sha256_verified        = YES  (03eb25ef…, 9015 B)
input_package_sha256_verified  = NOT_REPRODUCIBLE — derivation rule unpublished;
                                 14/14 members verified on sha256+sha512+bytes,
                                 SHA256SUMS consistent, 57452 B reconciles
manifest_sha256_verified       = YES  (8aad5e78…)
owner_addendum_sha256_verified = YES  (b8a2174f…, 3631 B)

admission_boundary            = CONFORMANT
absence_conflict_conservation = CONFORMANT
fallback_vs_ztl_boundary      = CONFORMANT
pre_result_input_integrity    = CONFORMANT
frozen_governance_compatibility = CONFORMANT

semantic_oracle_change_required   = FALSE
human_action_plan_change_required = FALSE

implementation_seen  = FALSE
machine_results_seen = FALSE

blocking_issue = admitted_control.on_unknown = "ESCALATE" on all nine chains is
  unaddressed by the Stage-1 component profile, and ESCALATE is a member of the
  frozen permitted_disposition_vocabulary. Blocking for AUTHORIZATION OF THE
  EVALUATOR / WARRANT BUILDER, not for the reviewed artifacts, which are
  conformant as frozen. Settle by owner statement whether on_unknown is consumed
  at Stage 1 (M09 risk) or explicitly not consumed and recorded as such.
  Secondary, non-blocking: publish the package-digest derivation rule.
```

Scope ceiling: this review establishes semantic admissibility of the
named inputs only. It establishes nothing about production conformance,
CDC acceptance, legal validity, institutional authority, or readiness;
`assurance_mode = SYNTHETIC_EVALUATION_ONLY` is carried forward. The
frozen separation holds — OBSERVATION ≠ ORACLE ≠ ADJUDICATION ≠ OWNER
CLAIM DECISION — and this artifact is none of the last three.
