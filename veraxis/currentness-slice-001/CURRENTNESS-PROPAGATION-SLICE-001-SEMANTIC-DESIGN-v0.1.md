# CURRENTNESS PROPAGATION VERTICAL SLICE 001 — SEMANTIC DESIGN v0.1

```
author            Vitaliy Reznik — architecture / semantics only
assurance_class   INTERNAL_TECHNICAL_DEMONSTRATION
status            READY_FOR_OWNER_REVIEW
result_bearing    false
authorizes        nothing
```

Scope of this document: the semantic layer — state lattice, schema, resolver
semantics, gate semantics, closed reason-code set, test universe, adversarial
cases, evidence obligations, claim ceiling. **It deliberately contains no source
changes and no source commit/tree**: implementation is the implementer's lane
and I do not write in that repository.

**Role disclosure, stated at full strength.** In Mission-001 I authored the
oracle and protocol and later adjudicated against them, which is why that
adjudication carries `independent_review_claim = FALSE`. In this slice the
collapse is one step deeper: I am proposing the *mechanism's semantics* and the
*acceptance criteria* and will later adjudicate the result. Any adjudication I
produce here is therefore a self-check of my own design, not merely of my own
criteria. That must appear verbatim in the slice's claim ceiling, not only as a
disclaimer in a covering note.

---

## 1. The one architectural commitment everything else follows from

**Currentness is not a property of an artifact. It is a relation over
(artifact identity, institutional state, evaluation time).**

Three consequences, and they are not negotiable if the slice is to mean
anything:

1. Currentness is never stored *in* the historical artifact. The artifact's
   bytes are the record of what was true when it was made; they cannot carry
   what is true now.
2. Currentness is always **recomputed**, never read. A stored
   `CurrentnessResolution` is not a fact — it is a *claim with an expiry*, and
   it must carry the evaluation time and the basis it was computed from.
3. `HISTORICALLY_VALID` and `CURRENTLY_ELIGIBLE` live on different axes and must
   never be stored in each other's fields. The M11 defect in Mission-001 was
   exactly an axis substitution; this design must not repeat it one layer up.

## 2. State lattice

Currentness axis, closed set:

```
CURRENT · SUPERSEDED · INELIGIBLE · UNKNOWN
```

**Integrity is not a currentness state.** An artifact whose observed bytes do
not match its recorded digest yields `ARTIFACT_INTEGRITY_MISMATCH`, which is an
*integrity* outcome, not a currentness one. Collapsing it into `UNKNOWN` would
be the same axis error this slice exists to prevent.

**The asymmetry rule — the heart of the design.**

> `CURRENT` is the only state that requires positive evidence of **complete**
> basis coverage. Every other state is reachable on partial evidence.

Absence of a supersession record is not evidence of currentness. The resolver
must distinguish *"consulted an attested-complete basis set and found no
controlling record"* from *"found no controlling record"*. Only the first may
yield `CURRENT`; the second yields `UNKNOWN`. This single rule answers
adversarial case G by construction and is the executable form of the discipline
this whole programme runs on: truth is never inferred from absence.

Precedence when several conditions hold, applied in order:

```
1  ARTIFACT_INTEGRITY_MISMATCH      (integrity axis — evaluated first, terminal)
2  RESOLUTION_BINDING_MISMATCH      (the resolution does not bind this output)
3  RESOLUTION_STALE                 (expired, or superseded by newer basis)
4  UNKNOWN                          (basis incomplete, ambiguous, or unresolvable)
5  SUPERSEDED                       (controlling successor effective at evaluated_at)
6  INELIGIBLE                       (no successor, but a controlling ineligibility record)
7  CURRENT                          (only if 1–6 all fail AND coverage = COMPLETE)
```

`UNKNOWN` sits **above** `SUPERSEDED` and `INELIGIBLE` deliberately: if we do not
know whether the basis was complete, we must not assert *which* denial applies —
we assert only that we cannot certify currency.

## 3. Schema — `CurrentnessResolution`

Separately addressable. It must not overload the historical deliverable schema,
and no field of it may ever be written into a deliverable.

```
record_class                        "CURRENTNESS_RESOLUTION"
resolution_id                       stable id for this evaluation
output_ref                          literal identifier, unrenamed
requested_use                       echoed from the request, or null for advisory evaluation

artifact_identity {
  expected_digest                   from the frozen historical record
  observed_digest                   recomputed from bytes at evaluation time
  integrity                         MATCH | MISMATCH
  historical_state                  what the artifact recorded when frozen
}

currentness_state                   CURRENT | SUPERSEDED | INELIGIBLE | UNKNOWN
eligibility                         ELIGIBLE
                                    | INELIGIBLE_PENDING_REGENERATION_OR_EXPLICIT_HUMAN_RESOLUTION
                                    | NOT_DETERMINED
controlling_successor_ref           null iff currentness_state = CURRENT
superseding_event_ref               null iff no controlling successor
controlling_records []              every record that forced the outcome

basis {
  index_ref                         the governed currentness index consulted
  index_digest                      exact digest of that index
  records []                        {ref, digest, class} for every record consulted
  basis_digest                      digest over the ordered basis set
  coverage                          COMPLETE | INCOMPLETE
  coverage_attestation_source       how completeness was established
}

times {
  effective_at                      when the institutional change takes effect
  observed_at                       RUNTIME_OBSERVED_UTC
  admitted_at                       when the controlling record entered institutional state
  evaluated_at                      when this resolution was computed
  expires_at                        evaluated_at + ttl; a resolution is a claim, not a fact
}

reason_code                         from the closed set in §5
resolver_version                    exact
claim_ceiling                       "INTERNAL_TECHNICAL_DEMONSTRATION"
resolution_digest                   sha256(canonical(record minus this field))
```

Canonical form, matching the rule already published for this programme: UTF-8,
keys sorted lexicographically, `ensure_ascii=false`, separators `,` and `:`, no
indentation, no trailing newline, self-digest excluded.

**Time semantics, pinned rather than left to the implementation:**

- A controlling record participates only if `effective_at ≤ evaluated_at`. A
  future-dated supersession does **not** yet supersede.
- A resolution is usable only for `evaluated_at ≥ admitted_at` of every record it
  relied on.
- Backdating prohibited; `effective_at` comes from owner-issued prospective time,
  never from a local clock reading chosen after the fact.
- `observed_at` and `effective_at` may not be substituted for one another — a
  fourth axis-substitution guard.

## 4. Use gate

One bounded gate, evaluated **before** a historical output may participate in a
new consequential operation.

```
in    output_ref, currentness_resolution (or its digest), requested_use, run_metadata
out   UseGateDecision { decision, reason_code, controlling_successor_ref,
                        resolution_digest, artifact_observed_digest,
                        consequential_gate_reached: false, evaluated_at, run/trace ids }
```

Behaviour, in precedence order:

```
integrity MISMATCH        → DENY  ARTIFACT_INTEGRITY_MISMATCH
binding mismatch          → DENY  RESOLUTION_BINDING_MISMATCH
resolution expired/stale  → DENY  RESOLUTION_STALE_REEVALUATION_REQUIRED
caller-supplied state     → DENY  CALLER_SUPPLIED_CURRENTNESS_REJECTED
UNKNOWN                   → DENY  CURRENTNESS_UNKNOWN_FAIL_CLOSED
SUPERSEDED                → DENY  OUTPUT_SUPERSEDED            + successor pointer
INELIGIBLE                → DENY  OUTPUT_INELIGIBLE…           + controlling record pointer
CURRENT                   → PROCEED_TO_NEXT_GATE
```

Three properties that must hold and must be observable:

- **`PROCEED_TO_NEXT_GATE` is not an authorization.** The output is `PROCEED`,
  never `ALLOWED`. Mission-001 earned the distinction between a gate decision and
  an institutional transition; this gate sits one layer earlier and must not
  quietly reintroduce the collapse.
- **The gate emits no institutional event and performs no transition.**
- **Currentness is never accepted from the caller.** The gate either derives the
  resolution from governed state itself, or verifies a supplied resolution
  against governed state by digest. A caller-asserted `CURRENT` is refused as
  such — not ignored, refused, with its own reason code, so the attempt is
  visible in evidence.

For this slice the `UNKNOWN` profile is fixed to `DENY` for any consequential
requested use. `ESCALATE` is permitted only for explicitly non-consequential
use, and if used must be recorded as `ESCALATE`, never as `PROCEED`.

## 5. Closed reason-code set

```
CURRENTNESS_RESOLVED_CURRENT
OUTPUT_SUPERSEDED
OUTPUT_INELIGIBLE_PENDING_REGENERATION_OR_EXPLICIT_HUMAN_RESOLUTION
CURRENTNESS_UNKNOWN_FAIL_CLOSED
BASIS_COVERAGE_INCOMPLETE
BASIS_AMBIGUOUS_COMPETING_SUCCESSORS
ARTIFACT_INTEGRITY_MISMATCH
RESOLUTION_BINDING_MISMATCH
RESOLUTION_STALE_REEVALUATION_REQUIRED
CALLER_SUPPLIED_CURRENTNESS_REJECTED
SUCCESSOR_BINDING_MISMATCH
SUCCESSOR_FOR_DIFFERENT_OUTPUT
EFFECTIVE_TIME_NOT_YET_REACHED
```

No code outside this set may appear. Adding one after execution is a criteria
modification and is prohibited.

## 6. Test universe

Stale population — the five literal identifiers from the frozen RUN-002
evidence, unrenamed and unaliased:

```
CDC-TEST-MISSION-001/CDC-E2E-OUTPUT-01
CDC-TEST-MISSION-001/CDC-E2E-OUTPUT-02
CDC-TEST-MISSION-001/CDC-E2E-OUTPUT-03
CDC-TEST-MISSION-001/CDC-E2E-OUTPUT-04
CDC-TEST-MISSION-001/CDC-E2E-OUTPUT-05
```

Controlling successor for all five: `EBAWU-P-001-C-TENDER-01-CORR-002`,
correction event `CDC-E2E-M12-CORRECTION-EVT-002`, sourced read-only from the
frozen RUN-002 result `8b81e62a…` at evidence commit `806490b6…`. RUN-002 is
consumed as an input fixture and is neither modified nor re-executed.

**A gap in the frozen population that must be declared, not papered over.** All
five outputs are affected by CORR-002, so the population contains **no unaffected
output**, and the §8 positive test has no natural subject. The honest resolution
is an explicitly synthetic control output, labelled as synthetic in its
identifier and in every evidence record, existing only to exercise the `CURRENT`
path. It must never be presented as a historical CDC output, and the slice must
not claim a `CURRENT` result on real mission data — because there is none to
have.

## 7. Adversarial cases

Their eight, each with the required outcome:

```
A  currentness record removed              → UNKNOWN, DENY  CURRENTNESS_UNKNOWN_FAIL_CLOSED
B  pointer to wrong successor              → DENY  SUCCESSOR_BINDING_MISMATCH
C  output_ref / artifact digest mismatch   → DENY  ARTIFACT_INTEGRITY_MISMATCH or
                                                   RESOLUTION_BINDING_MISMATCH per §2 precedence
D  expired / stale resolution supplied     → DENY  RESOLUTION_STALE_REEVALUATION_REQUIRED
E  caller injects CURRENT                  → DENY  CALLER_SUPPLIED_CURRENTNESS_REJECTED
F  historical bytes modified               → DENY  ARTIFACT_INTEGRITY_MISMATCH
G  predecessor-only evidence, successor hidden → UNKNOWN (never CURRENT) via coverage=INCOMPLETE,
                                                 BASIS_COVERAGE_INCOMPLETE
H  valid successor for a different output  → DENY  SUCCESSOR_FOR_DIFFERENT_OUTPUT
```

Two more I propose adding, because each is a way the resolver can fabricate a
verdict quietly and neither is covered above:

```
I  successor exists but effective_at is in the future
   → must NOT return SUPERSEDED; returns CURRENT only if coverage COMPLETE,
     otherwise UNKNOWN;  EFFECTIVE_TIME_NOT_YET_REACHED recorded
     (tests time-awareness rather than mere record presence)

J  two competing successors for one predecessor
   → must NOT silently choose;  UNKNOWN,  BASIS_AMBIGUOUS_COMPETING_SUCCESSORS
     (a resolver that picks one is inventing authority)
```

Case G is the load-bearing one. If the resolver returns `CURRENT` when a
successor was merely withheld, the whole slice is worthless regardless of how the
other seven behave.

## 8. Evidence obligations

Immutable, hash-addressable, and none of it dependent on console text:

- the governed currentness index, with its digest;
- one `CurrentnessResolution` per (output × evaluation), self-digested;
- one `UseGateDecision` per gate attempt, binding the resolution digest and the
  observed artifact digest;
- an adversarial ledger: case id, exact mutation applied, expected reason code,
  observed reason code, pass/fail per case;
- a **byte-identity table** for all five historical outputs, digests before and
  after the entire slice — this is the artifact that carries the headline claim;
- run metadata, authority and attempt records in the pattern already used;
- the published derivation rule for every digest class introduced, frozen
  **before** execution. This programme has three times had to reconstruct an
  unpublished digest rule; do not make it four.

## 9. Claim ceiling

May be established, if measured:

```
EXECUTABLE_CURRENTNESS_RESOLUTION                              MEASURED
STALE_OUTPUT_PRESENT_USE_REFUSAL                               MEASURED
HISTORICAL_ARTIFACT_PRESERVATION_DURING_CURRENTNESS_CHANGE     MEASURED
```

May **not** be established: institutional reliance, official CDC issuance,
external consumer propagation, legal effect, production conformance, CDC
acceptance, general rollback resistance, distributed consistency across
institutions.

Two further ceilings that follow from this design and belong in the frozen list:

- **The gate protects only paths that call it.** A consumer that reads the
  historical bytes directly is entirely unaffected. What can be measured is
  *refusal at the gate*, not *propagation to consumers*. This is the same shape
  as the boundary recorded in the RUN-002 adjudication — recorded ≠ propagated —
  moved one layer outward, and it must not be reported as having been closed.
- **Self-check disclosure.** Any adjudication I produce for this slice checks a
  mechanism whose semantics I proposed. `independent_review_claim = FALSE` is
  necessary but not sufficient wording; the ceiling should say
  `self_designed_and_self_adjudicated = TRUE`.

## 10. Success condition, restated in the form I will adjudicate against

Not: *the five outputs were marked stale.*

But: **the five historical outputs remained byte-identical across the entire
slice, while an independently maintained currentness layer refused their present
use and named the controlling successor evidence — and refused equally in every
adversarial case where the basis for asserting currency was absent, ambiguous,
mis-bound, expired or caller-supplied.**

The second clause is what separates a working currentness layer from a lookup
table that happens to say the right thing five times.

## 11. Return

```
CURRENTNESS_SLICE_DESIGN = READY_FOR_OWNER_REVIEW

exact_schema              §3
exact_resolver_semantics  §2 + §3 time rules
exact_use_gate_semantics  §4
exact_reason_codes        §5 (closed, 13 codes)
exact_test_universe       §6 (5 literal + 1 declared-synthetic control)
exact_adversarial_cases   §7 (A–H as given, plus proposed I and J)
exact_evidence_artifacts  §8
claim_ceiling             §9

exact_source_changes      NOT SUPPLIED — implementer's lane; this author does not
                          write in the implementation repository
source_commit_tree        NOT APPLICABLE to this document

result_bearing_execution  NONE PERFORMED
prior_history_modified    FALSE  (RUN-001, RUN-002, and all prior adjudications untouched)
```

Frozen before any result-bearing execution of this slice, so that it can serve as
the pre-result criteria record.
