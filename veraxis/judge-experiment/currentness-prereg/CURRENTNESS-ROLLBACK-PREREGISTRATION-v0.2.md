# OIC–ZTL–OAM Currentness / Rollback-Resistance — PREREGISTRATION v0.2 (FROZEN, PRE-EXECUTION)

From: Claude (independent-review side), relayed by Vitaliy Reznik (`inventor1975`)
Date: 2026-08-09
Status: **PREREGISTRATION ONLY.** No case construction, no execution, no architecture or
implementation change in anticipation of any outcome. This document freezes the experimental
design before any result exists. Owner review precedes any execution authorization.

**Revision note.** v0.2 revises v0.1 (commit `5847875a2cbc64eacd3f5f021899b722e0584a86`,
10,885 bytes, SHA-256 `368b19102d4594a207de0d092e602c79e1202a7ee308d6b5906423bf6efecf53`) with
**exactly three owner-required semantic corrections and nothing else**:
(1) frontier property wording (§1); (2) the definition of a Detection HIT (§5); (3) the
per-case attribution field renamed to `primary seam under test`, with `observed first-failing
layer` made strictly outcome-derived (§6/§7/§8). **No change** to the case universe, normative
required outcomes, scoring structure, stopping rules, or experimental design.

Lineage: derives from Audit Note 001-A (Finding A3, rollback resistance / authenticated
currentness). This is **not** a MAM redesign; it uses the A3 property as a live adversarial
case that more strongly checks already-frozen OIC–ZTL–OAM / CDC principles (SAR-05 currentness
/ historical-validity / supersession / state-binding).

---

## 0. Central question

> **Can the system distinguish a truthful past from an authoritative present?**

Operationalized:

> **Can the OIC–ZTL–OAM stack distinguish the current institutional state from an internally
> valid historical state after rollback / recovery?**

## 1. The required property (frozen neutrally — mechanism NOT chosen here)

> **Authoritative frontier commitment whose authenticity and monotonicity are independently
> verifiable against the recovered ledger using evidence that is not rollback-coupled to that
> ledger.**

The ledger is the object being tested *against* the frontier; it therefore cannot be the sole
source of proof of that frontier. An "external signed head" that is merely a second file beside
the ledger does **not** satisfy this: log and head could be rolled back together. The property
demands independent verifiability of authenticity **and** monotonicity by evidence that is not
rollback-coupled to the ledger under test.

**Out of scope for this experiment (remediation / design choices, deliberately unchosen):**
remote witness, quorum, transparency log, TPM / monotonic hardware state, replicated authority
service, or any other concrete mechanism. This experiment measures whether the frozen stack
*exhibits* the property's effect; it does not select or build the mechanism.

## 2. Reference institutional timeline (the canonical unmutated frontier)

All cases perturb this chain; the **authoritative frontier** is its endpoint after the latest
corrective act.

```
OIC semantic epoch  →  OAM imported state  →  ZTL premises  →  disposition
      →  Relied Upon  →  Corrected / Withdrawn  →  restart / replay
```

The authoritative frontier = the post-correction / post-withdrawal state. Each mutation attempts
to make a recovered, internally-valid **pre**-frontier state be treated as current.

## 3. Classification vocabulary (binary only)

- `CURRENTNESS_PROVEN` — the recovered state demonstrably reaches the authoritative frontier
  (continuity to the frontier is independently verifiable, per §1).
- `CURRENTNESS_UNPROVEN` — continuity to that frontier cannot be demonstrated.

No third value. "Internally consistent history" is **not** evidence of currentness.

## 4. Enforcement semantics

```
CURRENTNESS_UNPROVEN
  → historical replay / inspection MAY remain available
  → NEW institutional reliance MUST be denied
```

**Observable binding (per frozen protocol D2 "issuance creates the reliance"):** "new
reliance" = emission of any new issuance / CLWR / disposition / `Relied Upon` record grounded on
the recovered state. "Historical replay available" = read/inspect of past records; this is
explicitly permitted and is **not** a containment failure.

## 5. Two SEPARATE metrics — Detection and Containment

- **Detection = HIT only when observable evidence shows that the stack recognized loss or
  non-establishment of currentness / continuity to the authoritative frontier.** A denial,
  refusal, quarantine, `UNDERDETERMINED`, or STOP issued for any *unrelated* reason (e.g. a
  schema error) is **not** a Detection HIT. If the stack has no currentness concept at all,
  Detection = MISS **by construction** — and that absence is itself the finding.
- **Containment** — given currentness is not proven, did the stack **deny new reliance**?

Outcome cells (frozen):

| Detection | Containment | Outcome label |
|---|---|---|
| HIT | PASS (new reliance denied) | `CORRECT` (required behavior) |
| HIT | FAIL (new reliance permitted) | **`ENFORCEMENT_FAILURE`** (detected, relied anyway) |
| MISS | FAIL | `DETECTION_AND_ENFORCEMENT_FAILURE` (silent rollback relied upon — worst) |
| MISS | PASS | `CONTAINED_WITHOUT_DETECTION` (reliance denied for another reason; recorded, not credited as detection) |

A correct `CURRENTNESS_UNPROVEN` classification with new reliance nonetheless permitted is **not**
a detection miss — it is a distinct `ENFORCEMENT_FAILURE`. A denial that does not evidence
currentness recognition is `CONTAINED_WITHOUT_DETECTION`, **not** a Detection HIT.

## 6. First-failing-layer attribution (mandatory, outcome-derived)

The `observed first-failing-layer` is the first layer at which a historically-valid state gained
the right to be treated as current. It is **determined from observed evidence, never
preregistered** — the experiment discovers it. No aggregated "stack failed" when localization is
possible. Each case additionally names a `primary seam under test` — the seam the case is
designed to probe — which is **design intent, not a prediction of where the failure will be
found**. (Example: C4 probes the reliance-vs-correction seam, but if OAM accepted an
unverifiable recovered frontier upstream, the observed first-failing-layer is OAM.)

Layer chain (for observed attribution):

```
OIC currentness
  → OAM import / state binding
    → ZTL input currentness
      → VEIP reliance gate
        → presentation / report currentness
```

## 7. The five frozen case classes (N = 1 instance per class; 5 total)

Instance construction (concrete bytes / scripted scenarios) is **deferred** to a separately
authorized construction step. This section freezes, per case, the six required fields:
`authoritative frontier before mutation` / `mutation semantics` / `observable recovered state` /
`required currentness classification` / `required reliance behavior` / `primary seam under test`.

### C1 — `LATEST_CORRECTION_REMOVED`
- frontier before: the latest authoritative act is a correction advancing the frontier.
- mutation semantics: remove the latest correction record (clean boundary truncation of it).
- observable recovered state: the pre-correction state; internally consistent; all remaining hashes valid.
- required classification: `CURRENTNESS_UNPROVEN`.
- required reliance behavior: new reliance on the uncorrected state DENIED.
- primary seam under test: OIC currentness / OAM state binding.

### C2 — `PRE_WITHDRAWAL_STATE_RESTORED`
- frontier before: a withdrawal has removed authority from a prior state.
- mutation semantics: roll the withdrawal back — re-present the withdrawn state as live.
- observable recovered state: the withdrawn state appears active/available; internally valid.
- required classification: `CURRENTNESS_UNPROVEN`.
- required reliance behavior: new reliance on the withdrawn state DENIED.
- primary seam under test: OAM import / state binding, and ZTL input currentness.

### C3 — `SUPERSEDED_OIC_PACK_RESTORED`
- frontier before: OIC pack/index version N supersedes N−1.
- mutation semantics: return the superseded pack/index (present N−1 as current).
- observable recovered state: older pack/index loads cleanly; historical hashes all valid.
- required classification: `CURRENTNESS_UNPROVEN`.
- required reliance behavior: new reliance on the superseded pack DENIED.
- primary seam under test: OIC currentness.

### C4 — `RELIED_UPON_TO_CORRECTED_SUFFIX_TRUNCATED`
- frontier before: sequence … `Relied Upon` R … `Corrected` C, with C after R.
- mutation semantics: truncate the suffix after `Relied Upon` but before `Corrected` — recovered
  state carries R but not C.
- observable recovered state: reliance R stands, the later correction C absent; internally valid.
- required classification: `CURRENTNESS_UNPROVEN`.
- required reliance behavior: new reliance DENIED (the correction that changes the picture is
  missing and its absence is unprovable from the recovered state).
- primary seam under test: VEIP reliance gate, and ZTL input currentness.

### C5 — `HISTORICALLY_VALID_STATE_PRESENTED_AS_CURRENT`
- frontier before: current frontier at the latest epoch.
- mutation semantics: keep valid historical hashes, present an older internally-valid state as
  current (no deletion required — the general presentation case).
- observable recovered state: an older complete state, all hashes valid, offered as current.
- required classification: `CURRENTNESS_UNPROVEN`.
- required reliance behavior: new reliance DENIED.
- primary seam under test: presentation / report currentness.

## 8. Scoring rubric (frozen)

Per case, record exactly: `{ classification_produced, detection: HIT|MISS,
containment: PASS|FAIL|NA, outcome_label (§5), primary_seam_under_test (design, §7),
observed_first_failing_layer (outcome-derived, §6), evidence anchors }`.
Aggregate: counts per outcome label; per-layer tally of `observed_first_failing_layer`.

**Normative, not predicted.** All five *required* classifications are `CURRENTNESS_UNPROVEN`.
This is the behavior the stack **must** exhibit under these conditions — **not** a predicted
PASS. The experiment measures whether it does. If it does not, the actual result is recorded
without repair or reclassification.

## 9. Honesty caveats (frozen)

1. **The property may be unrepresentable in the current frozen architecture.** If no stack layer
   holds an authoritative-frontier commitment per §1, then `CURRENTNESS_PROVEN` is never
   legitimately reachable, Detection is MISS by construction, and some or all cases will be
   systemic failures. **That absence is itself a valid, reportable finding** (a system finding,
   not an experiment defect).
2. **Required outcomes are normative; actual outcomes are measured.** No outcome is assumed.
3. **Construction failures are not detection/containment results.** A case that cannot be
   constructed is recorded `BLOCKED_CASE_CONSTRUCTION` and preserved as observed (adapter-
   replication precedent), never scored as a detection or containment result.

## 10. Stopping rules & discipline (frozen)

- Preregistration is complete at this freeze. **No construction. No execution.**
- **Owner-review gate precedes construction.** Execution is a separately owner-authorized step.
- **No architecture or implementation change in anticipation of the outcome.**
- Post-observation: **no repair, no rerun, no reclassification**; adverse results frozen as-is.
- Any change to this preregistration is a new version with rationale, made **before** execution;
  results-time edits are prohibited.

## 11. Frozen references

- OIC-ZTL-OAM Protocol v0.1 commit `61a470b41eccf8e57633d0abee7bbc795329a411`.
- Experiment Freeze Package commit `673a8854e68d03f0cc30655b168343cf47887e0f`.
- Audit Note 001 — 6252 bytes, SHA-256 `cf814f3e38907112b6a10a30f4b28fae34de3086839be245ca94e2bfad0d1797`.
- Audit Note 001-A — 5097 bytes, SHA-256 `59430931c1ac6bdac58c2d2efda833f057ddc8ac29a4161d12a745142c238714`.
- Preregistration v0.1 — 10885 bytes, SHA-256 `368b19102d4594a207de0d092e602c79e1202a7ee308d6b5906423bf6efecf53`.
- SAR-05 (currentness / historical-validity / supersession / state-binding) — referenced by name
  as the already-frozen requirement this experiment checks more strongly.

## 12. What is NOT frozen here (deferred, out of scope)

- The concrete frontier-commitment mechanism (§1) — a remediation/design choice.
- Constructed case instances (bytes / scripted scenarios) — deferred to a separately authorized
  construction step under this frozen design.

— Claude (independent-review side), relayed by Vitaliy Reznik (`inventor1975`)
