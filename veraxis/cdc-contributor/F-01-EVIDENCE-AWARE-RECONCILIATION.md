# F-01-EVIDENCE-AWARE-RECONCILIATION — substrate (skeleton, no conclusions)

From: Vitaly Reznik (`inventor1975`), integration owner for F.
Date: 2026-08-10. Status: **SKELETON — cells intentionally unfilled.**
Final permitted wording is set only at F-04, as the **intersection** (never
the average) of `INTERNAL_EVIDENCE_CEILING` (Codex track) and
`EXTERNAL_NOVELTY_CEILING` (Claude track + owner adjudications). The two
tracks never raise each other's evidence class. Disagreement is preserved as
a first-class record. A–E are not touched; a real contradiction with frozen
A–E becomes a `CHALLENGE / CHANGE-REQUEST CANDIDATE`, never a silent edit.

## 0. Frozen inputs of this reconciliation

- A–E freeze: commit `973f9eba2dfe410efdadad132ce2348d3875e302`
  (`00-A-E-FREEZE-MANIFEST.md`; canonical `CDC-AE-FROZEN-INPUT-v0.1`,
  five SHA-256 verified byte-identical). Controlling claim register:
  **artifact 04 only** (`CDC-CLAIM-01..13`).
- Codex track: `F-02B = CLAIM_ALIGNED_RECONCILIATION_COMPLETE_WITH_DISCLOSED_
  TRACEABILITY_GAPS` (owner-accepted state); traceability gaps addressed in
  `F-02B-TRACEABILITY-SUPPLEMENT.md` (this directory).
- Claude track: `F-03D = ACCEPTED_WITH_OWNER_ADJUDICATION` (external research
  cycle CLOSED for F; no new broad searches).
- Observation-mode vocabulary (fixed): `ARTIFACT_INSPECTION` ·
  `RECORDED_PRIOR_MEASUREMENT` · `REEXECUTED_IN_CURRENT_AUDIT` ·
  `NO_EXECUTION` · `BLOCKED_BEFORE_EXECUTION`. Codex constraints:
  `tests_executed = 0`, `historical_measurements_reexecuted = false`.

## 1. INTERNAL_EVIDENCE_CEILING — fixed from F-02B (owner relay)

Preserved challenge records — honest limitations / future release work; not
to be closed by new execution:

- `F02B-01` — no frozen end-to-end OIC→OAM execution.
- `F02B-02` — no manifest-bound end-to-end candidate-binding execution result.
- `F02B-05` — no frozen R-CDC-04 offline/no-egress release-gate result.

Standing internal facts: CDC-CLAIM-08 stays
`BASELINE_REFLECTED_CLARIFICATION / PROVENANCE_CAVEAT` until the original
applicant-retained source is actually re-read (no upgrade from memory or
retelling). CDC-CLAIM-05 figure `371 theorems / 21 modules / empty axiom
lists` = frozen snapshot figure at the veraxis input pin (byte-bound in the
traceability supplement §D), never the current state. Currentness:
`5 × BLOCKED_CASE_CONSTRUCTION`, `EXECUTABLE_DENOMINATOR = 0`, no
pass/fail/measurement.

## 2. EXTERNAL_NOVELTY_CEILING — fixed from F-03D + owner adjudications

Withdrawn (established or heavily anticipated in reviewed SOTA — XACML,
VC 2.0, Catala, SACM, sovereign-boundary/broker lines, records-management
lineage):

```
BROAD_STACK_NOVELTY = WITHDRAWN
RUNTIME_PRIMITIVE_NOVELTY = WITHDRAWN
GENERIC_SEMANTIC_PRESERVATION_NOVELTY = WITHDRAWN
GENERAL_WARRANT_VS_AUTHORITY_NOVELTY = WITHDRAWN
ADVERSE_EVIDENCE_NON_PROMOTION_NOVELTY = WITHDRAWN
```

Survived (residual core, still exposed to falsification):

```
S2_INSTITUTIONAL_MEANING_ADMISSION = SURVIVES_REVIEWED_SOTA_WITH_STRONG_PARTIAL_NEIGHBORS
T1_SEMANTIC_CONSERVATION_ACROSS_HETEROGENEOUS_IMPLEMENTATION_SUBSTITUTION = SURVIVES_REVIEWED_SOTA
S2_PLUS_T1 = SURVIVES_REVIEWED_SOTA
NOVELTY_FINDING = NOT_CLAIMED
```

Canonical formulation: **overall comparative surface was narrowed; residual
core survived.** The residual proposition: the system treats institutionally
admitted meaning as a distinct computational state and requires that state's
*meaning* — not merely its bytes — to remain conserved across heterogeneous
implementation change.

Owner adjudication #1 (S2 / VC 2.0): strengthened operational S2 test — all
eight conditions required: (1) authoritative source S exists before
admission; (2) proposition P is represented from S; (3) P exists as
candidate/unadmitted; (4) the admission transition acts on P itself; (5) the
actor has authority to admit P in this context; (6) ACCEPT/REFUSE does not
change P's propositional content; (7) ACCEPT changes P's admissibility for
downstream institutional computation; (8) the record binds P to
S/version/admitting authority/transition. Action/effect/access/schema/
credential issuance alone ≠ S2. Under this test:
`VC_2_0 = STRONG_PARTIAL_EQUIVALENT` (not PASS) — VC materially anticipates
issuer assertion, issuance, verification/currentness, third-party reliance
structure, but the reviewed standard does not establish the
source→candidate-meaning→institutional-admission transition.

Owner adjudication #2 (T1): PASS requires simultaneously — equivalent
re-encoding survives substitution; meaning-changing mutation is
detected/rejected; the check is independent of byte/schema identity and of
the substituted component; admitted source/meaning identity remains
traceable. Reject-all-representation-changes ≠ PASS; accepting a
meaning-changing transformation ≠ PASS.

Owner adjudication #3: `HITL_ROW = CONTEXTUAL_NON_LOAD_BEARING` — not a basis
for residual novelty/advancement claims.

Ceiling discipline: **S2/T1 are architectural advancement claims, not
executable achievement claims.** Any claim external SOTA permits but internal
evidence does not support stays design-level; any implemented property that
is established prior art does not become an advancement claim.

## 3. Per-claim reconciliation records — CDC-CLAIM-01..13 (artifact 04 verbatim)

Fields per record: `frozen_claim_id` · `exact_frozen_proposition` (verbatim
from 04) · `architectural_basis` · `codex_evidence` · `observation_mode` ·
`denominator` · `claude_external_challenge` · `conflict` · `evidence_class` ·
`maximum_permitted_wording` · `nonclaim_or_limitation` · `status`.

<!-- Codex column transfers from the F-02B document upon receipt;
     Claude column from the F-03D document upon receipt.
     No cell below is filled until then; ceilings only at F-04. -->

### CDC-CLAIM-01
- exact_frozen_proposition: PENDING_TRANSCRIPTION_FROM_FROZEN_04
- architectural_basis: PENDING
- codex_evidence: PENDING_RECEIPT_OF_F02B_DOCUMENT
- observation_mode: PENDING
- denominator: PENDING
- claude_external_challenge: PENDING_RECEIPT_OF_F03D_DOCUMENT
- conflict: PENDING
- evidence_class: PENDING
- maximum_permitted_wording: NOT_SET_BEFORE_F04
- nonclaim_or_limitation: PENDING
- status: OPEN

### CDC-CLAIM-02
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-03
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-04
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-05
(same field set — all PENDING; status OPEN; note: evidence binding for the
Lean figure per §1 and traceability supplement §D)

### CDC-CLAIM-06
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-07
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-08
(same field set — all PENDING; status OPEN; standing:
`BASELINE_REFLECTED_CLARIFICATION / PROVENANCE_CAVEAT` per §1)

### CDC-CLAIM-09
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-10
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-11
(same field set — all PENDING; status OPEN)

### CDC-CLAIM-12
(same field set — all PENDING; status OPEN; frozen: Phase-A =
`FAIL_AND_INCOMPLETE`, 6/8 classes 50/50, 2 UNMEASURED, §24.5 defect = 1)

### CDC-CLAIM-13
(same field set — all PENDING; status OPEN; frozen: currentness `BLOCKED`,
denominator 0 — neither pass nor fail)

## 4. Release/benchmark propositions (beyond the 13 claims)

Rows to be enumerated from the F-02B document upon receipt (R-CDC-01..05
release objects; preserved F02B-01/02/05 map here). PENDING.

## 5. Blocking conditions for F-04

F-04 (`CLAIM-EVIDENCE-CEILING-FINAL`) starts only when: (a) the F-02B
document is in hand for the Codex column transfer; (b) the F-03D document is
in hand for the Claude column transfer; (c) this skeleton's per-claim records
are filled with both tracks held separate. Stop conditions for F closure are
the owner's seven (each material claim has an evidence class; each measured
claim a denominator; each external comparative claim a substantiation;
blocked/unmeasured preserved; no public sentence above its ceiling; no silent
contradiction with frozen A–E; gaps listed as nonclaims/open work).
