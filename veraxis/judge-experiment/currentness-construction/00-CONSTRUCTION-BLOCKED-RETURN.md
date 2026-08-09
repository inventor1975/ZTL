# Currentness / Rollback benchmark — CONSTRUCTION RETURN: BLOCKED (all five cases)

From: Claude (independent-review side), relayed by Vitaliy Reznik (`inventor1975`)
Date: 2026-08-09
Authority: `CONSTRUCTION_AUTHORITY = CONTINUE_FOR_BLOCKED_FINDING_ONLY`; `EXECUTION_AUTHORITY = NONE`.
Preregistration governing this construction: v0.2 — 12585 bytes, SHA-256
`5c8c4bb337cba02f34df54d90d485f2cab324e01e9bf5856c4f551aa8a29fb3d`, commit
`61772f78b98f009f93c01a21ded7a64c3d35ff19`.
Frozen stack under test (owner decision): `EFP executable Phase-A substrate as preregistered`.
`ALTERNATE_RUNTIME_SUBSTRATE = NONE`.

---

## Disposition — all five preregistered case classes

| Case | Class | Construction disposition |
|---|---|---|
| C1 | `LATEST_CORRECTION_REMOVED` | `BLOCKED_CASE_CONSTRUCTION` |
| C2 | `PRE_WITHDRAWAL_STATE_RESTORED` | `BLOCKED_CASE_CONSTRUCTION` |
| C3 | `SUPERSEDED_OIC_PACK_RESTORED` | `BLOCKED_CASE_CONSTRUCTION` |
| C4 | `RELIED_UPON_TO_CORRECTED_SUFFIX_TRUNCATED` | `BLOCKED_CASE_CONSTRUCTION` |
| C5 | `HISTORICALLY_VALID_STATE_PRESENTED_AS_CURRENT` | `BLOCKED_CASE_CONSTRUCTION` |

**Shared exact reason:** `EXECUTABLE_CURRENTNESS_RELIANCE_SUBSTRATE_ABSENT`.

## System finding (frozen wording)

> **The frozen executable Phase-A substrate implements logical-warrant evaluation but does not
> implement the institutional-currentness, issuance, reliance, and lifecycle execution required
> to operationalize Protocol R-26/R-17. Constructing executable CURRENTNESS cases would therefore
> require adding the capability under test.**

## The distinction that IS the finding

- **Design representability = PRESENT.** The Protocol expresses current / corrected / superseded
  / revoked / reliance semantics: R-26 (current status computed fail-closed from issuance terms
  **and** lifecycle events — revocation, supersession, corrections), R-17 (reliance requires an
  **active** issuance at the reliance event; a revoked/expired/superseded issuance does not
  satisfy it), R-08 (CLWRs immutable; corrections are new records), R-25 (markings immutable;
  correction only via successor markings; predecessor preserved), R-15 (load-bearing references
  resolve to content hashes).
- **Executable representability = ABSENT in the frozen substrate.** No executable component
  realizes R-26 / R-17 / issuance / reliance / lifecycle. The only evaluator emits logical-warrant
  records (CLWRs) over fixed markings.

This gap is the finding. It is **not** a failure of the OIC–ZTL–OAM architecture — the
architecture already *requires* the property; the benchmark found that the current Phase-A
executable boundary does not yet reach it. It is also **not** a measured currentness detection
failure, and it is **not** characterized as a stronger confirmation of A3: it is an **earlier
structural boundary** — the frozen executable substrate contains no executable carrier of the
property the preregistration set out to measure.

## Evidence (reproducible — see `search-evidence.txt`)

- EFP evaluator inventory: `efp/evaluate.py` (4953 bytes, SHA-256
  `f52fd4b67ce338c7ddcf3fbf1ac80ea96011779d0abc9ed5986f78019d9bcee7`) is the only evaluator; its
  docstring declares it emits one **R-06/R-07/R-15-conformant CLWR per gate**; it imports only
  `ztljudge.judge` (the pinned logical kernel).
- `grep` in `evaluate.py` for `issuance|reliance|current.?status|lifecycle|supersed|revocation|
  R-26|R-17` → **no matches**.
- `grep` across all `efp/*.py` for `issuance|reliance|current.?status|lifecycle|supersed` →
  **no files match**.
- `grep` repo-wide (`*.py` + `*.json`) for `issuance|reliance|current.?status|R-26|R-17` →
  **no files match** outside the preregistration documents (prose, not executable carriers).
- Frozen EFP identity: accepted commit `673a8854e68d03f0cc30655b168343cf47887e0f`, tree
  `c02c5b1e1078aef385908c1ab64cad077bbe9b12`.

## Why the existing CLWR evaluator is insufficient (not a substitute)

The CLWR evaluator establishes a contemporaneous **logical**-warrant record over a fixed marking.
By Protocol design (revision-2 item 2; R-25; R-17), lifecycle events "never retroactively modify
logical results," and a reliance record "cites the issuance record and its current-status
determination, **not** the CLWR directly." The logical layer is therefore currentness-agnostic by
construction: re-evaluating a rolled-back marking yields a valid CLWR over whatever marking it was
given, with no notion of whether that marking is the current institutional state. Establishing
currentness requires the R-26/R-17 institutional layer, which the frozen substrate does not
implement.

## Discipline observed (per owner directive and frozen preregistration)

For every case, the following are **not set** — a construction failure is not a detection or
containment result:

- `Detection` — NOT set (not MISS, not HIT).
- `Containment` — NOT set (not PASS, not FAIL).
- `observed first-failing-layer` — NOT set.
- No case executed. No case bytes/instances constructed. No lifecycle/issuance/reliance schema
  invented.

**Executable CURRENTNESS case denominator = 0.** The five preregistered classes remain valid as
**`NON_EXECUTABLE_PREREGISTERED_CASE_SPEC`** (their design fields live in preregistration v0.2 §7);
they are not constructed executable instances and carry no outcome data.

Each case's `primary seam under test` (design intent, carried from frozen preregistration v0.2,
adds no capability):

- C1 → OIC currentness / OAM state binding
- C2 → OAM import / state binding, and ZTL input currentness
- C3 → OIC currentness
- C4 → VEIP reliance gate, and ZTL input currentness
- C5 → presentation / report currentness

## Successor (not started; not authorized here)

Implementing R-26/R-17 is a separate future workstream `OAM-EXEC-CURRENTNESS-001`, gated behind
the appropriate OAM semantic gate, to be executed against a real lifecycle/reliance substrate under
separate authorization — **not** via repair or substitution of this experiment. No such
implementation is begun. Current CDC state remains `semantic_implementation_gate = BLOCKED`,
`runtime_execution = NOT_AUTHORIZED`; SAR-05 audit-lineage current/superseded report selection is
**not** treated as a substitute (its claim ceiling does not establish present institutional
authority or reliance).

— Claude (independent-review side), relayed by Vitaliy Reznik (`inventor1975`)
