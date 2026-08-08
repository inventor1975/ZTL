# Experiment Freeze Package v0.1

**Package ID:** `EXPERIMENT-FREEZE-PACKAGE-v0.1`
**Status:** CANDIDATE — submitted for owner acceptance (`EXPERIMENT_FREEZE_PACKAGE_ACCEPTED` pending). Phase A authority does not exist until that acceptance (frozen Protocol §28).
**Frozen protocol:** `OIC-ZTL-OAM-PROTOCOL-v0.1`, commit `61a470b41eccf8e57633d0abee7bbc795329a411`, SHA-256 `98bbb05ba82d61638b063da9898827492b679dbcbba33784231482f092c14273`.
**Built:** 2026-08-09, by Claude (Fable 5) under the steering role (V. Reznik), per the productive-implementation authority of the freeze decision.

## The fourteen §28 bindings

| # | Binding | Where |
|---|---------|-------|
| 1 | Exact corpus index | `corpus-index.json` |
| 2 | Every included head/tree/package identity | `corpus-index.json` (12 items, measured from the ledger objects and the legacy zip) |
| 3 | Complete inclusion/exclusion list with reasons | `corpus-index.json` (`excluded`) |
| 4 | Harvesting rules | `harvesting-rules.json` (19 rule classes; default-deny; witness must support the specific atom/status) |
| 5 | Harvester implementation identity | `harvester.py` (its SHA-256 is stamped into every marking it emits; bound in the package manifest) |
| 6 | Complete formula set | `formulas.json` — 34 gates, 94 atoms |
| 7 | Source anchor for every formula | `formulas.json` (`source_anchor` per gate) |
| 8 | Pinned ZTL/judge implementation identity | `judge-pin.json` (repo commit + kernel module hashes); the EFP commit recorded in the return is the canonical checkout |
| 9 | Exact scored seam identities / recorded substitutions | `seam-dispositions.json` — S-1, S-4, S-5 BOUND to persisted artifacts; S-2, S-3 REMOVED_NOT_BINDABLE per Protocol §22 (relay-channel history), defect shapes covered by the sealed mutation classes; scored denominator = 3 |
| 10 | Reproduction commands/procedure | `REPRODUCTION.md` + `evaluate.py` (CLWR emitter, R-07 ten fields) |
| 11 | Mutation classes | `mutation-denominators.json` (8 classes per the accepted charter) |
| 12 | Exact mutation denominator per class | `mutation-denominators.json` — structural ceilings enumerated from the bound atom sites; frozen N = 10 for every class (all ceilings ≥ 10) |
| 13 | Sealed-manifest commitment procedure | `sealed-manifest-procedure.md` |
| 14 | Remaining §24 scoring constants | `scoring-constants.json` (thresholds 100%/90%, zero tolerances, EH-4 population, residue ≤ 10%, denominators) |

## Conformance notes

- **Protocol conformance: PASS** (self-assessed; subject to owner adjudication). Every T/F the harvester admits carries a witness binding the specific atom at the specific status (R-02/R-03); markings are emitted as immutable hash-stamped documents; `evaluate.py` emits ten-field CLWRs binding formula hash, marking hash, judge identity and ClaimContext id (R-06/R-07).
- **Development verification disclosure.** Constructing this package required machinery verification: a harvesting run over the corpus (to validate rule bindings; one formula mis-binding was found and corrected before this freeze) and a synthetic-marking unit test of the evaluator. Per the freeze decision, these are construction steps, **not experimental evidence**; no seam scoring, no EH adjudication, no blinded runs, and no Phase A conclusions were produced, and no dev output ships in this package.
- **Phase A remains unexecuted.** `Phase_A_started = false`; `result_bearing_evaluations = 0`.

## Package manifest

`package-manifest.json` — self-excluded; binds every other member by path, bytes, SHA-256, SHA-512.
