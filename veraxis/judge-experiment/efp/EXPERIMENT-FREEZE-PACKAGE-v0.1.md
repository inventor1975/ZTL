# Experiment Freeze Package v0.1

**Package ID:** `EXPERIMENT-FREEZE-PACKAGE-v0.1`
**Status:** REVISION 2 — OWNER ACCEPTANCE CANDIDATE, returned after `REVISION_REQUIRED` (four implementation-contract blockers). Phase A authority does not exist until acceptance (frozen Protocol §28).
**Frozen protocol:** `OIC-ZTL-OAM-PROTOCOL-v0.1`, commit `61a470b41eccf8e57633d0abee7bbc795329a411`, SHA-256 `98bbb05ba82d61638b063da9898827492b679dbcbba33784231482f092c14273`.
**Built:** 2026-08-09, by Claude (Fable 5) under the steering role (V. Reznik), per the productive-implementation authority of the freeze decision.

## The fourteen §28 bindings

| # | Binding | Where |
|---|---------|-------|
| 1 | Exact corpus index | `corpus-index.json` |
| 2 | Every included head/tree/package identity | `corpus-index.json` (12 items, measured from the ledger objects and the legacy zip) |
| 3 | Complete inclusion/exclusion list with reasons | `corpus-index.json` (`excluded`) |
| 4 | Harvesting rules | `harvesting-rules.json` (19 rule classes; default-deny; witness must support the specific atom/status) + `handler-conformance.json` (per-rule handler matrix; unimplemented rules fail closed to Z) |
| 5 | Harvester implementation identity | `harvester.py` (its SHA-256 is stamped into every marking it emits; bound in the package manifest) |
| 6 | Complete formula set | `formulas.json` — 34 gates, 91 atoms |
| 7 | Source anchor for every formula | `formulas.json` (`source_anchors` per gate — every anchor a persisted hash-bound artifact, a legacy-zip member, or the accepted-decision registry entry; zero relay-channel anchors) |
| 8 | Pinned ZTL/judge implementation identity | `judge-pin.json` (repo commit + kernel module hashes); the EFP commit recorded in the return is the canonical checkout |
| 9 | Exact scored seam identities / recorded substitutions | `seam-dispositions.json` — S-1, S-4, S-5 BOUND to persisted artifacts; S-2, S-3 REMOVED_NOT_BINDABLE per Protocol §22 (relay-channel history), defect shapes covered by the sealed mutation classes; scored denominator = 3 |
| 10 | Reproduction commands/procedure | `REPRODUCTION.md` v0.2 (exact statically-verified invocations) + `evaluate.py` (R-06/R-07/R-15-conformant CLWR emitter) + `claim-context-templates.json` (frozen institutional envelope per gate) |
| 11 | Mutation classes | `mutation-denominators.json` (8 classes per the accepted charter) |
| 12 | Exact mutation denominator per class | `mutation-denominators.json` — structural ceilings enumerated from the bound atom sites; frozen N = 10 for every class (all ceilings ≥ 10) |
| 13 | Sealed-manifest commitment procedure | `sealed-manifest-procedure.md` |
| 14 | Remaining §24 scoring constants | `scoring-constants.json` (thresholds 100%/90%, zero tolerances, EH-4 population, residue ≤ 10%, denominators) |

## Revision-2 change account (the four blockers, nothing else)

1. **Source anchors re-bound.** Every gate's `source_anchors` now resolves to a
   persisted hash-bound artifact (owner-decision blobs at their persisted heads;
   the verbatim owner order inside the accepted legacy zip; persisted
   authorization-reference records) or to the accepted-decision registry entry of
   `corpus-index.json` (review id + token — accepted decisions, not observed
   objects). Zero relay-channel anchors remain. Three scope atoms whose only
   governing text was a relay order were removed (PR#5 three-file set, PR#8 and
   PR#10 one-file sets), with the removals recorded in the gates' notes; the
   affected gates keep their identity/coordinate atoms (34 gates, 91 atoms).
2. **`tree_identity` fixed.** Atoms now bind `expected_tree` from the frozen
   corpus index; the handler compares observed vs expected (T/F), fails closed
   to Z on unresolvable input, and its witness records head + expected_tree +
   observed_tree. Negative unit test included in the dev disclosure. The full
   handler matrix is `handler-conformance.json`; unimplemented rules (doc_cites)
   fail closed to Z and can never return T.
3. **CLWR emitter made conformant.** Individual `formula_sha256` under a frozen
   canonicalization (exact formula string, UTF-8); the marking itself embedded
   with `marking_sha256` (canonical JSON); every load-bearing reference
   hash-bound (marking document by bytes+sha256; formula set by bytes+sha256;
   source anchors carried); the arbitrary CLI claim-context string removed —
   the institutional envelope is frozen per gate in
   `claim-context-templates.json`, the JudgeContext identity is computed from
   formula+marking+judge-pin hashes, and the ClaimContext identity is the hash
   of the frozen template combined with that JudgeContext identity. A synthetic
   unit run demonstrates all R-07/R-06 fields mechanically.
4. **Reproduction procedure fixed and statically verified.** `REPRODUCTION.md`
   v0.2 carries the exact five-argument evaluator invocation and explicit
   commands for checkout/pins, corpus verification, zip verification,
   harvesting, provenance audit, context construction/evaluation, and output
   comparison (invocation_time excluded per R-23). A static interface check
   confirms every documented command matches its tool's arity.

## Conformance notes

- **Protocol conformance: PASS** (self-assessed; subject to owner adjudication). Every T/F the harvester admits carries a witness binding the specific atom at the specific status (R-02/R-03); markings are emitted as immutable hash-stamped documents; `evaluate.py` emits ten-field CLWRs binding formula hash, marking hash, judge identity and ClaimContext id (R-06/R-07).
- **Development verification disclosure.** Constructing this package required machinery verification: a harvesting run over the corpus (to validate rule bindings; one formula mis-binding was found and corrected before this freeze) and a synthetic-marking unit test of the evaluator. Per the freeze decision, these are construction steps, **not experimental evidence**; no seam scoring, no EH adjudication, no blinded runs, and no Phase A conclusions were produced, and no dev output ships in this package.
- **Phase A remains unexecuted.** `Phase_A_started = false`; `result_bearing_evaluations = 0`.

## Package manifest

`package-manifest.json` — self-excluded; binds every other member by path, bytes, SHA-256, SHA-512.
