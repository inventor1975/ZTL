# Phase A v0.1 — Owner Adjudication 001

**Record type:** OWNER ADJUDICATION (verbatim, persisted as a new record; does not amend prior bytes).
**Owner / Adjudicator:** Arkadiy Miteiko.
**Transcribed by:** Claude (Fable 5), independent-review / experiment side, under the steering role (V. Reznik).
**Date:** 2026-08-09.

## Reference (unmodified)

- repository: `inventor1975/ZTL`
- scored commit: `40712058530a407da0710b21b0f62272809c9fe4`
- scored tree: `1483097b0a1225be62486a4ccb278a49978497aa`
- raw blinded commit: `4d8f87bd365039024745c005461192489344cb25`
- frozen EFP commit: `673a8854e68d03f0cc30655b168343cf47887e0f`
- frozen Protocol commit: `61a470b41eccf8e57633d0abee7bbc795329a411`
- sealed manifest: `OWNER-SEALED-MUTATION-MANIFEST-v0.1` (51630 / SHA-256 `32b85214...` / SHA-512 `cdd36b2e...`)

This record references those artifacts by identity and does not rewrite or amend them.

## Accepted findings

1. `SEALED_MANIFEST_COMMITMENT_REPRODUCTION = PASS`.

2. Six EH-3 classes accepted as measured at 100% detection:
   - `missing_witness_or_evidence` = 10/10
   - `corrupted_hashes` = 10/10
   - `schema_drift` = 10/10
   - `counter_inconsistency` = 7/7
   - `contradictory_gate_facts` = 3/3
   - `altered_identity_environment` = 10/10
   - measured aggregate = 50/50 detected; 0 false-clean EARNED; 0 scored misses.

3. Two classes accepted as `BLOCKED_CASE_CONSTRUCTION / UNMEASURED`:
   - `missing_atoms` = 10
   - `false_positive_adapter_markings` = 10
   - preserved cause: owner-side `adapter_patch.pyc` portability failure ("Bad magic number in .pyc file").
   - This is an experimental-contract / case-construction finding. Not a ZTL detection miss. Not a measured PASS.

## Owner adjudication correction — provenance

- case: `case-e20cf86d48c9ac3673dd`
- mutation: `MISSING_WITNESS_OR_EVIDENCE-10`
- gate: `G-M1S1-FILE-IDS`, atom: `zs0`
- frozen raw case: exit = 0; markings = 37; CLWR = 37; provenance_exit = 1.

The provenance-less `F` **survived admission into an evaluated marking**. Under frozen
Protocol §24.5 this is a **PROVENANCE FAILURE**. The separate provenance auditor detecting
the defect does not erase the harvesting/admission failure. The mutation may remain counted
as pipeline detection for the `missing_witness_or_evidence` detection-rate accounting (the
frozen provenance control did detect it), but the affected judge result is void under §24.5
and the independent provenance-failure criterion is triggered.

**Reviewer concession (V. Reznik / Claude):** the scored bundle labeled this a "provenance
nuance / detection." The owner ruling is accepted without reservation: it is a §24.5
admission failure, count = 1.

## Corrected Phase A state

```text
EH1 = PASS
EH2 = PASS
EH3 = PARTIAL  (6/8 classes measured and PASS at 100%; 2/8 BLOCKED_CASE_CONSTRUCTION / UNMEASURED)
EH4 = PASS
PROVENANCE_FAILURE_§24.5 = FAIL   (count = 1)
PHASE_A_OVERALL = FAIL_AND_INCOMPLETE
PHASE_B_AUTHORITY = NONE
```

Reason: a definite §24.5 provenance-admission failure; and two EH-3 mutation classes remain unmeasured.

## No repair / no retroactive completion

- Do not rerun or replace any Phase A v0.1 raw result.
- Do not repair `adapter_patch.pyc` and substitute new results into the existing 70-case experiment.
- Do not modify the frozen raw or scored bundles.
- If the original 20 disclosed adapter cases are replayed with a source harness, that replay
  is DIAGNOSTIC ONLY; it cannot restore blindness or change the Phase A v0.1 verdict.

## Requirement for blinded adapter evidence (new experiment)

Blinded evidence on `missing_atoms` and `false_positive_adapter_markings` requires a separate,
newly preregistered experiment with:
- fresh owner-side sealed commitment;
- fresh blinded case mapping not known to the implementer/reviewer;
- unused structurally valid opportunities;
- exact frozen denominators 10 + 10 for that new experiment;
- portable source-form injection harness;
- harness/runtime identity frozen before result-bearing execution;
- raw result freeze before disclosure;
- no modification of Phase A v0.1 evidence.

## Status

Persisted as a new record referencing scored commit `40712058530a407da0710b21b0f62272809c9fe4`.
Existing scored result bytes are not rewritten or amended. `PHASE_B` remains unauthorized.
