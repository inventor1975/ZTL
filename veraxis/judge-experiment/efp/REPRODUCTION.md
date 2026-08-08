# Reproduction Procedure v0.1

An independent party reproduces every result from public materials alone:

1. Clone github.com/inventor1975/ZTL at the pinned commit (judge-pin.json;
   the EFP commit recorded in the package return supersedes it as the
   canonical checkout point — it contains both the judge and this package).
2. Clone the Review Ledger and fetch the 11 corpus heads listed in
   corpus-index.json (refs are immutable commit hashes; verify trees).
3. Obtain m1-s1-measurement-001.zip and verify 103189 bytes /
   SHA-256 e9250d19... / SHA-512 958cf644... per corpus-index.json.
4. Phase A harvest:  python3 harvester.py <ledger_clone> <zip> formulas.json <out>
5. Provenance audit: python3 provenance_audit.py <out>
6. Judge evaluation (Phase A only, after EXPERIMENT_FREEZE_PACKAGE_ACCEPTED):
   python3 evaluate.py <out>  — emits one CLWR per gate binding the
   JudgeContext (formula hash, marking hash, judge pin) per Protocol R-07.
7. Compare CLWR verdicts/grades/weak links byte-wise with the published
   bundle. Divergence = §24.8 failure.

Note: evaluate.py is part of the package (frozen); running it before package
acceptance is prohibited for result-bearing purposes (owner freeze decision).
