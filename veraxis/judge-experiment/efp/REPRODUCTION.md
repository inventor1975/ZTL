# Reproduction Procedure v0.2

An independent party reproduces every result from public materials alone.
`$EFP` below denotes this package directory (`veraxis/judge-experiment/efp`)
inside the checked-out ZTL repository; `$LEDGER` a local clone of the Review
Ledger; `$ZIP` the legacy package file; `$WORK` any empty working directory.
No hidden local state is required; every argument is explicit below.

## 1. Exact checkout / pins

    git clone https://github.com/inventor1975/ZTL
    cd ZTL && git checkout <EFP_COMMIT>          # the accepted package commit
    sha256sum veraxis/judge-experiment/efp/package-manifest.json   # must match the accepted identity

The judge kernel identity must match `judge-pin.json` (kernel module hashes):

    sha256sum ztl.py ztljudge.py zverify.py

## 2. Corpus verification

    git clone https://github.com/veraxis-protocol/Institutional-Compiler-Review-Ledger $LEDGER
    cd $LEDGER
    # for every entry in corpus-index.json with a "head":
    git rev-parse <head>^{tree}      # must equal the recorded "tree"

## 3. Legacy ZIP verification

    stat -c%s $ZIP        # must be 103189
    sha256sum $ZIP        # must be e9250d1938bbbd5f607add695ce2273c52d00428da26481834b2dd020348d30a
    sha512sum $ZIP        # must be 958cf6449f9d7a838bac755e029421ced5de15a5a6bed18f9ce65ed15fafd9b9f77709fbd4e541bedd94fa44055e28dae557a1ce1122ea4331f922320abed5f5

## 4. Harvesting

    python3 $EFP/harvester.py $LEDGER $ZIP $EFP/formulas.json $WORK/markings

## 5. Provenance audit

    python3 $EFP/provenance_audit.py $WORK/markings

Exit status 0 required (zero provenance-less T/F).

## 6-7. JudgeContext/ClaimContext construction and evaluation

Both are performed by the evaluator (contexts are computed per the frozen
canonicalization declared in `evaluate.py`'s header, from the frozen formula
set, the emitted markings, `judge-pin.json` and
`claim-context-templates.json`):

    python3 $EFP/evaluate.py $WORK/markings $EFP/formulas.json $EFP/judge-pin.json $EFP/claim-context-templates.json $WORK/clwr

PROHIBITED for result-bearing purposes before
`EXPERIMENT_FREEZE_PACKAGE_ACCEPTED = true`.

## 8. Output verification / scoring inputs

Compare each `$WORK/clwr/<gate>.clwr.json` against the published Phase A
bundle: `verdict_and_disposition`, `grade`, `weak_links`, `judge_context_id`
must be byte-equal (invocation_time necessarily differs and is excluded from
the comparison; it identifies the replay as a NEW verification event per
frozen R-23). Divergence in any compared field = §24.8 failure. Scoring
inputs (per-gate dispositions, seam recall, mutation detection) are computed
from the CLWR set exactly as bound in `scoring-constants.json`.
