# FORECAST — fixing the judge's worst cases (frozen BEFORE the change)

**Date:** 2026-09-27. **Written by:** Claude (Opus 5.5), curator Vitaly Reznik («Да»).
**Source:** PR #4, `inventory/probes/JUDGE-WORST-2026-09.md`. Reproduced on master first:
nested `->` over one atom, zfl.run — 14 levels 0.48 s, 16 levels 1.92 s, 18 levels 7.63 s
(127 characters, no validation error). A live cost on the public servers.

## Exact changes (answers must not move)
- **W1** `ztljudge._lazy`: `a -> b` from the values in hand (`~a | b`), not re-evaluated.
- **W2** `zbackward.backward(..., memo)`: the three targets of `zfl.what_to_check` share one
  memo of the disposition per filling.
- **W3** the epoch floor in `zfl.run`: "before" judged once; "after" memoised on the marking of
  the atoms the claim reads (a mark foreign to the claim never matters — PR #3).

## Caps (the curator accepted the table of PR #4)
- formula length 4096 → **2000** characters;
- `BACKWARD_CAP` 6 → **3** unverified inputs for the reverse pass;
- at most **6** expiry events per document;
- plain atoms stay **10**; comparisons: the rule is set by measurement after W1–W3, the largest
  count whose worst case stays < 0.5 s (PR #4 measured 16 on one numeric name: 0.148 s);
  mixed plain + comparison claims are measured before the rule is written, not assumed.

## Predictions
- **P1** `test_judge_worst.py` GREEN (it is RED 5 of 13 on master).
- **P2** nested `->` × 22 over one atom: zfl.run < 0.05 s (was 63.7 s in PR #4).
- **P3** 800 unrelated expiry events: validation refuses above 6; the epoch floor on 6 events
  costs ≈ one judge, not 12.
- **P4** the W2 grid at 10 atoms (PR #4, verbatim): 7.97 s → below 0.5 s (÷3 memo, and u = 6 >
  the new cap of 3 refuses the reverse pass outright).
- **P5** equivalence: the judge's whole output identical old vs new on the million-claim harness
  (`judge_equiv.py`, prop + doc) wherever no cap refuses; `test_redteam_logic`, `test_int_refine`,
  `test_redteam_numeric`, `test_judge_perf` GREEN; run_all ALL GREEN.
- **P6** the catalogue: all 46 examples still validate (none near the new caps).
