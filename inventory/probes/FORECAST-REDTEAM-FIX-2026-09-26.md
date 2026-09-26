# FORECAST — fixing the two lies the cloud red team found (frozen BEFORE the change)

**Date:** 2026-09-26. **Written by:** Claude (Opus 5.5), curator Vitaly Reznik («Да»).
**Source:** PR #1, `inventory/probes/REDTEAM-NUMERIC-2026-09.md` — 8.45 M claims, two wrong
forced verdicts on 4cc5504, both reproduced independently on master before this file.

## LIE-1 — `sum` inherits a lattice it does not have (since 2026-08-11)
`znum._linear` (957adf2) and `znum._ev` (facfd96) compute the step of `sum` as
`s2 if step is None or s2 is None else (...)`: after one argument without a lattice the NEXT
argument's step is taken for the whole sum. Change: the sum keeps a step only if EVERY
argument has that same step — `step = step if (step is not None and s2 == step) else None`.

## LIE-2 — `_real_roots` skips (m − ROOT_WIDTH/4, m) when a bisection midpoint m is a root
(since c3f3514, 2026-09-24). Change: when m is a root and more roots remain in (l, m], step
left from m by halving until (m − d, m] holds only m, then solve (l, m − d]. Roots are
isolated, so the halving ends; no fixed gap is skipped.

## Predictions
- **P1:** `test_redteam_numeric.py` GREEN — all 6 checks, including LIE-1 (compare and zfl.run),
  LIE-1b (`_ev` branch) and LIE-2 (the quartic is no longer T; expected Z, the truth is
  undetermined there).
- **P2:** `sum(y, x) == 1/2` (order swapped) stays Z; `sum` of int arguments keeps step 1.
- **P3:** unchanged elsewhere: bounded-int-claims v1/v2 exact 69 696 / 69 696 (no `sum`);
  `lab/numexact/measure.py` 0 misses, 0 lies; `test_int_refine.py` GREEN.
- **P4:** blind fuzz (fuzz_int seeds 1–6): wrong 0; open-but-decided may rise by a few where a
  correct F rested on the false lattice — none expected, since a correct F never needed it.
- **P5:** `run_all.py` ALL GREEN with the red-team stand registered (159 stands + Lean).
