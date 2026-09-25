# FORECAST — integer refinement of numeric comparisons (frozen BEFORE the change)

**Date:** 2026-09-25. **Written by:** Claude (Opus 5.5), curator Vitaly Reznik.
**Why:** a dataset of bounded-integer claims with exact enumerated gold
(`ztl-private/datasets/bounded-int-claims`) showed `znum.compare` (commit b1ea6d6)
answers OPEN on decided integer claims: 840 of 69 696 on the narrow grid (v1),
1 364 of 69 696 on the wide grid (v2, bounds up to ±1000). It never answered wrongly (0).
A local model WITH reasoning scored 300/300 on a v1 sample, ZTL 286/300.

**Cause, MEASURED by structure before any code:** on v2 all 1 364 are integrality —
the claim is decided over the integers but open over the reals (`x == 1 - x`,
`x <= x * x` on `[0,1000]`). On v1, 16 more are the interval dependency problem
(`x * x <= x * y`), decided even over the reals.

## The change (scope, stated before writing it)

Only when `compare` would return Z, and only when every name read is an `int`-typed,
finitely bounded, non-`sample` quantity, the difference of the sides is expanded
EXACTLY to a polynomial (integer coefficients after scaling), and decided over the
integer box by exact arithmetic, never by listing the box:

1. one free name, degree <= 2 — integer extremes at the ends and the floor/ceil of the
   vertex; `==` by exact integer roots (isqrt);
2. two free names, one of them only linear with a constant coefficient
   (`k*y + h(x)`) — reduced to (1) for `<=`/`<`; `==` by residues mod k and the
   integer range of a quadratic;
3. two free names, bilinear `a*x*y + b*x + c*y + d == 0` — via
   `(a*x + c)(a*y + b) = b*c - a*d` and the divisors of that number.

Anything else keeps Z. A decided verdict is never touched (the refinement runs only on Z).

## Predictions (to be checked with the same instruments)

- **P1 (soundness):** wrong verdicts stay **0** on v1, on v2, and on `lab/numexact/measure.py`.
- **P2:** v2 abstentions on decided rows **1 364 → 0**.
- **P3:** v1 abstentions on decided rows **840 → 32** (the coupled `x*x` vs `x*y`
  inequalities stay OPEN: 16 integrality + 16 dependency).
- **P4:** `lab/numexact/measure.py` misses fall; lies stay 0.
- **P5:** `run_all.py` stays ALL GREEN; no verdict of any existing stand changes.
- **P6:** a reasoning model's advantage on v1 (300 vs 286) closes on the same 300 rows.

Out of scope, stated: two free names coupled nonlinearly (`x*x < x*y`), degree > 2,
more than two free names, non-integer lattices (`decimal`, `frac`), division, roots.
