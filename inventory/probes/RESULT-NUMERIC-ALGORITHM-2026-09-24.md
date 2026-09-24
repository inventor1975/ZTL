# RESULT — the numeric floor's algorithm against its semantics (2026-09-24)

Forecast frozen first: `FORECAST-NUMERIC-ALGORITHM-2026-09-24.md` (commit
`3e3a532`). This file records the day as it went, because the day went wrong
twice before it went right, and the record is worth more than a clean story.

## What was decided, and by whom

The curator settled the meaning of names on the numeric floor, step by step:

1. For numbers `m - m = 0`. `m - m != 0` only for a `sample`, where each
   occurrence is a separate act of measurement.
2. `==` over numbers is arithmetic, so `m == m` is true. The ZTL table
   (`Z <-> Z = F`) belongs to the logical connective, not to numbers:
   «в логике не бывает m==m, а бывает m nxor m».

So a name is ONE NUMBER across the whole claim, both sides of a comparison
included; Z is a status of a logical input, never put on a number.

## How the day went

* The judge (`znum.compare`) bounded each side of a comparison separately,
  while the solver (`znumsolve`) read the difference of the sides. Against
  one-value-per-name the judge left 12,834 of 120,384 integer claims open
  (10,122 of them `m == m`-like). A joint reading was built (`ff8a852`),
  measured, deployed — and reverted within the hour (`d3c4efd`), because the
  assistant took the curator's «m==m — это False, если m не проверен», said of
  a ZTL atom, for a statement about numbers. The decision above settled it:
  the joint reading was right for numbers.
* The audit the curator asked for then found two defects on the live
  service, independent of that question: `1/inf` was the float 0.0, which the
  floor took for an infinity (printed as -∞, and `k == 0/d` refuted for an int
  k that can be 0 — a false verdict), and ZFL could not read an interval with
  a negative bound (`[-1,1]` → E_UNREADABLE).

## The floor now (this commit)

Pool: integer `x`, `y` on [0,1], [1,3], [-2,2], [2,2]; both sides from the 52
expressions of depth ≤ 2 over `x, y, 1, 2` with `+ − ×`; `le`, `lt`, `eq`;
the decided semantics enumerated exactly (one value per name, whole claim).

| fragment | claims | exact | missed (forced, left Z) | false verdicts |
|---|---|---|---|---|
| linear | 69,870 | 69,170 | 700 | 0 |
| linear, a name on both sides | 37,860 | 37,244 | 616 | 0 |
| nonlinear | 5,778 | 5,370 | 408 | 0 |
| nonlinear, a name on both sides | 6,876 | 5,272 | 1,604 | 0 |
| **total** | **120,384** | 117,056 | **3,328 (2.8%)** | **0** |

* Old floor against new: 9,506 claims raised from Z to a verdict, **0
  overturned**. Continuous linear claims (exact semantics at the box's
  vertices): 101,184, all exact.
* The misses left are integer-lattice gaps (`1 == x + x`: `2x` is never odd)
  and the dependency problem of nonlinear terms (`x <= x * x`). They are
  honest Z, and they are the open work.
* `1/inf` is an exact zero: `k == 0/d` is Z, as it must be. `[-1,1]` reads.

Guarded by `test_numeric_names.py` (in `run_all.py`, 148 stands + Lean ALL
GREEN): it fails on the floor before the decision (`m == m`), on a floor
without the exact zero (`k == 0/d`), and on the old reader (`[-1,1]`).

## Still to do, by the same decision

Lean: `ZNumCoherent`'s `Forced*` read the sides separately — the decided
semantics needs its own definition and the algorithm's exactness against it;
`ZNumPrice` (E62) and `ZExped.mark_self_not_earned` are true of samples and
must be re-framed. The published v2.0.0 (§15; §26 R3's «m−m ≠ 0») is
corrected in the next version.
