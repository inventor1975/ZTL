# RESULT — the numeric floor's algorithm against its semantics (2026-09-24)

Forecast frozen first: `FORECAST-NUMERIC-ALGORITHM-2026-09-24.md` (commit
`3e3a532`). Measured with a lab probe (`lab/numexact/`, not in git): integer
quantities `x`, `y` on the intervals [0,1], [1,3], [-2,2], [2,2]; both sides
drawn from the 52 expressions of depth ≤ 2 over `x, y, 1, 2` with `+ − ×`;
kinds `le`, `lt`, `eq`; the coherent semantics enumerated exactly (one value
per name). 120,384 claims.

## Before the fix

| fragment | claims | exact | missed (forced, left Z) | false |
|---|---|---|---|---|
| linear, no name on both sides | 69,870 | 69,170 | 700 | 0 |
| linear, a name on both sides | 37,860 | 27,738 | **10,122** | 0 |
| nonlinear | 5,778 | 5,370 | 408 | 0 |
| nonlinear, a name on both sides | 6,876 | 5,272 | 1,604 | 0 |
| **total** | **120,384** | 107,550 | **12,834** | **0** |

Live on the studio's own path (`znumjudge.judge_sheet_claim`):
`m - m == 0` → ON CREDIT, `m == m` → OPEN; `x - x <= 1` → ON CREDIT,
`x <= x + 1` → OPEN. The same fact, two spellings, two dispositions.

## The fix (`znum.compare`, `znum._ev_linear`)

On the linear fragment the difference of the two sides is read in ONE pass,
each name counted once; outside it the old separate-bounds path runs
unchanged. And a name that cancels (`m - m`) contributes exactly 0 even when
unbounded (it was `0 * inf = nan`).

## After the fix

| fragment | missed before | missed after |
|---|---|---|
| linear, no name on both sides | 700 | 700 |
| linear, a name on both sides | 10,122 | **616** |
| nonlinear (both kinds) | 2,012 | 2,012 |
| **total** | **12,834** | **3,328** |

* Old against new on all 120,384 claims: 110,878 unchanged, 9,506 raised
  from Z to a verdict, **0 overturned**.
* False verdicts: **0** before, **0** after.
* Continuous quantities, linear claims, the exact semantics taken at the
  box's vertices (a linear form peaks at a vertex): 101,184 claims, **all
  exact** after the fix.
* Unbounded `m`: `m == m` and `m - m == 0` both T; `m == m` no longer
  reported as riding on `m`'s bounds.

## The first version of the fix was wrong — the full regression caught it

The first version passed every measurement above and every quick check, and
the full `run_all.py` came back RED on `dilemmas/omnipotence.py`: the stone
against an unlimited capacity (`capacity=inf`, a quantity pinned AT +inf,
against an unbounded `stone`) went from REFUTED to OPEN. The joint lower
bound summed `+inf + (-inf) = nan`. I had argued that a lower bound can only
collect `-inf` or finite ends — true of every interval except one pinned at
+inf, which none of my pools contained. A claim reached by reasoning where a
measurement was available (ONBOARDING §0).

Cured twice over: a nan joint difference falls back to the separate bounds,
which still decide there; and the zero-coefficient skip applies only to
quantities with finite readings (`inf - inf` stays undefined). The stand now
carries a pool with infinities and the stone itself, and it fails on the
version without the cure.

## Scorecard of the forecast

| | predicted | measured |
|---|---|---|
| P1 sound everywhere | 0 false | 0 false on this pool (÷ and √ NOT yet measured) |
| P2 linear, one side per name, continuous: exact | exact | exact (after the fix, also across sides) |
| P3 a name on both sides loses co-reference | the largest miss | 10,122 of 12,834 — confirmed, now fixed |
| P4 nonlinear coherent: incomplete | misses | 1,604 — confirmed, NOT fixed (dependency problem) |
| P5 integer lattice, coefficient ≠ 1: incomplete | misses | the 700 + 616 left, e.g. `1 == x + x` — confirmed, NOT fixed |
| P6 samples, continuous, + − ×: complete for le/lt | complete | NOT measured |

## What is still open

Division and the root; samples on continuous quantities (P6); the lattice
gaps (P5) and the nonlinear dependency problem (P4), which stay honest Z.
Next: the kernel-checked counterpart in Lean — the joint linear reading is
exact against `ZNumCoherent`'s coherent semantics, on the empty axiom list.

Guarded by `test_joint_sides.py` (in `run_all.py`): it fails on the old
floor at its first check, `m == m is forced true`.
