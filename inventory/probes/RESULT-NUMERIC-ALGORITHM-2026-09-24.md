# RESULT — the numeric floor's algorithm against its semantics (2026-09-24)

Forecast frozen first: `FORECAST-NUMERIC-ALGORITHM-2026-09-24.md` (commit
`3e3a532`). This file records what was measured, the mistake made on the way,
and the corrected result. Nothing in it is argued without the run beside it.

## The mistake, first

The forecast took as its reference "the coherent semantics: one value per
name" and the lab enumerated ONE assignment for BOTH sides of a comparison.
That is the classical reading, not ZTL's. ZTL does not grant identity on
credit (`V.ax_xnor_ZZ : zxnor Z Z = F` — self-identity is not certified): a
name co-refers WITHIN a term (2026-08-11: `m - m` is 0), but the two sides of
a comparison are two readings. `lean/ZNumCoherent.lean` says exactly that:
`ForcedEQ m a b := ∀ x y, CReads m a x → CReads m b y → x = y`.

Against the classical reference the floor looked incomplete — 12,834 of
120,384 claims "missed", 10,122 of them `m == m`-like — and a "fix" reading
the sides together was built, measured, pushed (ZTL `ff8a852`, ztlstudio
`7d53c67`) and deployed on 2026-09-24 at 15:04. The curator caught it within
the hour: «Ну да m==m — это False ... если m не проверен». Reverted at 15:14:
the server from its 15:04 backups, the repositories by revert commits. The
9,506 verdicts the fix added were, by ZTL's own standard, truths granted on
credit.

The lesson is ONBOARDING §1.1 and §3 verbatim, read by the assistant the same
hour: "the logic refuses to identify two occurrences of the same unverified
atom"; "identity is not granted, it is exhibited".

## The corrected measurement

Same pool (integer `x`, `y` on [0,1], [1,3], [-2,2], [2,2]; both sides from the
52 expressions of depth ≤ 2 over `x, y, 1, 2` with `+ − ×`; `le`, `lt`, `eq`),
now against ZTL's semantics: each side read coherently, the sides
independently. The floor as it stands (the reverted, original algorithm):

| fragment | claims | exact | missed (forced, left Z) | unforced verdicts |
|---|---|---|---|---|
| linear | 69,870 | 69,170 | 700 | 0 |
| linear, a name on both sides | 37,860 | 37,804 | 56 | 0 |
| nonlinear | 5,778 | 5,370 | 408 | 0 |
| nonlinear, a name on both sides | 6,876 | 6,840 | 36 | 0 |
| **total** | **120,384** | 119,184 | **1,200 (1.0%)** | **0** |

* **Sound: 0 verdicts the semantics does not force.** The floor never lied.
* The misses are integer-lattice gaps inside a side (`1 == x + x`: `2x` is
  never odd; `2 == y * y`) and the interval dependency problem inside a side
  (`y - y <= y * y`). They are honest Z, and they are the open work.

## Scorecard of the forecast, corrected

| | predicted | measured against ZTL's semantics |
|---|---|---|
| P1 sound | 0 false | 0 unforced (÷ and √ NOT yet measured) |
| P2 linear exact (continuous) | exact | measured only under the classical reference — to redo |
| P3 incomplete across sides | the largest miss | **WRONG PREMISE**: across sides ZTL refuses by design |
| P4 nonlinear coherent incomplete | misses | 36 within a side (`y - y <= y * y`) |
| P5 integer lattice, coefficient ≠ 1 | misses | the bulk of the 1,200 |
| P6 samples, continuous | complete | NOT measured |

Guarded by `test_identity_not_granted.py` (in `run_all.py`): `m == m` is not
granted while `m` is unverified, `m - m == 0` is; it fails on the reverted
fix at its first check.
