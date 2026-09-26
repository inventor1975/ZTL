# RED TEAM — the numeric judge against its own promise (2026-09-26)

**The promise:** `znum.compare` never gives a WRONG forced verdict. T means the
claim holds under every admissible reading, and F means it fails under every one.
Z and E are never wrong, so they were not counted as errors.

**Verdict of the search: the promise is broken twice**, on the judge of
`4cc5504` (master at the time of writing):

| | where | how found | reach |
|---|---|---|---|
| **LIE-1** | `sum(...)` lattice step: `znum._linear` and `znum._ev`, the line `step = s2 if step is None or s2 is None else (...)` | random search (578 hits) | public: `compare()` and `zfl.run` |
| **LIE-2** | `znum._real_roots` skips `(m - ROOT_WIDTH/4, m)` when a bisection midpoint `m` is a root | reading the code, then a constructed claim | public, but needs critical points closer than 2.5·10⁻¹³ |

Outside these two, **no lie was found in the space described below**: 8,450,000
claims. Of the forced verdicts in the search runs, 3,320,130 were checked
exhaustively (`exact-enum`) and 503,118 exactly by lines (`exact-lines`). The
rest were checked against a finite candidate set, or against a planted reading.
"Found none" means none in that space. It does not mean none exist.

`znum.py` and every other core file are untouched. The fix is decided separately.

---

## The two lies

### LIE-1: `sum` inherits a lattice it does not have

`sum` computes the lattice step of its arguments like this:

```python
step = s2 if step is None or s2 is None else (s2 if s2 == step else None)
```

Once an argument without a lattice (`None`) has been seen, `step is None` holds,
and the NEXT argument's step is taken as the step of the whole sum. So
`sum(x, y)` with x continuous and y an integer is treated as "an integer". The
lattice-miss rule of `compare` then refutes any equality with a non-integer
point. The same line appears twice, in `_linear` (the coherent linear read) and
in `_ev` (the fallback, reached as soon as one argument is non-linear).

Minimal reproductions. Each claim is true at the stated reading and the judge says F:

```python
znum.compare("eq", ("sum", ["x", "y"]), Q(1, 2),
             {"x": qty(0, 1), "y": qty(0, 5, discrete="int")})          # F; x=1/2, y=0
znum.compare("eq", ("sum", [("mul", "x", "x"), "y"]), Q(1, 4), <same>)   # F (_ev branch)
# the order matters: sum(y, x) is Z, correctly
```

Through the public document path (`zfl.run`, `report["numeric"]["disposition"]`):

```
claim  sum(qa,qb) == 1/2
rows   qa = [0,1]            (scale empty)
       qb = [0,5]  scale int
-> REFUTED        (true at qa = 1/2, qb = 0)
```

Integer constants count as stepped arguments, so the lie also needs no second
name: `sum(qa, 1, 2) == 1/2` with `qa` decimal2 on (-∞, ∞) is REFUTED, but
`qa = -5/2` makes it true.

**Diagnosis verified, not argued.** On a scratch copy of `znum.py` (never on the
repository file), both lines were replaced by

```python
step = step if (step is not None and s2 == step) else None      # _linear (st in _ev)
```

With that change, the fragments that had produced every LIE-1 hit (`sum`,
`doc`, `p-sum`, `p-doc`, 3,000 claims each, seed 20260926) return **0 lies**.
On the unpatched code, the same seeds give 0, 1, 3 and 7 lies: `sum` had none at
this size, so the drop is 11 → 0. The `doc` fragment loses exactly one F, which
was the lie and is now Z. The
patch below is shown as the diagnosis. It is not a proposed commit.

### LIE-2: a critical point the root finder never looks at

`_ev_upoly` bounds a polynomial of degree 3–8 in one name by its ends and the
roots of its derivative, which `_real_roots` isolates by bisection. When a
midpoint `m` is itself a root, the search continues on `(l, m - ROOT_WIDTH/4]`
and `(m, h]`. **Roots in `(m - ROOT_WIDTH/4, m)` are never counted.**

The constructed claim (it is in the stand, `test_redteam_numeric.py`):

* `f'(x) = -(x - p)(x - m)(x - 1)`, with `m = 1 - 1/(7·10¹²)` and `p = m - 2·10⁻¹³`;
* box `x ∈ [0, 2m]`, continuous. The first bisection midpoint is `m`, a root,
  so `p` falls in the skipped gap. `1` is recovered exactly as the simplest
  rational of its final window;
* `f(p)` is the true maximum. The judge's maximum is `f(1) < f(p)`;
* `f(x) <= (f(p) + f(1))/2` is judged **T**, and is false at
  `x = 8749999999997/8750000000000` (= p).

Two critical points 2·10⁻¹³ apart need coefficients like these, so no claim a
person writes by hand is likely to hit this. It is still a forced verdict that
is wrong. The same skip has a second failure: when the gap step lands left of
the window's own left end (itself a root), the root count goes negative and the
recursion never ends. `f' = x(x - m)(x - 2m)` with `m = 1/(8·10¹²)` on
`[0, 2m]` raises `RecursionError` after about 113 ms. That is a refusal, not a
lie (see *Refusals* below).

---

## What was searched

The generator is seeded. A chunk's generator is
`random.Random(f"{fragment}:{seed}:{chunk}")`, and the seed is `20260926`.
Claims are `e1 REL e2` with `REL ∈ {<=, <, ==}`. Each side is an expression of
depth ≤ 3 over 1–3 names, with constants `-6..6`, `±1/2`, `1/3`, `-2/3`,
`3/4`, `-5/7`, `1/10`, `-3/2`, `5/2`, `1/100`, `7/3` (plus `1000`, `-999`,
`10⁶`, `1/1000` in `mixed`).

**Gold.** The gold comes from the semantics and imports none of znum's
evaluators. Readings of a quantity are lattice ∩ [lo, hi], and continuous means
the rationals. A name is one number across the whole claim, except a `sample`,
where every occurrence is its own variable. Arithmetic is exact
(`fractions.Fraction`). A non-square root is a rational enclosure of width
10⁻⁴⁰, and a comparison that enclosure cannot decide is left undecided, never
counted. Every forced verdict gets one label, strongest first:

* **exact-enum**: the whole finite reading set is enumerated (at most 1,500 readings).
* **exact-lines**: the claim is a polynomial of degree ≤ 2 in one name once the
  others are fixed. Every fixing of the others is enumerated (at most 400), and
  along each line the extremes and lattice or rational roots are computed
  exactly. That decides the whole box without listing it, including boxes of ±10⁹.
* **searched**: a candidate set. It covers bounds and their lattice neighbours,
  lattice points near 0, rational midpoints, random lattice points, critical
  points of every quadratic face of the box, and roots and critical points along
  coordinate lines (bracketed, refined to 2⁻⁷⁰, snapped to the lattice and to
  small denominators).

Every recorded counterexample is re-verified from the semantics before it is
counted (`--attribute`).

### Search mode: 5,830,000 claims

`python3 inventory/probes/redteam_numeric_search.py --seed 20260926 --workers 4 --out R.json`
(3,842 s wall, 4 workers), plus `--only docmin --seed 20260926 --workers 4` for the last row.

| fragment | what | claims | T | F | Z | E | refused¹ | exact-enum | exact-lines | searched | **lies** |
|---|---|---|---|---|---|---|---|---|---|---|---|
| int | int, small boxes, + − × | 900,000 | 248,157 | 466,311 | 169,449 | 16,083 | 0 | 712,156 | 2,240 | 72 | 0 |
| intref | int, 1–2 names, degree-2 polynomials (±10³…±10⁹ boxes in a third) — `_int_refine`'s territory | 700,000 | 164,069 | 344,936 | 181,936 | 9,059 | 0 | 385,097 | 68,366 | 55,542 | 0 |
| decimal | decimal1/2 | 450,000 | 141,083 | 254,008 | 46,810 | 8,099 | 0 | 394,285 | 789 | 17 | 0 |
| frac | frac 2,3,4,6,7 | 450,000 | 129,873 | 233,395 | 78,658 | 8,074 | 0 | 362,812 | 449 | 7 | 0 |
| cont | continuous | 700,000 | 200,909 | 355,935 | 143,156 | 0 | 0 | 120,772 | 296,369 | 139,703 | 0 |
| mixed | every type, pinned 25 %, ÷ and √, big constants | 500,000 | 114,949 | 203,612 | 86,095 | 95,344 | 0 | 288,019 | 17,326 | 13,216 | 0 |
| sample | every type, `sample` 50 % | 400,000 | 106,524 | 197,038 | 90,057 | 6,381 | 0 | 254,079 | 29,227 | 20,256 | 0 |
| inf | every type, infinite bounds 60 %, ÷ and √ | 350,000 | 47,494 | 76,944 | 171,885 | 43,322 | 10,355 | 73,893 | 8,076 | 42,469 | 0 |
| fine | decimal6, decimal30, frac997, frac10⁹ | 150,000 | 41,096 | 73,658 | 29,334 | 5,912 | 0 | 81,315 | 17,820 | 15,619 | 0 |
| sqrtdiv | ÷ and √ heavy | 450,000 | 92,814 | 161,650 | 100,469 | 95,067 | 0 | 226,826 | 13,825 | 13,813 | 0 |
| sum | `sum(...)` | 250,000 | 75,125 | 133,520 | 37,460 | 3,895 | 0 | 182,506 | 24,963 | 1,176 | **32** |
| upoly | one name, degree 3–8 products of `(x - r)` | 150,000 | 26,114 | 53,468 | 70,416 | 2 | 0 | 49,181 | 1,759 | 28,642 | 0 |
| units | units m, kg, m2, m/kg | 100,000 | 17,056 | 29,134 | 11,933 | 39,735 | 2,142 | 41,570 | 3,258 | 1,362 | 0 |
| edge | pinned at ±∞, empty lattices, off-lattice pins | 100,000 | 24,334 | 42,995 | 10,965 | 21,706 | 0 | 47,458 | 5,070 | 289 | 0² |
| doc | `zfl.run`, rows with scale int/decimal1/decimal2/frac3/frac4/exact, sample rows, fully parenthesised claims, `>=` `>` spellings | 120,000 | 26,474 | 55,978 | 29,004 | 8,338 | 206 | 66,846 | 9,061 | 6,545 | **23** |
| docmin | the same, claims in **minimal** parentheses (`a - b - c`, `a / b * c`) — the ZFL reader's precedence | 60,000 | 13,228 | 27,925 | 14,649 | 4,097 | 101 | 33,315 | 4,520 | 3,318 | **19** |
| **total** | | **5,830,000** | 1,469,299 | 2,710,507 | 1,272,276 | 365,114 | 12,804 | 3,320,130 | 503,118 | 342,046 | **74** |

For the document rows, T and F are the claim's disposition: EARNED or ON CREDIT
toward T counts as T, and REFUTED or ON CREDIT toward F counts as F. They are
never the per-row dispositions.

¹ *refused*: `compare()` raised an exception, or `zfl.run` returned `ok: false`.
None of these is a verdict. See *Refusals*.
² 14,512 forced verdicts in `edge` are on a claim with an **empty** reading set
(see *Vacuous verdicts*). They are not counted as lies, because no reading
refutes them.

Also measured: 0 forced verdicts at a reading where the claim is undefined
(x/0, √ of a negative), and 0 forced verdicts on mismatched units.

### Planted mode: 2,620,000 claims

`python3 inventory/probes/redteam_numeric_search.py --planted --seed 20260926 --workers 4 --out P.json`
(414 s wall)

In this mode the reading comes first. For an admissible reading `r`, let
`d = (e1 - e2)(r)` exactly and put `e2' = e2 + d`, so the claim is tight at `r`.
Each base claim then gives five claims, and `r` alone says which verdict each
one may **not** get:

* `e1 == e2'`, `e1 <= e2'` and `e1 < e2' + δ` are true at `r`, so F is a lie;
* `e1 <= e2' - δ` and `e1 < e2'` are false at `r`, so T is a lie;
* δ is one of 1, 1/2, 10⁻⁹, 10⁻³⁰.

No search is involved: the witness is known before the judge is asked. The
reading `r` is drawn from bounds, lattice neighbours, points near 0, midpoints
and random lattice points.

| fragment | claims | bases | T | F | Z | E | refused | **lies** |
|---|---|---|---|---|---|---|---|---|
| p-int | 300,000 | 60,000 | 65,408 | 47,833 | 186,759 | 0 | 0 | 0 |
| p-intref | 400,000 | 80,000 | 48,579 | 36,977 | 314,444 | 0 | 0 | 0 |
| p-decimal | 150,000 | 30,000 | 41,515 | 32,182 | 76,303 | 0 | 0 | 0 |
| p-frac | 150,000 | 30,000 | 36,386 | 27,173 | 86,441 | 0 | 0 | 0 |
| p-cont | 300,000 | 60,000 | 60,469 | 44,273 | 195,258 | 0 | 0 | 0 |
| p-mixed | 250,000 | 50,000 | 74,814 | 53,936 | 121,250 | 0 | 0 | 0 |
| p-sample | 200,000 | 40,000 | 41,436 | 30,854 | 127,710 | 0 | 0 | 0 |
| p-inf | 200,000 | 40,000 | 33,354 | 23,643 | 142,133 | 0 | 870 | 0 |
| p-sqrtdiv | 200,000 | 40,000 | 52,941 | 38,888 | 108,171 | 0 | 0 | 0 |
| p-sum | 150,000 | 30,000 | 37,451 | 28,331 | 84,218 | 0 | 0 | **257** |
| p-upoly | 50,000 | 10,000 | 6,071 | 4,696 | 39,233 | 0 | 0 | 0 |
| p-fine | 100,000 | 20,000 | 25,019 | 18,661 | 56,320 | 0 | 0 | 0 |
| p-units | 50,000 | 10,000 | 11,395 | 8,324 | 19,946 | 9,595 | 740 | 0 |
| p-doc | 60,000 | 12,000 | 14,396 | 10,703 | 34,891 | 0 | 10 | **121** |
| p-docmin | 60,000 | 12,000 | 14,050 | 10,410 | 35,530 | 0 | 10 | **126** |
| **total** | **2,620,000** | 524,000 | 563,284 | 416,884 | 1,628,607 | 9,595 | 1,630 | **504** |

### Every lie is LIE-1

`python3 inventory/probes/redteam_numeric_search.py --attribute R.json` (and the
same for `P.json` and the docmin file). The command re-verifies each recorded
witness from the semantics. It then rewrites every `sum(a, b, c)` as
`(a + b) + c`, which is the same claim with the same readings, and judges it
again. For all **578 of 578** lies (55 + 504 + 19), the witness verifies, the
lie disappears when `sum` is spelled with `+`, and a direct `compare()` gives
the same wrong verdict as the document path. None is unattributed.

LIE-2 did not appear in the random search, and was not expected to. Its
critical points sit 2·10⁻¹³ apart, and the generator's constants never produce
that. It was found by reading `_real_roots`.

---

## Refusals (exceptions on admissible input): not lies, but not E either

These claims have admissible readings and consistent units, yet the judge raises
an exception instead of returning a verdict or E. ZFL turns them into
`E_UNREADABLE`.

| exception | cause | minimal reproduction | seen |
|---|---|---|---|
| `AttributeError: 'float' object has no attribute 'numerator'` | `_rat_sqrt(INF)`: `_iv_sqrt` over an interval unbounded above | `compare("le", "x", ("sqrt","z"), {x:[0,1], z:[4,∞)})` | 10,355 (inf) + 870 (p-inf); also every one of the 206 `doc` and 101 `docmin` refusals (checked; the 20 planted-doc refusals were not classified) |
| `ValueError: E_UNIT: cannot read the unit '1/m'` | `_unit_str` writes `1/m` and `_unit_map` cannot read its own output | `(1/x)*x <= 5`, `x` in metres | 2,142 (units) + 740 (p-units) |
| `RecursionError` | `_real_roots`, the same `ROOT_WIDTH/4` step, with a negative root count | `f' = x(x-m)(x-2m)`, `m = 1/(8·10¹²)`, box `[0, 2m]` | constructed |
| `OverflowError` | `qty(INF, INF, discrete="int")`: `math.ceil(inf)` | the call itself | constructed |

`python3 inventory/probes/redteam_numeric_load.py` prints each of these.

## Vacuous verdicts: a question for review, not a lie

A continuous quantity pinned at an infinity, `qty(INF, INF)`, has **no reading**
under the stated semantics (the rationals ∩ [∞, ∞] is empty), yet it receives
forced verdicts. For example, `y <= x` with `x` pinned at +∞ is T, and `x < x`
is F. In `edge`, 14,512 forced verdicts are of this kind, and all 800 of the
recorded ones involve a quantity pinned at ±∞. No reading refutes them, so by
the task's definition they are not lies. They do contradict the corpus's own
rule that emptiness is separated as E and never quantified over. The code
comments show a deliberate extended-real reading instead
(`dilemmas/omnipotence.py`, "a quantity pinned AT +inf"). Which reading is
intended is the curator's call. `x == x` is Z here while `x < x` is F, which
suggests the extended-real reading is not applied uniformly either.

## Load: compare() calls over 50 ms

Each run timed every `compare()` call under 4 parallel workers. Claims over
50 ms were then re-timed as the median of 5 runs
(`--retime R.json --workers 4`, `--retime P.json --workers 4`):

| run | first timing > 50 ms | stay > 50 ms | > 100 ms | max |
|---|---|---|---|---|
| search | 7,324 | **6,466**: upoly 6,426, sample 40 | 41 | 145.4 ms |
| planted | 2,468 | **2,162**: p-upoly 2,135, p-sample 27 | 14 | 132.6 ms |

* **upoly**: degree 6–8 in one name, typically a product of `(x - r)` with
  small-denominator roots on a wide or infinite box. The time goes to Sturm
  sequences and bisection to `ROOT_WIDTH` in exact rationals. The worst:
  `(-2(x-1/3)(x+3/2)(x+4)(x+3/2)(x-7/3)(x+4)) <= x³`, x ∈ (-∞, 5/2], 145 ms.
* **sample**: many sample occurrences become many multilinear keys, up to
  2¹⁰ corners (e.g. 83 ms for a claim with two sample names occurring 8 times).
* Targeted probes (`redteam_numeric_load.py`): a degree-8 product with roots
  `k/7` on ±10⁶ takes **162 ms**, roots `k/997` 144 ms, roots `k/(10⁶+3)` 134 ms.
  The `RecursionError` claim takes 113 ms before it raises. `_int_refine` stays
  under its ceilings: the bilinear `x*y == 9999999967` (a prime near the 10¹⁰
  cap) takes 7.6 ms. Ten sample keys multilinear take 14.6 ms.

UPOLY_MAX_DEGREE = 8 caps the degree, but nothing caps the time of a degree-8
claim. On a public API one request costs about 0.15 s of CPU.

---

## Limits of this search (read before quoting "none found")

* **searched** claims (342,046 in search mode) were checked against a finite
  candidate set. A lie that hides in a sliver of a continuous box, like LIE-2,
  can pass it. Only `exact-enum` and `exact-lines` are proofs.
* The generator never produces expressions deeper than 3 per side, more than 3
  names, or constants outside the lists above. The `solve` path (`?` values,
  `exact` roots via `znumsolve`) was not tested. Neither was the provenance
  axis, on purpose.
* `inf` boxes were checked with finite candidates (±10³, ±10⁹, and far points
  up to 10⁴⁸ along a line), not symbolically.
* Timing is machine-dependent. The counts above are not, given the seed.

## Reproduce everything

```sh
S=/tmp/rt; mkdir -p $S
python3 test_redteam_numeric.py                        # the stand: RED, 4 of 6 checks, ~16 s
python3 inventory/probes/redteam_numeric_search.py --seed 20260926 --workers 4 --out $S/R.json
python3 inventory/probes/redteam_numeric_search.py --only docmin --seed 20260926 --workers 4 --out $S/D.json
python3 inventory/probes/redteam_numeric_search.py --planted --seed 20260926 --workers 4 --out $S/P.json
python3 inventory/probes/redteam_numeric_search.py --attribute $S/R.json   # also P.json, D.json
python3 inventory/probes/redteam_numeric_search.py --retime $S/R.json --workers 4   # also P.json
python3 inventory/probes/redteam_numeric_load.py      # targeted load + refusals
# LIE-1 diagnosis on a scratch copy (never on znum.py):
mkdir -p $S/patched && cp znum.py $S/patched/ && python3 - "$S" <<'EOF'
import sys; p = sys.argv[1] + "/patched/znum.py"; s = open(p).read()
s = s.replace("step = s2 if step is None or s2 is None else (\n                s2 if s2 == step else None)",
              "step = step if (step is not None and s2 == step) else None")
s = s.replace("step = st if step is None or st is None else (\n                st if st == step else None)",
              "step = step if (step is not None and st == step) else None")
open(p, "w").write(s)
EOF
for A in "--only sum,doc" "--planted --only p-sum,p-doc"; do
python3 -c "import sys,runpy; sys.path[:0]=['$S/patched','$PWD']; import znum; \
assert znum.__file__.startswith('$S'); \
sys.argv=['x']+'$A --n 3000 --workers 1 --seed 20260926'.split(); \
runpy.run_path('inventory/probes/redteam_numeric_search.py', run_name='__main__')"
done                                                   # 0 lies in all four
```

The stand `test_redteam_numeric.py` is **not** registered in `run_all.py`.
Registering it would change the counted claims of the paper, so that is decided
in review. It fails on this code and names each lie. Its seeded sweep (every
fragment, 250 claims each, both modes) fails on its own for any lie that cannot
be attributed to LIE-1.
