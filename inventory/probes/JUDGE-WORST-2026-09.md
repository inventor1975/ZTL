# JUDGE WORST — the judge's worst cases after the 2026-09-27 speed-up (2026-09-27)

**Question.** The public cap (`zfl.validate`: 10 atoms, 9 with any comparison)
was set for the OLD cost of the warranty grade. After `zverify._only` (PR #2),
how far can it go so that one request stays under **0.5 s of one core**?

**Answer: the atom count is no longer what decides it.** The search found four
costs, and three of them are not bounded by any atom cap:

| | component | what it grows with | worst measured | bounded by the atom cap? |
|---|---|---|---|---|
| **W1** | `ztljudge._lazy` evaluates both children of `->` twice | 2^(nested `->`) | **63.7 s**: 22 nested `->` over ONE atom, 155 chars, real `zfl.run` | **no** — atom count 1 |
| **W2** | `zfl.what_to_check` (the reverse pass): 3 × Σ C(u,k)·2^k whole judges | u = unverified inputs (≤ 6) × claim length | **30.7 s** at u = 6, 2000 chars; **8.0 s** at 10 atoms, 308 chars | **no** — u ≤ 6 of any atom count |
| **W3** | the epoch floor: 2 judges per declared `expires_on` event | events (rows are uncapped) | **76.7 s**: 800 events, 126 KB | **no** |
| **W4** | `zverify._only`: Shannon splits on every repeated mark | repeated marked atoms × claim length | **64 s**: 16 atoms, each 13–14 times, 1753 chars (judge alone) | yes — 16 is above today's cap |

W2 is the "≈1 s at 10 atoms on both old and new code" the task asked to
identify: it lives outside the judge proper, in the reverse pass that `zfl.run`
adds whenever a claim has 1–6 unverified inputs, and it calls the whole judge
~1,400 times. W1 is new: an exponential that no cap in the validator touches —
**a 141-character claim over one atom passes the validator and costs 15.6 s**.

No verdict was found wrong on the way. Core files and the cap are unchanged;
the fixes below are proposals.

---

## 1. W1 — `_lazy` doubles its work per nested implication

`ztljudge._lazy` (the lazy register and the receipt), line 292, evaluates both
children of every binary node; then the `imp` branch, line 306, re-reads the node
as `~a | b` and evaluates both children again:

```python
(a, la), (b, lb) = _lazy(phi[1], m), _lazy(phi[2], m)      # line 292
...
if op == "imp":
    return _lazy(("or", ("not", phi[1]), phi[2]), m)       # line 306: again
```

Each nested `->` doubles the work beneath it. It has been there since the file
was written (old and new code alike); the grade speed-up only made it visible.
`python3 inventory/probes/judge_worst.py impdepth --budget 120`:

| nested `->` over one atom | chars | judge as-is | **zfl.run as-is (real, cap in force)** | judge, fixed | zfl.run, fixed |
|---|---|---|---|---|---|
| 12 | 85 | 0.005 | 0.059 | 0.004 | 0.000 |
| 14 | 99 | 0.022 | 0.265 | 0.004 | 0.000 |
| 16 | 113 | 0.114 | **0.951** | 0.004 | 0.000 |
| 18 | 127 | 0.399 | **4.413** | 0.000 | 0.004 |
| 20 | 141 | 1.627 | **15.559** | 0.000 | 0.004 |
| 22 | 155 | 6.993 | **63.731** | 0.000 | 0.004 |

(`zfl.run` costs ~10× `judge` here because W2's reverse pass calls the judge
again for the one unverified input.)

**Proposed fix (not applied):** compute the `imp` case from the values already in
hand — `a := ~a`, then the `or` case. `judge_worst.lazy_fixed` is that function;
it equals `ztljudge._lazy` on 100,000 random formulas (value and label) and on
20,000 more in the stand. Every "with the fix" number below uses it as an
in-process stand-in (`--fix-lazy`); it is never written into the core here.

## 2. W2 — the reverse pass (`what_to_check`) is the "~1 s"

`zfl.run` → `what_to_check` → `zbackward.backward` for three targets (EARNED,
REFUTED, SETTLED); each visits every set S of ≤ 4 unverified inputs and every
T/F filling of S, and for each filling runs the WHOLE judge (`_disposition` →
`judge`, with its grade and its `_joint` probes). The count depends only on u,
the unverified inputs (refused above `BACKWARD_CAP = 6`):

| u | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| judge calls, 3 × Σ_{k≤4} C(u,k)·2^k | 6 | 24 | 78 | 240 | 630 | 1,416 |

Profiled (grid claim, 10 atoms, 4 unverified and 4 defined rows — u = 6 once
the definitions resolve): 1,419 judge calls, 6,555 grades, 44,923
evaluations — `what_to_check` is 18.55 of 18.56 s under the profiler. The three
targets recompute the SAME fillings; memoising the disposition per filling would
cut the count by 3 exactly.

Measured, `zfl.run` worst of 2 per cell, 10 atoms, u unverified and the rest
verified/refused, balanced claims, WITH the W1 fix
(`judge_worst.py lenscan --fix-lazy --variants 2 --budget 60`):

| u \ chars | 100 | 250 | 500 | 1000 | 2000 | 4000 |
|---|---|---|---|---|---|---|
| 1 | 0.002 | 0.006 | 0.010 | 0.016 | 0.032 | 0.064 |
| 2 | 0.008 | 0.012 | 0.024 | 0.048 | 0.096 | 0.176 |
| 3 | 0.024 | 0.059 | 0.084 | 0.180 | 0.298 | **0.770** |
| 4 | 0.068 | 0.140 | 0.240 | **0.655** | **1.282** | **1.989** |
| 5 | 0.224 | **0.556** | **1.189** | **1.761** | **5.850** | **9.018** |
| 6 | **0.798** | **0.976** | **3.180** | **6.031** | **10.968** | **23.425** |

The structured sweep (§4) shows the same at every atom count: with exactly 6
unverified inputs, `zfl.run` costs 1.0–5.2 s from 10 to 24 atoms even with W1
fixed. The worst found at 10 atoms, verbatim (pinned as W2 in the stand):

```
((((((((((((((((((((a6 <-> a7) | (a0 <-> a3)) & (a1 <-> a2)) & (a5 <-> a6)) | (a4 ^ a7))
 -> (a7 <-> a0)) | (a7 <-> a8)) | (a8 ^ a9)) -> (a2 <-> a5)) -> (a5 <-> a8)) -> (a1 <-> a4))
 -> (a8 ^ a1)) & (a9 ^ a2)) -> (a2 <-> a3)) -> (a0 <-> a1)) -> (a9 ^ a0)) | (a4 ^ a5))
 -> (a3 ^ a6)) & (a6 ^ a9)) | (a3 <-> a4))
rows: a0 a1 a4 a6 a8 a9 unverified; a2 a7 verified; a3 a5 refuted
```

`zfl.run`: **7.97 s** as-is, **2.81 s** with W1 fixed (the claim has 9 `->`).

## 3. W3 — the epoch floor: two judges per declared event

For every distinct `expires_on` event, `zfl.run` judges the claim before and
after the crossing. Rows are not capped, so events are not; the "before" judge
is the same for every event, and when the expiring row is not read by the claim,
"after" is the same too. `judge_worst.py epoch --budget 200` (a 10-atom grid
claim, all unverified; each event on a verified row the claim never reads):

| events | body | zfl.run (real) |
|---|---|---|
| 0 | 0 KB | 0.04 s |
| 10 | 2 KB | **0.75 s** |
| 50 | 8 KB | **3.50 s** |
| 200 | 32 KB | **15.27 s** |
| 800 | 126 KB | **76.74 s** |

About 0.075 s per event: **6 events** is the most under 0.5 s. Profile (200
events): 401 judge calls, each dominated by `_joint` → `_moves` (2 grades per
unverified atom).

## 4. The judge proper, and W4 — `_only`'s own tail

With W2 and W3 out of the way (every atom unverified, so u > 6 and the reverse
pass is refused; no events), what remains is `judge` itself: the grade (now
`_only`) and `_joint`, which asks for 2 grades per unverified atom.

**Structured families** — `judge_worst.py shapes --fix-lazy --sizes
10,12,14,16,20,24 --variants 4 --budget 20` (worst of 4 per cell, seconds; the
`judge` column, all atoms unverified):

| atoms | random | xor/↔ cycle | each atom 2–4× | grid (each 3–4×) | nested `->` | long chain ~4000 ch | long balanced ~4000 ch |
|---|---|---|---|---|---|---|---|
| 10 | 0.023 | 0.020 | 0.004 | 0.032 | 0.000 | refused¹ | 0.140 |
| 12 | 0.004 | 0.056 | 0.020 | 0.060 | 0.000 | refused¹ | 0.435 |
| 14 | 0.004 | 0.040 | 0.027 | 0.052 | 0.000 | refused¹ | 0.305 |
| 16 | 0.028 | 0.084 | 0.020 | 0.078 | 0.004 | refused¹ | 0.251 |
| 20 | 0.028 | 0.096 | 0.032 | 0.121 | 0.000 | 0.124 | **2.404** |
| 24 | 0.058 | 0.092 | 0.036 | 0.201 | 0.000 | 0.382 | **0.762** |

¹ a left-nested chain that long is refused by the parser (`RecursionError` →
`E_UNREADABLE`), in 0.004 s — a refusal, not a cost.

The shapes built to defeat folding (cycles, grids, repeats) stay under 0.21 s
up to 24 atoms when the claim is short. Hill-climbing from the slowest (120
mutations each, `judge_worst.py climb --fix-lazy --family F --n N`): grid at 10
atoms → 0.056 s, at 12 → 0.136 s. **The cost is in the LENGTH**: long balanced
claims climb to 0.72 s (judge) / 0.90 s (run) at 10 atoms and 2.0 s / 1.66 s at 12.

**Atoms × length**, the judge alone, worst over 20 variants per cell
(`judge_worst.py judgescan --fix-lazy --ns 8,10,12,14 --lengths 500,1000,2000,4000
--variants 20 --budget 30`):

| atoms \ chars | 500 | 1000 | 2000 | 4000 |
|---|---|---|---|---|
| 8 | 0.052 | 0.083 | 0.204 | 0.488 |
| 10 | 0.064 | 0.156 | **0.175** | 0.411 (climbed: 0.72) |
| 12 | 0.100 | **0.734** | **0.554** | **0.866** (climbed: 2.0) |
| 14 | 0.166 | **0.783** | 0.303 | **1.381** |

And the one extreme case, 6 variants at 16 atoms and 2000 characters
(`judge_worst.py judgescan --fix-lazy --ns 16 --lengths 2000 --variants 6`):
five seeds take 0.003–0.36 s, the sixth **64 s** — **W4**, pinned in the stand:
each of the 16 atoms occurs 13–14 times, and one grade builds 57,838 Shannon
residues of a ~200-node formula (`_values` → `_fold`: 31 of 31 s of one grade
under the profiler). This is fact (a) of the task, now with a witness. It is
above today's cap and is what a raised cap would expose; the old 3^16 walk
would have been slower still.

**Studio documents with numeric comparisons** (`judge_worst.py shapes
--fix-lazy --families numeric --sizes 9,10,12,14,16,20`; x in [0,50], every
comparison unverified; xor-joined, mixed connectives, or ONE comparison text
repeated n times, which the cap counts as 1 atom):

| comparisons | 9 | 10 | 12 | 14 | 16 | 20 |
|---|---|---|---|---|---|---|
| worst `zfl.run`, with W1 fixed | 0.056 | 0.016 | 0.040 | 0.081 | 0.148 | 0.352 |
| worst `zfl.run`, as-is (to 14) | 0.055 | 0.020 | 0.036 | 0.076 | — | — |

Numeric claims are cheap: the bearing probe costs one judge per comparison, and
with a single numeric name no reverse pass runs. The repeated-text trick
(counted as 1 atom, read as n) costs at most 0.17 s at n = 20.

## 5. Proposed caps (the decision is yours)

Target: **< 0.5 s of one core** for any request. W1 must be fixed first — with
it as-is, **no atom cap works**: 16 nested `->` over one atom already cost
0.95 s, and the only stand-in would be a cap on `->` nesting (≤ 14: 0.27 s).

With W1 fixed, the budget is set by four independent knobs, not one:

| knob | today | proposed | measured worst at the proposal | why |
|---|---|---|---|---|
| atoms (plain claim) | 10 | **10** | 0.175 s at ≤ 2000 chars (20 variants); 0.72 s climbed at ~3400 chars | 12 atoms reaches 0.73 s at 1000 chars |
| claim length | 4096 chars | **2000 chars** | see row above | at 4000 chars, 8 atoms 0.49 s, 10 atoms 0.72 s climbed |
| comparisons (numeric) | 9 | **16** | 0.148 s (20: 0.352 s) | the bearing probe is linear |
| reverse pass `BACKWARD_CAP` | 6 unverified | **2** (or 3 with ≤ 2000 chars) | 0.176 s at 4000 chars (u = 3: 0.298 s at 2000) | u = 4 is 0.65 s at 1000 chars; u = 6 is 0.8 s at 100 chars |
| expiry events per document | uncapped | **≤ 6** (or: judge "before" once, skip events the claim does not read) | ~0.45 s | 0.075 s per event |

Cheaper than caps, and exact: memoise the disposition per filling across the
three `backward` targets (÷ 3 on W2), judge "before" once per document and skip
events whose rows the claim does not read (W3 → ~0 for the measured case).

**Confidence.** High for W1 and W3 — they are analytic (2^depth; linear in
events) and measured through the real path. High that W2 is the "≈1 s" (profiled,
and the counts follow the formula). **Moderate** for the atom × length boundary:
20 variants per cell and four 120-step climbs; the 16-atom 64 s tail was 1 seed
in 6, so heavier tails at 12–14 atoms may exist beyond this search — which is
why the proposal stays at 10 atoms and cuts the length rather than raising the
cap. The numeric cap of 16 is measured on one numeric name only.

**Not searched:** claims mixing comparisons with plain atoms AND u ≤ 6 (the
reverse pass on numeric claims), defined rows beyond the random `mixed` rows
(passports of cycles over many rows), ledger chapters (`zbook`) with many
citations, and any hill-climbing on W2/W3 — both are analytic and were measured
directly instead. Timings are CPU seconds on this machine while other probes
ran (process CPU, not wall); the public server's cores may differ.

## Reproduce every number

```sh
python3 test_judge_worst.py                                          # the stand: RED 5 of 13, ~8 s
J=inventory/probes/judge_worst.py
python3 $J impdepth --budget 120                                     # W1 table
python3 $J lenscan --fix-lazy --variants 2 --budget 60               # W2 table (u x length)
python3 $J epoch --events 0,10,50,200,800 --budget 200               # W3 table
python3 $J shapes --sizes 10 --variants 3 --budget 10                # as-is, 10 atoms (W2 grid: 7.97 s)
python3 $J shapes --fix-lazy --sizes 10,12,14,16,20,24 --variants 4 --budget 20
python3 $J shapes --fix-lazy --families numeric --sizes 9,10,12,14,16,20 --variants 4 --budget 20
python3 $J shapes --families numeric --sizes 9,10,12,14 --variants 4 --budget 20
python3 $J judgescan --fix-lazy --ns 8,10,12,14 --lengths 500,1000,2000,4000 --variants 20 --budget 30
python3 $J judgescan --fix-lazy --ns 16 --lengths 2000 --variants 6 --budget 200    # W4: 64 s
for f in grid longbal; do for n in 10 12; do
  python3 $J climb --fix-lazy --family $f --n $n --mix unverified --steps 120 --budget 20
done; done
```
