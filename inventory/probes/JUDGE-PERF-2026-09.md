# JUDGE PERF — the warranty grade, exact and in no order (2026-09-27)

**The problem, reproduced.** One claim, one answer, and a running time that
depended only on `PYTHONHASHSEED`. A studio table with one unverified number
`x ∈ [0,50]` and the claim `(x <= 1) ^ (x <= 2) ^ … ^ (x <= 12)`, run through
`zfl.run` (with `zfl.validate` stubbed, because the cap now refuses the claim):

| PYTHONHASHSEED | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| CPU s (before) | 0.41 | **16.20** | 0.22 | **16.25** | 0.80 | 0.30 | 0.25 | 2.07 |

Every seed gave OPEN / F / until-verification. Profile of seed 2: 66 of 66.5 s
in `zverify.hereditary_bit`, 1,279,525 refinements walked; seed 3: 0.05 s there.

**Result.** The same answers, now computed without the walk:

* **1,000,000 seeded claims, identical whole output, old vs new** (see §3);
* the 12-comparison claim: **0.027–0.038 s on every seed 1..50** (before:
  __OLD_S1__);
* no shape found where the new code is slower; on 400 random 10-atom formulas
  with repeated atoms its worst judge call is 0.045 s, where the old code took
  up to 7.3 s on the same formulas;
* the regression: __RUNALL__.

`zverify.py` is the only core file changed. No verdict, grade, disposition,
`joint` or `why` moved anywhere in the space tested.

---

## 1. The cause

**What is searched.** Every judge call computes the warranty grade
(`zverify.grade`): the verdict `v = ev(φ)` under the greedy reading, then

* `hereditary_bit`: is `ev(φ, r) = v` for EVERY partial refinement `r` of the
  marking (each mark stays a mark, or becomes T, or F) — 3ⁿ refinements;
* `stable_bit`: the same over every completion — 2ⁿ worlds.

Both first try cheap witnesses (all marks T, all marks F) and two theorems
(`no_gift`, `f_locked`); when those are silent they end in
`all(ztl_eval(φ, r) == v for r in refinements(marking))`. A studio claim does not
ask once: `judge_sheet_claim` calls `ztljudge.judge` once plus once per
comparison atom (the bearing probe), and each `judge` asks `grade` in
`_happened` and twice per unverified atom in `_joint → _moves`. For the
12-comparison claim that is **143 grade calls**.

**Why order matters.** `all` stops at the first refinement that disagrees with
the verdict. `refinements` walks `itertools.product(("M","T","F"), repeat=n)`
with the marks in the order of the marking dict, and that dict is built in
`ztljudge._full` from `_atoms(φ)` — a Python `set` of atom names, whose
iteration order is the string hash, i.e. `PYTHONHASHSEED`. The last mark in
that order varies fastest.

On the xor chain the position of the witness is extreme. A Z leaf makes its own
`⊕` node F (`Z ⊕ y = F` for every y), and the chain then continues classically
from that F. So the claim reads T only when the leaves AFTER the last Z are all
classical with an odd number of T. When `nc12`'s mark varies fastest, the
second refinement (`nc12 := T`, all else marked) is a witness. When it varies
slowest, the walk passes every refinement that keeps `nc12` a mark — 3¹¹ of
them — first. Instrumented (`hereditary_bit` calls, 143 per run): seed 3 walks
a handful of refinements per call, seed 2 walks 1.28 M in total.

**The worst case.** When the verdict IS hereditary (or sound) there is no
witness, and every order pays the full 3ⁿ (2ⁿ) — on every one of the ~n·2
grade calls. The hash seed only decides how much of that worst case a
non-hereditary claim happens to pay.

## 2. The change

`zverify._only(φ, fixed, free, v)` answers the walk's question — "is φ equal to
v under every choice of the free atoms?" — exactly, without an order:

1. **Compositional values.** A node's value is its connective applied to its
   children's values, and only a leaf can be Z (`ztl.ev`). If every free atom
   occurs ONCE, the two subtrees of a node read disjoint atoms, so the set of
   values the node takes over all readings is exactly
   `{op(x, y) : x ∈ left set, y ∈ right set}` — one pass (`_reach`).
2. **Shannon only where needed.** An atom that occurs more than once is split
   on — each of its choices substituted in turn — and the residue is decided
   the same way (`_values`). The atom split first is the most frequent, ties by
   name: a fixed rule, no hash.
3. **Constant folding.** After a substitution, a node whose value no longer
   depends on its free side is replaced by that value (`_fold`; e.g. `F ∧ ·`,
   `Z ⊕ ·`). Sound because the folded side can only read T, F or Z.
4. **Memo and early exit.** Residues are memoised within a call; the split
   stops as soon as a value other than `v` appears.

`hereditary_bit` asks it with each mark free over (Z, T, F) — `ztl_eval` reads a
mark as Z — and `stable_bit` with every non-T/F atom free over (T, F), exactly
the readings `refinements` and `worlds` enumerate. Everything before the old
walk is untouched: the theorems, the cheap witnesses, the budget (a budget still
refuses at the same point, so `check_budget_never_lies` is unaffected). The
walk stays, as the definition and as the fallback: `_only` returns None when an
atom has no value (the walk then raises exactly as before) and on
`RecursionError` (the walk, which never recurses, answers).

The worst case is still exponential — in the number of marked atoms that occur
MORE THAN ONCE and survive folding — but it is fixed, not a lottery, and on
every shape tried it is at or below the old best seed.

## 3. Equivalence: 1,000,000 claims, whole output

`inventory/probes/judge_equiv.py` prints one sha1 per claim of the judge's
ENTIRE output (keys sorted). Old = `origin/master` @ `99f8592`, new = this branch
@ `f38853b`, both run with `PYTHONHASHSEED=0`, in 25,000-claim chunks:

| stream | claims | what is compared | differing |
|---|---|---|---|
| `prop` 0..799,999 | 800,000 | `ztljudge.judge(text, marking)`: verdict, grade, disposition, why, unverified, absent, pending, lazy, joint, forgone | __DIFF_PROP__ |
| `doc` 0..199,999 | 200,000 | `zfl.run(doc)`: the whole report (numeric disposition, verdict, grade, next_check, …) | __DIFF_DOC__ |
| **total** | **1,000,000** | | __DIFF_TOTAL__ |

`prop`: a formula over 1–10 atoms (the studio cap), connectives
`& | ^ -> = ~`, depth 1–6, constants T/F/Z, a random marking over T/F/Z/E with
atoms left out (read as Z). `doc`: 1–3 numeric names with values, statuses and
scales (int / decimal2 / frac3 / exact), 1–8 comparisons joined by connectives,
run through the real validator and cap. Claim `i` of stream `K` is
`random.Random(f"{K}:{i}")`.

Also: `test_judge_perf.py` compares new against the walk IN-PROCESS (`_only`
switched off) on 6,000 `grade` calls with budgets and 1,500 judge outputs, and
a direct check of `_only` against `refinements`/`worlds` on 20,000 pairs gave
0 divergences.

## 4. Timing over PYTHONHASHSEED 1..50

`python3 inventory/probes/judge_perf_timing.py --tree TREE --seeds 1-50`: one
fresh interpreter per seed, CPU seconds of the judge call alone. Measured while
the equivalence run occupied the other cores (CPU time, not wall; the old
numbers are, if anything, flattered by less cache contention on no seed).

__TIMING__

Shapes: S1 the 12-comparison studio claim above (validate stubbed); S2 the
same with 9 comparisons (the most the cap admits, real `zfl.run`); S3
`a0 ^ … ^ a9`; S4 `a0 & … & a9`; S5 `(a0 ^ … ^ a9) & (~a0 | … | ~a9)` (every
atom twice); S6 `(a0 & ~a0) & …` (F hereditary: no witness, the full walk);
S7 a ring of ten equivalences under implication (every atom twice). All
unverified.

## 5. Regression

__RUNALL_DETAIL__

## Commands

```sh
python3 test_judge_perf.py                                   # the stand, ~10 s
python3 inventory/probes/judge_perf_timing.py --tree . --seeds 1-50
python3 inventory/probes/judge_perf_timing.py --tree OLD --seeds 1-50   # OLD = a worktree of 99f8592
for s in $(seq 0 25000 775000); do
  PYTHONHASHSEED=0 python3 inventory/probes/judge_equiv.py --tree T --kind prop --start $s --n 25000
done > T_prop.txt                                            # T = OLD and NEW
for s in $(seq 0 25000 175000); do
  PYTHONHASHSEED=0 python3 inventory/probes/judge_equiv.py --tree T --kind doc --start $s --n 25000
done > T_doc.txt
python3 inventory/probes/judge_equiv.py --compare OLD_prop.txt NEW_prop.txt   # and _doc
python3 run_all.py --no-lean
```
