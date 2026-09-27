# RED TEAM — the logic core against its own definitions (2026-09-27)

**Target:** master @ `99f8592` — `ztl.py` (tables, `ev`, `atoms`), `zmodal.py`,
`zverify.py` (hereditary / sound / grade, budgets), `ztljudge.py` (the parser,
`judge`, the lazy register, `joint`), `fixedpoint.py`, `zpassport.py`, and the
laws and numbers SPEC.md, CLASSIC-VS-ZTL.md and lean/ZTL.lean state.

**Method:** an independent oracle, `inventory/probes/redteam_logic_oracle.py`,
written from the documents and importing none of the code under test — the
tables from the generating principle (SPEC.md: T iff T under every classical
reading, Z read as both), the grades from zverify's docstrings and Lean's
`refines`, the dispositions from `judge`'s docstring, the lazy register as
strong Kleene, the passports from zpassport's docstring. Every check compares
code with oracle, seeded; the search is `redteam_logic_search.py`.

**Result: three findings — one in the CODE, two in the DOCUMENTS — and three
notes.** Outside them, **no disagreement** anywhere in the space below: the
tables, evaluation, grades, dispositions, passports, and every law and number
checked agree with their definitions.

| # | kind | what | where |
|---|---|---|---|
| **L1** | CODE | the lazy register reads the constants T and F as unverified marks | `ztljudge._lazy` |
| **L2** | DOCUMENTS vs CODE | "verdicts are always two-valued" — an atomic claim's verdict is Z | ONBOARDING §1, `ztl.py` vs `ztljudge.judge` |
| **L3** | DOCUMENTS | "the same 588 validities … the same set" — the set has 584 | CLASSIC-VS-ZTL.md, the preprint, `paper/core_logic_checks.py` |

No core file is changed; the stand `test_redteam_logic.py` fails on this code,
pinning each finding, and is not registered in `run_all.py`.

---

## Findings

### L1 — CODE: `_lazy` reads the constants T and F as marks

`ztljudge._lazy` (the lazy register and the receipt of pending grounds) starts:

```python
if isinstance(phi, str):
    v = m.get(phi, Z)
    return (v, {phi}) if v == Z else (v, set())
```

`m` is the marking of the claim's ATOMS; a constant `T`, `F` or `Z` is never in
it, so every constant reads as Z and is put on the label as a pending ground.
Strong Kleene — the register the docstring names ("Kleene's tables … Z & F is
F, Z | T is T"), and Lean's `labF`, which handles `top`/`bot` — decides these:

| claim | verdict / disposition | code: lazy, pending | strong Kleene |
|---|---|---|---|
| `F` | F / REFUTED | Z, `['F']` | F, nothing pending |
| `T \| p` | T / EARNED | Z, `['T', 'p']` | T, nothing pending |
| `F & p` (p = T) | F / REFUTED | Z, `['F']` | F, nothing pending |
| `p & F` | F / REFUTED | Z, `['F', 'p']` | F, nothing pending |

The greedy verdict, grade and disposition are right (`ev` handles constants);
the second register — "whether the matter is still running" — says a settled
matter is running, and names a constant as the ground it waits on. It reaches
the studio: `zfl.run` with the claim `x > 1 | T` reports disposition **EARNED**
with `"lazy": "Z"`. In the judge sweep, 4,045 of 100,000 claims hit it — every
one a claim containing a constant — and no claim without a constant does.

### L2 — DOCUMENTS vs CODE: an atomic claim's verdict is Z

ONBOARDING §1: *"It is a TWO-VALUED logic. Not three-valued. Verdicts are always
T or F."* `ztl.py`: *"verdicts are always two-valued"*. But `judge("p")` with `p`
unverified returns **verdict Z** (grade until-verification, disposition OPEN);
`judge("Z")` returns verdict Z, grade hereditary, disposition OPEN.

The code follows the generating principle, which bars Z from COMPOUNDS only
(SPEC: "no compound formula ever takes the value Z — Z lives only on atoms");
a bare atom is not a compound, and Lean's `evalF (.atom n) = v n` agrees. So the
sentence overstates the principle — or the judge should translate/refuse an
atomic claim. Which side moves is the curator's decision; the stand pins the
disagreement. (`judge("Z")` also lands in a case the disposition table does not
define: hereditary with a verdict that is neither T nor F; the code says OPEN.)

### L3 — DOCUMENTS: "588 … the same set" counts four formulas twice

CLASSIC-VS-ZTL.md, row *Nothing lost*: "the same **588** validities of the
depth-≤2 pool, the same set element for element"; the preprint and
`paper/core_logic_checks.py` say the same of "the depth-≤2 pool of **2926**
formulas". That pool is built as a LIST without de-duplication (`d1 + d2`, where
`d2` re-creates the 20 binary formulas over `p, q`), so 20 formulas appear
twice, four of them tautologies (`p→p`, `q→q`, `p↔p`, `q↔q`). As a set it has
**2906** formulas and **584** validities — exactly what `zledger.py` asserts
and what the card's own schedule table prints ("both atoms 584 / 584"). The
equality 588 = 588 survives (both logics count the duplicates alike); "the same
set" has 584 elements, and the card uses two numbers for one quantity.

## Notes (not findings)

* **515 of 19683** (CLASSIC-VS-ZTL.md) is produced by no code in the repository,
  although the card says every number comes from `zledger.py`. Recomputed from
  the definition (closure under ¬ ∧ ∨ → ⊕ ↔): **515** when the constant `Z` counts
  as a formula, **514** from `p, q` alone (T and F are derivable; the constant-Z
  function is not). Right, with the convention unstated.
* **Precedence is undocumented.** `ztljudge.formalize` binds `& > | > ^ > -> > =`
  and every binary operator is LEFT-associative, so `a -> b -> c` reads
  `(a → b) → c`, the reverse of the usual convention. No document states either;
  nothing contradicts it, so it is a note.
* **Terminology.** SPEC.md lists `q → (p → q)` among the fallen laws as
  "affirmation of the consequent"; the formula is the K axiom (verum ex
  quolibet) — lean/ZTL.lean calls it `k_axiom_needs_ground`. The law itself is
  right: it holds on T/F and fails on Z.

---

## What was searched (all seeded)

`python3 inventory/probes/redteam_logic_search.py --seed 20260927 --only S`,
one process per section (`--json` keeps the counts):

| section | space | checked | disagreements |
|---|---|---|---|
| tables | every cell of ¬ ∧ ∨ → ⊕ ↔ vs the principle; the strong-Kleene tables of `fixedpoint`; all 84 cells of ZTL-TABLES.txt (10 tables); the 7 anchor cells; isZ on T/F/Z | 276 + 84 + 10 | **0** |
| eval | random formulas, 1–10 atoms, depth ≤ 6, constants T/F/Z, random T/F/Z markings: `ztl.ev`, `_ev_rec`, `_ev_iter`, `zmodal.ztl_eval`, `fixedpoint.ev_reg`; `atoms`; chains of 500 / 1500 / 5000 links | 400,015 | **0** |
| exhaustive | EVERY formula up to 7 nodes over {p, q, T, F, Z} (526,285 formulas) × EVERY marking of p, q: value and grade | 2,298,513 | **0** |
| classical | `evalF_agrees` (T/F markings: ZTL = classical), `ztl_taut_is_classical` (8,318 ZTL-valid formulas, all classically valid), `not_conversely` | 200,001 | **0** |
| grade | 1–7 atoms, depth ≤ 6: `grade`, `hereditary_bit`, `stable_bit` vs the definitions; every budget 1…243 only weakens (never changes); foreign marks never matter | 200,000 | **0** |
| judge | 1–7 atoms, depth 1–6, marks T/F/Z/E: parse, verdict, grade, unverified, absent, disposition, lazy value, and the receipt (no unverified atom off `pending` moves the verdict) | 100,000 | **0** outside L1 (4,045 = L1, all with a constant) |
| joint | `joint` ("no single ground moves the verdict or grade") and `joint_sets` (the minimal moving sets) vs the definition | 3,007 (172 non-empty) | **0** |
| parse | `formalize(fully parenthesised text)` returns the AST | 200,000 | **0** |
| passport | random systems of 1–5 sentences over Tr(names) and T/F/Z: lazy lfp, kind, model count, greedy period | 50,000 | **0** |
| stipulation | `stipulation_theorem` on random systems of 1–4 sentences | 3,000 | **0** |
| laws | SPEC's 12 laws that extend to the mark (each holds on T/F/Z) and 14 that fall (each holds on T/F, fails on Z); the 14-rule battery (12 alive; dead exactly ¬¬-elimination and "tautology in the conclusion"); the one-way deduction theorem; greediness (no compound takes Z, all ≤ 5-node formulas); the depth-≤2 pool counts 584 / 379 / 212 and classes 16 → 195, all 16 split; the paradox catalogue (liar PARADOX 2, truth-teller UNDERDETERMINED period 1, carousel PARADOX 4, even cycle UNDERDETERMINED period 2, odd 3-cycle PARADOX 2); the parity law on all 126 cycle patterns n ≤ 6 | — | **0** (and L3) |
| negFree | `zverify.neg_free` vs a transcription of Lean's `negFree` / `occurs` (ContextClosure.lean) | 20,000 in the stand | **0** |

"Found none" means none in that space: formulas up to 10 atoms and depth 6
randomly, every formula up to 7 nodes exhaustively (two atoms), systems up to 5
sentences. Not covered: the propositional parser on text in MINIMAL parentheses
(its precedence is undocumented, so there is nothing to hold it to), the
zbackward `what_to_check` search, the epoch layer (`zexpire`, `ztime`), the
first-order / tableau modules, and Lean itself — Lean is not installed in this
environment, so its theorems were not rebuilt; they were used as definitions,
and their statements were checked as properties of the Python code.

## Reproduce

```sh
python3 test_redteam_logic.py                         # the stand: RED, 11 of 12 checks, ~10 s
S=inventory/probes/redteam_logic_search.py
python3 $S --seed 20260927 --only eval,classical,parse
python3 $S --seed 20260927 --only grade
python3 $S --seed 20260927 --only judge
python3 $S --seed 20260927 --only passport,laws
python3 $S --seed 20260927 --only exhaustive
python3 $S --seed 20260927 --only joint,stipulation
python3 -c "import ztljudge; print(ztljudge.judge('T | p'))"          # L1
python3 -c "import ztljudge; print(ztljudge.judge('p')['verdict'])"   # L2
python3 paper/core_logic_checks.py | grep -A1 'pool size'             # L3: 2926 / 588
python3 -c "
import sys; sys.path.insert(0, 'inventory/probes'); import redteam_logic_search as S
S.s_laws('x', 1)"                                                      # L3: 584, and 515/514
```
