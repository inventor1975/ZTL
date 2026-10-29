# The judge's API — the whole surface, on one page

Five entry points. Everything else in the corpus is a stand that rides on
these.

```python
from ztljudge  import judge                  # pure logic, marks T/F/Z
from znumjudge import (parse_quantities, judge_sheet_claim,
                       load_sheet, e_census)  # claims with numbers
from znumsolve import solve_claim            # the solver, with receipts
from zpassport import passports              # what KIND of refusal
```

## 1. A propositional claim

```python
judge('paid & delivered', {'paid': 'T', 'delivered': 'Z'})
# disposition OPEN, dirty ['delivered'], why "...verify [...]"
```

Operators: `&  |  ~  ->  ^  =`. Marks: `T`, `F`, `Z` (dirty — a parameter that is not ours: its owner may change it between two reads, so each occurrence is read on its own; verification cleans it, i.e. replaces it with a checked value).

The report carries **two registers side by side**:

| field | register | question it answers |
|---|---|---|
| `disposition`, `verdict`, `grade` | greedy | do I sign this, and how well is it held up? |
| `lazy` | Kleene | is the matter still running (`Z`) or settled? |
| `dirty` (also returned as `unverified`) | — | the dirty atoms the verdict rests on — every hole |
| `pending` | Kleene label | the holes still holding the answer up |

**Dispositions** (since 2026-10-29: seven):

| disposition | meaning |
|---|---|
| `EARNED` | T under every read of every occurrence (strong Kleene T): true whatever the dirty atoms turn out to be, even if each occurrence is read on its own |
| `EARNED IF STABLE` | not settled read by read, but T in every cleaning (every completion of the dirty atoms by T or F): true once they are verified, to either value; for a claim about the world, if each dirty atom stands for one fact at all its occurrences (between check and use; in premise and conclusion). On a formula about the mark itself the cleaning decides: `~(p = p)` (p is dirty) is `REFUTED IF STABLE`. `if_stable` names the repeated dirty atoms — enough to make every atom stable, not necessarily the fewest. Verify the dirty atoms to settle it. |
| `ON CREDIT` | T now, and the completions disagree: a verification can overturn it |
| `OPEN` | not T now, and the completions disagree: not established |
| `REFUTED IF STABLE` | the mirror of `EARNED IF STABLE`: F in every completion |
| `REFUTED` | F under every read of every occurrence (strong Kleene F) |
| `E` | unjudgeable: what the claim rests on has no subject |

`if_stable` is empty except on the two `IF STABLE` dispositions. Examples, all
atoms dirty: `p -> p` and `p | ~p` are `EARNED IF STABLE` on `['p']`;
`~(p -> p)` is `REFUTED IF STABLE`; `~~p` is `ON CREDIT`; `p` is `OPEN`; the Cogito,
`(t & (t -> i)) -> i`, is `EARNED IF STABLE` on `['i', 't']` — valid if "I"
means the same in premise and conclusion. A constant `Z` is not an atom: nothing
completes it, so its occurrences stay free reads. The judge grants (`EARNED` or
`EARNED IF STABLE`) exactly what classical evaluation over all completions
grants; `EARNED` marks the part that also holds when each occurrence is read on
its own. **Changes:** 2026-10-29 afternoon, what was `EARNED`/`REFUTED` split
into the strict word and the `IF STABLE` one; 2026-10-29 evening, `IF STABLE` is
decided by completions (see CHANGELOG).

**Field names.** The list of dirty atoms is returned under BOTH names:
`dirty` (the name from now on) and `unverified` (the older name, kept for
compatibility; it will be retired in a later release, announced in the
CHANGELOG). Read `dirty`.

**Statuses (ZFL).** The status value `unverified` is still accepted;
`dirty` is accepted too and is mapped to `unverified` internally.

`pending` is a **safe candidate list**: measured over 10806 pending cells
it never missed a load-bearing hole and named an innocent one in 1778 of
them. Fill what it names and the matter moves; probe (`bounds_bearing`)
when the exact set is needed.

## 2. A claim with numbers

```python
q, m = parse_quantities('sum=4500 earned:inv-17 RUB, '
                        'budget=[4000,5000] credit RUB')
judge_sheet_claim('sum <= budget', q, m)
# OPEN, next_check ['measure budget', 'document budget']
```

Quantity syntax — `name=` then one of `5` / `[lo,hi]` / `?` (unknown) /
`inf`, then any of these tokens in any order:

| token | meaning |
|---|---|
| `earned:ref` | the bounds have a witness, and this is it |
| `earned:a\|b` | ALTERNATIVE grounds — either one suffices; the quantity holds while at least one stands (independence is declared, never verified) |
| `earned:performed/x` | a ground with no inputs; withdrawing it raises `NotAMove` — the move is refused, not survived (nullarity is declared, never verified) |
| `credit` | bounds unwitnessed (the default) |
| `int`, `decimal2`, `frac3` | the lattice: whole numbers, hundredths, thirds |
| `RUB`, `m2`, `RUB/m2` | units, read as exponents (`m·m` = `m2`; `km` never meets `m`) |
| `sample` | each occurrence is a separate act of measurement (default: one thing in the world, so `m - m` is 0) |

Dispositions: `EARNED`, `REFUTED`, `ON CREDIT` (+ `polarity`), `OPEN`,
and **`E`** — unjudgeable, the reading set is empty, with `why` naming
the defect. Cures in `next_check`: `measure X`, `document X`,
`contest type X:int`, `verify atom`, `repair the claim: ...`.

## 3. Solving, not just checking

```python
q, m = parse_quantities('x=? int, total=10 earned:doc')
solve_claim('x + x == total', q, m)
# solved {'x': 5}, EARNED — and the provenance comes from the DERIVATION
```

Exact on the linear fragment (Gaussian elimination over rationals);
outside it, interval narrowing, and it never drops a true solution.
**Do not put a NORM through the solver** — narrowing pins the unknown to
the compliant range and the norm comes out satisfied by construction.
Compliance is measured (`judge_sheet_claim`), never derived.

## 4. A whole sheet, and who breaks it

```python
load_sheet('claims.txt')      # lines: label :: formula :: quantities
e_census(claims)              # -> unjudgeable, by_signature, pairings
```

`e_census` counts what cannot be judged and gives it an address: an empty
domain names its own quantity and charges its signature; a unit mismatch
has no single author and is recorded as a pairing, charged to nobody.
One E is a slip; a stream from one signature is a hand.

## 5. What kind of refusal is this

```python
passports({'liar': ('not', 'liar')})
# PARADOX — no classical models, period 2, refusal PERMANENT
```

Classes: `PARADOX` (0 models, incurable), `INTRINSIC` (1 model, forced),
`UNDERDETERMINED` (≥2, cured by stipulation), `INPUT` (dirty),
`DOWNSTREAM` (infected, culprits named).

**Two registers, and mixing them is the classic slip.** The passport reads
the LAZY register (Z propagates: what kind of refusal is this?); the judge
reads the GREEDY one (Z collapses: do I sign this or not?). The same cell
can be Z in one and F in the other, and that is not a contradiction.

## For humans, not for scripts

ZTLStudio at `ztl.vitalyreznik.com` runs the same cores behind a text
box. Three tabs today; the plan is one door that detects the genre and
prints verdict + warranty + refusal class + cure together — deferred
until the judge stops changing weekly, since a shop window over a moving
product is rebuilt every time.
