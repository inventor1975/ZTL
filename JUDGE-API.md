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
# disposition OPEN, unverified ['delivered'], why "...verify [...]"
```

Operators: `&  |  ~  ->  ^  =`. Marks: `T`, `F`, `Z` (unverified).

The report carries **two registers side by side**:

| field | register | question it answers |
|---|---|---|
| `disposition`, `verdict`, `grade` | greedy | do I sign this, and how well is it held up? |
| `lazy` | Kleene | is the matter still running (`Z`) or settled? |
| `unverified` | — | every hole |
| `pending` | Kleene label | the holes still holding the answer up |

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
`UNDERDETERMINED` (≥2, cured by stipulation), `INPUT` (unverified),
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
