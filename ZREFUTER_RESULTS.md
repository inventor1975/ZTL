# zrefuter — the trust spectrum is a closed form

`zrefuter.py` sorts every hypothesis (formula) by its behaviour over
`{T,F,Z}` (decidable → guaranteed) into four buckets:

- **VALID** — `T` under **every** assignment, including any unverified (`Z`). Robust.
- **FRAGILE** — `T` under all `{T,F}`, but `F` under some `{T,F,Z}`. A classical
  tautology that breaks when an input is unverified — the
  *Strong-Law-of-Small-Numbers* class.
- **INVALID** — `F` under some `{T,F}`. Not a law.
- **CONTRADICTION** — `F` everywhere.

## The result — a closed form (no enumeration, any n)

We expected mountains of machine work. Instead the whole distribution is a
**closed form.** A `{T,F}`-output function over `n` atoms is fixed by its value
on each of the `3^n` cells; the `2^n` all-classical cells decide classical
validity, and the remaining `z = 3^n − 2^n` cells (those touching a `Z`) decide
fragility. Hence, over the external clone (all `{T,F,Z}^n → {T,F}` functions,
plus the `n` projections):

| bucket | count |
|---|---|
| **VALID** | `1`  (only ⊤, the constant true) |
| **CONTRADICTION** | `1`  (only ⊥) |
| **FRAGILE** | `2^(3^n − 2^n) − 1` |
| **INVALID** | `2^(3^n) − 2^(3^n − 2^n) − 1`  (+ the `n` projections) |

Checked against the exhaustively-measured `n = 2`: FRAGILE `31`, INVALID `481`
— exact.

### Census (VALID = CONTRADICTION = 1 for every n)

| n | FRAGILE = 2^(3^n−2^n) − 1 | INVALID |
|--:|---|---|
| 2 | 31 | 481 |
| 3 | 524 287 | 133 693 442 |
| 4 | 36 893 488 147 419 103 231 | 2 417 814 745 741 110 930 309 |
| 5 | 2^211 − 1 | 2^243 − 2^211 − 1 |
| 6 | 2^665 − 1 | 2^729 − 2^665 − 1 |
| 8 | 2^6305 − 1 | 2^6561 − 2^6305 − 1 |
| 12 | 2^527345 − 1 | 2^531441 − 2^527345 − 1 |
| 20 | 2^3485735825 − 1 | 2^3486784401 − 2^3485735825 − 1 |

The fragile class dwarfs everything as `n` grows; but VALID stays **exactly 1**.

## What it means

**No contingent law is robust under full ignorance — only the constant truth.**
Over `{T,F,Z}` the single unconditionally-VALID function is `⊤` itself
(`not(xor(a,a))`); every non-trivial law either fails classically (INVALID) or
holds classically yet breaks once an input is left unverified (FRAGILE). This
is *"truth is never granted on credit"* stated as a theorem about the whole
spectrum — the machine analogue of the Strong Law of Small Numbers (a claim can
survive every check you make and die on the one you didn't).

## Example fragile formulas (enumerated, `n = 2`)

    imp(not(a),imp(b,b))     kill a=F, b=Z     (sneaky, min 1 verified)
    imp(and(a,a),imp(b,b))   kill a=T, b=Z     (sneaky, min 1 verified)
    imp(imp(a,a),imp(b,b))   kill a=T, b=Z     (sneaky, min 1 verified)

"sneaky" = survives full ignorance (T at all-`Z`), yet a verified combination
breaks it — the `min_verified_to_break` records how deep you must check.

## Reproduce

    python3 zrefuter.py --max-atoms 20                 # census 2..20, instant
    python3 zrefuter.py --ex-cap 6561 --ex-budget 300 --cores 30   # more example formulas
    tail -f zrefuter_runs/progress.log                 # watch a run

The census is instant at any depth; only exhibiting example *formulas* costs
compute, guarded by a wall-clock budget (heavier work → a separate deferred
report). Run dumps live in `zrefuter_runs/` (git-ignored).
