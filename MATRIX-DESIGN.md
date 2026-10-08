# Matrices on the numeric floor — linear systems with uncertain coefficients

Written 2026-10-09 before any code, on the curator's word ("матрицы для ZTL сделать надо", 01:41), for the
night's work. The occasion: an electrical circuit with toleranced parts could not be judged by the floor.
Each law of the circuit is school-level (Ohm's law U = I·R per part, a sum of currents per node), but with the
resistance R known only as an interval and the current I unknown, `I*R` is a product of two non-pinned names:
`_linear` refuses it, `_solve_linear_system` skips it, the loop narrows nothing, and the unknowns stay
(-inf, inf) — measured 2026-10-08 on a two-resistor series circuit.

## What a "matrix" is here — no new syntax

A system of EQUALITIES, written with the claim syntax that already exists, in which

* the UNKNOWNS are quantities declared `?` (an unbounded box), and every equality is LINEAR in them;
* the COEFFICIENTS (and the right-hand sides) are expressions over KNOWN quantities — pinned ones are
  constants as before; a quantity with a finite box `[lo, hi]` is a PARAMETER: its value is one number in
  the world (F1, a name is one number across the claim), not yet known exactly.

So `V - U1 == I1*R1 & U1 == I2*R2 & I1 == I2` with `R1, R2` boxes and `U1, I1, I2` unknown is a 3x3 system
A(p) x = b(p). The matrix is not written as a matrix; it is READ out of the rows, exactly as
`_solve_linear_system` already reads a matrix of constants. No grammar changes, nothing new for a model or a
person to learn — the studio and the API accept the documents they accept today.

## What it answers

For every unknown x_i: the set of values x_i takes when every parameter ranges over its box — the
generating principle on numbers: a comparison over x_i is T if forced under every reading, F if its negation
is, otherwise Z. The narrowed box of x_i carries the grounds of every quantity the system read (pinned or
parameter); a credit parameter makes the answer ride credit, and the judge's cure names it — as for every
narrowed value today.

## How — exact where it can be exact, and it says which

**Exact class (vertex-exact).** By Cramer's rule x_i = det(A_i(p)) / det(A(p)). If, for every parameter p_k,
the derivative block [dA/dp_k | db/dp_k] has rank at most one for EVERY value of the other parameters, then
det(A) and every det(A_i) are affine in p_k, so x_i is linear-fractional in p_k (Sherman-Morrison). If det(A)
keeps one strict sign over the box — and since det(A) is then multiaffine its extremes sit at the corners, so
"one strict sign at every corner" decides it exactly — x_i is monotone in each parameter and its extremes over
the box sit at CORNERS. Then the hull of the solutions at the 2^k corners IS the exact range: no enclosure,
no overestimate. Electrical networks are in this class (each part sits in one rank-one block: Ohm's law row,
or g·s·s^T in nodal form; the vertex result for DC networks is Brayton–Hoffman–Scott 1977, the bilinear
mechanism Bode 1945 — stated as prior art, not as ours). The rank condition is checked SYMBOLICALLY (the
coefficients are multilinear polynomials, the 2x2 minors of the block must vanish identically), never by
sampling.

Cost: 2^k exact solves for k parameters. Capped at PARAM_MAX_KEYS (10, the multilinear floor's cap, and the
studio's atom cap) — above it the system is left as before, unnarrowed, and the log says why.

**Outside the class** (a parameter in a block of rank two, a coefficient non-multilinear, det(A) changing
sign or vanishing at a corner, more parameters than the cap): nothing is narrowed and the log says which
condition failed. A verified OUTER enclosure for that case (Rump's parametric residual iteration, in exact
rational arithmetic) is the next stage — sound but possibly wide — and is NOT claimed until built and stood.

**When it runs at all.** Only when some parameter MULTIPLIES an unknown (sits in A). A parameter only on
the right-hand side (x + y == 10, y a box) is already read by the existing hull narrowing, and that path is
kept word for word — the first build caught exactly this: it intercepted the old case, same box, different
log line.

**Square and uniquely solvable — or refused.** The equalities linear in the unknowns form the system. It is
solved only if their number equals the number of unknowns and they are independent at the box's midpoint
(then det(A) at every corner decides the rest). An OVERDETERMINED system is refused: an extra equality that
holds at every corner need not hold inside the box (its residual is not multiaffine), and a reading where it
fails has no solution. A singular corner or a sign change of det(A) is refused for the same reason.

**A fork left to the curator (not decided tonight).** The narrowed unknowns are exact boxes, but the
equalities that defined them are then judged like any comparison — reading the unknown's box and the
parameters' boxes APART — so they come back Z, and a claim "laws & requirement" stays OPEN even when every
requirement atom is T. This is the floor's existing semantics (`(x + y == 10) & (x <= 9)` with y in [1, 2]
is OPEN today, measured), so it is kept. Discharging the defining equalities (they hold by construction at
every reading) would change that old case too; it is the curator's call.

## What it does NOT do (say it before it is asked)

* Parameters are boxes of the CONTINUOUS reals. A typed parameter (int, decimal) is read as its box here; the
  lattice is not enumerated (it would only shrink the range — sound, possibly wider than the lattice truth).
* `sample` quantities are never parameters of a system (each occurrence is its own act).
* Inequalities are not part of the system; they are judged on the narrowed boxes as every comparison is.
* Correlation between an unknown and a parameter in a LATER comparison is lost (x*R <= c reads x's box and
  R's box separately) — sound, possibly wide, the same honest price as everywhere on the floor.

## Checks that must exist before it ships (stand: test_param_system.py, wired into run_all.py)

1. The circuits of 2026-10-08: the series pair, a divider, the Wheatstone bridge with all parts boxed — every
   unknown's box equals the hull over all corners computed independently (exact fractions).
2. Random small networks (enumerated topologies) against brute-force corners: zero mismatches.
3. A system outside the class (a parameter in two rows of rank two, e.g. x*p + y*p == 1, x - y*p == 0 with
   p in a box... chosen so the rank condition fails) is NOT narrowed and the log names the reason.
4. Nothing changes where the floor already worked: the solver's own bench and conformance/solver_table.py
   stay green; a sheet with no parameter in a coefficient takes exactly the old path.
5. Mutation: break the rank check (always "exact") and the stand must turn red on case 3.

## Second stage, 2026-10-09 02:40 — a solved unknown remembers its dependence; the verdict is not self-fulfilling

The curator's word (02:32, "Да, делай. Только проверь потом все."), after measuring that `x + y == 10` with y in
[1, 2] is OPEN even ALONE — not because of `&`, but because the solved x is remembered as the box [8, 9] and the
judge reads x and y apart. Measuring the fix exposed an older SOUNDNESS fault it would have unmasked:

**The fault (pre-existing, live on the server).** `solve_claim` narrows every quantity by the claim's committed
comparisons — the measured ones too — and then judges the claim on the narrowed ledger. So `(y >= 3/2) & (x == 1)`
with y verified in [1, 2] came back EARNED, T: the claim's own assumption served as its evidence. A claim about a
measured quantity holds for EVERY reading of it; only an unknown `?` is a question whose answer the claim may
narrow.

**Fix 1 — the verdict reads the sheet as given.** The solver still narrows everything (that is the answer, shown
under `solved`), but the judge receives the ORIGINAL boxes of every quantity that carried a ground, and the
narrowed boxes only of the unknowns (a box (-inf, inf), `_is_ground` false).

**Fix 2 — dependence instead of a box.** When the committed equalities form a linear system in the unknowns that is
uniquely solvable at every reading of the parameters (the conditions of the first stage; parameters on the
right-hand side only are now allowed too, for this purpose), each unknown is a function of the parameters, known
exactly at every corner. Then, for the verdict:
* the system's own rows are T — they hold at every reading by construction;
* any other comparison whose unknown terms have CONSTANT coefficients, and whose parameter terms appear only when
  no parameter sits in the matrix, is read at the corners: it is then linear-fractional (or multiaffine) in each
  parameter, so its extremes are at the corners and the corner reading is exact — T if it holds at every corner,
  F if it fails at every corner (for `==`: one strict sign at every corner), Z otherwise;
* anything else keeps the separate reading (sound, possibly wide).
Readings are taken over the ORIGINAL parameter boxes (fix 1), never the narrowed ones: `(x + y == 10) &
(x <= 17/2)` with y in [1, 2] must stay OPEN (x = 9 at y = 1).
