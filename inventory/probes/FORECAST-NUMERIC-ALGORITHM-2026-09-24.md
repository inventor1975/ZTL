# FORECAST — does the numeric floor's ALGORITHM issue exactly its SEMANTICS' verdicts?

Frozen 2026-09-24, before any measurement and before any proof line.
Course approved by the curator the same day ("да на курс").

## The question

`lean/ZNum.lean` and `lean/ZNumCoherent.lean` prove what a numeric verdict
MEANS: reading sets, heredity under narrowing, coherent readings finer than
sample readings. They do not prove that the algorithm the studio actually runs
issues those verdicts. The algorithm is `znum._ev` (the coherent linear
fragment `c + Σ k·x`, else plain interval arithmetic) plus `znum.compare`
(the bounds of EACH SIDE, compared). Two properties per comparison kind,
against the default coherent semantics (`sample=False`: one value per name):

* **SOUND** — every T/F the algorithm issues is forced under the semantics.
* **COMPLETE** — every verdict the semantics forces is issued, not left Z.

## Predictions (read from the code, not run)

* **P1 — SOUND everywhere** on `+ − ×`, `÷` by an interval without 0, and
  `sqrt`: no false T/F. What would falsify it: one (claim, quantities) where
  the algorithm says T or F and some coherent reading disagrees. This is the
  one that matters most — a violation is a lie in the public studio.
* **P2 — COMPLETE on the linear fragment when every name sits on ONE side**,
  continuous quantities: `le`, `lt`, `eq` exact.
* **P3 — INCOMPLETE ACROSS SIDES.** `compare` bounds each side separately, so
  a name occurring on both sides loses co-reference. Instance:
  `x <= x + 1`, `x ∈ [0, 10]` → algorithm Z, semantics T. Expected to be the
  largest source of misses on claims that repeat a name across sides.
* **P4 — INCOMPLETE on nonlinear coherent expressions** (the dependency
  problem): `x*x - x <= 0`, `x ∈ [0, 1]` → algorithm Z, semantics T.
* **P5 — INCOMPLETE on integer lattices with a non-unit coefficient:**
  `2*x = 5`, `x` int in `[1, 3]` → algorithm Z (the lattice step is tracked
  as 1, and 5 sits on it), semantics F (readings are 2, 4, 6).
* **P6 — `sample=True` quantities, continuous, `+ − ×`: COMPLETE for `le`
  and `lt`** (hull endpoints are attained and the image is connected).

What would surprise me: any P1 violation; P3 failing, i.e. some layer
compensating across sides that I did not find by reading.

## How it will be measured, then proved

Brute force on small integer and rational grids: enumerate the coherent
readings (one value per name), compute the forced verdict, set it against
`znum.compare`. Count SOUND violations (predicted 0) and COMPLETENESS misses
per kind and per fragment. Then Lean, on the empty axiom list: soundness of
the interval evaluator against the coherent semantics; completeness where P2
and P6 predict it; P3–P5 each as a kernel-checked counterexample.
