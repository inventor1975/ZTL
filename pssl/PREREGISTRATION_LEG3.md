# Leg 3 — pre-registration

Written before the measurement ran. Same discipline as legs 1 and 2.

**Date:** 2026-07-20. **Author:** Vitaly Reznik, with Claude (Opus 4.8).

---

## The question

The curator, after PSSL v1.1.0: do the eight grounds fall apart so that
"our three" (intuitionistic, quantum, ZTL) form a monolith while the four
extras (K3, LP, weak Kleene, Ł3) flow out of classical logic?

My answer in words was that the line runs elsewhere, and that ZTL lands
on the wrong side of his: **structurally** ZTL is a three-valued matrix
over the Boolean base, exactly like the four extras — the preprint itself
concedes that its {¬,∧,∨} fragment coincides cell for cell with Bochvar's
external layer. On that reading there is one parameter space of five
matrices {K3, LP, weak Kleene, Ł3, ZTL}, and two objects of a different
species: intuitionistic logic (no finite characteristic matrix, Gödel
1932) and the ortholattice.

But that is an argument about the KIND of object. This leg measures
something else — **agreement on verdicts** — and the two need not
coincide. Being the same kind of thing does not make two logics say the
same things.

## What is measured

Distance between two grounds = the fraction of questions on which they
disagree, over a shared pool:

* **law distance** — fraction of φ with `valid₁(φ) ≠ valid₂(φ)`;
* **rule distance** — fraction of (γ, φ) with `derives₁([γ],φ) ≠ derives₂([γ],φ)`.

Both are reported. The rule distance is expected to be the informative
one: K3 and weak Kleene have **no tautologies at all**, so on laws they
agree with each other trivially and disagree with everything that has
theorems — which measures "having theorems" rather than kinship.

## Predictions

**R1 (my reframing).** The five matrices are mutually closer than any of
them is to intuitionistic logic or to the ortholattice: kind predicts
proximity.

**R2 (the alternative, which I half expect to win).** They do NOT cluster
by kind. Proximity follows what a ground DESIGNATES and what it
VALIDATES, and cuts across kinds — so ZTL could sit nearer the
ortholattice than nearer K3, despite sharing a species with K3.

**If R2 wins, R1 is refuted and so is the curator's split**, but in a way
that is more interesting than either: it would mean the family has two
independent axes — kind of object, and verdict behaviour — and that
neither is a relabelling of the other.

## Claim ceiling, in advance

A disagreement rate on a bounded pool is tier C. It cannot establish that
two grounds are close in any absolute sense; it can only rank pairs
against each other on the questions asked. Nothing here says the eight
are all the grounds, and nothing says the measured proximity is a
metric with meaning beyond this pool.

---

# Results — appended 2026-07-20

## R1 FAILS. R2 HOLDS. The refuted prediction was mine.

Rule distance, single-premise, 256 pairs over a depth-1 pool:

|  | CPC | IPC | MO2 | ZTL | K3 | LP | WK | Ł3 |
|---|---|---|---|---|---|---|---|---|
| **CPC** | — | .000 | .023 | .070 | .070 | .000 | .117 | .000 |
| **IPC** | .000 | — | .023 | .070 | .070 | .000 | .117 | .000 |
| **MO2** | .023 | .023 | — | .094 | .094 | .023 | .094 | .023 |
| **ZTL** | .070 | .070 | .094 | — | **.000** | .070 | .109 | .070 |
| **K3** | .070 | .070 | .094 | **.000** | — | .070 | .109 | .070 |
| **LP** | .000 | .000 | .023 | .070 | .070 | — | .117 | .000 |
| **WK** | .117 | .117 | .094 | .109 | .109 | .117 | — | .117 |
| **Ł3** | .000 | .000 | .023 | .070 | .070 | .000 | .117 | — |

Blocks at distance exactly 0 — identical single-premise consequence:

    {CPC, IPC, LP, Ł3}    {MO2}    {ZTL, K3}    {WK}

**Not one of these is a block of kinds.** Intuitionistic logic, which has
no finite characteristic matrix at all, sits at distance 0 from two
three-valued matrices. Weak Kleene, a matrix, is the most isolated ground
in the family. So R1 — my claim that kind predicts proximity — is
refuted, and the curator's three-versus-four split with it: **the family
has two independent axes, kind of object and verdict behaviour, and
neither is a relabelling of the other.**

## The finding neither prediction anticipated

`ZTL|K3` is **0.000 on rules and 0.089 on laws**: identical
single-premise consequence, different theorems.

That is the rules-versus-laws split of the ZTL preprint reappearing one
level up, as a property of the FAMILY rather than of one logic. Two
grounds can **transport the same and say different things** — which is
also why the law matrix must not be read as a family tree on its own. K3
and weak Kleene sit at law distance 0.000 from each other while having no
tautologies at all: that column measures "has theorems", not kinship, and
a reader shown only the law matrix would draw a false tree from it.

## Claim ceiling

Tier C throughout. A disagreement rate on a bounded pool ranks pairs
against each other on the questions asked; it is not a metric with
meaning beyond this pool, and the zero blocks are "no disagreement we
could reach", not proofs of coincidence. The one block that could be
lifted cheaply is `{ZTL, K3}`, whose single-premise agreement looks
structural rather than accidental — that would be leg 4 if it is ever
wanted.
