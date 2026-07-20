# Leg 1 — pre-registration

Written **before** the generator was run. Committed separately from the
results so that tomorrow it is possible to tell a prediction from a
fitted reading. The whole point of a price list is that its currency
cannot be minted after the fact; the same discipline applies to us.

**Date:** 2026-07-20. **Author:** Vitaly Reznik, with Claude (Opus 4.8).

---

## What leg 1 does

PSSL (§2) arranges four logics as four resolutions of one diagonal, each
"classical logic minus exactly one structural principle". That sentence
is written as a *description*. Leg 1 reads it as a **parameter** and
turns the arrangement into a generator:

> a **ground** is what you refuse to grant;
> its **witness** is the price list of what still transports.

Four grounds — classical, intuitionistic, quantum (MO2), ZTL — are put
through **one** procedure on **one** pool, and each is asked exactly one
question: does Γ ⊨ φ. Four columns, comparable by construction rather
than by hand.

## Design decisions, settled in words first

**D1 — a ground is given by an oracle, not by a matrix.** The temptation
is one matrix for all four. The wall is IPC: it has no finite
characteristic matrix (Gödel 1932). So the generator asks each ground
`entails(Γ, φ)` and does not care how the answer is produced. No corner
is forced into another's vocabulary.

**D2 — the quantum corner declares its implication.** MO2 has no
canonical →. We take the **Sasaki hook**, already measured in this
repository (`dilemmas/quantum_ladder.py`: Sasaki MP holds, 216/216
triples). This is a declaration in the column header, not neutral
plumbing: which → you use is part of the ground.

**D3 — the price list is double: laws AND rules, for every ground.** The
central finding of ZTL is that these come apart (the rules/laws split,
the one-directional deduction theorem). A single-number column would
therefore lie. The gap between them is a measured quantity, not a
by-product.

## The prediction

**P1.** The rules/laws gap is **zero for classical and for
intuitionistic** logic — both have the deduction theorem in both
directions — and **nonzero for ZTL and for quantum**: ZTL's arrow is
one-directional (measured), and the deduction theorem fails in
orthomodular lattices.

**If P1 holds**, the family splits 2/2 along an axis PSSL does not use.
PSSL cuts by *which principle is dropped*; this would cut by *whether
the ground has a deduction theorem*. A second axis arising from
measurement rather than curation would be the first result in PSSL that
is neither borrowed nor arranged.

**If P1 fails**, that is the better outcome to have registered: it would
mean the axis is single, and PSSL's arrangement is stronger than it
claimed.

**P2 (weaker, stated for completeness).** Non-contradiction — the floor
of PSSL §3 — survives in all four columns. This is currently asserted
over four curated points; here it becomes refutable on a generated pool.

## What leg 1 does NOT establish

It does not establish that four is the number of resolutions; PSSL says
"at least four" and does not claim exhaustiveness, and neither do we. It
does not discover a new logic. The map "which principles are dropped ⟼
what remains derivable" is broadly the subject matter of abstract
algebraic logic and the lattice of subclassical consequence relations —
a populated field, named here once as a handle.

What is ours is the **operational reading**: a ground is not a position
but an **act**, and the act has a receipt. The price list is the witness
of laying a ground.
