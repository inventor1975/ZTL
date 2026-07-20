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

---

# Results — appended 2026-07-20, after the run

Pre-registration without a result record is half the discipline. This
section is appended, never edited above the line.

## Measurement

Pool of 16 formulas over p, q; contexts of size 0 and 1; the deduction
theorem in its real form, `Γ, γ ⊨ φ ⟹ Γ ⊨ γ → φ`.

| ground | laws | rules | DT gap | first witness |
|---|---:|---:|---:|---|
| classical | 27 | 14 | 0 | — |
| intuitionistic | 20 | 12 | 0 | — |
| quantum MO2 | 22 | 9 | 194 | `p, q ⊨ p` but `p ⊭ q→p` |
| ZTL | 15 | 12 | 128 | `p ⊨ p` but `⊭ p→p` |

**P1 HOLDS.** **P2 HOLDS** — non-contradiction survives in all four; the
PSSL floor is no longer four curated points but a measured invariant.

Both are now `assert`ed in the stand, not printed, and the stand runs in
`run_all.py` on every push.

## The claim ceiling, and why it is not the pool size

The counts 194 and 128 are tier C: they are artefacts of a 16-formula
pool and mean nothing in absolute terms. The **qualitative** split does
not depend on them, and was deliberately lifted out of tier C rather
than defended by a bigger sweep:

* classical — the deduction theorem is a classical theorem (cited);
* intuitionistic — standard (cited; the prover agrees on the battery);
* ZTL — `lean/ZTL.lean`, `dt_one_way`: `p ⊨ p` while `p→p = F`;
* quantum — `lean/QuantumWitness.lean`, `deduction_theorem_fails` and
  `deduction_witness`, added for this leg. Empty axiom list.

So the 2/2 split rests on two citations and two machine-checked
witnesses. Enlarging the pool would have produced bigger tier-C numbers
and no more certainty. The Python MO2 is cross-checked against the Lean
MO2 in the stand (`calibrate_against_lean`), which aborts leg 1 if they
diverge — the `bridge.py` discipline applied to new work on the day it
was written.

## Three instrument failures, recorded because they are the substance

Each pass tested a *convenient* form and read the answer as if it were
the real statement — the exact move ZTL exists to catch, performed three
times by ZTL's own authors.

1. **The curated 14-rule battery reported gap 0 for MO2.** False: the
   deduction theorem fails there on 32 of 216 triples. The classical
   canon contains no non-commuting instance. *You cannot price a ground
   with another ground's battery.* (This is the same principle the VRG
   programme states for benchmarks — do not force a system into another's
   vocabulary — arrived at here from the opposite direction.)
2. **A one-premise generated sweep is blind too.** In any ortholattice
   `a ≤ b` already gives `a →s b = ⊤`, so a single premise always
   discharges; the failure needs three independent elements.
3. **Folding the premises into one conjoined antecedent is blind to
   both.** In MO2 for the same reason; in ZTL because `∧` collapses the
   mark (`Z∧Z = F`) before `→` ever sees it.

The moral is not "we were careless". It is that **a ground's failure mode
is invisible to instruments built from another ground's habits**, and
that this is precisely why the price list has to be generated rather than
inherited. Leg 1's method had to learn its own lesson before it could
report it.

## What leg 1 did not settle

Whether the 2/2 split is one axis or a coincidence of two. Classical and
intuitionistic share the deduction theorem; quantum and ZTL lack it — but
for visibly different reasons (non-commutation vs the mark). Whether
those are one phenomenon is leg 2's question, and the identity criterion
for grounds is the tool for asking it.
