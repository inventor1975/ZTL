# Leg 2 — pre-registration

Written **before** anything was run, committed separately from results.
Same discipline as leg 1: a price list whose currency can be minted after
the fact is worth nothing.

**Date:** 2026-07-20. **Author:** Vitaly Reznik, with Claude (Opus 4.8).

---

## The question leg 1 left open

Leg 1 measured a 2/2 split: classical and intuitionistic have the
deduction theorem, quantum MO2 and ZTL do not. **Is that one axis or two
coincidences?** The two failures look different — non-commutation in the
lattice, the mark reaching the operator in ZTL.

## The framing, and it is native

The cycle's own R3: *apartness is earned, identity is not.* Applied to
grounds:

* "these two grounds are the same" quantifies over all formulas. Not
  performable. Identity of grounds is never earned.
* "these two grounds are apart" is one formula and one disagreement.
  Finite, checkable, cheap.

So the object of leg 2 is not an identity relation but a family of
**apartness witnesses** — the same shape as identity in `SetsOp` and
apartness of reals in `Continuum`.

## Tack 2a — the arrow control. We attack our own result first.

Leg 1's decision D2 gave the quantum corner the **Sasaki hook by
declaration**. If a different implication — Dishkant, or a relevance
arrow — restores the deduction theorem in MO2, then the quantum half of
the 2/2 split is a property of *our declaration*, not of the lattice, and
the split is partly an artefact.

This is done first, deliberately. Not because it is likely, but because
if we do not check it a referee will, and then it is their finding rather
than ours.

## Tack 2b — move along the parameter

Four is a sample, not a classification (PSSL says "at least four"). If
the parameter is real, one should be able to *walk* it. Grounds to add,
each either already in the core or a small matrix:

* **weak Kleene** — this is the cycle's own lazy register (`kand`, `kor`,
  `knot`), already machine-checked;
* **K3** (strong Kleene) and **LP** (its paraconsistent dual);
* **Ł3 (Łukasiewicz)** — the decisive one. Three-valued like ZTL, ZTL's
  nearest neighbour in the lineage (the Pykacz bridge), and it *keeps the
  involution that ZTL breaks*.

## Tack 2c — apartness witnesses

For each pair of grounds, the **minimal** formula on which their verdicts
differ. Minimality is computable and needs no interpretation. The result
is not "they differ" (leg 1's columns already show that) but a **receipt
of apartness**: this is what it costs to tell these two grounds apart.

---

## Predictions

**Q1.** The deduction-theorem failure in MO2 **survives** the change of
arrow — it is orthomodularity, not the hook. Confidence: medium. This is
exactly why it is tested first.

**Q2.** **Ł3 has the deduction theorem.** Its arrow is built for it. If
so, ZTL and Ł3 are two three-valued neighbours differing precisely on the
deduction theorem — the sharpest available localisation of what ZTL's
refusal actually costs, against the closest point outside it.

**Q3.** Weak Kleene — the lazy register — **lacks** the deduction
theorem, for ZTL's reason rather than the quantum one: the mark reaches
the operator. If so, "lacks DT" collects {ZTL, weak Kleene, quantum} and
the question "one axis or two" becomes the sharper question of what those
three share.

**If Q1 fails** it is the most valuable outcome available here: our own
leg-1 result is partly an artefact of a declaration we made, and we will
say so in the same place we said the result.

## Claim ceiling, stated in advance

Nothing in leg 2 establishes that the grounds enumerated are all the
grounds; PSSL claims "at least four" and we claim no more. The map
"principles refused ⟼ what still transports" is broadly the territory of
abstract algebraic logic and the lattice of subclassical consequence
relations — named once as a handle. What is ours is the operational
reading: a ground is an **act**, and the act has a receipt.

---

# Results — tack 2a, appended 2026-07-20

Appended below the line; nothing above it edited.

## Q1 HOLDS — and then stopped being a survey

Six implications proposed for orthomodular lattices (Kalmbach's five plus
the material one) were run against MO2. Four are usable — classical on
the Boolean sublattice and keeping modus ponens: Sasaki, Dishkant,
non-tollens, relevance. **None restores the deduction theorem.**

| arrow | classical | MP | DT | failures /216 |
|---|---|---|---|---:|
| material | yes | no | no | 32 |
| Sasaki (leg 1's declaration) | yes | yes | no | 32 |
| Dishkant | yes | yes | no | 32 |
| Kalmbach | yes | no | no | 48 |
| non-tollens | yes | yes | no | 32 |
| relevance | yes | yes | no | 40 |

So the quantum half of leg 1's 2/2 split is **not** an artefact of
decision D2. It survives its own control.

## The survey was unnecessary — the result is an impossibility

Six arrows failing is evidence. It is not the statement. The deduction
theorem

    a ≤ (b → c)  ⟺  a ∧ b ≤ c

says `b → c` must **be** the greatest element whose meet with `b` lies
below `c` — a relative pseudocomplement. A lattice possessing one for
every pair is a Heyting algebra, hence distributive. MO2 is not
(`distributivity_fails`).

**Therefore no binary operation whatever on MO2 satisfies the deduction
theorem.** Measured: 16 of 36 pairs (b,c) have a set {x : x∧b ≤ c} with
no maximum — at b = a, c = ⊥ the set is {⊥, a′, b, b′} with three
incomparable maximal elements. Machine-checked as
`no_arrow_has_deduction_theorem` in `lean/QuantumWitness.lean`, empty
axiom list, with `above_two_atoms` as the supporting fact.

This is the upgrade that matters for the claim ceiling. Leg 1 could say
"MO2 with the Sasaki hook lacks the deduction theorem". It can now say
**"MO2 cannot have one"** — and the difference is exactly the difference
between a measurement of our choices and a fact about the object.

## Corpus effect

`lean/QuantumWitness.lean` grew from 5 theorems to 11; the corpus is 344
theorems in 17 modules, all on the empty axiom list. `pssl/arrow_control.py`
asserts Q1 and the impossibility, and runs in `run_all.py` (42 stands).

## A Lean pitfall, refined

Applying an `Iff` as a function (`.1` / `.2`) is clean. Only `rw` with an
`Iff` drags `propext`. The impossibility proof uses both `.1` and `.2`
plus a `rw` by an `Eq`, and prints the empty list — which sharpens the
rule recorded earlier for the corpus.

## Still open, unchanged

Q2 (Łukasiewicz Ł3 has the deduction theorem) and Q3 (weak Kleene — the
cycle's own lazy register — lacks it, for the mark's reason rather than
the lattice's) are untouched. They are tack 2b, and they are what decides
whether the 2/2 split is one axis or two.

---

# Results — tack 2b, appended 2026-07-20

## Q2 is RETRACTED. Q3 holds.

**Q2 predicted that Łukasiewicz Ł3 has the deduction theorem. It does
not.** On a depth-1 pool Ł3 reads gap 0, and that reading was printed
before it was checked. The counterexample

    p ⊨ ¬(p→¬p)      but      ⊭ p→¬(p→¬p)      (at p = u the arrow gives u)

has depth 3; the shallow pool cannot contain it. On a depth-2 pool the
gap is 6404. **A pool is not a proof, and a zero on a pool is only the
absence of a counterexample we could reach.** This is the fourth
instrument blindness of this work and the same shape as the other three.

Q3 holds: weak Kleene — the cycle's own lazy register — lacks discharge,
gap 245130 at depth 2, first witness `p ⊨ p`.

## What the family showed, which neither prediction anticipated

| ground | ¬¬x=x | MP | DT |
|---|---|---|---|
| classical | — | yes | **yes** |
| intuitionistic | — | yes | **yes** |
| quantum MO2 | — | yes | no |
| ZTL | — | yes | no |
| K3 | yes | yes | no |
| **LP** | yes | **NO** | yes |
| weak Kleene | yes | yes | no |
| Ł3 | yes | yes | no |

**The arrow has two halves, and outside the classical/intuitionistic pair
every ground pays with one of them.**

* *transport* — modus ponens: the arrow carries earned truth;
* *discharge* — the deduction theorem: a rule can be exported into the
  object language as an arrow.

Only classical and intuitionistic logic keep both. Five grounds keep
transport and lose discharge; LP keeps discharge and loses transport
(modus ponens is not valid in LP). **No ground in the family pays with
neither.**

**ZTL and LP are the two poles of one trade.** ZTL keeps transport and
loses discharge — `p ⊨ p` while `p→p` falls. LP keeps discharge and loses
transport. The cycle's own rules-versus-laws split reappears here as a
property of a *family* rather than of one logic, which is what leg 2 was
for.

Involution is **not** the discriminator: all four matrix grounds satisfy
¬¬x = x and they split on both halves. The framing that made Ł3 "the
decisive contrast because it keeps the involution ZTL breaks" was true
and irrelevant.

## The answer to leg 1's question: two shapes, not one axis

| ground | arity 0 | arity 1 | first fails at |
|---|---:|---:|---:|
| quantum MO2 | 0 | 194 | **1** |
| ZTL | 14 | 114 | **0** |
| K3 | 84 | 724 | **0** |
| weak Kleene | 72 | 1220 | **0** |

The three-valued grounds lose the arrow's *identity* itself. The
ortholattice keeps identity (`x →s x = ⊤`) and loses only discharge under
a standing context. Leg 1's 2/2 split lumped two structurally different
failures together; the arity of first failure is what tells them apart.

## A category error caught by our own assertion

The first draft of this table filled the "DT" column with the *arity-0*
gap, which put MO2 in the "has DT" column — contradicting the
impossibility theorem proved in tack 2a two hours earlier. The `assert`
placed on the both-halves club is what caught it. A convenient proxy read
as the real property: the same move, for the fifth time in this work, and
the reason every conclusion here is asserted rather than printed.

## Claim ceiling

Gap 0 is tier C everywhere except classical and intuitionistic, where the
deduction theorem is a cited theorem. **LP's "has DT" is measured, not
proved** — no counterexample was found in the pools swept, which is not
the same statement. The two zero-gap entries that are safe are safe by
citation, not by our sweep.
