# ZTL against classical logic — the card

One page, four columns, every number produced by `python3 zledger.py`
(part of `run_all.py`). Quote from here; do not improvise the comparison.

| | |
|---|---|
| **Shared** | On Z-free markings ZTL **is** classical logic. Not sampled — **proved**: `lean/ClassicalAgreement.lean`, `evalF_agrees`, structural induction over the whole formula language, empty axiom list. (The 2906 × 4 measurement that preceded it stands as the sanity check.) |
| **Lost** | As a system of laws we are strictly weaker: 12 classical laws alive, **14 fallen** (`audit.py`) — both De Morgans, contraposition, `¬¬p = p`, excluded middle, `p → p`, idempotence. In the depth-2 pool: 584 classical tautologies, **212** ours. |
| **Gained (laws)** | **Zero, and now machine-checked:** `ztl_taut_is_classical` — every ZTL tautology is a classical one, for every formula, empty axiom list. And the inclusion is **strict** (`not_conversely`: `p → p` is classically valid and fails here at a mark), so "conservative" never reads as "the same logic". This column can never fill. |
| **Gained (sight)** | Classical logic sorts two-variable formulas into **16** equivalence classes; we sort them into **195**, and **all 16** classical classes are split. Twelvefold refinement: same truths, finer eyes. |
| **Only here** | `¬(p ↔ p)` answers F, F, **T** on T, F, Z — the mark is sayable *inside the object language*. A two-valued logic has no words for the question, not merely no proof. |

## "So you abolished De Morgan?" — the schedule

No. A classical law costs exactly the verification of its atoms, and the
toolbox returns as they are paid for (measured, `zledger.py` §1):

| verified | classical tautologies that hold |
|---|---|
| both atoms | 584 / 584 — **100%**, and this one is a theorem, not a sample |
| one of two | 379 — 64% |
| nothing | 212 — 36% |

De Morgan itself: `p=T, q=T → T`; `p=T, q=Z → F`. The licence is per
FORMULA and needs EVERY atom in it verified — not most of them.

**Expiry is a WORLD problem, not a proof problem.** A verification can
lapse (§E25), and the licence lapses with it — but only for empirical
grounds: invoices, measurements, inspections, certificates. In
mathematics a proof does not expire, so the temporal layer never fires
there; what mathematics has instead is refutation, which is a different
transition. Audit needs both; proof needs only one.

## The instance to quote

```
p -> p     T->T  F->T  Z->F      can fail, honestly
~p -> ~p   T->T  F->T  Z->T      cannot fail — negation burns the mark
```

Classically one class, one truth. Here, two fates — which is why proving
`p → p` through `¬p → ¬p` is a forgery (the counterfeit test from the Job
dilemma).

## Why the poverty is the point

The two moves we lack are exactly the engines of the paradoxes:

* `¬(p → q) ≡ p ∧ ¬q` — classically valid, **not** here. This is the
  sorites' engine: it turns "this step failed" into "here is the cliff".
* `p ∨ ¬p` at an unchecked `p` — **F** here. Asserting the excluded
  middle about the undecided is what launches the surprise-exam
  elimination.

Modus ponens is **untouched**, and so is the rest of the working kit —
syllogism, reductio, and **proof by cases** `((p→q) ∧ (¬p→q)) → q`, which
is ZTL-valid (measured in `zprove.py`; an earlier claim in this corpus
that case analysis was lost was simply wrong). What dies is Peirce's law
— the one that separates classical from intuitionistic logic — and the
excluded middle on unchecked atoms. The resolutions were not bought by
breaking inference; what is gone is the free-truth kit.

## Two traps in our own numbers

* **Vacuous validity.** Under default deny an unverified antecedent is
  F, so *every* conditional over unchecked atoms is ZTL-valid for free.
  "ZTL-valid" for a conditional must always be read with "and its
  antecedent is earnable at all" (`zprove.py`, section 2).
* **Validity is not derivability.** From an empty ledger nothing is
  derivable, not even a guarded tautology (E26); the twelve rules are
  incomplete. Inference *transports* verification into compound claims —
  the pigeonhole conclusion is earned with three of six atoms still
  unverified — but never mints the first coin.

## What a theorem costs

The pigeonhole principle (3 pigeons, 2 holes) is ZTL-valid, and valid
non-vacuously: of 729 markings, 125 earn the antecedent and all 125 give
the conclusion. The **verification bill is exactly 3 atoms** — one
witness per pigeon, the price of the theorem's own subject matter. That
is the currency here: not steps, witnesses.

## The honest boundary

This makes a good **auditor** and a thin **mathematician** — thinner than
classical, not crippled. Real theorems go through and cost their own
data; what cannot be done is starting from nothing, or reasoning by
excluded middle about something nobody checked. Narrow search is a virtue
when judging claims and a constraint when building proofs.

## The first objection from a logician: "p → p fails, that is not a logic"

Nobody in the literature says that. What exists is Tomova's class of
**natural implications** (Reports on Mathematical Logic 47, 2012), four
criteria: (1) classical on {0,1}; (2) Łukasiewicz–Tarski normality —
modus ponens preserves the designated value; (3) `p ≤ q ⇒ p→q`
designated; (4) free elsewhere. **We meet (1) and (2)** — (1) is now a
Lean theorem — **and violate (3) in exactly one cell: (Z, Z)** (measured,
`zledger.py` §6).

`p → p` is not a primitive of that definition; it is the diagonal of (3),
and (3) presupposes a linear order on the values — the middle one being a
*degree* of truth (Łukasiewicz's ½, "possible, not yet determined").
Ours is a status mark barred from compounds: `Z ≤ Z` does not say
"equally true", it says "neither side examined", and designating the
conditional there is exactly granting truth on credit. So we are outside
the family the classification is built for, not in breach of a law.

The constitutive test of logicality is elsewhere and we pass it: the
consequence relation is Tarskian — reflexive, monotone, closed under cut
— so **`p ⊨ p` holds where `⊨ p→p` fails**. The price, named: the
deduction theorem holds left to right only (→-elimination works,
→-introduction does not). Ł3 lacks the deduction theorem too, so this is
a family trait, not an exile.

## What NOT to say

* ~~"ZTL equals classical logic"~~ — false: strictly fewer validities.
* ~~"ZTL can express everything"~~ — false on three values: 515 of 19683
  binary functions are expressible (2.6%), a consequence of greediness
  (compound formulas never take Z).
* ~~"we solved the paradoxes"~~ — we priced them. The diagnoses have
  prior art (Quine 1953 and Sorensen 1988 for the surprise exam;
  paracomplete treatments for the sorites); what is ours is that each
  diagnosis is a reproducible run with a warranty and a named cure.
* ~~"Lean proves our choices are right"~~ — Lean proves our theorems have
  no holes (405, empty axiom list). The adequacy of `¬Z = F` is not a
  theorem and cannot be one.
