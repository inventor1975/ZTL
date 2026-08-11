# ZTL against classical logic — the card

One page, four columns, every number produced by `python3 zledger.py`
(part of `run_all.py`). Quote from here; do not improvise the comparison.

| | |
|---|---|
| **Shared** | On Z-free markings ZTL **is** classical logic: 2906 formulas × 4 verified markings, **0 divergences**. Verify everything and the classical machine is back untouched. |
| **Lost** | As a system of laws we are strictly weaker: 12 classical laws alive, **14 fallen** (`audit.py`) — both De Morgans, contraposition, `¬¬p = p`, excluded middle, `p → p`, idempotence. In the depth-2 pool: 584 classical tautologies, **212** ours. |
| **Gained (laws)** | **Zero, and provably so.** A ZTL tautology holds under every marking, hence under the Z-free ones, where we are classical — so our validities are a subset by construction. This column can never fill. |
| **Gained (sight)** | Classical logic sorts two-variable formulas into **16** equivalence classes; we sort them into **195**, and **all 16** classical classes are split. Twelvefold refinement: same truths, finer eyes. |
| **Only here** | `¬(p ↔ p)` answers F, F, **T** on T, F, Z — the mark is sayable *inside the object language*. A two-valued logic has no words for the question, not merely no proof. |

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
* `p ∨ ¬p` at an unchecked `p` — **F** here. Case analysis on the
  undecided is what launches the surprise-exam elimination.

Modus ponens is **untouched**. The resolutions were not bought by
breaking inference; what is gone is the free-truth kit.

## The honest boundary

This makes a good **auditor** and a poor **mathematician**. Case analysis
on an undecided proposition is ordinary mathematical practice and we
cannot do it; from an empty ledger nothing is derivable here, not even a
guarded tautology (E26). Narrow search is a virtue when judging claims
and a cage when building proofs.

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
