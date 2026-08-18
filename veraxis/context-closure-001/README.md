# Context Closure 001 — selective disclosure against an unchanged ZTL kernel

Downstream material, like the rest of `veraxis/`: it exists because a consumer
asked the question. Nothing here changes the logic.

**The question.** Cryptography proves a disclosed fragment came from a signed
object. It does not prove the fragment SUFFICES for the conclusion drawn from
it. Three clauses of forty are shown, every hash verifies, and the picture is
false — because what defeats the conclusion is what was not shown.

**The property tested.** Boundary-relative context closure: given a declared
finite boundary `B` of admissible completions, a partial disclosure warrants a
claim only if the claim survives every admissible completion of what was
withheld. The index `B` is not decoration — the boundary is a premise, not a
discovered fact, and case 4 of the bench exists to make that visible.

**The constraint.** `ztl.py` is imported and never modified. Everything here is
a harness. Had the property required a change of semantics, the result would be
much weaker; it did not.

## Run it

```
python3 veraxis/context-closure-001/closure.py
```

~2 seconds, standard library only, deterministic, exit 0 when green.

## Three results, at three different levels of confidence

**1. Non-equivalence — established, with an executable minimal witness.**
The kernel's verdict is not the same property as completion closure. For
`q = ¬¬b` with `b` withheld, the kernel yields `T` while the completion
`b = false` defeats the claim. In the census of 5,306 (claim, disclosure) pairs
there are 983 such cases. *The existence of this class is a general fact about
the semantics; the count and the share characterise this finite census only —
depth ≤ 2, two atoms — and are not an error rate.*

The attack-resistant statement: **under some non-monotone claim structures the
present kernel can grant a positive warrant even though an admissible
completion of withheld information defeats that claim.**

**2. Positive-fragment coincidence — measured, not proved.**
Where every withheld atom occurs under no negation, in no antecedent and in no
xor/xnor, kernel verdict and closure coincide in both directions: 818 of 818
pairs, against the unrestricted boundary `B_⊤`. The fragment is **sufficient
and not maximal** — 1,102 formulas outside it also coincide on every disclosure
tested. Candidate for a monotonicity proof in the Lean corpus; until then it is
an empirical regularity with an exhibit.

**3. Boundary relativity — demonstrated.**
One disclosure, two declared boundaries, two different closure results, with
the kernel verdict unmoved. Therefore no closure guarantee may be stated
without an explicit `B` — and, since the kernel does not take `B` as an input,
a boundary-relative theorem needs `B` to enter the admitted grounds explicitly.
That formalisation is not done.

## What the bench shows about disclosure, in one line each

* Full disclosure warrants.
* **Immaterial concealment warrants anyway** — this is not a demand for full
  disclosure; privacy survives when what is hidden cannot defeat the claim.
* **Material concealment does not warrant, while every cryptographic check on
  the same disclosure passes** — authenticity of what is shown is not
  sufficiency for what is concluded.
* The declared boundary changes the answer, visibly.

## Two limits that do not move

1. **The boundary is declared, not discovered.** Whether `B` is the right
   boundary is an institutional question, not a computational one.
2. **A dependency that was never encoded is invisible.** The bench defends
   against selective disclosure from a committed structure. It does nothing
   against a formalizer who never recorded the proviso. Internal correctness
   can preserve externally grounded legitimacy; it cannot originate it.

## Architecture note

The kernel is not being changed to fit this property, and should not be: it
carries a machine-checked corpus on a specific semantics. Context closure is a
*different* property and belongs to a separate judge above the kernel — one
that may use the kernel's verdict inside the proved-safe fragment and check
completions outside it. Enumeration here is a reference oracle, not a
requirement of the theory; any complete method (SAT, BDD, symbolic checking)
satisfies the same condition.

## Files

| file | what it is |
|---|---|
| `closure.py` | the bench — four cases, census, fragment |
| `PREDICTIONS.md` | frozen before the bench existed; P1 was refuted by the run |
| `RESULTS.md` | the full reading, including what may and may not be said |

Prepared with AI assistance (Claude, Anthropic) under human direction;
responsibility for the text is the author's. — Vitaly Reznik, 2026-08-18
