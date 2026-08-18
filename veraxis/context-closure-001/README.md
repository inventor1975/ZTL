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

**Cite this artifact by tag, not by `master`.** Tag `context-closure-001-v1`
pins the whole tree; the kernel it imports is `ztl.py` at
`sha256 a57324b39ebb66ee1fe39d834a1a891f8b1927882b1dc6df4c808cc2ef335d81`.
`master` moves; a research citation should not.

## Four results, at different levels of confidence

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

**2. Positive-fragment coincidence — PROVED, on the empty axiom list.**
Where every withheld atom occurs under no negation, in no antecedent and in no
xor/xnor, kernel verdict and closure coincide in both directions. The bench
measured this on 818 of 818 pairs; `lean/ContextClosure.lean` now proves it for
**the whole formula language and every valuation**:

```
theorem closure_coincides (a : Nat) (v : Nat → V) (hv : v a = Z) :
    ∀ φ : Fm, negFree a φ = true →
      (evalF v φ = T ↔
        (evalF (setA a T v) φ = T ∧ evalF (setA a F v) φ = T))
```

`#print axioms` → *does not depend on any axioms*, as do the monotonicity
lemma it runs through and the independence lemma under that. The boundary of
the theorem is itself a theorem: `outside_fragment_fails` exhibits `¬¬b` with
`b` withheld — the kernel warrants it, the completion `b := F` does not.

The fragment is **sufficient and not maximal** — 1,102 formulas outside it also
coincide on every disclosure tested, and none of that is claimed by the proof.

**3. Boundary admissibility — a mine, found and disarmed.**
A declared boundary that admits **no** completion makes the universal
quantifier vacuously true, so a naive implementation returns `T` for every
claim: one could "prove closure" by declaring a contradictory boundary. The
bench now returns `BOUNDARY_INVALID` instead, and decides admissibility of the
boundary *before* computing closure — closure reasons inside an admitted
boundary and has no standing to produce that boundary's own admissibility. A
second condition rides along: a boundary may not assign values to grounds the
discloser already published (that is a rewrite of the disclosed part, not a
completion of the withheld part). *Found by Arkadiy on a static read of the
file, before it reached anything.*

**4. Boundary relativity — demonstrated.**
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
  the same disclosure passes** — and those checks are **computed in the run**,
  not stipulated: the bench builds a CLWR-shaped record (formula digest, a
  digest per ground, a self-excluding `record_sha256`) under the consumer's own
  canonical serialization — sorted keys, `,`/`:` separators, no trailing
  newline, self-digest excluded by key removal — verifies it, and prints
  `CryptographicVerification = PASS` beside `ContextClosure = F`. The withheld
  ground is present in the record *as a digest*, so nothing was dropped or
  forged. Authenticity of what is shown is not sufficiency for what is
  concluded.
* **A boundary admitting nothing returns `BOUNDARY_INVALID`**, not a vacuous
  `T`.
* The declared boundary changes the answer, visibly — **and now prints a
  receipt**: which completions it excluded, and which of those would have
  defeated the claim. A boundary that turns `F` into `T` names the reading it
  removed, so its admissibility can be contested by whoever has standing.

## Two limits that do not move

1. **The boundary is declared, not discovered.** Whether `B` is the right
   boundary is an institutional question, not a computational one. What the
   machine can do is print the boundary's price (the receipt above) and, if the
   boundary is later contested, **recompute** rather than ask to be trusted —
   the verdict is reproducible from pinned inputs.
   Note also that the machine-checked theorem covers the **unrestricted**
   boundary; under a declared narrower one, closure is a reproducible
   computation, not a theorem.
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
| `closure.py` | the bench — five cases, crypto fixture, census, fragment |
| `BRIEF-FOR-ADRIAN.md` | the one-page summary written for the legal side |
| `PREDICTIONS.md` | frozen before the bench existed; P1 was refuted by the run |
| `RESULTS.md` | the full reading, including what may and may not be said |

Prepared with AI assistance (Claude, Anthropic) under human direction;
responsibility for the text is the author's. — Vitaly Reznik, 2026-08-18
