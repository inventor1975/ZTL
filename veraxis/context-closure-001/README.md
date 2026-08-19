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

**5. No purely syntactic condition can be exact — PROVED.**
The positive fragment is sufficient and cannot be sharpened into a
characterisation *by looking at the formula alone*, because soundness is not a
property of the formula. The same formula with the same withheld atom is sound
under one disclosure and unsound under another:

    ¬(a ∧ b), with b withheld
      a = F  →  the conjunction is false whatever b is; the kernel's T
                survives every completion.            SOUND
      a = T  →  the conjunction reads F only because b is unverified, and
                the completion b := T defeats the claim.   UNSOUND

`no_syntactic_characterisation` in `lean/ContextClosure.lean`, on the empty
axiom list. Measured first: of 2,244 out-of-fragment formulas, 885 are
degenerate (the kernel can never say `T` at all — it did not swim, so it did
not drown), 580 are soundly non-lying, 566 always lie, and **213 flip with the
disclosure**. The curator predicted the 580 before the run, and named
implication as the source: `b → a` is the first of them, because there the `T`
comes from a true consequent rather than from an unverified antecedent.

So the syntactic criterion is **maximal in its class**. A sharper condition must
look at the disclosure as well, and ask the one question the examples point at:
is the `F` the kernel reasoned from a real falsehood, or merely an unverified
ground?

## Where this sits relative to what the corpus already proved

The greedy register's non-monotonicity is **not a discovery of this artifact** —
it has been a theorem since the kernel was written: `eager_and_not_monotone` and
`eager_not_not_monotone` in `lean/ZTL.lean`. The corpus also proves the other
half: the LAZY register (`knot`/`kand`/`kor`, strong Kleene) **is** monotone —
`kleene_not_monotone`, `kleene_and_monotone`, `kleene_or_monotone` — and that is
where the liar has a home (`liar_kleene_home : knot Z = Z`).

So ZTL is not a logic that lacks the monotone, sound-under-completions
behaviour. It carries **both registers and separates them by role**: verdicts
are greedy, self-reference is lazy. The risk this artifact measures lives
specifically in the register that issues verdicts.

What is new here is therefore narrower than "the kernel is unsound under
partial disclosure": that non-monotonicity was known. New is **where exactly it
damages context closure and where it provably does not** — the first is a fact
about connectives, the second a fact about what those connectives do to partial
disclosure.


## Round 2 — maximality, a recipe, and where it meets the corpus

Run: `python3 veraxis/context-closure-001/normalize.py` (~2s, exit 0 when green).

**No purely syntactic condition can be exact — proved.** 213 formulas outside
the fragment are sound under one disclosure and unsound under another; the
witness is `¬(a ∧ b)` with `b` withheld, sound at `a = F` and unsound at
`a = T`. So soundness is a property of the PAIR (formula, disclosure), and the
round-1 criterion is maximal in its class. `no_syntactic_characterisation`,
empty axiom list.

Of 2,244 out-of-fragment formulas: 885 degenerate (the kernel can never say `T`
at all — it did not swim, so it did not drown; counting these as "agreement" was
round 1's own measurement bug), 580 soundly honest, 566 always lying, 213
flipping with the disclosure.

**A recipe, without touching the kernel.** Normalise before judging a partial
disclosure — expand `xor`/`xnor` by the corpus's proved definitions
(`xor_def`, `xnor_def`), push negations to the atoms — and **every one of the
983 credit-warrants disappears**.

**Its price, measured.** 369 honest warrants go with them (2.66 lies discarded
per honest warrant lost), because normalisation surfaces the excluded middle,
which this logic gave up by construction (`lem_fails`). What is lost is exactly
what rested on a classical law ZTL declines. And on verified data the recipe
costs nothing at all: 11,624 comparisons, zero disagreements — where nothing
carries the mark, ZTL agrees with classical logic formula for formula
(`ClassicalAgreement.evalF_agrees`).

**Where this meets what the corpus already knew.** The unsound witness is the
Sheffer stroke, and `ZClone.lean` proved long before this work that NAND and
NOR *lose functional completeness* under the greedy lift — `nand_cannot_and`,
`nand_cannot_or`, and their NOR twins — with both stalling in the same 18-table
cage, reaching negation but, in that file's own words, unable to *rebuild
their own De Morgan partner*. Loss of completeness and loss of soundness under
partial disclosure are therefore **two projections of one break: de Morgan
fails** (`deMorgan1_fails`). This result is not a separate discovery; it is the
second face of a fracture the corpus had already mapped from the other side.

**Round 2 addendum, 2026-08-19 — the recipe is now proved, and so is its cost.**
`normal_form_sound`: on a formula in normal form, a warrant granted by the
kernel survives every completion of the withheld ground. No `T` on credit, for
the whole language rather than a census. The reason is one sentence: in a normal
form the withheld atom can only appear in a literal, and a literal over a
withheld atom is never `T` — the atom reads `Z`, its negation reads `F` — so no
warrant can rest on it, and one that does not rest on it survives every
completion.

`normal_form_incomplete`: and the loss is real. `b ∨ ¬b` is in normal form,
upheld by every completion, and refused by the kernel, because the excluded
middle fails here by construction. That is the 369 honest warrants of the
census, as a theorem.

Both on the empty axiom list. Keeping them there took the corpus's own warning
twice over: a nested pattern (`.neg (.atom _)`) and a wildcard row each pull
`propext` in through the compiled matcher, exactly as `ZTL.lean` notes beside
`kand`; the definitions enumerate every constructor instead.

**So the trade-off is now machine-checked on both sides.** Normalise and you
never grant a warrant the hidden ground could defeat; normalise and you lose
warrants that every completion upholds. The machine proves both and chooses
neither.

**Status.** The maximality theorem is proved; the census figures are MEASURED — a
census of depth ≤ 2 over two atoms. "Normalisation implies soundness" needs an
induction over normal forms and is not done. Normalisation is also *not* an
equivalence in ZTL: the normalised formula is a different, strictly weaker
formula, which is precisely why it is safe.

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
| `closure.py` | round 1 — five cases, crypto fixture, census, fragment |
| `normalize.py` | round 2 — maximality, the normalisation recipe, its price |
| `BRIEF-FOR-ADRIAN.md` | the one-page summary written for the legal side |
| `PREDICTIONS.md` | frozen before the bench existed; P1 was refuted by the run |
| `RESULTS.md` | the full reading, including what may and may not be said |

Prepared with AI assistance (Claude, Anthropic) under human direction;
responsibility for the text is the author's. — Vitaly Reznik, 2026-08-18
