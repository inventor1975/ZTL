# Context Closure Bench — three results, and the middle one refutes the hope

Run 2026-08-18, ~23:20. `lab/closure/closure.py`, exit 0. Predictions frozen in
`PREDICTIONS.md` before the bench existed. **The ZTL core was imported and not
modified** — the whole bench is a harness, as required.

## 1. The four demonstration cases — all four behave as specified

| case | ZTL | CC_B |
|---|---|---|
| full disclosure | T | T |
| immaterial concealment (hidden atom cannot defeat) | **T** | **T** |
| material concealment (the exception withheld) | **F** | **F**, defeated by `exception=T` |
| same disclosure, boundary B1 unrestricted | F | **F** |
| same disclosure, boundary B2 "exception cannot fire" | F | **T** |

Case 2 matters as much as case 3: the system does **not** demand full
disclosure. Privacy survives whenever the withheld ground cannot defeat the
conclusion. Case 3 is the exhibit — every cryptographic property holds and the
conclusion is nonetheless unwarranted. Case 4 shows the boundary doing visible
work, which is what keeps Agrippa outside rather than inside the result.

**P5 held:** case 3 yields `F`, not `Z`. The claim does not become "unknown",
it becomes unwarranted. That is the phrase the paper may use.

## 2. Census — P1 REFUTED, and in the dangerous direction

5306 (formula, disclosure) pairs, every formula of depth ≤ 2 over `{a, b}` with
`b` withheld.

```
agree                                3764
ZTL grants T while closure FAILS      983      <- soundness refuted
ZTL withholds T while closure holds   559
```

I predicted zero in the first category and gave a reason — atom substitutions
are a subset of occurrence substitutions. The reason is wrong, because ZTL
lifts each **connective**, not the formula: `znot(znot(Z)) = znot(F) = T`.

**Read the two halves with different force** (Arkadiy's correction, accepted):
the EXISTENCE of this class of counterexamples is a general fact about the
semantics; the count 983 and the share 18.5% characterise **this finite census
only** — depth ≤ 2, two atoms, one withheld. They are not an error rate and
must never be quoted as one.

Smallest witness: **`¬¬b` with `b` withheld — ZTL says `T`, and `b = F`
defeats it.** Also `¬(a ∧ b)` with `a = T`.

The precise statement, and it is the attack-resistant one:

> Under some non-monotone claim structures, the present kernel can grant a
> positive warrant even though an admissible completion of withheld
> information defeats that claim.

The legal illustration comes second, as illustration: a claim of the form
"… and no exception applies" is non-monotone in the exception, so with the
exception withheld the kernel can return a positive warrant — *not shown that
the exception applies* ending up with the force of *shown that it does not*.

So the comfortable formulation — *"the property was already contained in the
core"* — **is false as stated**, and had it gone out unchecked it would have
been the strongest objection available to a reviewer.

## 3. A sufficient syntactic fragment — not a characterisation

Restrict to disclosures where the withheld atom occurs **under no negation, in
no antecedent, and inside no xor/xnor**:

```
818 of 5306 pairs qualify
ZTL grants T while closure fails      0
verdicts coincide                   818   (100%)
```

Coincidence in both directions, zero exceptions — measured against the
**unrestricted** boundary `B_⊤ = {T,F}` per withheld atom, which is what the
census actually ran.

**The fragment is sufficient and demonstrably NOT maximal.** Measured after
Arkadiy's objection: **1,102 formulas outside the fragment also coincide on
every disclosure tested** (409 formulas inside coincide, 0 fail; outside, 1,102
coincide and 1,142 do not). So this is a safe sufficient criterion, not a
characterisation of the safe cases, and must not be presented as one.

**Positive-disclosure coincidence (candidate theorem, corrected).** For the
UNRESTRICTED completion boundary `B_⊤`, if every withheld atom occurs in `q`
under no negation, no antecedent and no xor/xnor, then
`ZTL(q, D) = T ⟺ CC_{B_⊤}(q, D) = T`.

The earlier form of this statement carried an arbitrary `B` on the right and
nothing on the left — **wrong, and refuted by our own case 4**, where one
disclosure gives `CC_{B₁} = F` and `CC_{B₂} = T` while the kernel verdict never
moves. The kernel does not take `B` as an input. A boundary-relative theorem
requires `B` to enter the admitted grounds explicitly, and that formalisation
is not done.

Status: **PROVED**, 2026-08-19, `lean/ContextClosure.lean`, and it generalises
past the census — the statement holds for the whole formula language and every
valuation, not for depth ≤ 2 over two atoms.

The proof runs where the measurement said it would: through a **monotonicity**
lemma. On this fragment, reading the withheld ground as `T` instead of `F` can
only preserve a warrant, and that is exactly what fails outside it. Three
lemmas and the theorem, all `#print axioms` → *does not depend on any axioms*:

| object | what it says |
|---|---|
| `eval_indep` | a formula not mentioning the atom cannot notice the completion |
| `mono` | on the fragment, `F`-reading ⟹ `T`-reading preserves a warrant |
| `closure_coincides` | kernel verdict ↔ every completion warrants |
| `outside_fragment_fails` | `¬¬b` — the coincidence provably fails outside |

Keeping it axiom-free took the corpus's own discipline: `simp` and `by_cases`
put `propext` and `Classical.choice` into the term on the first attempt, so the
whole file is `cases` + `noConfusion` + explicit rewrites, and atom equality
goes through `decide` rather than `BEq`.

## 4. Two corrections applied after Arkadiy's static read

**The empty boundary was a real hole.** `closure_verdict` iterated the
completions, skipped those the boundary rejected, and returned `T` if it never
found a defeating one — so a boundary admitting NOTHING returned `T` for every
claim. Universal quantification over the empty set, mathematically ordinary and
institutionally fatal: one could "prove closure" by declaring a contradictory
boundary. The bench now decides `BoundaryAdmissible(B, D)` FIRST and returns
`BOUNDARY_INVALID` when the boundary admits nothing — closure reasons inside an
admitted boundary and has no standing to produce that boundary's own
admissibility. A second condition came with it: a boundary may not assign a
value to a ground the discloser already published. Case 5 of the bench pins
both. **Found by reading, not by running — the bench was green before it.**

**The cryptographic half is now computed, not stipulated.** Case 3 previously
asserted in prose that signature and provenance still pass. It now builds a
CLWR-shaped record — formula digest, a digest per ground, a self-excluding
`record_sha256` — under the consumer's own canonical serialization from
`INTEGRATION-SLICE-001-DIGEST-DERIVATION-v0.5.md` (sorted keys, `,`/`:`
separators, no trailing newline, self-digest excluded by key removal), verifies
it, and prints `CryptographicVerification = PASS` beside `ContextClosure = F`.
The withheld ground is in the record **as a digest**, so nothing was dropped or
forged. The claim "authentic ≠ sufficient" is now one executable end-to-end
witness rather than an illustration.

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


## What to say, and what not to say

Sayable: *ZTL permits selective disclosure without requiring full-context
disclosure — a withheld proposition may stay hidden whenever every admissible
completion preserves the conclusion — and the unchanged kernel decides this
exactly when what is withheld can only add support.*

Sayable, and must accompany it: *where the withheld ground can defeat the
conclusion — which is where exceptions, exclusions and conditions of defeat
live by their grammar — the kernel alone is not sound for this property, and
the closure must be computed by enumeration over the declared boundary.*

Not sayable: "ZTL already computes context closure". Not sayable: any form of
the guarantee without the index `B`.

## The two limits, unchanged by any of this

The bench cannot show the boundary `B` is the right boundary. And it cannot
reach a dependency the formalizer never encoded — the second adversary. Both
belong in the result, not in a later erratum.
