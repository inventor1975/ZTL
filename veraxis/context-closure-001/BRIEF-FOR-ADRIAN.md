# Selective disclosure and the sufficiency of what is shown — one measured result

**For:** Adrian (Ignacio Adrian Lerer) · **From:** Vitaly Reznik · 2026-08-18

A single technical result, with its negative half and its limits. It is offered
before any joint framing, so that whatever you write about the legal object
rests on what is measured rather than on what we intend to build.

## The question

Cryptography can prove that a disclosed fragment came from a signed document —
this is what selective disclosure (SD-JWT, now RFC 9901) and provenance (C2PA)
establish. **Neither establishes that the disclosed fragment suffices for the
conclusion drawn from it.** Three pieces are shown out of forty; every hash
verifies; the picture is false, because what defeats the conclusion is what was
not shown.

We tested one property against that gap, on an existing verification kernel
(ZTL), **without modifying the kernel** — the whole test is a harness around it.

**Boundary-relative context closure.** Given a *declared, finite* boundary `B`
of admissible completions, a partial disclosure warrants a claim only if the
claim survives **every** admissible completion of what was withheld.

The index `B` is essential and is not a technicality: the boundary is a
premise, not a discovered fact. We do not claim to compute the unique meaning
of a document, and the bench is built to make that visible rather than to hide
it.

## What was measured

Claim modelled: *entitlement ∧ condition ∧ ¬exception*.

| case | outcome |
|---|---|
| everything material disclosed | warranted |
| a withheld fact that cannot defeat the claim | **still warranted** — privacy without loss of warrant |
| the **exception** withheld | **not warranted**, while every cryptographic check on the same disclosure passes |
| same disclosure, two different declared boundaries `B₁`, `B₂` | **two different results** |

Case 2 matters as much as case 3: the system does **not** demand full
disclosure. Case 4 is the honest one — it shows the boundary doing visible
work, so the guarantee is never stated without it.

## The negative result, which is the part worth having

The kernel's own verdict is **not** the same property. In an exhaustive census
of 5,306 (claim, disclosure) pairs the kernel granted the claim in **983 cases
where an admissible completion of the withheld information defeats it**.

Stated carefully, because the two halves have different force: *the existence
of this class of counterexamples is a general fact about the semantics; the
count and the proportion characterise this finite census only* — formulas of
depth ≤ 2 over two atoms, one atom withheld. They are not an error rate.

The minimal witness is executable and one line long: for `q = ¬¬b` with `b`
withheld, the kernel yields **T** while the completion `b = false` yields
**false**.

The precise statement, which is the one that is hard to attack:

> Under some non-monotone claim structures, the present kernel can grant a
> positive warrant even though an admissible completion of withheld
> information defeats that claim.

The legal illustration of why this is materially dangerous: a claim of the
form *"… and no exception applies"* is non-monotone in the exception. With the
exception withheld, the kernel can return a positive warrant — that is, *not
shown that the exception applies* can end up carrying the force of *shown that
it does not*.

So the comfortable claim — *the kernel already computes contextual
sufficiency* — is **false as a general statement**, and we would rather report
it ourselves than have it found.

## A syntactic fragment in which the two coincide

Restrict to disclosures where every withheld element occurs **under no
negation, in no antecedent, and in no exclusive-or**, against the
**unrestricted** completion boundary `B_⊤ = {T,F}` per withheld atom:

    818 of 818 such pairs — kernel verdict and completion-based closure
    coincide, in both directions, with zero exceptions.

Readable rule: **the kernel's verdict may be relied on under partial disclosure
when what is withheld could only add support, never remove it.** Exceptions,
exclusions, provisos and conditions of defeat sit under a negation by their
grammar, and for those the closure must be checked over completions rather than
read off the kernel.

**This is now a theorem, not a measurement** (`lean/ContextClosure.lean`,
proved on the empty axiom list, for the whole formula language and every
valuation — not for the sampled cases only).

**And the criterion cannot be sharpened by looking at the formula alone — also
a theorem.** Soundness is not a property of the formula: the same claim with
the same withheld element is safe under one disclosure and unsafe under
another. `¬(a ∧ b)` with `b` withheld is safe when `a` is false (the
conjunction fails whatever `b` is) and unsafe when `a` is true (it fails only
because `b` is unverified). So the syntactic criterion is *maximal in its
class*: any sharper rule must read the disclosure as well, and ask whether the
falsity the system reasoned from is a real falsehood or merely an unverified
ground.

## Status, stated precisely

Three separable results, at three different levels of confidence:

1. **Non-equivalence** — kernel verdict ≠ completion closure. Established by an
   executable minimal counterexample; the strongest of the three.
2. **Positive-fragment coincidence** — **proved** (machine-checked, empty axiom
   list), together with a second theorem showing that no purely syntactic
   condition can be exact.
3. **Boundary relativity** — one disclosure yields different closure results
   under two declared boundaries. Therefore no closure guarantee may be stated
   without an explicit `B`.

Note that the kernel does not take `B` as an input while closure does — so any boundary-relative statement needs `B` to enter the
admitted grounds explicitly, and that formalisation is not yet done.

## Two limits that do not move

1. **The boundary is declared, not discovered.** Every guarantee above is
   relative to `B`. Whether `B` is the right boundary is a legal and
   institutional question, not a computational one — and it is, I think,
   exactly where your part of the work begins.
2. **A dependency that was never encoded is invisible.** The bench defends
   against a party who discloses selectively from a committed structure. It
   does nothing against a formalizer who never recorded the proviso in the
   first place. Internal correctness can preserve externally grounded
   legitimacy; it cannot originate it.

## What can and cannot be said

**Can:** selective disclosure need not be all-or-nothing — a withheld
proposition may stay hidden whenever every admissible completion preserves the
conclusion; and against a declared finite boundary this is decidable.

**Must accompany it:** where the withheld ground can defeat the conclusion, the
kernel alone is not sound for this property, and the completions must be
checked.

**Cannot:** that the kernel computes contextual sufficiency in general; that
the syntactic fragment *characterises* the safe cases (it does not, and we
prove it cannot); any version of the guarantee without the boundary index; or
that any of this settles what a document means.

**One practical addition, measured rather than proved.** Rewriting a claim into
a normal form before judging it — pushing negations inward — removes every
credit-warrant we found, at the cost of losing about a sixth of the honest ones,
and costs nothing at all on fully verified data. Which of those two errors an
institution prefers — never granting a warrant it should not, versus never
losing one it should — is a second question of the same kind as the boundary:
the machine can price both outcomes, and cannot choose between them.

## One architectural note, since it bears on how you frame the object

The kernel is **not** being changed to fit this property. It carries a
machine-checked corpus of 428 theorems on a specific semantics, and bending it
would damage what that semantics exists for. Context closure is a *different*
property, so it belongs to a separate judge sitting above the kernel — one that
may use the kernel's verdict directly inside the proved-safe fragment and check
completions outside it. Enumeration is the reference oracle of the bench, not a
requirement of the theory: any complete method (SAT, BDD, symbolic checking)
satisfies the same condition.

## What the bench can already give the legal side

Two things, both concrete, offered because they bear directly on the question
of the boundary.

**A receipt for every declared boundary.** When a boundary turns an unwarranted
claim into a warranted one, it does so by removing readings. The bench now
prints which ones — and, of those, which would have defeated the conclusion:

    BOUNDARY RECEIPT for boundary B2
      admitted   1: exception=F
      excluded   1: exception=T
      of those, DEFEATING under B_top   1: exception=T

So a declared boundary stops being a word and becomes an object with a named
price: *this conclusion is warranted only because this specific reading was
excluded.* Whoever has standing to decide admissibility can then contest that
reading rather than the abstraction.

**Re-adjudication rather than trust, if a boundary is later contested.** The
verdict is reproducible — formula, grounds and the judging kernel are all
pinned by hash — so a challenged boundary does not require anyone to trust the
earlier verdict. It is recomputed under the new boundary, deterministically and
cheaply. That moves the legal question from *was the verdict right* to *under
which boundary was it obtained*, which is a question law already knows how to
handle.

**One precision, so the strength is not over-read.** The machine-checked
theorem covers the UNRESTRICTED boundary. Under a declared, narrower boundary
the closure is a reproducible computation, not a theorem — the kernel does not
take a boundary as an input at all.

---

*Prepared with AI assistance (Claude, Anthropic) under my direction; the
measurements are reproducible from the bench and the responsibility for this
text is mine. — V.R.*
