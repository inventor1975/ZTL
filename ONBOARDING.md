# ONBOARDING — ZTL and VR, for a cold start

Written 2026-08-17 for the case where the assistant has lost context and the
curator says **"восстановись по ZTL и VR"**. It is a briefing, not a summary of
everything: what is here is what turned out to be load-bearing, and every claim
below carries the command that re-checks it.

**Read this file, then run the checks in it.** Do not take it on trust — that
is the whole lesson of the day it was written. Anything here can have gone
stale; the code is the arbiter.

---

## 0. The single most important habit

The corpus's failures are almost never wrong numbers. On 2026-08-17 four
adversarial review rounds found dozens of defects and **every figure any
program printed was correct**. The defects were all in *sentences about* the
figures, and they had one shape:

> a claim reached by REASONING where a MEASUREMENT was available.

Concretely, the forms that died that day, each more than once:

* "no existing tool does X" — four such died in one day, three of them within
  an hour of somebody installing the tool. `\df provsql.sr_*` ended two of them.
* "this holds at step 0.05" — a one-seed fact stated as a property of the grid
  (it holds on 2 of 7 seeds).
* "there is no symmetric case" — true of the table above it, false of the table
  thirty lines below it, in the same program's output.
* "withdrawn in the probe and in both notes" — a commit message that was false;
  it was in one note.

So: **install the predecessor, sweep the seeds, read the function list, and
grep the whole corpus for the claim you just withdrew.** Three stands exist for
the last of these: `inventory/withdrawn_claims.py`, `inventory/note_claims.py`,
`inventory/prose_batch.py`.

The predecessor rule has a second edge, learned again on 2026-08-19: **search
the neighbouring FIELD, not just this one.** A result about withheld grounds
turned out to have fourteen years of prior art in access control, under a name
nobody here would have grepped for. An hour of reading before publication is
cheaper than a correction after it.

**`lab/` is the laboratory — a store of our own mistakes, and it is in
`.gitignore` on purpose.** One folder per idea inside it. Only what survives
leaves, and it leaves as a self-contained artifact under `downstream/`. If a `git
add` is refused there, that is the rule working, not an obstacle.

---

## 1. ZTL — what it is, in the order that matters

**It is a TWO-VALUED logic.** Not three-valued. Verdicts are always T or F. This
is the single most common error to make about it, and the assistant made it in
a letter to a citing reader before checking.

The alphabet is five symbols **of four different kinds** — do not count them
together, and never say "five-valued":

| symbol | kind | where it lives |
|---|---|---|
| `T`, `F` | truth values | input and output |
| `Z` | **mark on an input** — Łukasiewicz's indeterminate, "a truth not yet settled" | input only; barred from the value of any compound |
| `N` | **solver state** — Kleene's undefined, "a computation not yet run" | only under self-reference; provably finite; never escapes outward |
| `E` | **the empty case** — no readings at all | a disposition of the judge |

The preprint's own §10 is the canonical positioning and beats any paraphrase:

> Truth values: `T, F` · Input mark: `Z` "unverified" · Solver state: `N` "not
> yet computed" · Reading policy: local, default deny.
> **"ZTL is a two-valued logic that refuses to lie about the unverified."**

Two-valuedness of the values is **not** classicality: the entailment relation
differs (LEM falls, the deduction theorem is one-directional, `¬¬p ⊭ p`). A
logic is defined by its entailment, not by its palette.

### 1.1 One generating principle, and the cells it forces

    f*(x₁…xₙ) = ⋀ { f(v₁…vₙ) : vᵢ ∈ subs(xᵢ) },  subs(Z) = {T,F}

**Every occurrence of Z is substituted INDEPENDENTLY.** That one word is where
all the unusual behaviour comes from:

    Z ∨ Z = F      not Z, not T
    ¬Z = F,  ¬¬Z = T    the involution is BROKEN
    Z ∧ Z = F      idempotence falls

Under the strict Kleene lift these would be `Z∨Z = Z` and `¬¬Z = Z` — involution
intact, and ZTL would sit inside Kleene's family. **The independence of
occurrences is what puts it outside.** Read it as: the logic refuses to identify
two occurrences of the same unverified atom. "This unknown" and "that unknown"
are not the same unknown until checked.

    python3 ztl.py                 # the six internal tables
    python3 -c "import ztl; print(ztl.OR('Z','Z'), ztl.NOT(ztl.NOT('Z')))"

**Ten tables, not six.** Six internal (`¬ ∧ ∨ → ⊕ ↔`) plus the external layer,
definable from the core: `isZ(x) = ¬(x↔x)`, `isT`, `isF`, and an external
implication. Quarantine is **detectable from inside**.

### 1.2 Its identity in the literature — the one separating rule

`¬¬p ⊨ p` separates ZTL's consequence relation from each of its
involutive-negation neighbours (K3, LP, weak Kleene, Ł₃) and, by one lemma
(`involution_gives_dne`), from **any** matrix with involutive negation. The
cause is the one broken cell `¬¬Z = T`.

On `{¬,∧,∨}` ZTL coincides cell-by-cell with the **external layer of Bochvar's
B3** (1938) — found in the literature search *after* the tables were generated,
not a source. The delta is 7 cells in `→, ↔, ⊕`. The mark's *meaning* is
Łukasiewicz's; the tables are Bochvar's; nobody occupied their conjunction.

**Suszko's thesis** says every structural logic is logically two-valued.
ZTL's difference is not that it escapes the reduction — nothing does — but that
it needs none. The machine-measurable discriminator: does the third symbol ever
appear as the value of a *compound*? Neighbours: 602–784 of 784 depth-2
compounds. ZTL: **0 of 784** (the greediness theorem, `evalF_classical`).

**Expressiveness is NOT classical, and this surprises people (it surprised the
curator).** Under the greedy lift, Sheffer's stroke and Peirce's arrow each
*lose* functional completeness — `ZClone.lean`: `nand_cannot_and`,
`nand_cannot_or`, `nor_cannot_and`, `nor_cannot_or`. Both stall in the same
18-table cage; both still reach negation, and neither can rebuild its own De
Morgan partner. The sole surviving solo basis is **nonimplication `↛`**. Say
"identical to classical logic on verified data" (true, `evalF_agrees`); do not
say "as expressive as classical logic" (false in this sense).

**Known gap in §4:** strict-tolerant logic (ST — Cobreros, Egré, Ripley, van
Rooij) is not mentioned anywhere in the preprint. It is the leading contemporary
paradox-handling logic. The contrast is favourable and should be *written*: ST
buys paradox tolerance by **giving up transitivity** (cut fails); ZTL keeps cut
(`lean/ZSequent.lean:cut_admissible`, and `zsequent.py`: 5292 instances, 0
violations) and pays elsewhere. Do not claim "only we can treat paradoxes
machine-checkably" — that is false, and it is the exact claim-shape from §0.

### 1.3 What is machine-checked

**Empty axiom list including definitions**, audited per object. Do not quote a
count from this file — print it, the corpus grows:

    python3 inventory/axiom_audit.py   # -> ALL CLEAN: N theorems across M modules
    python3 run_all.py                 # all stands + Lean, green or it exits non-zero

At 2026-08-19 that reads 440 theorems across 30 modules, and `run_all.py` runs
123 stands.
    cd lean && lake env lean <<< 'import ZTL
    #print axioms V.ax_xnor_ZZ'    # -> does not depend on any axioms

Two anchors worth knowing, both zero-axiom, the "two registers" in one line
each:

    V.ax_xnor_ZZ       : zxnor Z Z = F    greedy — self-identity not certified
    V.liar_kleene_home : knot Z = Z       lazy  — negation has a fixed point

Classically `(x=x)=T` always and `(x=¬x)` is impossible. **Z overturns both.**

**THE TWO REGISTERS ARE NOT A DETAIL — get them wrong and you will misdescribe
the logic.** The assistant did, on 2026-08-19, saying "ZTL lacks the monotone,
sound-under-partial-information behaviour". It does not. It has both, and both
halves are proved:

    kleene_not_monotone / kleene_and_monotone / kleene_or_monotone
        the LAZY register (knot/kand/kor = strong Kleene) IS monotone
    eager_and_not_monotone / eager_not_not_monotone
        the GREEDY register (znot/zand/zor) is NOT, and that is a theorem too

So: **verdicts are greedy, self-reference is lazy.** ZTL does not lack the
well-behaved register — it separates the two by role. Any sentence of the form
"ZTL cannot do X" must first say *in which register*.

### 1.4 Lean traps — read before writing a proof, not after

Every one of these cost the assistant a rewrite on 2026-08-19. A proof that
compiles is not done; a proof that compiles **on the empty axiom list** is.

* **`simp` and `by_cases` pull `propext` and `Classical.choice` into the term.**
  Use `cases` + `noConfusion` + explicit `rw`. This is the single most common
  way to land on the full classical tier without noticing.
* **Nested patterns and wildcard rows pull `propext` through the compiled
  matcher** — the warning already stands beside `kand` in `ZTL.lean`. Enumerate
  every constructor instead of writing `| _ => false` or `| .neg (.atom _)`.
* **Atom equality: use `decide (n = a)` with `of_decide_eq_true` /
  `of_decide_eq_false`, not `==`.** The `BEq` bridge `n == a` → `Nat.beq n a`
  does not go through elaboration and wastes a cycle.
* **Print the axioms of every new object** and read the output — `#print axioms`
  at the bottom of the file, the way every module here already does.

Also proved for the whole formula language (not sampled): on a **Z-free**
valuation ZTL agrees with classical logic formula for formula
(`lean/ClassicalAgreement.lean:evalF_agrees`). So ZTL expresses all of classical
logic and is cautious *only* where the unknown enters. Never say "weaker than
classical" without that second half — strictly fewer *tautologies*, identical
on verified data.

### 1.5 The live branch, 2026-08-19 — selective disclosure

`downstream/context-closure-001/` (cite by tag `context-closure-001-v1.5`, never by
`master`) plus `lean/ContextClosure.lean`. Cryptography proves a disclosed
fragment came from a signed object; it does not prove the fragment SUFFICES for
the conclusion drawn from it. Five theorems, empty axiom list:

    closure_coincides            kernel verdict = completion closure, on the
                                 positive fragment (withheld atom under no
                                 negation, no antecedent, no xor/xnor)
    outside_fragment_fails       and provably not outside it (¬¬b)
    no_syntactic_characterisation  no condition on the FORMULA alone can be
                                 exact — soundness belongs to the pair
                                 (formula, disclosure)
    normal_form_sound            normalise first and no warrant is granted on
                                 credit
    normal_form_incomplete       and you lose warrants every completion upholds
                                 (b ∨ ¬b) — the excluded middle, priced

Two facts to carry into any conversation about it. **The prior art is 14 years
deep**: attribute-hiding attacks (Crampton & Morisset, PTaCL, POST 2012), policy
resistance certified in Isabelle (ATRAP, 2013), extended evaluation with BDDs
(2019). Never present the problem or the enumeration mechanism as new. **What is
ours** is the behaviour of THIS semantics — the greedy lift breaks de Morgan, so
it admits an attack Kleene-style languages do not have — and the two theorems
bounding it.

And the second fact: what the machine cannot decide is where the legal side
begins. Which completions are admissible, and whether to prefer never granting
a false warrant over never losing a true one, are institutional questions. The
bench prices both and chooses neither.

---

## 2. VR — what it is

A separate cycle in `../VR/VRCycle` (its own git root). Ten published works;
the mathematical cycle is complete and parked. **Do not reopen it unprompted.**

**Cold-start reading order** (the code is the arbiter; README/blueprint
narrative can be stale): `VR-LOGIC.md` (the compass) → `blueprint/.../
00_overview.tex` → `VRCycle/VR.lean` → `Continuum/` → `Forms/Transit.lean` →
`README.md`.

### 2.1 The four things that matter

**Axiom-free arithmetic.** Two primitives `{∅, t}`, no axioms of its own.
`∅ = base` is a **nullary operation** — the act taking no operands, not "nothing"
and not a thing. `1 = t(∅)`, `n = tⁿ(∅)`. Induction (A4) is the **recursor of
the inductive type**, not an axiom: what first-order exposition postulates, type
formation absorbs. `VR ≡ PA` is a constructive isomorphism `Nat ≃ VRObj`.

    cd ../VR/VRCycle && lake env lean <<< 'import VRCycle.VR
    open VR
    #print axioms VR.Theorem_11_VR_PA'    # -> does not depend on any axioms

**Sets are Aczel-style pointed graphs, and ZFC is a MODE.** `OpSet` is
`⟨V, E, pt⟩` — vertices, reveal-edges, a point. Identity is **witnessed
bisimulation**. `IsGrounded` is accessibility of the root, i.e.
well-foundedness — and `isGrounded_iff` proves it respects bisimulation, so, in
the file's own words, *"well-founded / ZFC-mode is a property of the SET, not of
the particular graph presenting it"*. `mem_grounded`: the mode is hereditary.

So **ZFC and ZFA are not competing axiomatisations but two modes of one
operational universe**, separated by a predicate on it — and both axiom-free.

    lake env lean <<< 'import VRCycle.SetsOp.Grounded
    #print axioms VRCycle.SetsOp.OpSet.isGrounded_iff'   # -> no axioms

**Two registers, with an asymmetry.** Operational `L₀` and formal `L₁`.
`translate_implies_realisable` gives **O→T** (an operational fact with a witness
makes the formal term realisable). The converse **has no mechanism**: from
`∃ s, …` no specific operational object is recoverable — no Skolemisation across
the existential. The operational is always built independently, never read off
the formal.

**"No ontology" is scoped, and the published slogan overshoots.** It means no
*substance* ontology — being relocated into doing. It is *not* a blanket denial:
the operational layer carries real commitments (global `∈`, potentialist
infinity, relational identity) which are **tracked** via register and axiom
tiers. `VR-LOGIC.md` says explicitly that the bare slogan in the published
*Numbers* v1.1.0 and *Forms* v1.0.2 preprints reads as a blanket denial and
collides with VR-Sets' global `∈`.

### 2.2 Axiom tiers — the vocabulary

`[]` axiom-free · `[Quot.sound]` · `[propext, Quot.sound]` (the cycle's
constructive ceiling) · `[propext, Classical.choice, Quot.sound]` (full
classical). The tier is a property of the **construction**, stated per object.

**Construction-relativity of the choice floor:** there are two ℚ and two ℝ.
`ℚ_VR`/`ℝ_VR` are proved isomorphic to mathlib and are therefore Tier-3 by
necessity (`ℝ_VR ≅ ℝ` is the full uncountable line). `Qop`/`Real` in `Continuum`
are choice-free and make **no** iso claim. Choice-free OR iso-to-mathlib, never
both.

---

## 3. What connects them

One move, at two levels: **identity is not granted, it is exhibited.**

* ZTL: `Z ∨ Z = F` — two occurrences of one mark are not one unknown.
* VR: set identity is a **witnessed bisimulation**, not a coincidence of graphs.
* The ledger built on ZTL: two ground names may be one document, and the cost of
  assuming otherwise is printed as a bracket rather than collapsed.

If ZTL "stitches the compiler to the protocol" downstream, this is what stitches
it to VR upstream.

---

## 4. What this file does NOT cover

The applications. As of 2026-08-17 the honest position is that ZTL's
*applications* are covered by existing tools — ProvSQL closed four of four
properties an internal note had claimed as its own, and the note was rewritten
to measurements and their limits. See `paper/PROVSQL-REVIEW-FINDINGS.md` and
`paper/AVAILABILITY-SURVEY.md` before claiming any application is new.

What survived every round is the *logic* and the *negative measurements*.
Deposited: `10.5281/zenodo.21981727`.
