# ZTL — Zero-Trust Logic

**V. Reznik. Preprint, v1.2-draft (unpublished, accumulating). v1.1
published 2026-07-12:
DOI [10.5281/zenodo.21323552](https://doi.org/10.5281/zenodo.21323552);
concept DOI
[10.5281/zenodo.21318981](https://doi.org/10.5281/zenodo.21318981)
(v1.0: [10.5281/zenodo.21318982](https://doi.org/10.5281/zenodo.21318982)).
Accumulated for v1.2: the measured narrowing of the
hereditary-characterization question (no depth-1 fence — §22 roadmap,
zverify §5); E23 (Zhegalkin: the {∧,⊕} basis survives entirely, the
GF(2) ring falls, Sheffer's stroke loses completeness) — section to be
folded in at release.
v1.1 corrects §19: the verdict warranty is a two-grade ladder
(sound — never lies / hereditary — never revoked); the v1.0 equivalence
claim "stability ⟺ invariance" (90/90) was pool-relative — falsified by
the or(ladder, gap) cells, found by E21 (the identity atoms of VR
Part II) and cross-checked by the section's own instruments. Same-day
self-correction, published as soon as three further expeditions
(E21–E22) had leaned on the corrected machinery and it held.**
The tag MEASURED means "verified by machine enumeration" (code in this
repository), as opposed to "argued"; references to Lean mean proofs
checked by the Lean 4 kernel with an **empty axiom list**.

---

## Abstract

Six independent engineering traditions — IEEE 754 arithmetic (NaN),
SQL's three-valued logic (NULL), taint tracking in security, abstract
interpretation in static analysis, imprecise probabilities in decision
theory, and provenance semirings in database theory — have spent decades
solving one and the same problem: how to compute honestly over
unverified data. We show (MEASURED) that all six implement fragments of
a single logic, and that this logic is generated in its entirety by one
principle: **truth is never granted on credit** — a connective returns T
only if T is forced under every classical reading of the unverified.
There are exactly two truth values (verdicts are always classical); the
third symbol Z is a mark on an unverified input, not a truth value.

For this logic (ZTL, Zero-Trust Logic) we build: a complete semantic
account with a measured price list (12 surviving laws, including modus
ponens, and 14 fallen ones — all the fallen laws are "truth from form");
the discovered split between *rules* and *laws*, with a one-directional
deduction theorem for the primitive arrow; a signed tableau calculus
with machine-proven soundness, completeness and cut admissibility; an
algebraic passport (the fallen idempotence yields exact truth
detectors, the external layer is expressively complete, a definable
external implication restores the full deduction theorem, Craig
interpolation holds, and the Blok–Pigozzi conditions are verified on
the matrix — ZTL is algebraizable, yet not self-extensional);
quantifiers; a modal identification (local
modality over the S5 frame of completions — versus global
supervaluation); a probabilistic identification (verdicts are the
{0,1}-threshold of Dempster–Shafer belief functions); a theory of
verification (a verdict is a pair "value + warranty", where the
warranty is a two-grade ladder: sound — never lies; hereditary — never
revoked) and of
evidence combination (conflict is never renormalized — Zadeh's paradox
is resolved in Smets' favor); and a quarantine passport that types
every refusal by its genesis — paradox (permanent), intrinsic (the
stipulation is forced), underdetermined (until a choice), unverified
input (until verification), inherited — with a measured stipulation
theorem separating the liftable from the permanent. The entire development — the core,
both engine certificates with cut admissibility, the algebraic
witnesses, the general fixed-point theorem and the expedition twins,
ten modules in all — is formalized in Lean 4 **with an empty axiom
list, definitions included**. As a
test bench the logic is run over the classical paradoxes — the liar,
Jourdain's carousel, Curry, Yablo, the crocodile, Russell — and in every
case explosion is replaced by pointwise quarantine (for Russell, 8 of 9
membership facts stay grounded; the uncountability of the continuum
splits into two independent failures). Functionally the {¬,∧,∨}
fragment coincides, cell by cell, with the external layer of Bochvar's
logic (1938) — a kinship found in the literature search after the
tables had been generated, not a source; the contribution of this work
is the generating principle, an implicational floor lying outside the
Rosser–Turquette standardness conditions, the calculus, the machine
verification, and the bridges to the engineering traditions. An interactive studio ships with the repository: natural
language is negotiated into ZFL, a small formal language whose
validity guarantees loadability, and judged by the measured core — the
pipeline itself obeys the logic it serves (the LLM's output is an
unverified input; the deterministic core is the customs).

## 1. Motivation: one problem, six independent solutions

Most of the data over which modern software computes is unverified:
sensor readings, user input, third-party databases, answers of network
services. Engineering answered not with a single theory but with local
inventions:

* IEEE 754 (1985): NaN — arithmetic is infected, comparisons refuse;
* SQL (1986): NULL — three-valued logic inside expressions, forced
  falsehood at the WHERE boundary;
* taint tracking (Denning, 1976; Perl taint mode, TaintDroid): a
  distrust mark flows through computations, and only an explicit check
  sanitizes;
* abstract interpretation (Cousot & Cousot, 1977): interval values flow,
  assertions are checked for being forced;
* imprecise probabilities (Walley, 1991) and Dempster–Shafer theory:
  ignorance is an interval [Bel, Pl], not a point probability;
* provenance semirings (Green–Karvounarakis–Tannen, 2007): trust in a
  fact is a polynomial over its sources.

Each of these inventions parried its own special case of one disease:
naive treatment of the unverified manufactures confidence out of
nothing. We show that the six practices share a common denominator — a
two-valued logic over marked inputs with a single generating principle —
and that this denominator survives a full logical development: a
calculus, quantifiers, modal and probabilistic semantics, machine
verification. Along the way the classical paradoxes of self-reference,
from the liar to Russell, receive a uniform diagnosis (quarantine
instead of explosion) — they serve as a test bench, not as the point of
departure.

The principle from which everything is built borrows its name from
security: default deny. A defective input may be granted neither
classical value, but every compound assertion about it must receive a
classical verdict — "true only if forced".

## 2. Definitions

**Truth values:** T (earned truth), F (falsehood). **Input mark:**
Z (zero-trust, "not earned") — a property of an atomic datum, not a
truth value; it participates in the calculating tables as a third
symbol.

**Generating principle.** For any classical connective f, its ZTL lift:

    f*(x₁,…,xₙ) = ⋀ { f(v₁,…,vₙ) : vᵢ ∈ subs(xᵢ) },
    where subs(Z) = {T,F}, subs(v) = {v} otherwise;
    ⋀ is classical conjunction over all combinations.

Every occurrence of Z is substituted independently; the result is always
classical.

**Corollary (greediness theorem, MEASURED):** no compound formula ever
takes the value Z; Z lives only on atoms.

**Tables** (generated by the principle; the anchor cells were postulated
at design time and are reproduced by the principle — `ztl.py`):

| x | ¬x |   | ∧ | T | F | Z |   | ∨ | T | F | Z |   | → | T | F | Z |
|---|----|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| T | F  |   | T | T | F | F |   | T | T | T | T |   | T | T | F | F |
| F | T  |   | F | F | F | F |   | F | T | F | F |   | F | T | T | T |
| Z | F  |   | Z | F | F | F |   | Z | T | F | F |   | Z | T | F | F |

⊕ and ↔: every cell involving Z equals F; on classical inputs —
classical.

**Generating basis (MEASURED):** {¬,∧,∨} generates everything:
p→q = ¬p∨q, p⊕q = (p∧¬q)∨(¬p∧q), p↔q = (p∧q)∨(¬p∧¬q) are surviving
identities.

**Entailment:** Γ ⊨ φ iff every valuation making all premises T makes
the conclusion T. Tarskian by construction.

## 3. Results (all MEASURED)

### 3.1 Laws: 12 alive, 14 fallen

Alive: MP, non-contradiction, transitivity of →, commutativity and
associativity of ∧/∨, both distributivities, and the three canonical
definitions of the derived connectives. Fallen: ¬¬p=p, both De Morgan
laws, contraposition-as-identity, ⊕=¬(↔), idempotence of ∧/∨,
absorption, the units (p∧T=p, p∨F=p), excluded middle, p→p, Peirce's
law, q→(p→q). The common trait of the fallen: each fails only on Z, and
each is a law of "free truth" (truth from form or from polarity flip).

### 3.2 The split between rules and laws

Of 14 classical inference rules taken as entailments, 12 survive —
including contraposition-as-a-rule (p→q ⊨ ¬q→¬p) and the K-rule
(q ⊨ p→q), whose law twins fell. Two fall: ¬¬-elimination (¬¬p ⊨ p; Z
leaks through double negation) and "tautology in the conclusion"
(p ⊨ q∨¬q; a fresh atom earns no truth). Classical logic cannot see the
split because the deduction theorem glues it shut; in ZTL the deduction
theorem works **left-to-right only**: ⊨A→B implies A⊨B, but p⊨p while
⊭p→p. The arrow is stricter than entailment: entailment transports
earned truth, the arrow is a verdict that must earn its own. (The
one-way-ness is a property of the primitive arrow, not of the language:
a definable external implication satisfies the full deduction theorem —
§3.6.)

### 3.3 Classification: paracompleteness

ZTL is paracomplete (LEM fell) but not paraconsistent in the ⊨ sense:
v(p)=v(¬p)=T is unsatisfiable, there are no gluts, explosion is
vacuously valid. Semantic MP is intact — ZTL is stronger in inference
than Priest's LP.

### 3.4 Paradoxes: quarantine, not tables

Negation has no fixed point (¬Z=F) — the liar cannot be seated by the
tables (MEASURED: enumeration of all values). Paradoxes are extinguished
by the quarantine flag: Z-sentences are exempted from the Tarski schema.
Quarantine is detectable from inside: isZ(x) = ¬(x↔x). The same formula
expresses the revenge liar; its content evaluates to T while the
sentence is denied truth — a price paid deliberately (it is the standard
price of all quarantine theories; here it is written out explicitly).

### 3.5 Incompatibilities (mini-theorems)

1. {¬Z=F, T→Z=F} ⟹ contraposition-as-identity is impossible
   (verified by substitution).
2. A value housing the liar must be a fixed point of ¬; pessimism
   (¬Z=F) excludes this ⟹ the quarantine flag is irremovable.
3. Collapsing Z→F at the atom (instead of at the operator) restores all
   classical laws and turns the system verbatim into Bochvar's isomorph
   B3□ — the novelty and the rules/laws split vanish.

### 3.6 The algebraic passport: completeness as a logic (MEASURED + Lean)

The fallen laws pay for the algebra. The chain, each link verified by
total enumeration and kernel-checked in Lean (module `ZAlgebra`, empty
axiom list):

1. **Fallen idempotence is a truth detector.** J_T(p) = p∧p takes T
   exactly at p=T (the decorrelated readings of Z kill the Z-diagonal);
   J_F(p) = ¬p∧¬p detects F; J_Z = isZ detects Z. Three exact disjoint
   indicators — the Rosser–Turquette J-operators, grown from ZTL's own
   connectives.
2. **Expressive completeness of the external layer.** Every external
   function Vⁿ → {T,F} is a disjunction of indicator conjunctions over
   the cells of its table (MEASURED totally: 8 of 8 unary, 512 of 512
   binary; the unary construction is a Lean theorem). The basis {¬,∧,∨}
   generates the entire external clone.
3. **The full deduction theorem returns — one floor up.** The definable
   external implication E(p,q) = ¬(p∧p) ∨ (q∧q) satisfies
   Γ,A ⊨ B ⟺ Γ ⊨ E(A,B) in both directions (MEASURED: 0 divergences on
   324 triples where the primitive arrow diverges 20 times; Lean:
   `ddt_E` over the whole language, with premise lists). The logic does
   internalize its own consequence — with the meta-level "if A is true
   then B is true" made internal, not with the zero-trust arrow, whose
   one-way-ness (§3.2) stands.
4. **Algebraizability.** The same-value detector
   Δ(p,q) = (J_T p ∧ J_T q) ∨ (J_F p ∧ J_F q) ∨ (J_Z p ∧ J_Z q) and the
   truth equation p∧p ≈ ¬(p∧¬p) (which holds exactly at p=T) witness
   the Blok–Pigozzi conditions: ⊨Δ(p,p); p, Δ(p,q) ⊨ q; congruence for
   all six connectives; p ⊣⊨ Δ(p∧p, ¬(p∧¬p)). All four verified on the
   matrix (MEASURED + Lean); by the Blok–Pigozzi characterization
   [31] **ZTL is algebraizable** — its equivalent algebraic semantics
   is the quasivariety generated by the three-element algebra. This is
   family kinship, not discovery: Bochvar's external logic is
   algebraizable via the quasivariety of Bochvar algebras
   (Bonzio–Pra Baldi [32]); ZTL grows the witnesses from its own
   primitives, and we verify the conditions directly rather than
   inherit them.
5. **Yet not self-extensional.** p ⊣⊨ p∧p (idempotence is dead as a
   law, alive as interderivability) while ¬(p∧p) ⊭ ¬p (at p=Z):
   interderivability is not a congruence. The same failure that breaks
   self-extensionality builds the detectors — one design decision seen
   from two sides.
6. **Structurality.** The substitution lemma (Lean: `evalF_subst`, by
   induction on the formula) gives: Γ ⊨ φ implies σΓ ⊨ σφ for every
   uniform substitution σ. Together with reflexivity, monotonicity and
   cut (immediate from the definition), ⊨ is a **structural Tarskian
   consequence relation** — finitary and decidable, since the matrix is
   finite.
7. **Craig interpolation** holds, and its proof is one line on top of
   item 2: if A ⊨ B, the projection of A onto the shared atoms ("some
   completion of A's private atoms makes A true") is an external
   function of the shared atoms, hence a formula — and its J-DNF
   interpolates: A ⊨ I (A's own valuation is the witness), I ⊨ B (glue
   the A-witness to the current valuation; B does not read A's private
   atoms). MEASURED totally: 400 of 400 entailing pairs on the
   one-shared-atom pool, 32 of 32 on a two-atom cross-sample. The
   standard caveat: with an empty shared set the interpolant is a
   constant, and in the constant-free language ⊤ = ¬(x∧¬x) spends a
   spare variable — exactly as classically.

### 3.7 The quasivariety, scouted (MEASURED)

A reconnaissance of the equivalent algebraic semantics — the
quasivariety generated by A = ({T,F,Z}; the six connectives) — before
committing to its structure theory:

* **Subalgebras:** exactly two — the Boolean core {T,F} and A itself.
  C-extension, algebraically: the classical world is the unique proper
  subalgebra.
* **Congruences:** the measurement corrected our guess — A is NOT
  simple. The partition {T,F}|{Z} is a congruence, and it is exactly
  the *greediness kernel*: its compatibility IS the statement that no
  operation ever outputs Z. The congruence lattice is the three-chain
  Δ < θ_Z < ∇, so **A is subdirectly irreducible with monolith θ_Z** —
  greediness is not merely a theorem about the algebra, it is its
  monolith. The quotient A/θ_Z is the two-element algebra in which
  every operation lands in the classical class: the mark evaporates,
  algebraically.
* **The clone theorem (exact):** the term operations of A are
  *precisely* the projections plus all external functions (unary
  1 + 8; binary 2 + 512, by closure computation) — §3.6's expressive
  completeness sharpened to a clone identity: nothing else sneaks in.
* **The Plonka probe (the structural discriminator):** Bochvar
  algebras [32] are built over Plonka sums, and Plonka sums of Boolean
  algebras satisfy every *regular* Boolean identity. A fails the
  regular identities p∧p = p, p∨p = p, ¬¬p = p — so **A is not a
  Plonka sum of Boolean algebras**: the greedy quasivariety is
  structurally foreign to the weak-Kleene/BCA landscape. Kinship in
  expressive power, divorce in structure.

What a dedicated paper would need: a quasi-equational axiomatization
of Q(A), its subquasivariety lattice, and a representation theorem
replacing Plonka sums. The reconnaissance says the ore is there; the
mining is left as a separate work.

## 4. Place in the literature

The pedigree, with the ledger kept honestly. Nothing here was taken
from Bochvar constructively: the tables were generated by the
zero-trust principle (§2; the anchor cells were design axioms), and
the kinship below emerged only in the subsequent literature search —
the repository's commit history is the lab notebook of that order.
What the search found: on {¬,∧,∨} ZTL coincides verbatim with the
external layer of Bochvar's B3 (1938; built against the paradoxes) —
¬ = ⌉ (the ◇-negation), ∧ = ∩□, ∨ = ∪□ — and the truth detector
J_T = p∧p of §3.6, derived here from the fallen idempotence, carries
the table of Bochvar's *primitive* assertion operator: what he
postulated, the principle re-derives. There the coincidence ends. The
delta is 7 cells in →, ↔, ⊕: a systematic closing of the places where
Bochvar's quarantine begets vacuous truth (his ½⊃0 = 1, our Z→F = F).
The internal dynamics are opposite — his meaninglessness is infectious
(the internal layer), our mark evaporates at the first operator — and
so is the ontology: his third symbol is a *value* sentences take; our
verdicts are two-valued, and the non-classical letters are *marks*
(Z on a datum, N in the solver, §10) — the alphabet is four letters,
N, F, T, Z, in the genetic order. ZTL's implication is his
◇A⊃□B taken as a primitive; a polarity-adaptive translation (□ in
positive positions, ◇ in negative ones) instead of a uniform one. ZTL
falls outside Tomova's classification of "natural implications" (it
fails p→p) and coincides with none of the literal paralogics of the
Karpenko–Tomova lattice (2017). Kindred in spirit: supervaluationism
(rigid, non-tabular), subvaluationism/Jaśkowski (its dual), SQL NULL
(lazy), IEEE NaN (comparisons), exceptions with try/catch at every node
(greediness). The motivation "greedy local supervaluation / default
deny" was not found in the surveyed literature.

**Devyatkin (2016, "Non-classical modifications of many-valued
matrices", read in full).** The {¬,∧,∨} core of ZTL fits the templates
of his class 8Kb* — the paracomplete duals of the 8Kb family
(Carnielli–Marcos, 8192 matrices): ¬Z=F, Z∧x=F, Z∨T=T land in the
permitted "0 or 1" cells. So our triple is a member of a catalogued
class — a stronger pedigree than previously known. However, the entire
catalogue is built under the Rosser–Turquette standardness conditions
for implication: middle→0 must be designated. ZTL with Z→F = F and
Z→Z = F violates these conditions deliberately — the
implication/equivalence floor of ZTL lies outside the catalogue, and it
is precisely this floor that carries all the system's signatures. The
significance logics of Goddard–Routley (checked at survey level) use
infectious nonsense plus classical external operators — Bochvar's
architecture, not per-operator collapse.

**Database-theory neighbours.** The closest kin is Libkin's line:
(a) certain answers ("true in every completion of an incomplete
database") = global supervaluation, the high-complexity theoretical
gold standard (Libkin, ICDT'15/TODS'16); (b) Libkin–Peterfreund, "SQL
Nulls and Two-Valued Logic" (PODS'23): SQL without the third value —
atomic comparisons with NULL yield false (in both polarities, the same
NaN asymmetry), while the Boolean layer is fully classical, restoring
all laws (their goal is optimization). On the "where does indeterminacy
collapse" scale, three of four positions are taken:

| where the indeterminacy collapses | system |
|---|---|
| at the atom (predicate) | Libkin–Peterfreund 2VL ≈ Bochvar's B3□ |
| **at every operator** | **ZTL — position not found occupied** |
| over the whole formula at once | certain answers / supervaluation |
| never (it flows) | Kleene / SQL 3VL inside expressions |

The per-operator position is the only one that yields tabularity,
two-valued verdicts and the internal signatures (¬¬Z=T, Z↔Z=F) at once;
the price is the rewriting laws, which the atomic position preserves
(which is why the optimizers chose it). A terminological caution:
"local/global validity" in the philosophy of supervaluationism
(McGee–McLaughlin, Varzi) is a distinction at the level of inferences,
not of operators; our "locality" is a different notion.

## 5. The calculus: signed tableaux (MEASURED)

Hilbert style is closed off (axiom K fell, valid formulas are scarce),
the deduction theorem is one-directional — the calculus is built as
signed tableaux (the Rousseau–Hähnle architecture for finitely-valued
logics).

**Signs** — four sets of values:

* strict: **T** = {T}, **F** = {F};
* weak: **P** = {T,Z} ("possibly T"), **N** = {F,Z} ("did not earn T").

**Rules** (branches separated by "|", a comma puts both nodes on one
branch):

```
T:¬φ  →  F:φ                       F:¬φ  →  P:φ
T:(φ∧ψ) →  T:φ, T:ψ                F:(φ∧ψ) →  N:φ | N:ψ
T:(φ∨ψ) →  T:φ | T:ψ               F:(φ∨ψ) →  N:φ, N:ψ
T:(φ→ψ) →  F:φ | T:ψ               F:(φ→ψ) →  P:φ, N:ψ
T:(φ⊕ψ) →  T:φ,F:ψ | F:φ,T:ψ       F:(φ⊕ψ) →  P:φ,P:ψ | N:φ,N:ψ
T:(φ↔ψ) →  T:φ,T:ψ | F:φ,F:ψ       F:(φ↔ψ) →  P:φ,N:ψ | N:φ,P:ψ
```

On compound formulas P≡T and N≡F (the greediness theorem: a compound is
never Z). **Branch closure:** the intersection of some formula's signs
is empty (T against N, F against P, T against F); a pair P and N on an
atom does *not* close the branch — their intersection {Z} yields a
Z-countermodel. **Procedure:** Γ ⊢ φ ⟺ the tableau from
{T:γ | γ∈Γ} ∪ {N:φ} closes entirely.

**The zero-trust signature inside the calculus.** T-polarity rules
demand strict certificates (only T/F); weak signs appear exclusively in
F-polarity. Classical tableaux are these same rules with P≡T, N≡F
glued — the whole contribution of Z is the unglueing of the negative
signs. Proving truth in ZTL costs the same as classically; refuting is
cheaper, because a countermodel may hide in Z.

**Soundness and completeness (MEASURED):** (a) each rule is
machine-checked against the preimage of its table — the branches cover
the preimage exactly; (b) the tableau decisions coincide with semantic
⊨ on 2462 entailments (the rule battery + all pairs of a generated
formula pool + a sample of two-premise sequents). For finitely-valued
tableaux with exact preimage coverage, soundness/completeness is the
standard constructive result; the machine cross-check is an independent
control of the implementation (and §8 upgrades it to a kernel-checked
proof).

**The sequent reading and semantic cut elimination.** Read bottom-up,
the tableau engine is a cut-free sequent calculus for the refutability
judgment ⊢ S ("the signed set S is jointly unsatisfiable"): axioms are
the contradictory atom constraints, the rules are the twelve signed
expansions with premises above the line, derivability is the engine's
closure. The cut rule on a covering sign pair (every value lies in
{T} ∪ {F,Z}):

    ⊢ S, T:φ    ⊢ S, N:φ
    ─────────────────────  (cut)
           ⊢ S

is sound, and the cut-free system is already complete — hence **cut is
admissible**: the classic semantic cut elimination, here with a machine
certificate. Kernel-checked with zero axioms (Lean: `cut_admissible`,
`weakening_admissible`, `identity_refutable` on top of `closes_iff`);
MEASURED directly as well (identity 14/14; weakening 696 checks, 0
violations; cut 406 fired instances on each covering pair, 0
violations). What remains proof-theoretic future work is a *syntactic*
cut-elimination procedure with complexity bounds — the admissibility
itself is settled.

## 6. Quantifiers: finite domains and beyond (MEASURED)

By the generating principle: **∀xφ = T if every instance is strictly T,
else F** (one Z-witness poisons the universal); **∃xφ = T if some
instance is strictly T, else F** (a Z-candidate does not count as a
witness). Greediness extends: quantified formulas never take Z.

Measured over all interpretations (unary P,Q — domains 1..3; binary R —
domains 1..2):

* **Identities:** both distributions survive (∀ over ∧, ∃ over ∨); both
  quantifier De Morgan laws fell (counterexample: a one-element domain
  with P=Z — Z hides under negation).
* **Instantiation asymmetry:** UI survives even as a **law**
  (⊨ ∀yP(y)→P(a) — the universal has earned its truth, spend it
  freely), EG as a law fell (⊭ P(a)→∃yP(y) at P(a)=Z); only the EG rule
  survives.
* **The rules/laws split continues on the quantifier floor, and the
  first rule casualty appears:** ¬∃yP ⊭ ∀y¬P — from "no strict witness"
  it does not follow that "all are strictly false": Z-elements remain.
  This is the quantifier twin of fallen ¬¬-elimination. The converse
  rule ∀y¬P ⊨ ¬∃yP survives, as does the quantifier swap ∃x∀yR ⊨ ∀y∃xR.
* **Classical ornaments:** quantified LEM fell; the "drinker paradox"
  ∃y(P(y)→∀zP(z)) — a classical validity — fell in ZTL (in a bar with
  one Z-patron there is no drinker).

**Quantifier tableaux** (MEASURED): the finite-domain rules continue
the sign signature — T:∀ unfolds into strict T:φ(aᵢ) on one branch,
F:∀ into weak N:φ(aᵢ) across branches; ∃ mirrors. Tableau decisions
coincide with semantic enumeration on 28 sequents (domains 1–2).
A by-product: ¬∀yP ⊭ ∃y¬P even as a rule — the second fallen quantifier
bridge, symmetric to ¬∃ ⊭ ∀¬ (negation hides Z in both directions).
The finite-domain quantifier tableaux are now **kernel-checked** (Lean
module `ZQuant`, zero axioms): over a finite domain the quantifiers are
strict folds expressible in the certified language (∀ as a conj-fold,
∃ as a disj-fold — on a singleton domain both collapse to the J_T guard
φ∧φ of §3.6), the n-ary signed rules are theorems about the folds
(`cover_allF_T/F`, `cover_exF_T/F`), UI/EG hold in membership form over
the whole language (`ui_mem`, `eg_mem`), and eight battery verdicts —
including the failing drinker and quantified LEM — are kernel
evaluations of the certified engine itself.

**Arbitrary domains: parameter tableaux (MEASURED).** Over arbitrary
domains the finite unfolding is unavailable; the standard cure —
parameter (free-variable) tableaux with γ/δ rules — carries the
zero-trust sign discipline over exactly:

    γ (reusable, every parameter):   T:∀xφ → T:φ(c)     F:∃xφ → N:φ(c)
    δ (fresh parameter, once):       F:∀xφ → N:φ(c*)    T:∃xφ → T:φ(c*)

Fresh witnesses appear exactly where the propositional calculus allows
weak signs (F-polarity) or demands a strict witness (T:∃). Status,
honestly split: **soundness is measured** — every sequent the engine
proves is re-checked by total enumeration over finite domains, every
saturated open branch yields a countermodel that is verified by
evaluation (battery of 13: UI/EG, distribution, quantifier bridges,
swap and its failing converse, the failing unguarded drinker and
quantified LEM — all 13 verdicts confirmed). **Completeness is the
standard Hintikka-saturation argument** for finitely-valued signed
tableaux [27] — argued, not measured. Two honest FO phenomena appear on
cue: on invalid sequents whose branches spawn witnesses forever
(the unguarded drinker; the converse quantifier swap) the tableau does
not terminate and invalidity is certified by a finite countermodel
instead; and FO-ZTL is **undecidable** — the J-guard translation
P ↦ P∧P (§3.6) makes every atom classical, embedding classical
first-order validity (the guarded drinker is ZTL-valid and needs the
classic two γ-rounds). The tableaux give semi-decidability, as
classically.

## 7. Limitations and honest caveats

* No new three-valued functions exist or are claimed (functional
  completeness — Finn); the contribution is the choice of primitives
  and the principle. Positively: the chosen primitives generate the
  whole external clone (§3.6), so ZTL is the external layer presented
  by different primitives — its abstract metatheory (algebraizability
  included) is a matter of verification, not invention.
* "Deviation from classical logic" is merchandise here, not defect: on
  classical inputs the deviation is zero (C-extension); all exotica is
  the price of the policy toward Z.
* The price list is not negotiable item by item: the fallen laws are
  consequences of three fixed design forks (¬Z=F; greedy collapse;
  Z↔Z=F); regaining any law requires flipping a fork (see §3.5).

## 8. Machine verification in Lean 4

The core is ported to Lean 4 (v4.29.1, no mathlib): the connectives are
generated by the lift (tables are not postulated — computed), the anchor
cells are turned from postulates into theorems, the 12 alive and 14
fallen laws, semantic MP, the greediness theorem, the homelessness of
the liar (∀v, ¬v ≠ v), the isZ detector and the quantifier UI/EG
asymmetry — all proven.

**Axiom status: the empty list.** `#print axioms` over the whole corpus
returns "does not depend on any axioms": no Classical.choice, no
Quot.sound, not even propext; pure computation. This is the strictest
possible tier — rare for a substantial logical system.

**Part II** (same file): the entailment rule battery (11 alive + 2
fallen, including the split contraposition-rule vs contraposition-law),
no-gluts, the lazy Kleene register with proven monotonicity of all
connectives in the information order, non-monotonicity of the greedy
register, the liar's home in the lazy register (knot Z = Z — rfl), the
absence of a greedy carousel model (all 9 pairs), lazy grounding, and
the computed revenge bullet.

**Part III — the tableau pillars over the whole language.** An
inductive formula type Fm with evaluation; **pillar 1**: greediness is
proven for the entire language (every compound formula is classical
under every valuation — by constructor analysis, not by battery);
**pillar 2**: the preimage coverage of each of the 12 tableau rules — as
⟺-theorems for arbitrary subformula values (`cover_*`).

**The trade certificate (lean/TableauCert.lean).** The tableau engine
is formalized in full: working rules over the generating basis
{¬,∧,∨} (weak signs only in F-polarity), atoms handled by constraint
intersection, the heavy connectives →,⊕,↔ reduced to the basis by the
surviving identities (imp_def/xor_def/xnor_def — theorems of the core).
Proven:

* `closes_iff` — **soundness and completeness**: the tableau closes ⟺
  the signed nodes are unsatisfiable (induction on weighted size, for
  all formulas);
* `tproves_iff` — **the entailment certificate**: Γ ⊢ φ by the engine ⟺
  every valuation making the premises T makes the conclusion T.

Six smoke runs of the certified engine coincide with the measured
results (⊬ p→p, MP ⊢, ¬(p∧¬p) ⊢, ⊬ LEM, contraposition-rule ⊢,
¬¬-elimination ⊬). **The certificate's axiom status: the empty list** —
same as the core. This was achieved by disinfecting every known source:
structural recursion on fuel instead of well-founded recursion (the WF
machinery pulls in propext/Quot.sound), signs as functions V→Bool
instead of lists (Lean core's list-membership decision procedure
carries propext), a recursive satisfaction predicate instead of
∀-membership, combinator chains of Iff instead of rewriting by
equivalences (rw with an Iff applies propext), and hand-rolled Nat
arithmetic instead of omega (omega carries propext and Quot.sound).
**The native engine (TableauCertN.lean):** the engine with the native
signed rules for →,⊕,↔ is certified by the same induction
(closesN_iff), and the theorem engines_agree shows both engines return
identical verdicts; the former footnote about their equivalence is
closed by a theorem. Additionally (all with zero axioms): the Lean port
of marked sets (§12: a mark earns membership nowhere; a marked set is
not provably a subset of itself; {Z,Z}≠{Z}; |{Z}|=[1,1]) and a corpus of
facts — domain-2 quantifiers (∀=zand, ∃=zor: the UI law alive; EG,
¬∃⊭∀¬, ¬∀⊭∃¬, quantified LEM, the drinker — fallen) and dynamics (liar
period 2, carousel period 4 with no fixed points, Curry homeless
greedily and grounded lazily, cycle parity for lengths 2/3, the Yablo-3
truncation with a unique grounded model, the nullity of the crocodile's
deal). **The algebraic passport (`ZAlgebra`, zero axioms):** the
J-indicators, unary expressive completeness as a single theorem over
all 8 target tables, the full deduction theorem for E over the whole
language with premise lists (`ddt_E`), all Blok–Pigozzi witnesses
(Δ-spec, reflexivity, detachment, congruence for the six connectives,
the truth equation, condition (iv)), the failure of
self-extensionality, the substitution lemma and structurality of ⊨
(`entails_structural`). **The sequent reading (`ZSequent`, zero
axioms):** cut admissibility on top of the engine certificate
(`cut_admissible`), admissible weakening, derivable identity — the
semantic cut elimination of §5, kernel-checked. **Quantifier tableaux
(`ZQuant`, zero axioms):** finite-domain quantifiers as strict folds,
the n-ary signed rules as preimage-coverage theorems, UI/EG in
membership form, and the battery of eight tableau verdicts as kernel
evaluations of the certified engine (§6). **General Knaster–Tarski
(`ZGround`, zero axioms):** the lazy register over the whole language,
monotonicity, the least fixed point by bounded iteration, and the
absoluteness of the grounded part (§9). **Expedition twins (`ZExped`,
zero axioms):** streams — the equality atom never earns T, one finite
witness earns apartness and it persists, Cantor's diagonal earns strict
non-membership against every registry entry (§13); one marked pair
collapses the injectivity certificate for every function including the
identity (§14); interval decorrelation and unearned self-identity of a
nondegenerate mark (§15); Dempster–Shafer thresholds (§16); atom
verdicts as □/◇ thresholds with the ¬¬-cell separating the local
ladder from global supervaluation (§17). The certified language now carries the
constants ⊤/⊥ (the engines and both certificates extended, the
sequent/quantifier/algebra modules unaffected), which closes the last
expedition remainder: **Russell's grounding half is kernel-computed**
— `lfp RUSSELL = [F,F,T,F,T,F,F,F,Z]` by the certified iteration of
§9: eight membership facts ground, exactly R∈R stays quarantined
(`russell_grounded`, `russell_verdicts`); ⊢ ⊤, ⊥ ⊢ φ and ⊬ ⊥ run
through the certified engine. **The stitch (`bridge.py`):** one questionnaire, two
engines — 141 kernel-computed answers (both registers cell by cell,
the J-operators, E and Δ, certified-engine verdicts on a shared
propositional and quantified battery with constants, lazy lfp of the
zoo up to the nine-fact Russell system) compared mechanically against
the Python stands on every regression run: zero divergences. Two further disinfection
pitfalls surfaced here: an overlapping wildcard row in a match taints
the DEFINITION itself with propext through the compiled matcher
(invisible to theorem-level axiom prints — `kand`/`kor` were rewritten
with explicit cells, and the corpus now prints definition-level axiom
checks too), and core's `List.length_map`/`length_replicate` are
simp-proved and carry propext — replaced by hand-rolled inductions
(likewise the core Int order lemmas, omega-proved: general interval
statements live over Nat, Int stays for computation).

## 9. Quarantine as a fixed point: the two-register architecture
(MEASURED)

The quarantine flag of fork 2 in §3.5 is formalized à la Kripke. A
system of sentences with a truth predicate (λ: ¬Tr(λ) etc.); the "jump"
J re-evaluates the sentences under the current valuation; fixed points
of J are self-consistent valuations. Two registers with DIFFERENT
negations are put on trial: the greedy one (ZTL tables, verdicts:
¬Z = F — "not earned") and the lazy one (strong Kleene, the solver:
¬Z = Z — "do not judge the uncomputed"; Z flows through connectives).
What follows shows these are not two candidates for one role but two
mandatory different roles.

**Enumeration results** (the zoo: liar, truth-teller, Jourdain's
carousel, the even cycle, a grounded chain, the avenger):

1. **The greedy jump is non-monotone** in the information order
   (witnesses found on every system) — the Knaster–Tarski argument does
   not apply to it.
2. **On odd cycles the greedy jump has no fixed points at all**; the
   iteration oscillates: liar — period 2 (F→T→F...), carousel — period
   4 (FF→FT→TT→TF), avenger — period 2. The oscillations of revision
   theory (Gupta–Belnap) arise here not as a postulate but as the
   behavior of the greedy iteration.
3. **The lazy jump is monotone** and has a least fixed point
   everywhere: grounded sentences receive classical values, paradoxical
   ones — Z. The even cycle: three fixed points ({T,F}, {F,T}, {Z,Z}),
   the least being mutual quarantine (underdetermination, not paradox).
4. **Verdicts are greedy, read over the finished point**: the content
   of the avenger μ at grounded μ=Z evaluates greedily to T, while μ is
   denied truth — the "bullet" is paid inside the formal construction,
   not by a disclaimer.

**Conclusion (the architectural theorem of this stage):** the
two-register design is a necessity, not a convenience. The greedy
register cannot ground itself (no fixed points on the liar); the lazy
one cannot pass verdicts ("exactly falsehood"). Quarantine := the Z-set
of the lazy jump's least fixed point; ZTL := the greedy reading on top.
The engineering precedent — SQL (Kleene inside expressions, forced
falsehood at the WHERE boundary) — turns out to be not an analogy but
the same theorem, found by practice.

**The quarantine passport (MEASURED).** Z alone is blind: the liar and
the truth-teller land in quarantine with the same mark. The passport
cures the blindness without touching the logic — verdicts, tables and
greediness are intact; it is solver-side metadata computed per strongly
connected component of the dependency graph. Kinds: **PARADOX** — the
component has no classical model consistent with its grounded
environment (odd cycles; the greedy oscillation period is recorded:
liar 2, carousel 4) — the refusal is *permanent*; **INTRINSIC** — exactly one
classical model exists (Kripke's intrinsic value): ungrounded, yet
uniquely consistent — the stipulation is forced, not chosen;
**UNDERDETERMINED** —
classical models exist (≥ 2: even cycles, the truth-teller) — the
refusal stands *until stipulation*; **INPUT** — a plain unverified datum — the
refusal stands *until verification* (§19); **DOWNSTREAM** — inherited
quarantine with the culprits listed (the provenance of refusal, §14
again). The operational content is the **stipulation theorem**
(MEASURED totally on a mixed zoo carrying every kind at once, with the
grounded part untouched): a component carries classical models
(INTRINSIC or UNDERDETERMINED) iff stipulating any of them grounds it
cleanly — the forced choice and the free one obey the same mechanics —
and it is PARADOX iff every decree contradicts the component's own
definitions: the liftable and the permanent, mechanically separated. The
passport is thereby a *biography* of the mark — there are exactly three
ways to acquire it, and liftability follows genesis: **born** with the
datum (INPUT — lifted by verification), **hardened** out of a solver
phase that completed without resolving (INTRINSIC — lifted by the
forced stipulation; UNDERDETERMINED — lifted by a chosen one;
PARADOX — lifted by nothing), or **inherited**
(DOWNSTREAM — lifted with the culprits). "Completed" is a theorem, not
a hope: the lazy iteration provably terminates within n+1 steps (§8,
`ZGround`), so the phase N always dies — the liar is never "still
computing"; the solver's verdict on it is final, and what is eternal
is not the process but the refusal. (Contrast revision theory [7],
where the process itself never settles.) The parity
theorem of §11 re-derives through the passport (62 of 62 cycles), and
Russell (§18) reads: R∈R — PARADOX, permanent; the twin S∈S —
UNDERDETERMINED, awaiting an external decision; eight facts grounded.
This is Kripke's taxonomy plus revision-theoretic signatures
[5, 7], packaged as a computable instrument; the refusal classes now
mirror §19, and quarantine = (Z, passport). Honest caveat: Yablo stays
invisible — every finite truncation is grounded (§11), so the passport
of infinite regress needs an infinite instrument.

**The architecture, kernel-checked in general form.** The two-register
theorem no longer rests on per-instance measurements: the Lean module
`ZGround` (zero axioms) proves, for EVERY finite system of definitions,
that lazy evaluation is monotone over the whole language
(`evalK_mono`), hence the lazy jump is monotone (`jumpL_mono`); the
iteration from ⊥ ascends and stabilizes within n+1 steps at the least
fixed point (`kt_fixed`, via an information-measure pigeonhole — no
classical choice, no well-founded machinery); the least point lies
below every fixed point (`kt_least`); and a coordinate grounded in the
least point carries the same classical value in every fixed point
(`grounded_absolute`) — quarantine is well-defined, machine-checked.
Together with the greedy register's kernel-checked non-monotonicity
(§8, Part II), the necessity of two registers is now a theorem end to
end.

## 10. The ontological status of Z: the system's passport

The final and most precise formulation of what has been built:

```
Truth values:      T, F                    (verdicts are always two-valued)
Input mark:        Z "unverified"           (a property of data, not truth)
Solver state:      N "not yet computed"     (a computation phase, present
                                             only under self-reference;
                                             provably finite — §9 — and
                                             never escapes outward)
Reading policy:    local, default deny      (the three-symbol tables are
                                             the policy's calculator)
```

**ZTL is a two-valued logic that refuses to lie about the unverified.**
Two-valuedness of the values does not mean classicality: the entailment
relation is provably different (LEM fell, the deduction theorem is
one-directional, ¬¬p ⊭ p — §§3–5). A logic is defined by its
entailment, not by its palette.

**Local versus global reading of the mark.** "Z is a mark on the atom"
admits two readings of verdicts: the global one ("a formula is
assertable if true under all substitutions into the marked atoms at
once" — classical supervaluation) and the local one ("every operator
consults the mark on the spot" — ZTL). The anchor cells separate them
unambiguously: on ¬¬Z (ZTL: T, globally: F) and on Z↔Z (ZTL: F,
globally: T); the other five cells coincide. The global reading returns
all classical tautologies but loses tabularity (supervaluation is not
truth-functional) and both signature cells — the ladder of floors and
the NaN signature "not equal to itself". The anchors choose locality.

**Why not four values.** The temptation to include N as a fourth value
(precedent: Codd's two NULLs for RM/V2, rejected by industry) is
declined: values are not multiplied, non-values are typed. N is the ⊥
of the fixed-point iteration (§9), the pending of any promise: it
exists only inside the solver and never returns outward. The
four-valued algebra {T,F,Z,N} with the lazy lift over ZTL is coherent
and factorizes into our two registers ({T,F,Z} fragment = ZTL, {T,F,N}
fragment = Kleene), but it packs two phases into one type — a monolith
instead of modules; it is kept as a possible appendix, not as the core.

**Kleene, read through this passport.** Kleene's third element was
epistemic by intent — "undefined, not yet computed" — but his logic
has a single register, so the status had no home except inside the
value algebra, where it was forced to flow (¬N = N: negation passes
the unknown on). Typed by our passport, his element conflates the two
non-values: the *mark* on a datum (external, static, lifted only by
the act of verification) and the *phase* of a computation (internal,
dynamic, lifted by the iteration itself — and hardening, when it never
resolves, into the quarantine mark with its own passport of kinds,
§9). Strong Kleene logic is what results when both non-values are
made to share one symbol *as a value of assertions*; SQL NULL's
notorious ambiguity — "unknown", "not applicable", "pending" in one
symbol — is the same conflation observed in the wild. The fault is
not the shared symbol (our own solver reuses Z positionally during
iteration) but the promotion of a status to a truth value: ZTL splits
the *role*, not the alphabet, and revokes the status's right to be
what a statement evaluates to.

Consequence for positioning: ZTL's neighbours are not the many-valued
logics but the two-valued assertability policies of the supervaluation
family — from which it differs by locality, tabularity, and greedy
collapse.

## 11. Expeditions: Curry, parity, Yablo, the crocodile (MEASURED)

**Curry without negation.** c = (Tr(c) → ⊥) is the paradox that breaks
naive paraconsistent theories (it uses no ¬, so taming negation does
not help). Measured: no greedy fixed points, iteration of period 2,
lazy grounding gives Z. **The same mechanics as the liar**: quarantine
does not care which operator a sentence used to invert itself — only
the non-existence of a fixed point matters. Our construction silences
Curry for free, where LP must sacrifice contraction.

**The parity theorem — total.** All cycles of length 1–5, all inversion
patterns (62 systems): classical models exist ⟺ the number of
inversions around the ring is even (the XOR-sum of the edges is 0). Odd
rings are carousels (liar n=1, Jourdain n=2), even rings are
truth-tellers (underdetermination).

**Yablo: a third source of ungroundedness.** sᵢ = "all sⱼ, j>i, are
false" — a paradox without a single cycle. Measured: **every finite
truncation is fully grounded** (the unique model F…FT, empty
quarantine, exactly one greedy model). Yablo's paradox lives only at
actual infinity — a finite instrument cannot see it in principle. So
there are three distinct sources of ungroundedness: the odd cycle (the
liar), the odd infinite progression (Yablo), and the underdetermination
of even structures (the truth-teller); the first is caught finitely,
the second only in the limit.

**The crocodile.** "I shall return the child ⟺ you predict what I will
do"; the mother: "you will not return it". Formalization: R = Tr(M),
M = ¬Tr(R) — Jourdain's carousel in disguise (cycle 2, one inversion,
odd). MEASURED: no greedy models, iteration of period 4, mutual
quarantine under lazy grounding, and — the key measurement — **the
greedy verdict on the deal itself, R↔M, at the grounded point: F**. The
zero-trust reading of the ancient dilemma: the deal's condition cannot
be grounded — the contract is void, no obligation ever arose; the
crocodile is not "unable to comply" but "never contracted". The control
case (an optimistic mother, M = Tr(R), an even cycle): classical models
exist — (T,T) and (F,F), the word is kept in both — but the least fixed
point is still quarantine and the deal's verdict is still F: an
enforceable self-referential contract does not self-enforce — which
model realizes is decided by an external choice, not by logic. The
difference between paradox and underdetermination is the difference
between "the contract is void" and "the contract is valid but requires
the parties' will".

## 12. Sets with unverified elements (MEASURED)

Sets are not postulated — they are derived: element equality is an atom
(T/F for verified elements; Z whenever a mark is involved, including a
mark with itself), membership is an ∃-fold, inclusion an ∀-fold, set
equality mutual inclusion; everything computes through the core tables,
with not a single special rule. Representation: (a core of verified
elements, a quarantine multiset of marks).

**Measured:** {Z,Z} ≠ {Z} (merging is not earned — two unverified
witnesses are not one); **Z ∉ {Z}** even for the same mark (SQL: NULL
IN (NULL) is not true); on clean sets the whole classical set theory is
intact (C-extension); a mark fells exactly the **identity laws** —
idempotence S∪S=S and S∩S=S, self-subtraction S∖S=∅, reflexivity S=S
and S⊆S — the same families that fell in the logic: sets inherited the
price list from the tables.

**Cardinality is an interval:** |{1,2,Z}| ∈ [2,3], the exact value is
not earned (verdict F); but |{Z}| ∈ [1,1] — **cardinality is earned
even where identity is not**: one mark is exactly one thing.
Cardinality and identity have split into different currencies of trust.

**SQL's inconsistency is not inherited:** SQL holds NULL≠NULL in
comparisons yet merges NULLs in DISTINCT/GROUP BY — swapping equality
of values for equality of marks inside one syntax. Here the core
deduplicates classically and the marks live with multiplicity — each
operation honest about its own business.

## 13. The reals: two failures of enumeration (MEASURED)

A real-in-the-making is a stream of digits; at time t a prefix is
verified. Stream equality is an atom with a pinned fate: prefixes
diverged — **F earned** (apartness, a finite witness); they agree —
**Z**; **T is never earned at any t** (the comparison is infinite).
Finitely-presented objects (fractions p/q) are the contrast: equality
decides finitely, the atoms are T/F.

**Measured — uncountability splits into two distinct impossibilities:**

1. **Non-registrability (zero-trust, about presentation).** Membership
   of a stream in any registry — an ∃-fold of atoms from {F,Z} — is
   eternally F: even streams literally standing in the list (including
   a duplicate!) earn no membership. No enumeration of streams can
   certify coverage of a single element — including its own rows.
   Registries of fractions, by contrast, certify every element: the
   countability of ℚ is the earnability of presentation identity.
2. **Incompleteness (Cantorian, about cardinality).** The diagonal is
   an apartness-earning machine: against the i-th entry a finite
   witness is found by time i+1. The diagonal's non-membership is not
   postulated — it is earned.

Classical usage merges both impossibilities into the single word
"uncountable". The Z-optics splits them: the first fits into Z entirely
(it is a property of extensional presentation and strikes even
countable stream families), the second remains a cardinality fact which
the diagonal renders *earned*. Resonance: the split "how many / which
exactly" of §12 (cardinality earned without identity) is the same split
seen sideways.

## 14. Functions: taint mode (MEASURED)

A function is a computation, not a verdict ⇒ by the two-register
theorem it behaves lazily: **the mark flows through the function** with
a growing pedigree (f(m) is a new mark "f applied to m"). Measured:

* **Images:** verified collisions *earn* merging (f(1)=f(2) is a proven
  fact, the core deduplicates), marks keep multiplicity:
  |f({1,2,3,Z})| ∈ [2,3].
* **Composition:** taint is transitive (pedigree g(f(m))); the image is
  associative at representation level while verdict-equality is F
  (regularity R1, §21).
* **The preimage splits** into a verdict version (marks dropped —
  default deny) and a solver version (marks as candidates) —
  regularity R2 (§21).
* **The pearl: even the identity function is not certifiably injective
  on a marked domain** — pairs with a mark give Z-atoms, the
  implication Z→Z = F, the ∀-fold collapses. An injectivity certificate
  requires a fully verified domain; the echo of fallen S ⊆ S.
* **Laundering is forbidden:** functions do not remove marks; the only
  sanitizer is external verification of the value. In security terms:
  declassification only through proof.

**The third engineering twin.** After IEEE NaN and SQL NULL — **taint
tracking / information flow control** (Denning's lattice 1976, Perl
taint mode, TaintDroid): the Z-mark is taint, lazy flow through
computations is taint propagation, greedy verdicts are sanitizer
checks, the laundering ban is no-declassification.

## 15. Arithmetic with marks (MEASURED)

Numbers: verified values and marks with an interval of partial
knowledge [lo,hi] (ignorance = (−∞,∞)). Operations are computations ⇒
lazy: intervals flow (interval arithmetic, decorrelated). Comparison
atoms follow the generating principle extended to intervals: **T if
forced under all readings; F if falsehood is forced; else Z**. Measured:

* **Forcedness earns even on marks:** 0·w = an earned 0 even for a wild
  mark (forced on ℤ by all readings) — a point of deliberate divergence
  from IEEE (their 0·NaN = NaN: their domain contains inf/nan).
  m−m ∈ [−9,9] ≠ 0 — decorrelation (like NaN−NaN, like {Z,Z}).
* **Three fates of an atom:** [3,5]<[10,12] — T earned; [3,5]=[10,12] —
  **apartness earned by intervals** (the echo of §13: difference is
  finitely witnessable); overlap — Z; the same mark against itself — Z
  (coincidence of bounds ≠ coincidence: identity is earned by nothing
  short of full verification [x,x]).
* **Verification = interval narrowing:** the atom "4 < m" travels
  Z → Z → T along [0,9]→[3,7]→[5,7]; what is earned is never revoked —
  the monotonicity of the lazy register, now in numbers.
* **Price-list inheritance:** commutativity of addition survives at the
  interval level, verdict-equality is Z→F; the unit x+0=x falls
  verdict-wise with coinciding intervals (regularity R1, §21).

**The fourth twin: abstract interpretation** (Cousot & Cousot, 1977) —
interval value analysis (lazy flow of abstract values through
computations) + assertion checking (greedy verdicts). Four independent
engineering traditions — NaN, NULL, taint tracking, abstract
interpretation — turn out to be fragments of one logic.

## 16. The probabilistic bridge: Z ≠ p = 0.5 (MEASURED)

Three measurements answer how a mark of ignorance differs from a
uniform prior.

**Reparametrization (a discrete Bertrand).** Given only w ∈ [0,1]; the
question "w ≤ 0.25?". A Bayesian with a uniform prior on w answers 1/4;
a Bayesian with a uniform prior on w² (the same ignorance!) answers
1/16. One ignorance — two contradicting numbers: the choice of
parametrization is smuggled information. The ZTL atom at w∈[0,1] is Z
in both parametrizations: **ignorance does not convert into a number
without importing information**, and this is invariant.

**Dempster–Shafer.** On masses m({a})=m({a,b,c})=1/2 it is measured
that the ZTL verdict of an event is the threshold of belief functions:
**T ⟺ Bel = 1** (forced by all readings of ignorance), **F ⟺ Pl = 0**
(excluded by all), else Z. The generating principle of ZTL is the
{0,1}-threshold of Dempster–Shafer theory; the interval cardinality of
§12 is the elementwise [Bel-count, Pl-count].

**Ellsberg.** An urn with a verified 50/50 versus an urn of unknown
composition: EV(K)=[50,50] is an earned number, EV(U)=[0,100] an
interval; the atom "U is no worse than K" is not forced → default deny
→ choose K. The famous "irrationality" of Ellsberg's subjects (1961) is
the distinction between risk (verified p) and ignorance (a mark),
inaccessible to a point prior: zero-trust rationality.

**The second "SQL theorem" — about Bayesians.** A point prior made from
ignorance is a greedy laundering of Z into a number, the same
substitution as merging NULLs in DISTINCT, and it is punishable
(reparametrization). The honest architecture is two-registered:
ignorance lives in mass intervals (the lazy register — Dempster–Shafer
and **the fifth twin: Walley's imprecise probabilities, 1991**), while
decisions are verdicts by forcedness (the greedy one). Bayes remains
honest on verified probabilities — his C-extension; only minting
numbers out of emptiness is forbidden.

## 17. The modal layer: local □ versus global (MEASURED)

Worlds are the classical completions of the unverified atoms; □φ = in
all, ◇φ = in at least one. Measured:

* **Atom verdicts are modal thresholds** (totally): T ⟺ □p, F ⟺ □¬p,
  Z ⟺ contingency; the duality ◇ = ¬□¬ holds; nested modality collapses
  (□p is classical ⇒ □□=□) — the frame is S5-like. This is §16 one
  floor up: □/◇ are the Bel/Pl thresholds in probabilistic dress.
* **The tableau signs are modal claims**: strict T/F are □φ and □¬φ,
  weak P/N are ◇φ and ◇¬φ. The calculus signature reads modally: proof
  demands necessity, refutation settles for possibility.
* **Three logics on one formula** (classical | global □ | ZTL): p→p and
  LEM: T | T | F — supervaluation (one □ over the whole formula)
  preserves all classical tautologies, the local per-operator □ fells
  them. But ¬¬p: T | Z | T — **ZTL earns a verdict which global
  supervaluation cannot give** (the ladder of floors): the systems are
  incomparable, not ordered by strictness.

Result: **ZTL is a locally-modal logic over the S5 frame of
completions**; every operator carries its own □-collapse. Bochvar's
translations (→ = ◇A⊃□B, ¬ = □¬) acquire world semantics; the
supervaluation/ZTL split turns out to be the global/local modality
split. The theoretical relative is Hintikka's epistemic S5 (□ =
"known"): ZTL asserts only the known, but its modality is per-operator.

## 18. Russell: containment instead of explosion (MEASURED)

Russell is the liar dressed in membership: R = {x : x∉x} ⇒ R∈R ⟺
¬(R∈R). The test universe: a = ∅, b = {b} (a lawful eccentric), R; a
system of nine membership facts, with Russell's definition referring to
the facts x∈x. Measured:

* **The greedy jump**: zero models, iteration of period 2, and exactly
  one cell oscillates — R∈R; the whole storm is localized.
* **Lazy grounding**: 8 of 9 facts grounded; a∈R = T (does not contain
  itself — admitted), b∈R = F (contains itself — rejected). **Russell's
  set works as a set for everyone except itself**; quarantine is one
  cell.
* **Verdicts**: "R∈R?" — not earned, refusal; "R∉R?" — the greedy
  reading of ¬(R∈R) is F — also refusal. The NaN signature reaches set
  theory: neither membership nor non-membership is earned.
* **The twin S = {x : x∈x}**: three greedy models (T, F, Z), lazy
  grounding Z — the truth-teller of set theory, underdetermination.
  Even and odd, now in sets.

The contrast with the classical outcome is maximal: for Frege one cell
R∈R blew up the whole system (from an asserted contradiction everything
follows). In ZTL the same cell goes into quarantine and the rest of the
universe stays grounded: **explosion requires an asserted
contradiction, and quarantine asserts nothing**. The grounding is
kernel-checked: the certified least-fixed-point iteration of §9
computes the nine-fact system to [F,F,T,F,T,F,F,F,Z] — eight facts
classical, quarantine exactly at R∈R (Lean `russell_grounded`, zero
axioms). A comparison with an
earlier system of the author is instructive: in VR-Sets [Zenodo
10.5281/zenodo.20592428] Russell is excluded by grammar (forbidden to
write), in ZTL he is admitted and defused pointwise. Two honest answers
to one calamity: keep it out, or let it in under guard.

## 19. The verification operation and verdict warranties (MEASURED)

The act of verification — removing a mark and writing in the earned
value — exposes a narrow place: **greedy verdicts are non-monotone
under verification**. Not only refusals flip (p∨¬p: F → T upon p:=T —
expected: default deny until checked) but **T flips too**: ¬¬p = T (a
ladder report) dies at p:=F. A verdict without a warranty is a Frege
cell: an unfenced spot where a consumer who read T as "settled forever"
builds on sand.

**The fence is a warranty — and (corrected in v1.1) it is a ladder of
two grades, not one bit.**

* **The SOUND grade** (the stability bit of v1.0): all completions
  give one classical answer equal to the current greedy verdict — the
  global supervaluation of §17. It buys *never lies*: a sound verdict
  agrees with every possible resolution of the marks, so no truthful
  verification can ever reveal it to have been false. Cheap: one pass
  over the completions.
* **The HEREDITARY grade**: the verdict is unchanged under *every
  partial refinement* — any subset of the marks verified to any
  classical values. It buys *never spoils*: no verification path can
  revoke the verdict. Hereditary ⟹ sound (completions are among the
  refinements); the converse is **false**.

**Correction of the v1.0 claim (MEASURED).** v1.0 asserted an
equivalence — "stability-by-supervaluation ⟺ invariance under every
sequence of verifications (totally, 90 formula×marking pairs)" — and
a monotonicity corollary. Both were facts about that 10-formula pool,
not laws. The separating shape, found by the identity atoms of the
operational-sets expedition (E21) on a 3303-formula pool and
cross-checked with this section's own instruments, is
**or(ladder, gap)**:

> ¬¬p ∨ (q ∨ ¬q) — greedy T via the ¬¬ ladder, insured by a gap that
> is true in ALL completions yet greedy-F; verifying p:=F kicks the
> ladder away before the gap closes. The verdict was sound — and died.
> A simpler cell: (¬p) → (q→q), where the gap is the fallen law of
> identity itself.

Measured on the extended pool: hereditary-without-sound 0 (the ladder
is real), sound-without-hereditary > 0 (the grades separate); the
hereditary grade is monotone — never revoked, never degraded (0
violations, totally) — while sound-only verdicts are revocable.
Subsequently stress-tested at scale (2026-07-12): a 151.8-million-pair
hunt over four atoms at depth three, all six connectives, found 0
violations of the ladder inclusion and of hereditary monotonicity;
the grade separation is generic (1.2 million cells), not exotic.

**Result: a verdict is a pair (value, warranty grade).** The value is
greedy (local, fast); the warranty grades are global. Six verdict
classes now, and the honest advice differs by grade: **hereditary T —
build your house** (no verification path can revoke it); **sound T —
never a lie, but may stall to refusal before verification completes**;
T-until-verification — a ladder report (¬¬p), alive till the first
check; symmetrically for F, with F-until-verification as default deny.
The Frege cell is fenced by the top grade only; the middle grade
fences lying, not spoiling.

## 20. Evidence combination: conflict is not laundered (MEASURED)

Pieces of evidence about one value are constraints; **combination =
intersection**. Measured:

* **The unification theorem**: verify of §19 is a special case of
  combination (a singleton witness [v,v]); verification and evidence
  fusion are one operation. An honest side effect: the act of checking
  can itself earn a conflict (verify 7 against m∈[0,5] — the checker
  against the prior evidence).
* **An empty intersection is an earned contradiction of sources** (a
  sound F for the verdict "both are honest"), not noise for
  renormalization.
* **Zadeh's paradox (1984), resolved in Smets' favor.** Two doctors
  almost exclude a tumor (0.01 each); Dempster's rule renormalizes the
  0.9999 conflict away and outputs "tumor = 1" — an unshakable false
  certainty. Smets' conjunctive rule (TBM) keeps the conflict in m(∅) —
  our approach: the conflict is exhibited, the diagnostic verdict is
  refusal until the doctors are sorted out. **Renormalizing conflict is
  the same laundering of ignorance as the uniform prior (§16), in the
  chapter on combination: one principle, two diseases.**
* **The sixth twin: provenance polynomials
  (Green–Karvounarakis–Tannen, 2007).** The pedigrees of marks (§14)
  grow into polynomials over sources: a fact with derivations A·B + C
  stays alive while at least one monomial lives; retracting a source
  zeroes a variable. An algebra of trust in derivations, measured on
  retraction scenarios.

The twin count: **six** — NaN, NULL, taint/IFC, abstract
interpretation, imprecise probabilities, semiring provenance.

## 21. Cross-cutting regularities

Three facts recurred in every applied chapter; we fix them once.

**R1. Two levels of equality.** On every floor (sets, functions,
arithmetic) the operations coincide at the representation level (the
machine sees equality), yet verdict-equality refuses: the very act of
recognizing identity is default deny. The engineering level serves the
solver, the verdict level serves assertions.

**R2. Two-registeredness reproduces itself.** The verdict and solver
variants of each construction (preimages, cardinalities,
probabilities) arise without special design — as consequences of the
generating principle and the §9 theorem on the necessity of two
registers.

**R3. Apartness is earned, identity is not.** The difference of two
unverified objects is earned by a finite witness (diverged intervals,
diverged prefixes); identity is earned by nothing short of full
verification. Hence in one stroke: {Z,Z} ≠ {Z}, m−m ≠ 0, the
non-registrability of streams (§13), and the NaN signature x ≠ x.

## 22. Roadmap

A Lean port of the parameter (arbitrary-domain) tableaux of §6; a
syntactic cut-elimination procedure with complexity bounds
(admissibility is settled — §5); the mining of the equivalent
quasivariety scouted in §3.7 (axiomatization, subquasivariety lattice,
a representation theorem replacing Plonka sums — a separate work);
a cheap characterization of the hereditary warranty grade of §19
(sound is one pass over completions; is hereditary computable without
enumerating refinements? — open; MEASURED narrowing, 2026-07-12: no
depth-1 fence exists — a 151.8-million-pair hunt at four atoms found
verdicts invariant under every single verification yet killed by a
pair (the counterexample cell is kept under regression, `zverify` §5),
so any answer must look at least two moves deep);
a practical zero-trust validation library (verdicts with warranties +
evidence combination + provenance). The interactive studio — natural
language negotiated into ZFL and judged by the measured engines —
already ships in the repository (`tool/`); a possible essay,
"Reinventing Bochvar through NaN", remains on the horizon.

## References

1. Bochvar, D. A. On a three-valued logical calculus and its
   application to the analysis of the paradoxes of the classical
   extended functional calculus. *Matematicheskii Sbornik* 4(46):2
   (1938), 287–308. English translation: *History and Philosophy of
   Logic* 2 (1981), 87–112.
2. Kleene, S. C. *Introduction to Metamathematics*. North-Holland,
   Amsterdam, 1952.
3. Jaśkowski, S. Rachunek zdań dla systemów dedukcyjnych sprzecznych.
   *Studia Societatis Scientiarum Torunensis*, Sect. A, I:5 (1948).
4. van Fraassen, B. C. Singular terms, truth-value gaps, and free
   logic. *Journal of Philosophy* 63:17 (1966), 481–495.
5. Kripke, S. Outline of a theory of truth. *Journal of Philosophy*
   72:19 (1975), 690–716.
6. Priest, G. The logic of paradox. *Journal of Philosophical Logic*
   8:1 (1979), 219–241.
7. Gupta, A., Belnap, N. *The Revision Theory of Truth*. MIT Press,
   Cambridge MA, 1993.
8. Rosser, J. B., Turquette, A. R. *Many-Valued Logics*.
   North-Holland, Amsterdam, 1952.
9. Sette, A. M. On the propositional calculus P1. *Mathematica
   Japonicae* 18 (1973), 173–180.
10. Sette, A. M., Carnielli, W. A. Maximal weakly-intuitionistic
    logics. *Studia Logica* 55:1 (1995), 181–203.
11. Karpenko, A., Tomova, N. Bochvar's three-valued logic and literal
    paralogics: their lattice and functional equivalence. *Logic and
    Logical Philosophy* 26:2 (2017), 207–235.
12. Devyatkin, L. Yu. Non-classical modifications of many-valued
    matrices of classical logic. Part I. *Logical Investigations* 22:2
    (2016), 27–58 (in Russian).
13. Libkin, L. SQL's three-valued logic and certain answers. *ACM
    Transactions on Database Systems* 41:1 (2016), Article 1.
14. Libkin, L., Peterfreund, L. SQL nulls and two-valued logic. *Proc.
    PODS 2023*, 11–20.
15. Codd, E. F. *The Relational Model for Database Management: Version
    2*. Addison-Wesley, Reading MA, 1990.
16. IEEE Standard for Floating-Point Arithmetic (IEEE 754-2019). IEEE,
    2019.
17. Denning, D. E. A lattice model of secure information flow.
    *Communications of the ACM* 19:5 (1976), 236–243.
18. Cousot, P., Cousot, R. Abstract interpretation: a unified lattice
    model for static analysis of programs. *Proc. POPL 1977*, 238–252.
19. Dempster, A. P. Upper and lower probabilities induced by a
    multivalued mapping. *Annals of Mathematical Statistics* 38
    (1967), 325–339.
20. Shafer, G. *A Mathematical Theory of Evidence*. Princeton
    University Press, 1976.
21. Zadeh, L. A. Review of Shafer's *A Mathematical Theory of
    Evidence*. *AI Magazine* 5:3 (1984), 81–83.
22. Smets, P., Kennes, R. The transferable belief model. *Artificial
    Intelligence* 66 (1994), 191–234.
23. Walley, P. *Statistical Reasoning with Imprecise Probabilities*.
    Chapman and Hall, London, 1991.
24. Green, T. J., Karvounarakis, G., Tannen, V. Provenance semirings.
    *Proc. PODS 2007*, 31–40.
25. Hintikka, J. *Knowledge and Belief: An Introduction to the Logic
    of the Two Notions*. Cornell University Press, Ithaca, 1962.
26. Ellsberg, D. Risk, ambiguity, and the Savage axioms. *Quarterly
    Journal of Economics* 75:4 (1961), 643–669.
27. Hähnle, R. Tableaux for many-valued logics. In: *Handbook of
    Tableau Methods*, ed. M. D'Agostino et al. Kluwer, Dordrecht,
    1999, 529–580.
28. Yablo, S. Paradox without self-reference. *Analysis* 53:4 (1993),
    251–252.
29. Tarski, A. The concept of truth in formalized languages (1933).
    In: *Logic, Semantics, Metamathematics*. Clarendon Press, Oxford,
    1956.
30. Varzi, A. C. Supervaluationism and its logics. *Mind* 116:463
    (2007), 633–676.
31. Blok, W. J., Pigozzi, D. *Algebraizable Logics*. Memoirs of the
    American Mathematical Society 77:396. AMS, Providence, 1989.
32. Bonzio, S., Pra Baldi, M. On the structure of Bochvar algebras.
    *The Review of Symbolic Logic* (2024), doi:10.1017/S175502032400008X.

## Acknowledgements and AI disclosure

This work was carried out with the substantial participation of the AI
system Claude (Anthropic) in a dialogue setting: the system generated
the text, the test-bench code, and the Lean proofs. All design
decisions, fork choices, hypotheses, and the final responsibility for
the content rest with the human author. In accordance with COPE/ICMJE
recommendations, the AI system is not listed as an author. The
reliability of the results does not depend on trusting the AI: every
numerical claim is checkable by the repository code (`run_all.py` —
full regression), and every Lean claim by the Lean 4 kernel (empty
axiom list, `#print axioms`).
