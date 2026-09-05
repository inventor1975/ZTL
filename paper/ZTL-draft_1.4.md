# ZTL — Zero-Trust Logic — v1.4 (IN PREPARATION, not published)

**V. Reznik. Preprint, v1.4 — IN PREPARATION. No DOI yet: this file is
the working text of the next version, not the published one. The
published version is v1.3 (2026-07-21), version DOI
[10.5281/zenodo.21472971](https://doi.org/10.5281/zenodo.21472971) — a
frozen PDF on Zenodo; nothing edited here changes it. Zenodo publication
is the curator's manual step.**

**v1.4 will add** (accumulated since v1.3, not yet written into this
text): the numeric floor ZNUM — quantities with provenance, exact
rational lattices including `frac(m)`, units as exponents, the two
credit axes and their cures, and the kernel-checked narrowing-heredity
theorem (`lean/ZNum.lean`); the carrier discipline — a cure must be able
to cure, probed by widening, with the fourth cure `contest type` and the
polarity of a refutation bought on credit; and the four-column ledger
against classical logic, whose "shared" and "no new laws" columns are
now theorems rather than samples (`lean/ClassicalAgreement.lean`, empty
axiom list). Present in this text already: corrected corpus figures and
the precise position against Tomova's natural-implication criterion
(§28).**

**Carried over from the published v1.3 — version DOI
[10.5281/zenodo.21472971](https://doi.org/10.5281/zenodo.21472971).
Concept DOI:
[10.5281/zenodo.21318981](https://doi.org/10.5281/zenodo.21318981)
(v1.2: [10.5281/zenodo.21440066](https://doi.org/10.5281/zenodo.21440066);
v1.1: [10.5281/zenodo.21323552](https://doi.org/10.5281/zenodo.21323552);
v1.0: [10.5281/zenodo.21318982](https://doi.org/10.5281/zenodo.21318982)).
v1.3 adds: the Suszko positioning (§4) — Z as a mark rather than a third
truth value is Suszko's Thesis taken as architecture rather than
recovered by reduction, with the discriminator measured; the signature
result (§4) — the single rule ¬¬p ⊨ p separates ZTL from each of its four
involutive-negation neighbours (K3, LP, weak Kleene, Ł₃) and, by one
lemma, from any three-valued matrix with involutive negation, its cause
proved in `lean/Signature.lean` on the empty axiom list; **first-order
identity** (§24, `ZEq.lean`) — a `=` predicate whose reflexivity is an
earned verdict, falling to Z on an unverified reference, while Leibniz's
law licenses substitution only through an earned equality; and **free
logic with definite descriptions** (§25, `ZDesc.lean`) — a non-denoting
term takes the mark (existence = earned self-identity), and the greedy
collapse (excluded middle on it is F, not a gap and not super-true)
sets ZTL apart from the neutral free-logic school. v1.2 added: the central construction named — the zero-trust lift (§2);
§3.8, an explicit Lean-verified census of the sixteen lifted binary
connectives — re-deriving Finn's external-Bochvar completeness landscape
(Finn 1974): solo-completeness tracks non-commutative directionality (Sheffer's
stroke and Peirce's arrow fall, both implications and both abjunctions
survive), and the surviving basis ↛ reads as the credit detector; the
fence-depth theorem in §19 (exactly m−1; no constant-depth fence);
the at-scale stress-test of the warranty ladder; the recalculated
Bochvar ledger (§4); and the three-laws-of-thought reading — a denial is
free, an affirmation is on credit (§3.1); and the paradox engine (§11) — the
expeditions unified as one construction paradox(f)=ground(S=f(S)) with three
measured layers; and — the headline of this version — a TEMPORAL LAYER
(§§21–23) in which the only clock is the arrival of ground: the warranty
ladder read as temporal quantifiers (now / at every ending / always on
every path), the absorption and arrow theorems machine-checked
(`ZTime.lean`), an expiry event that opens epochs, and the EPOCH BOUNDARY
THEOREM (`EpochBoundary.lean`) — a verdict invariant across unrestricted
epoch crossing reads none of its grounds, so non-trivial guarantees
require the boundary between learning and world change; plus a price list
of derivations (§23) — the alive rules transport truth but cannot mint it.**
The tag MEASURED means "verified by machine enumeration" (code in this
repository), as opposed to "argued"; references to Lean mean proofs
checked by the Lean 4 kernel with an **empty axiom list**.

---

## Abstract

ZTL (Zero-Trust Logic) is a two-valued logic over marked inputs,
generated in its entirety by a single principle: **truth is never
granted on credit** — a connective returns T only if T is forced under
every classical reading of the unverified. There are exactly two truth
values (verdicts are always classical); the third symbol Z is a **mark**
on an unverified input, not a truth value. The mark is barred from the
value of any compound — the greediness theorem (`evalF_classical`, empty
axiom list): every compound assertion is already T or F, the middle never
appears above the atoms. This is more than Suszko's logical
two-valuedness, which every structural logic has for free; it is the
stronger, truth-functional fact that above the atoms the algebraic value
already *is* the logical value, so the reduction has nothing left to do
on compounds. Its identity among the three-valued matrices is precise and
machine-checked at its cause: a single rule, **¬¬p ⊨ p**, separates its
consequence relation from each of its four involutive-negation neighbours
(K3, LP, weak Kleene, Łukasiewicz Ł₃), and by one lemma from any matrix
with involutive negation — the cause a broken involution, ¬¬Z = T.

That the logic is not arbitrary is evidenced, case by case, rather than
asserted. Six independent engineering traditions — IEEE 754 arithmetic (NaN), SQL's
three-valued logic (NULL), taint tracking in security, abstract
interpretation in static analysis, imprecise probabilities in decision
theory, and provenance semirings in database theory — have each, over
decades, reinvented a fragment of this same discipline; for each we
exhibit a worked case in which the core reproduces its central move
(MEASURED). We argue, and do not claim to have proved, that each
therefore implements a fragment of one logic — the evidence that its
generating principle is a denominator and not a construction of
convenience.

For this logic we build: a complete semantic
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
quantifiers, first-order identity (a `=` predicate whose reflexivity is
an earned verdict — self-identity falls to Z on an unverified reference —
while Leibniz's law licenses substitution only through an earned
equality) and free logic with definite descriptions (a non-denoting term
takes the mark, not F and not a gap; existence is earned self-identity,
and the greedy collapse makes excluded middle on it F, apart from the
neutral free-logic school); a modal identification (local
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
theorem separating the liftable from the permanent; a temporal layer in
which the only clock is the arrival of ground — the warranty ladder read
as temporal quantifiers (now / at every ending / always on every path),
with the absorption and arrow theorems machine-checked, an expiry event
that opens epochs, and the Epoch Boundary Theorem (a verdict invariant
across unrestricted epoch crossing is constant, so non-trivial
guarantees require the boundary between learning and world change); and
a price list of derivations (the twelve alive rules transport truth but
cannot mint it — from no premises nothing is derivable, even the guarded
tautologies, even on credit). The entire development — the core, both
engine certificates with cut admissibility, the algebraic witnesses, the
general fixed-point theorem, the expedition twins, the temporal modules
and the frame's own mini-theorems, fifty-three modules in all — is
formalized in Lean 4 **with an empty axiom list, definitions
included**: 803 theorems, each one audited individually rather than by
sample (`inventory/axiom_audit.py`, re-run on every push). As of this
revision no section rests on measurement alone: every one of the seventeen
that carried the MEASURED tag now names kernel-checked theorems behind its
load-bearing claims. *The tag says what is backed, not that everything in the
section is* — several sections still list claims that are measured and not
formalised, and each says which ones. As a
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
language is negotiated into ZFL (the Zero-trust Formal Language), a
small language whose validity guarantees loadability, and judged by the
measured core — the
pipeline itself obeys the logic it serves (the LLM's output is an
unverified input; the deterministic core is the customs).

## 1. A logic, and six traditions that reinvented it

This paper presents a logic and argues that it was already in use. The
logic is generated by one principle — truth is never granted on credit
(§2) — and has a precise identity among the three-valued matrices: a
single rule, ¬¬p ⊨ p, separates its consequence relation from each of its
involutive-negation neighbours — and, by one lemma, from any matrix with
involutive negation — its cause proved on the empty axiom list (§4). What keeps it from being one more many-valued table is where it
was found. Most of the data over which modern software computes is
unverified — sensor readings, user input, third-party databases, answers
of network services — and engineering, facing this, answered not with a
single theory but with the same local invention six times over:

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
nothing. We exhibit, for each of the six, a worked case in which our
core reproduces that practice's central move (§§13–17), and argue from
those six correspondences to a common denominator — a two-valued logic
over marked inputs with a single generating principle. The claim
ceiling, stated here rather than left to the reader: a reproduced case
is not an embedding. For one of the six that ceiling still stands — we
do not formalise their semantics and prove a fragment map into ZTL, and
that remains open (§27). For five it no longer does. SQL's NULL is the fifth (`ZNull.lean`, empty axiom list, §27): its three-valued expression layer is a homomorphism onto the lazy register, its comparison with NULL lands on the very atom IEEE's `==` did, and its boundaries are the four signs — WHERE is `SignT`, CHECK is `SignP`, the <boolean test> the rest — with WHERE agreeing with ZTL's verdict on every negation-normal search condition and parting exactly on `¬¬Z`. IEEE 754's NaN is the fourth (`ZNaN.lean`, empty axiom list, §27): the four-way comparison and the §6.2.3 propagation rule are formalised as the standard states them; arithmetic infection is a homomorphism into the mark-carrying integers; every ordered predicate is proved to be the T-sign of a ZTL atom, the unordered predicate the mark test, and `!=` — alone — the N-sign, which is exactly where IEEE's `x != x` and ZTL's refusal of `¬(x = x)` part. The algebra of
semiring provenance is formalised and mapped into the lazy register as a
homomorphism, with the greedy operations proved to admit no such
structure at all (`ZProv.lean`, empty axiom list, §27); and
Dempster–Shafer is formalised as its own theory states it, with our
verdict proved to be its {0,1}-threshold for every finite frame and every
proper mass assignment (`ZDempster.lean`, §16); and abstract
interpretation's Galois connection is formalised, with our verdict proved
EXACT rather than merely sound on the abstract value, and the point where
exactness fails named in the same file (`ZAbsInt.lean`, §15). All three are
partial in the same way, and it is worth naming: provenance's K-relations,
Dempster–Shafer's combination rule and abstract interpretation's fixpoint
framework are not formalised. So three algebraic cores are closed, not three
traditions. Three demonstrations became theorems; three remain
demonstrations.
What is shown without qualification is that the denominator survives a
full logical development: a calculus, quantifiers, modal and
probabilistic semantics, machine verification. Along the way the classical paradoxes of self-reference,
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

**Definition (the zero-trust lift).** For any classical connective f,
its lift:

    f*(x₁,…,xₙ) = ⋀ { f(v₁,…,vₙ) : vᵢ ∈ subs(xᵢ) },
    where subs(Z) = {T,F}, subs(v) = {v} otherwise;
    ⋀ is classical conjunction over all combinations.

Every occurrence of Z is substituted independently; the result is
always classical. This one construction is the generating principle of
the whole system: every connective of ZTL is a lifted classical one,
and every result in this preprint is a property of the lift. It is NOT
the strict (Kleene-style) lift of domain theory, which propagates the
extra element (f(…,⊥,…) = ⊥): the strict lift passes the mark on, the
zero-trust lift interrogates it — every classical reading is taken and
truth must be unanimous. Throughout the text and the companion
repositories it is called simply *the lift*; its emblem is **↕** — the
lift raises the operation into the marked world, the greedy collapse
returns the verdict to the classical floor: the mark never lives above
the ground level. (In formulas the lift stays f*; ↕ is heraldry, not
notation.)

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

**The three laws of thought (MEASURED).** Of the classical triad, exactly
one survives the lift. Non-contradiction ¬(p∧¬p) is T under every marking
and hereditary (§19); identity p→p and excluded middle p∨¬p both fall on Z.
One reading covers the split: **a denial is free, an affirmation is on
credit.** Non-contradiction denies — "not both" is forced (p∧¬p is F under
every reading of a mark) without knowing p; identity and excluded middle
affirm — "p implies p", "p or ¬p" — and the lift will not affirm truth over
an unverified p. The classical duality breaks along the very line the
principle draws: non-contradiction and excluded middle are De Morgan twins,
yet the lift keeps the one that withholds and drops the one that grants. The
generating principle read on the oldest laws — truth is refused on credit,
never granted on it.

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

### 3.5 Incompatibilities (mini-theorems — Lean, `Frame.lean`)

Three statements about the frame itself. Until v1.2 they were argued in
a parenthesis ("verified by substitution"); they are now kernel-checked
on the empty axiom list, since a paper about the difference between
earned and borrowed truth should not carry the word *theorem* on
unformalised reasoning about its own core.

1. **{¬Z=F, T→Z=F} ⟹ contraposition-as-identity is impossible.** At
   p = T, q = Z the left side is T→Z = F while the right side is
   ¬Z→¬T = F→F = T (`mt1_contraposition_impossible`). The dependence is
   stated separately as an implication from the two named cells
   (`mt1_from_the_cells`): the failure is a consequence of those
   entries, so a rescue costs exactly the flip of one of them.
2. **The quarantine flag is irremovable.** Housing the liar means being
   a fixed point of ¬; the frame has none (`mt2_housing_means_fixed_point`),
   and at Z it is pessimism, ¬Z = F ≠ Z, that does the excluding
   (`mt2_pessimism_excludes_Z`). Quarantine is therefore not a fourth
   value one could reach by editing a cell — it is a property of the
   input mark, not a verdict the tables could return
   (`mt2_quarantine_irremovable`).
3. **Collapsing Z→F at the atom is the classical fork.** The claim
   proved is the strong one, not "some laws come back": under the
   atom-collapse the ZTL evaluation of *every* formula equals the
   embedded Boolean evaluation, term by term
   (`mt3_collapse_is_classical`), whence every classical tautology
   returns (`mt3_every_tautology_returns`) — p→p and excluded middle
   among them. With the price list empty the rules/laws split has
   nothing left to split, and the system is Bochvar's isomorph B3□.
   The fork is one step wide: the same p→p is F in ZTL proper, where
   the mark reaches the operator and is read there (`mt3_the_fork`).

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

### 3.8 Single-operator completeness: the census of sixteen (MEASURED + Lean)

Zhegalkin's classical theorem splits in two under the lift, and the
halves part ways. The *basis* survives entirely: the clone generated
by {∧, ⊕} + constants equals the clone of the canonical basis
{¬, ∧, ∨} + constants — a kernel clone equality, with negation
verbatim as x⊕⊤ and the disjunction witness J_T(x) ⊕ y ⊕ (x∧y), where
the truth detector J_T(x) = x∧x (the fallen idempotence law, §3.6)
repairs the classical polynomial. The *ring* falls: the unit law
x∧⊤ = x, idempotence and the distributivity of ∧ over ⊕ all die on Z
(only the characteristic-2 law x⊕x = ⊥ survives — it is an anchor
cell), so no multilinear canonical form exists; the normal-form role
belongs to the J-DNF of the external layer (§3.6).

The census. Lifting each of the sixteen binary Boolean kernels and
closing over projections and constants gives, totally:

| fate | kernels | clone size |
|---|---|---|
| complete alone | →, ←, ↛, ↚ | 514 |
| fallen | NAND, NOR | 18 (one shared cage) |
| fallen | ∧, ∨ | 7 |
| fallen | ⊕, ↔ | 258 |
| degenerate | p, q, ¬p, ¬q, ⊤, ⊥ | 4–8 |

**The census law: a lifted binary connective is complete alone (with
constants) iff its kernel is essentially binary and non-commutative.**
The four directional connectives survive — both implications (the
classical arrow-and-falsum basis of Hilbert systems crosses the lift
intact) and both abjunctions (nonimplication p∧¬q and its converse
¬p∧q, the *credit detector*: its single truth cell is "the consequent
stands, the ground does not" — the very situation the logic is built
to forbid). Every commutative kernel falls, including both classical
one-operator champions: Sheffer's stroke and Peirce's arrow stall in
the *same* eighteen-table cage, each still defining negation on its
diagonal (x↑x = ¬x = x↓x) yet unable to rebuild its own De Morgan
partner. Directionality, not any "mark-killing", is the mechanism:
the lifted implication mints forced truth over marked cells (Z→T = T)
and is complete regardless. Classical completeness theory is untouched
— these are statements about the lifted operations relative to the
lifted clone (for the classical landscape see Post; Martin [33];
Rosenberg [34]). The completeness landscape of the lifted clone itself,
however, is *not* new: this clone is the external-Bochvar class B³ₑₓ,
whose maximal (pre-complete) classes were determined by Finn [35,
Remark 1] — the five lifted Post classes (preserving falsehood,
preserving truth, self-dual, linear, monotone) together with **two
additional maximal classes generated by the NOR- and NAND-type
connectives**. A single binary kernel is complete alone in B³ₑₓ iff its
lift lies in none of these seven; both classical champions fall
precisely because each generates one of the two extra classes — the
fact our census re-derives and machine-checks. Our contribution here is
therefore not the completeness theory (Finn's) but (i) the explicit
kernel-verified census of all sixteen binary kernels with clone
cardinalities below, (ii) the observation that solo-completeness tracks
non-commutative directionality, and (iii) the reading of the surviving
basis ↛ as the credit detector. (Our census further finds the two
champions sharing a *single* eighteen-table clone, which reconciles with
Finn's two extra classes exactly. There are precisely two external
negations — the mark-intolerant J₀ (the mark reads as false) and the
mark-tolerant one (the mark reads as true); Finn's two extra maximal
classes are their respective ∩̇-clones (measured, `finn_reconcile.py`).
Our greedy NOR is J₀x₁ ∩̇ J₀x₂ cell-for-cell, and both zero-trust
champions generate its class B³ₑₓ,¬; the mark-tolerant negation generates
the distinct B³ₑₓ,−. Zero-trust is therefore, at the clone level, exactly
the choice of the mark-intolerant negation — the unverified reads as
not-true, never as true — and B³ₑₓ,− is the shadow it rejects. Matching
Finn's x̄ to the mark-tolerant negation is forced by elimination; its
verbatim definition is in [35].)

Machine verification (`lean/ZClone.lean`, the twelfth module, empty
axiom list throughout): the negative half by the certificate method —
the explicit 18-table cage, its closure under both champions a single
`decide`, with Boolean membership by own recursion (the core
decidability of list membership is propext-tainted); the positive half
by witness terms spliced through table extensionality as data (nine
cell equalities instead of `funext`), giving the kernel clone
equalities clone(↛) = clone({¬,∧,∨}) = clone({∧,⊕}), plus the
seven-table cage banning lone ∧ from negation. The only measured (not
kernel) remainder is the cardinality of the common clone: 514 = 2
projections + all 512 external binary tables, by exhaustive closure.

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
The internal dynamics are opposite — his meaninglessness is infectious,
our mark evaporates at the first operator — and so is the ontology. That
parting need not be argued at length, because it has a name.
**Suszko's Thesis** (Suszko 1977 [37]) holds that
every structural logic is *logically* two-valued: the many values of a
matrix are *algebraic*, administrative, while the *logical* values are
only two, designated and undesignated. On that thesis Łukasiewicz, K3
and Bochvar are already two-valued as logics, their third value an
algebraic bookkeeping symbol recovered as bivalent by the Suszko
reduction *after the fact*. ZTL's difference is not that it escapes the
reduction — nothing does — but that it needs none: it is bivalent **by
construction**. The discriminator is exact and machine-measurable: does
the third symbol ever appear as the value of a *compound* assertion? In
the neighbours it does — 602 to 784 of the 784 depth-2 compounds over
two atoms take the middle value (MEASURED). In ZTL it never does — **0
of 784**, the greediness theorem (`evalF_classical`, empty axiom list):
the mark evaporates at the first operator, so no *compound* assertion is
ever anything but T or F. Where a genuinely three-valued logic is shown
bivalent by Suszko's reduction, ZTL is bivalent before any reduction,
because the mark is barred from the value of compounds from the start.
That is the precise sense in which ZTL is a two-valued logic with a mark,
not a three-valued logic. ZTL's implication is Bochvar's
◇A⊃□B taken as a primitive; a polarity-adaptive translation (□ in
positive positions, ◇ in negative ones) instead of a uniform one. ZTL
coincides with none of the literal paralogics of the Karpenko–Tomova
lattice (2017), and its position against Tomova's class of **natural
implications** [38] deserves stating precisely, because the loose
version — "it fails p→p" — invites a charge it does not deserve. The
class is defined by four criteria: (1) the restriction to {0,1} is the
classical implication; (2) normality in the sense of Łukasiewicz–Tarski
[39, p. 134] — modus ponens preserves the designated value; (3) if
p ≤ q then p→q is designated; (4) anything elsewhere. ZTL satisfies
(1) — proved for the whole language, not sampled, in
`lean/ClassicalAgreement.lean` (`evalF_agrees`, empty axiom list) — and
satisfies (2), since T→Z = F blocks the only counterexample. It
violates (3), and MEASURED, in exactly **one cell**: (Z, Z). The law
p→p is not a primitive requirement anywhere in the definition; it is the
diagonal case of (3), and (3) presupposes a linear order on the values,
i.e. that the middle symbol is a *degree of truth* standing between
falsity and truth. Under that reading — Łukasiewicz's ½, "possible, not
yet determined" — the condition is compelling: an antecedent no truer
than its consequent should not falsify the conditional. Under ours it
has no subject. Z is not a degree but a mark of status, barred from the
value of compounds (the greediness theorem above); Z ≤ Z does not say
"equally true on both sides", it says "neither side has been examined",
and to designate the conditional there is precisely to grant truth on
credit. ZTL is therefore outside the class not by breaking a law of
logic but by falling outside the family the classification is built
for — and the constitutive test of logicality is met elsewhere and
independently: the consequence relation is Tarskian (reflexive,
monotone, closed under cut) by the shape of its definition, so p ⊨ p
holds even where ⊨ p→p fails. The price of that gap is named in §19:
the deduction theorem holds left to right only. The *meaning* of the mark, as
against its tables, has a separate and earlier ancestor:
Łukasiewicz's Ł₃ [36] (1920), the first three-valued logic, whose
middle value read *possible / not yet determined* — the nearest
kin to Z's *unverified until verification.* His motive was future
contingents, not the paradoxes, and his implication keeps p→p, so
the kinship is of intent, not of tables. The two axes separate
cleanly: the tables are Bochvar's external B3, the mark's meaning
is Łukasiewicz's, and no system in the surveyed literature occupied their
conjunction.

The *consequence* relation is separated from each of its four
involutive-negation neighbours by a single rule. Against each of them
(K3, LP, weak Kleene, Łukasiewicz Ł₃) ZTL is incomparable as a
consequence relation, and the witness on the "the neighbour derives it,
ZTL does not" side is the *same* for all four: **¬¬p ⊨ p**, double-
negation elimination as a rule (MEASURED, depth-2 pool; the witness is
of size 3 and exhibited, so underivability is settled, not merely
unfound). Every neighbour keeps it; ZTL breaks it, and the reason
is proved rather than tabulated: an involutive negation *forces* the
rule (`involution_gives_dne`, for an arbitrary negation and designated
set), and ZTL's greedy negation is not involutive — ¬¬Z = T ≠ Z, one
cell — so it breaks the rule with the involution
(`lean/Signature.lean`, empty axiom list). The broken involution is thus
the feature separating ZTL from each of these involutive-negation
neighbours — and, by `involution_gives_dne`, from *any* three-valued
matrix whose negation is involutive, an infinite class of which the four
are instances. Its non-involutive kin is the exception that keeps the
claim honest: external Bochvar shares the {¬,∧,∨} tables, hence the
broken involution itself, so ¬¬p ⊨ p does *not* separate the two — there
they part in the implication fragment (the seven cells above), not on
this rule. The same greedy ¬¬Z = T (i) makes the compounds classical
above, (ii) bars ZTL from *expressing* any mark-carrying neighbour —
greediness lets no compound output the mark, while every neighbour's
connectives do (MEASURED) — and (iii) witnesses the separation here. One
feature, three faces; the novelty is that feature and the principle that
generates it, not the shared external tables.
The passport's two non-classical letters carry two distinct
pedigrees accordingly — Z from Łukasiewicz's indeterminate (a
truth not yet settled), N from Kleene's undefined (a computation
not yet run, §10). Kindred in spirit: supervaluationism
(rigid, non-tabular), subvaluationism/Jaśkowski (its dual), SQL NULL
(lazy), IEEE NaN (comparisons), exceptions with try/catch at every node
(greediness). The motivation "greedy local supervaluation / default
deny" was not found in the surveyed literature. The passport spells four
letters, N, Z, F, T, in the genetic order — nothing (pending), the
unsettled (a question with no answer yet), the free denial (default-deny),
the earned affirmation (truth on a ground): nothing → doubt → default-no →
grounded-yes. Z is born second, as raw doubt, and returns last, as the
hardened liar (§10) — the pre-computer genesis, not the solver's lifecycle.

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

## 5. The calculus: signed tableaux (MEASURED + Lean)

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

## 6. Quantifiers: finite domains and beyond (MEASURED + Lean)

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
quantified LEM — all 13 verdicts confirmed).

**And the axiom tier of the four rules themselves is now measured, before
the port rather than during it** (`ZParamSound.lean` for three of them,
`inventory/ПАРАМЕТР-ЯРУС.py` for the fourth). Both γ rules and the δ rule
for `T:∃` are sound on the EMPTY axiom list: a universal delivers every
instance, `¬∃ → ∀¬` is constructive, and eliminating an existential to
interpret a fresh parameter chooses nothing. The fourth, `F:∀xφ → N:φ(c*)`,
is not: to interpret its fresh parameter one needs an instance that is not
strictly T, and the premise gives only that not every instance is — which is
`¬∀ → ∃¬`. Proved classically it carries `propext, Classical.choice,
Quot.sound`. *Per-point decidability does not rescue it:* `V` has decidable
equality, so each `φ(d) = T` is decidable, but the quantifier over an
arbitrary domain is not — the obstruction is the survey of the domain, which
is what this logic declines to call an act everywhere else. *And the split
falls where §6 already said the logic breaks:* `¬∀yP ⊭ ∃y¬P` is listed above
as the second fallen quantifier bridge, so the calculus's own metatheory
needs, at exactly one rule, the step the object logic refuses. The classical
proof is kept OUT of the corpus rather than exempted in the audit — the
corpus carries one invariant this paper leads with, and an exemption added to
silence one alarm is where the next one hides; it lives in
`inventory/probes/` with a stand that fails in BOTH directions, red if that
rule ever becomes constructive (a finding, not a nuisance) and red if any of
the three stops being clean. What is NOT claimed is that no choice-free route
exists: it is not found by the standard argument, and that is all the
measurement says.

**Completeness is the
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

**Axiom status: the empty list, audited exhaustively.** `#print axioms`
over the whole corpus returns "does not depend on any axioms": no
Classical.choice, no Quot.sound, not even propext; pure computation.
This is the strictest possible tier.

The claim used to rest on hand-placed prints — 158 of them at the time, against the then-current corpus of 371 —
with the rest covered transitively — a sound argument (a lemma carrying
an axiom infects every theorem that uses it), but an argument, and one
that an unused orphan theorem would escape. It is now a measurement:
`inventory/axiom_audit.py` extracts every theorem name from every
module, generates one `#print axioms` per name, and fails if a single
line reads otherwise. **803 of 803 clean**, re-run by CI on every push.
The same stand refuses a module that carries theorems and is built by no
target — the failure mode that let one module (`QuantumWitness.lean`) go
unchecked by any automation until 2026-07-20.

**The temporal modules** (v1.2): `ZTime.lean` — the verification tree,
with absorption, arrow and ladder-inclusion proven structurally for
every formula and marking; `EpochBoundary.lean` — the epoch boundary
theorem and the separation witness (§§21–22). Both self-contained,
both on the empty axiom list, both verifiable from zero by a bare
`lean` call.

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
through the certified engine. **The receipt trio (`Receipt`, `Linear`, `LabelExact`, zero
axioms):** the label's completeness in both registers, the
no-loss theorem at multiplicity ≤ 1, and the label's exactness on
linear claims with a proved counterexample showing the hypothesis is
load-bearing (§19). **The stitch (`bridge.py`):** one questionnaire, two
engines — 609 kernel-computed answers (both registers cell by cell,
the label battery of §19,
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
mirror §19, and quarantine = (Z, passport). The caveat that stood here — "Yablo
stays invisible: every finite truncation is grounded, so the passport of
infinite regress needs an infinite instrument" — is now discharged, and
by a theorem rather than by a passport (`ZYablo.lean`, empty axiom list,
§11). The instrument for the limit is not a procedure at all; the
infinite system simply admits no verdict assignment, and that is proved
in one step. What the caveat got right is that no finite stage could
show it: every truncation is grounded, at every n, and that too is now a
theorem rather than a check at n = 3.

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
(§8, Part II), **both halves of the necessity argument are
machine-checked**: the greedy register cannot ground itself, and the
lazy one is exactly what grounds. The inference joining them — therefore
two registers are necessary, not merely convenient — is ours, not the
kernel's: no Lean object states it. We say so because the distinction is
the subject of this paper. A composition of theorems is worth what its
parts are worth; it is not a further theorem.

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

**The passport on three axes.** The comparison with classical logic
runs in three different directions at once, and collapsing them into
"stronger" or "weaker" loses all three.

* *Conservative extension by data.* On a mark-free valuation ZTL
  agrees with classical logic formula for formula
  (`ClassicalAgreement.evalF_agrees`) — where nothing is unverified,
  nothing changes.
* *Strict contraction by law.* Every ZTL validity is classically
  valid, and not conversely: `p → p` is a classical tautology and
  fails here on a marked atom (`ztl_taut_is_classical`,
  `not_conversely`). Strictly fewer laws.
* *Strict expansion in expressive reach.* The clone is exactly the
  projections plus the external functions — 1 + 8 unary, 2 + 512
  binary, nothing else sneaking in (§3.6, §3.7). Those external
  functions speak about the **status** of a ground, which classical
  logic has no object to speak about at all; and single-operator
  completeness is *lost* in exchange (§3.8: NAND and NOR each stall,
  only `↛` survives).

So the honest one-liner is neither "stronger" nor "weaker": **wider in
subject, narrower in law, identical on verified data.**

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

**The global reading now has a branch of its own, with theorems.**
Asked by a downstream consumer whether a *partial disclosure* suffices
for the conclusion drawn from it, the global reading becomes an
operational question: does the verdict survive every admissible
completion of what was withheld? `lean/ContextClosure.lean` answers it
for this calculus, on the empty axiom list. The local and global readings **coincide exactly** where
the withheld atom occurs under no negation, no antecedent and no
xor/xnor (`closure_coincides`), and provably part company outside it —
the separating case being `¬¬Z`, the very cell named above
(`outside_fragment_fails`). No condition on the formula *alone* can be
exact, because the property belongs to the pair (formula, disclosure)
(`no_syntactic_characterisation`). Rewriting into a normal form
restores agreement in one direction — no verdict is then granted that a
completion could defeat (`normal_form_sound`) — at the cost of
verdicts every completion upholds, `b ∨ ¬b` being the witness
(`normal_form_incomplete`). Prior art for the *problem* is fourteen
years deep in attribute-based access control (attribute-hiding attacks,
PTaCL, POST 2012; policy resistance certified in Isabelle, 2013;
extended evaluation, 2019); what belongs to this calculus is the
behaviour of the **greedy** lift. The contrast with PTaCL is not that
its logic is immune — it is where the collapse is authored. PTaCL's
unary operators, read from its own table (Fig. 1(e)), are `¬⊥ = ⊥`
and a separate `∼` with `∼⊥ = 0`: turning an unverified ground into a
false one is an explicit act the policy author performs locally, by
writing `opt`. Under the greedy lift the same collapse is the
semantics, applied everywhere and unwritten. So the exposure is not
their oversight and not our discovery; it is the price of a default,
and it is bounded in their calculus by where `opt` appears and
unbounded in ours.

**Why not four values.** The temptation to include N as a fourth value
(precedent: Codd's two NULLs for RM/V2, rejected by industry) is
declined: values are not multiplied, non-values are typed. N is the ⊥
of the fixed-point iteration (§9), the pending of any promise: it
exists only inside the solver and never returns outward. Read N as
**Not-yet** — Kleene's undefined *by intent*, at last housed as a
phase rather than a value. The
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

A closing note on errors: the system has no error letter, and none is
missing. An *error* is an interface event — the premature read of a
phase: any value returned for a still-pending N is wrong whatever it
is, because nothing has been computed yet. The engineering cousin pair
makes the split visible: IEEE's quiet NaN behaves like the mark Z
(carried, tested, lifted by verification), while the signaling NaN is
the alarm on touching the phase. The alphabet stays four letters;
E is hardware, not logic.

That last sentence is about the alphabet of the LOGIC, and it does not
change. What it leaves open is whether the seam itself has letters, and
a candidate register is recorded outside this system rather than inside
it (repository `IDEAS.md` 12.6, staked and deliberately unimplemented):
two marks — `M`, no ground was ever offered, and `O`, the world's own
indeterminacy — beside two states, `E` for the world's silence and `σ`
for the world's answer. The register reads ONE WAY, from the physical
into the operational: a boundary letter arrives and becomes an internal
one, so the four letters above are what the seam delivered rather than a
second alphabet competing with them, and each is paired by what it is
ABOUT — `E` with the phase `N` it reads too early, `M` with `F`, `σ`
with `T`, `O` with `Z`.

Read that way, this section's own claim is explained rather than
weakened. `E` carries no logical content of its own precisely because it
is an interface accident concerning a phase that has no value yet — not
a value of any kind, and so not a letter the system is missing. The
other three arrows do carry content, `O` most sharply, since ontic
vacancy (a value that does not exist) is not the epistemic mark `Z` (a
value we have not looked at) — a distinction this repository measured on
hardware before it had a name for it. None of the register is built, and
it is mentioned here only so that a reader meeting `E` does not take it
for a fifth truth value.

Consequence for positioning: ZTL's neighbours are not the many-valued
logics but the two-valued assertability policies of the supervaluation
family — from which it differs by locality, tabularity, and greedy
collapse.

## 11. Expeditions: Curry, parity, Yablo, the crocodile (MEASURED + Lean)

**Paradox as an operator — the expeditions are one construction (MEASURED,
`pengine.py`).** A self-referential net is a system Sᵢ = fᵢ(S₁…Sₙ); to read it
is to ground it (§9). So a paradox is *paradox(f) = ground(S = f(S))* — feed an
operator, form its self-reference, ground it — and the specimens below are that
one construction on chosen operators: the liar is paradox(¬S), the truth-teller
paradox(S), Curry paradox(S→⊥), Russell's propositional shadow again
paradox(¬S). Three measured layers read a net, coarse to fine:

1. *Grounding* — the zero-trust verdict (§9): every pure self-reference lands in
   Z. Coarsest; it does not separate paradoxes.
2. *Solutions* — the classical models of the net: 0 = contradictory, ≥2 =
   underdetermined, 1 = determined. This is the content of the parity theorem
   below — an odd ring has no model ⟺ its reference graph is not 2-colourable.
3. *Dynamics* — the period spectrum of the greedy jump: finest. The period-1
   points are exactly the solutions, so dynamics refines (2); the higher periods
   separate what the model count merges — the liar and Curry are the *same*
   2-cycle, the k-ring carries 2k, the crocodile a 4-cycle.

Grounding is strictly the most conservative of the three: measured over all
9015 one-sentence nets up to six symbols, it reaches a classical value only when
the net has a *unique* model that is also reachable from ignorance; 1068 of them
have a unique classical model yet ground to Z (e.g. S = S∨¬S — classically ⊤,
here Z: zero-trust will not grant a truth it cannot ground). The ZTL-settled
nets are thus a strict subset of the classically-categorical ones.

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

**Kernel-checked (`Facts.lean`, zero axioms).** Every dynamic fact of this
section is a theorem, not a battery entry: Curry is homeless in the greedy
register without any negation (`curry_homeless`) and finds a home in the lazy
one (`curry_kleene_home`); the liar oscillates with period two
(`liar_period2`) and Jourdain's carousel has no fixed point and period four
(`carousel_no_fp`); the Yablo truncation at n = 3 has the unique grounded
model F, F, T (`yablo3_unique`); and the crocodile's deal is void at the
grounded point (`crocodile_deal_void`).

**Yablo at the limit** (`ZYablo.lean`, empty axiom list). Three theorems
replace the single truncation check. EVERY finite truncation is grounded,
for every n, with exactly one model — the last sentence true and all
earlier ones false — so the finite instrument is not too weak to see a
paradox; there is nothing at any finite stage to see. The INFINITE system
admits no verdict assignment whatever (`yablo_greedy_homeless`). And it is
satisfiable in the lazy register, where everything unverified is admissible
(`yablo_lazy_home`) — the diagnosis the liar and Curry receive, reached here
for a system no finite stage could diagnose.

*The classical step is avoided, and that is the point of doing it here.* The
textbook argument moves from "not every later sentence is false" to "some
later one is true", which is `¬∀ → ∃¬` and would have taken the file to the
classical tier. It is unnecessary: from "every j > i is false" it already
follows that every j > i+1 is false, so the fixpoint condition makes
`s_{i+1}` true outright, contradicting its falsity. No witness is extracted.
A paradox of infinite regress, refuted without a single classical step.

*Two things are assumed rather than derived, and the module says so:*
bivalence of the sentences is written into the admissibility condition as a
clause — it is §6's greediness, but posited here rather than re-derived from
an evaluation of an infinite quantifier, which would need the parameter
tableaux §27 still lists as open; and the rendering of `sᵢ` as "T exactly
when every later sentence is F" is the strict universal of §6 with the greedy
denial inside it. The truncation theorem is the positive control: an
impossibility result is worthless if its definition is unsatisfiable by
construction, and the same shape restricted to any finite n has exactly one
model.

## 12. Sets with unverified elements (MEASURED + Lean)

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

**SQL's inconsistency is not inherited** (a theorem now: `ZNull.two_equalities`, §27)**:** SQL holds NULL≠NULL in
comparisons yet merges NULLs in DISTINCT/GROUP BY — swapping equality
of values for equality of marks inside one syntax. Here the core
deduplicates classically and the marks live with multiplicity — each
operation honest about its own business.

**Kernel-checked (`ZSets.lean`, zero axioms).** The load-bearing claims are
theorems: a mark belongs to nothing, itself included (`memZ` — SQL's NULL IN
(NULL)); a marked set is not a subset of itself and not equal to itself
(`sub_marked_false`, `seteq_self_marked`), so the identity laws fall exactly
as they do in the tables; and on clean sets membership, inclusion and
equality are classical (`memL_classical`, `subL_refl_clean`,
`seteq_refl_clean`) — the C-extension, proved rather than sampled. And the
cardinality interval now has its general law (`ZTaint.card_earned_iff`): it
collapses to a POINT precisely when there are no marks at all, or exactly one
mark over an empty verified core. So |{Z}| = [1,1] is not a curiosity but the
second of exactly two cases — one mark is exactly one thing, and two marks
are not two things. The four instances above are consequences of it rather
than samples. The restatement used is proved equal to the corpus's own
`cardLo` rather than assumed so, which is the whole point of stating it.

## 13. The reals: two failures of enumeration (MEASURED + Lean)

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

**Kernel-checked (`ZExped.lean`, zero axioms).** Both failures are theorems.
The stream atom never earns T at any time (`eqStream_never_T`), not even a
stream against itself (`eqStream_self`); one finite witness earns apartness
(`eqStream_apart`) and earned apartness is never revoked
(`eqStream_F_persist`). Failure #1: no registry certifies membership of
anything, its own rows included (`mem_never_T`). Failure #2: the diagonal
earns its non-membership against every entry (`diag_not_member`). What is
*not* formalised is the contrast case — that registries of fractions certify
every element — so the countability of ℚ as earnable presentation identity
remains measured.

## 14. Functions: taint mode (MEASURED + Lean)

A function is a computation, not a verdict ⇒ by the two-register
theorem it behaves lazily: **the mark flows through the function** with
a growing pedigree (f(m) is a new mark "f applied to m"). Measured:

* **Images:** verified collisions *earn* merging (f(1)=f(2) is a proven
  fact, the core deduplicates), marks keep multiplicity:
  |f({1,2,3,Z})| ∈ [2,3].
* **Composition:** taint is transitive (pedigree g(f(m))); the image is
  associative at representation level while verdict-equality is F
  (regularity R1, §26).
* **The preimage splits** into a verdict version (marks dropped —
  default deny) and a solver version (marks as candidates) —
  regularity R2 (§26).
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

**Kernel-checked, and now in two places.** The pearl is a theorem:
`ZExped.inj_cert_marked` shows that ONE marked pair collapses the
injectivity certificate for EVERY function — the identity included —
resting on `eqAtom_z_right` (an atom against a mark is Z). And the
laundering ban is a theorem too (`ZTaint.no_laundering`): applied to an
unverified reference, a chain of verified functions OF ANY LENGTH returns an
unverified reference. The pedigree grows; the mark never comes off. The
sanitizer is not an application at all — a verified value is a different
ELEMENT, put there by an act of checking, and that is stated beside it. In
security terms: no declassification without proof, proved.

The rest of this section — images and multiplicity, transitivity of the
pedigree at representation level, the preimage split, the merge of verified
collisions — is measured on worked cases and is **not** formalised. The tag
stays MEASURED for that reason.

## 15. Arithmetic with marks (MEASURED + Lean)

Numbers: verified values and marks with an interval of partial
knowledge [lo,hi] (ignorance = (−∞,∞)). Operations are computations ⇒
lazy: intervals flow (interval arithmetic, decorrelated). Comparison
atoms follow the generating principle extended to intervals: **T if
forced under all readings; F if falsehood is forced; else Z**. Measured:

* **Forcedness earns even on marks:** 0·w = an earned 0 even for a wild
  mark (forced on ℤ by all readings) — a point of deliberate divergence
  from IEEE (their 0·NaN = NaN: their domain contains inf/nan) — now a theorem, `ZNaN.zero_times_mark` / `emb_mul_not_hom`, §27.
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
  verdict-wise with coinciding intervals (regularity R1, §26).

**The fourth twin: abstract interpretation** (Cousot & Cousot, 1977) —
interval value analysis (lazy flow of abstract values through
computations) + assertion checking (greedy verdicts). Of the four
engineering traditions named so far — NaN, NULL, taint tracking, abstract
interpretation — three are reproduced on worked cases in the sense of §1,
and this one is now an embedding.

**Kernel-checked embedding** (`ZAbsInt.lean`, empty axiom list). Their Galois
connection is formalised as they state it — α(S) = the least interval
containing the value set, γ the concretization — and proved in both
directions: α(S) ⊑ [a,b] ⟺ S ⊆ γ([a,b]). Against it our verdict is not
merely *sound* on the abstract value, which is what abstract interpretation
normally buys and pays precision for; it is **exact**. For a threshold atom,
the verdict computed from the interval alone equals the verdict computed over
the whole concrete value set, in all three cells. Nothing is paid.

*And the price appears exactly where this section already said it does.* The
moment one variable occurs twice the exactness is gone: over the value set
[1,3] every concrete `v − v` is 0, so the concrete verdict of `v − v < 1` is
T, while the decorrelated interval computation gives [0,2] and returns Z. The
witness is mechanical, not narrated — the concrete image and the abstract
interval are both computed in the file. So decorrelation is not an aside
about intervals; it is the exact boundary of the exactness theorem.

*What is not done:* the framework — widening, narrowing, fixpoint transfer —
is not formalised. One atom over one abstract domain is mapped, not the
method.

**Kernel-checked (`ZExped.lean`, `ZNum.lean`, `ZNumCoherent.lean`, zero
axioms).** Identity is earned by nothing short of full verification: a mark
against itself is Z even when the bounds coincide (`mark_self_not_earned`).
Narrowing-heredity — what is earned is never revoked as intervals shrink — is
a theorem for every comparison atom under both readings
(`forcedLE/NotLE/LT/NotLT/EQ/NE_hereditary`, twice over), together with the
transitivity of narrowing and the endpoint case. Decorrelation has a named
witness (`decorrelation_witness`). Forcedness on products (0·w) and the
price-list inheritance for commutativity and the unit are measured only.

## 16. The probabilistic bridge: Z ≠ p = 0.5 (MEASURED + Lean)

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

**The Dempster–Shafer bridge is now a theorem** (`ZDempster.lean`, empty
axiom list). Their side is formalised as they define it — a mass assignment
is a list of focal subsets of a finite frame with positive weights, Bel(A)
sums the focals lying inside A, Pl(A) those meeting it. Our side is defined
by the generating principle alone, with neither Bel nor Pl appearing in it:
forced true when every reading of the ignorance lands in A, forced false
when none can, marked otherwise. The two are then proved to agree in all
three cells, for every finite frame, every proper mass assignment and every
event — so what was measured on one assignment holds on all of them. With
it the fifth twin (Walley's imprecise probabilities, whose lower/upper pair
is exactly Bel/Pl) joins the sixth as an embedding rather than a
correspondence.

*The properness condition is not decoration, and finding that out is what
the theorem was for.* The first draft required only positive weights and was
FALSE: on the empty mass assignment the verdict comes out T vacuously while
Pl = 0, and the F-cell fails; an empty focal breaks it the same way. That is
Dempster–Shafer's own `m(∅) = 0`, which held silently on the one assignment
that had been measured. A single checked instance cannot show you the
condition it happens to satisfy.

**And the other two claims are now theorems as well** (`ZIgnorance.lean`,
empty axiom list).

*Reparametrization.* The two Bayesian numbers are computed and shown
different — by cross-multiplication, so that no division enters a file about
not importing what one was not given. Our verdict is Z in both, and not by
luck: it is proved invariant under EVERY strictly monotone relabelling, not
only under the squaring the example uses. A monotone map carries the gap to a
gap; the number moves and the verdict does not.

*Ellsberg.* The verified urn earns the claim "no worse than fifty-fifty" and
the unknown urn does not — and the module proves WHY it does not, which is
the whole content: the atom itself is Z, neither forced nor excluded, and the
denial of an unforced claim is classical (`¬Z = F`, §3.1). Default deny, with
no judgement passed on the unknown urn's merits. What Ellsberg's subjects
were reading is a mark, and a point prior has no place to put one.

## 17. The modal layer: local □ versus global (MEASURED + Lean)

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

**Kernel-checked (`ZExped.lean`, zero axioms).** The threshold reading is a
theorem in all three directions at once — T ⟺ □, F ⟺ ¬◇, Z ⟺ contingency
(`atom_thresholds`) — with the duality ◇ = ¬□¬ over completions
(`box_dia_duality`). And the separating cell is machine-checked
(`ladder_vs_global`): the local ladder earns ¬¬Z = T exactly where the global
□ goes mute, so the two layers are incomparable rather than one refining the
other.

## 18. Russell: containment instead of explosion (MEASURED + Lean)

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

## 19. The verification operation and verdict warranties (MEASURED + Lean)

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

**The fence depth is exactly m−1 (MEASURED).** How deep must a
verification-invariance check look before the hereditary grade is
certain? For a *sound* verdict all full completions agree with it by
definition, so heredity violations can live only at partial
refinements of size at most m−1 (m the number of marks): depth m−1
always suffices. This half is now a theorem too
(`ZFenceDepth.resolved_all_marks_agrees`, empty axiom list): a
refinement that has resolved every mark the formula *depends on* has
become an ending, and endings agree by soundness. It is stated
positively — "resolved everything relevant ⟹ agrees" — rather than as
the existential "a violation leaves a mark unresolved", because the
latter is an ∃ drawn from a negation and would have to come through
`Classical.byContradiction`, taking the whole file to the classical
tier for a cosmetic gain. The content is the same, read by
contraposition. It is also necessary: the guard family

    (b₁ ∧ … ∧ b_{m−1}) → (a → a)

— a conjunction guard of m−1 marks standing over the fallen law of
identity — is sound, invariant under every verification of fewer than
m−1 atoms, and dies the moment all guards are verified true, when the
door opens onto the greedy-F gap a→a. This was checked deterministically
for m = 3, 4, 5, with the m = 2 witness (¬p)→(q→q) above; **it is now a
theorem for every m at once** (`ZFenceDepth.lean`, empty axiom list),
because the guard family is uniform in m and so generalises whole. Three
clauses are proved: the cell is sound at every m; it is invariant under
every refinement leaving any single guard unverified — and that clause came
out *stronger* than the argument needed, since a sunk guard makes the arrow
vacuously true whatever happened to the gap atom; and it dies exactly when
the full guard set is verified. The violation is therefore not merely
reachable at depth m−1, it is reachable nowhere else. One step is
deliberately left as prose rather than smuggled into the formalisation:
that a check inspecting fewer than m−1 atoms must leave some guard
unverified is finite counting, not logic. Hence
**no constant-depth characterization of the hereditary grade exists**;
the cost of the full warranty grows with the number of unverified
inputs, and what remains open is a structural, non-enumerative
criterion.

**Result: a verdict is a pair (value, warranty grade).** The value is
greedy (local, fast); the warranty grades are global. Six verdict
classes now, and the honest advice differs by grade: **hereditary T —
build your house** (no verification path can revoke it); **sound T —
never a lie, but may stall to refusal before verification completes**;
T-until-verification — a ladder report (¬¬p), alive till the first
check; symmetrically for F, with F-until-verification as default deny.
The Frege cell is fenced by the top grade only; the middle grade
fences lying, not spoiling.

**A verdict carries a warranty; a refusal carries a receipt** (Lean,
`Receipt.lean` and `LabelExact.lean`, zero axioms). The lazy register
answers Z together with a label — which unverified atoms the answer is
still waiting on. That label is what makes a refusal accountable rather
than merely withheld, and it is now bounded from both sides.

*Nothing that could matter is omitted* (`receipt_complete`): for every
formula of the language, every valuation and every unverified atom, if
the label leaves that atom out then no value of it changes the answer.
Contrapositively — the reading that matters — **an atom that could
change the answer is always named.** The same holds in the register
that actually issues verdicts (`receipt_complete_greedy`). That second
theorem was predicted in writing to be FALSE, by us, before the census,
on the ground that the greedy lift is non-monotone and
connective-local; the census refuted the prediction (zero misses in
296,161 cells carrying an unverified atom) and the reason turned out to
be `greedy_agrees_when_decided` plus the shape of the greedy tables.
The prediction is recorded rather than dropped.

*And nothing idle is named — on a linear claim* (`label_exact_linear`):
if no unverified atom is read twice, every atom on the receipt is one
the answer is genuinely waiting on — there is a definite reading of the
other unverified atoms under which answering this one T and answering
it F give different verdicts.

Three things this pair does not say, each of them measured.

* **Relevance cannot be tested one atom at a time.** `p ⊕ q` is linear,
  both atoms are named correctly, and neither moves the answer alone
  (kxor Z Z = kxor T Z = kxor F Z = Z). Single-atom probing — the
  notion we first measured against, which produced our own inflated
  over-approximation figures of 16% at depth 2 and 35% at depth 6 —
  systematically reports jointly relevant atoms as idle. Against the
  joint notion (the union of minimal jointly moving sets) the label is
  exact in 93% of 14,530 pending cells and never once too small.
* **The linearity hypothesis is load-bearing, not decorative**, and
  this is proved rather than asserted: `clash_names_an_idle_atom`
  exhibits `p ∧ ¬p`, where the receipt names an atom that no reading
  can move. All of the residual inexactness (13–18%, pool-dependent)
  sits in cells where a marked atom occurs more than once — the same
  occurrence-independence that costs `p → p` and `p ∨ ¬p`.
* **The residue was attacked and did not yield.** A demand-driven label
  computed against reachable sibling values was built as a prototype
  and matched the existing label cell for cell — the existing analysis
  already IS that analysis. Closing the gap needs relational tracking
  of shared occurrences across branches, which is not cheap.

Two auxiliaries carry the result. `drivable`: a pending linear claim
can be driven to T and to F (48,759 pending linear cells, every one
reachable both ways) — so a refusal never hides a foregone conclusion;
this is also what makes the exactness proof go through, since holding a
pending sibling at Z would hide the pivot. And `Linear.linear_no_loss`,
from the other direction: at multiplicity ≤ 1 no truth is lost.
Together, **on a linear claim the judge is exact in both directions —
it loses no truth and names no idle ground.** What remains imperfect
there is the over-grant, and that one comes from the collapse ¬Z = F
rather than from multiplicity (`¬¬p` has one occurrence and still
grants).

**And the over-grant has its own fence (Lean, `NoGift.lean`, zero
axioms).** The gift is the dangerous half — an unearned T is
indistinguishable from an earned one, where a refusal at least announces
itself — so the question is which claims cannot produce one. The answer
is an axis orthogonal to multiplicity: **negation.** If every unverified
atom of a claim stands under no negation (`ContextClosure.negFree` for
each mark — which also bars it from an implication's antecedent and from
`⊕`/`↔` entirely), then a greedy T survives every refinement of the
marks:

    no_gift : posMarks v φ → refines v w → evalF v φ = T → evalF w φ = T

`closure_coincides` was the one-atom case; what is added is all marks at
once and all PARTIAL refinements, which is what the hereditary grade
actually asks for.

Three things must be said with it, and each is proved rather than
asserted. **Only T is protected** (`F_is_not_protected`): `p ∧ p` sits
inside the fragment, is greedily F, and revives at `p := T` — measured,
950 of 1700 in-fragment F cells are revocable. The asymmetry is the
point: a refusal that later becomes a verdict is inquiry working. **The
fragment is sufficient and narrow** (`fragment_is_not_necessary`):
`p → q` with `p` unverified and `q` verified true cannot be moved by any
refinement, and sits outside — and outside is where most safe verdicts
live, 66% of hereditary verdicts at depth 2, rising to 99% at depth 6.
Outside is unguaranteed, not unsafe. **And the two fragments are
incomparable**: gifts do not need multiplicity (594 linear cells gift at
depth 2) and in-fragment claims may read a mark twice without gifting
(184 such cells). Negation is the axis of the gift; multiplicity is the
axis of the loss.

Measured before the proof was attempted, predictions frozen in
`lab/nogift/PREDICTIONS.md`: 323,530 cells over three pools, zero gifts
inside the fragment; all five predictions held, including the one
recorded as the weakest.

Measured before each proof was attempted, in the order the method
requires: 412,593 cells for completeness, 14,530 pending cells for the
joint-exactness figure, 128,372 linear cells for exactness (zero
inexact), 48,759 for drivability. Label propagation of this kind is old
— de Kleer's ATMS [40] — and is named here rather than presented as
new; what is ours is the pair of bounds on this particular label.

**What the receipt cannot answer: how many at once (MEASURED).** The
label says which grounds could matter. It never says how many must be
settled *together* before anything moves, and the difference is
operational. Define, for an unsettled claim, its **width**: the size of
the smallest set of unverified grounds that, filled together, moves the
verdict. Width 1 is ordinary incremental inquiry — go check this one.
Width ≥ 2 means no partial progress is possible: the whole
configuration must be produced before anything at all happens.

**Width 1 dominates, and the judge's one-ground order is usually
honest**: 93% of unsettled cells over the exhaustive depth-2 pool, 91%
over random depth-5 formulas across five atoms. **But width is not
bounded.** The hunt found width reaching the number of available
grounds — 4 of 4 at four atoms, 5 of 5 at five, over ~24,000 unsettled
cells. The honest statement is a limit rather than a defect:

> **Step-by-step inquiry is not always possible.** There are claims of
> any size for which nothing moves until every unverified ground is
> filled at once.

That is Meno's second horn in a measurable form, and it is measured
narrowly: the claim is about this calculus's own pool, not about
inquiry in general.

**The prediction behind this was right in its conclusion and wrong in
its witness**, which is worth recording. We predicted unbounded width
with xor chains as the witnesses, having worked `p ⊕ q ⊕ r` by hand.
That formula has width **1** — the inner xor collapses to a definite
value and the outer one is sensitive to the last ground alone; the
hand-calculation had tested two atoms of three. The genuinely wide
cases are irregular mixed formulas, and they had to be hunted rather
than constructed.

**Width is invisible to the label**, and this is the
over-approximation half of §19 showing its operational face: `p ⊕ q ⊕ r`
names all three grounds and has width 1; `p ⊕ q` names both and has
width 2. So the fix could not be a better label — it had to be a new
computation. The judge now reports a `joint` field: when no single
ground moves the matter, it names the grounds that must be filled
together and says plainly that a one-at-a-time order would be empty
work. The exact width is **deliberately not computed** — that search is
exponential in the number of marks, and what a reader needs is the
difference between "go check this" and "no single check will move
this", not the cardinality.

## 20. Evidence combination: conflict is not laundered (MEASURED + Lean)

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

**The sixth twin is now an embedding, and the tag still says MEASURED.**
`ZProv.lean` (empty axiom list) formalises the provenance algebra and maps
it into ZTL — see §27 for what that theorem says and, more to the point,
what it does not. It settles the twin, not this section: combination as
intersection, the earned contradiction of an empty intersection, and the
Zadeh case remain measured on worked scenarios with `zcombine`, and the tag
is left alone for that reason. One further thing belongs here and is not
comfortable: our own probe against the installed package
(`db/probe_provenance.py`, PostgreSQL 16.14 / ProvSQL 1.13.0-dev) found that
semirings already do the cascade, the alternatives and the exposed set, and
that ProvSQL also carries magnitudes through aggregation — which an earlier
version of this corpus denied in print. That denial is withdrawn. Anyone
needing those four things should use ProvSQL; what this paper adds is where
their algebra sits inside the two registers, and where it provably cannot.

**Kernel-checked** (`ZCombine.lean`, empty axiom list). Combination is the
meet of constraints and its members are exactly the values both sources
allow; an empty meet is an EARNED contradiction in the sense that makes the
word mean something — no value whatever satisfies both, so the refutation
holds under every reading; and verification is that same operation against a
singleton, which is why the act of checking can itself earn a conflict when
the checked value lies outside what was already known. One operation, proved,
not two.

**And Zadeh's paradox is now a theorem rather than an anecdote.** Two doctors,
three diagnoses, each giving the tumour one part in a hundred and disagreeing
about the rest. Dempster's rule intersects the focal elements, discards what
intersects to nothing — 9999 parts of 10000 — and what survives sits on the
tumour alone. By the threshold theorem proved for their own theory in §16,
the verdict is then T and belief is full: an unshakable diagnosis
manufactured from two one-percent opinions. *The certainty is derived inside
our machinery, from their rule, using our theorem about their theory* — not
criticised from outside. Retaining the conflict instead puts the mass on the
empty focal, and the assignment is then improper: no verdict is issued and
the conflict stays visible. That is the refusal this section describes, and
it is a theorem about the precondition rather than a further verdict.

*Still measured, not proved:* the unification of verify with combination is
proved above for interval constraints only, and the provenance-polynomial
bullet is covered separately by `ZProv.lean` (§27). The Smets/TBM reading of
`m(∅)` as a modelling decision rather than an error is a position, not a
theorem, and is not claimed as one.

## 21. Logical time: verification is the only clock (MEASURED + Lean)

ZTL owns no physical clock, and §7 keeps it honest: duration, tense and
"how long" are outside the system's axis. Yet one clock was inside the
calculus all along, unnamed. The verification operation of §19 is a
tick: one act `verify` resolves one mark into an earned classical
value. A moment is a marking; the past is the verified prefix; the
future is a tree — every remaining mark can resolve either way, so
time branches, and "everyone's time differs" is just the choice of a
path through one tree.

**The ladder is a temporal logic.** The central identification costs
nothing and buys the whole layer: the warranty ladder of §19, read on
the verification tree, is a system of temporal quantifiers —

* *until-verification* — true **now** (the present tense of a verdict;
  credit);
* *sound* — true **at every ending** (all completed traces agree; the
  road may wobble);
* *hereditary* — true **always along every path** (the invariant of
  the tree; never revoked).

The modal layer of §17 is the statics of this structure (worlds =
completions); the temporal layer is its dynamics — the paths through
the partial refinements between here and the endings.

**Measured** (`ztime.py`; the grade automaton over the exhaustive
depth-≤2 pool, 2,906 formulas, 29,812 ticks): the hereditary states
absorb — not one tick leaves them (0 violations); no compound formula
is ever caught waiting (greediness in temporal costume); ground can
arrive all at once (14,818 direct U→H jumps) and credit can worsen
before it settles (108 S→U demotions); every completed trace ends
hereditary — the arrow of logical time points at the shelf (130 of
130); and settlement can come early — 68 of 130 traces reach a
hereditary verdict with marks still unresolved (after `p:=T` the
verdict of p∨q no longer cares about q). Settling times run from 0
(¬(p∧¬p) is born on the shelf) to every-mark (⊕ needs them all).

**Lean** (`lean/ZTime.lean`, empty axiom list, structural — for every
formula, marking and tick, not an enumeration): absorption (a
hereditary verdict survives any tick with its grade), the arrow (a
fully verified marking is hereditary), and the ladder inclusion
(hereditary ⟹ sound; an ending is a refinement). The proofs are
pointwise throughout — no function extensionality enters.

**A conjecture that lived one hour** — kept, as the method demands.
The first sweeps found no tick that ever *enters* the sound-only
grade, and for an hour the conjecture stood: *sound is a birth grade —
verification spends it but cannot mint it*. The proof attempt broke at
a specific spot, and the spot folded into a counterexample: the pools
had been shallow. The selector φ = (a ∧ X) ∨ (¬a ∧ p) with
X = ¬¬p ∨ (q ∨ ¬q) walks F/U → (a:=T) → T/S → (p:=T) → T/H from the
all-marked start: soundness is *earned* — by the tick that verifies
which world you are in — and the full strict ladder U→S→H is realized
rung by rung (`ztime.py` §§5–6, the record of the death included).

**The tool.** The ZFL statement genre carries an optional `timeline`
field (a list of verification ticks, validated with its own error
codes); the engine plays it into a chronicle — verdict and warranty
per tick, with settlement marked. The consumer sentence of the layer:
once a verdict is hereditary, every remaining check buys nothing —
stop paying (`usage/car.py`, the used-car stand: an affirmation is
earned at the last tick; a refusal is grounded at the first failure,
three checks saved; verifying the selector first saves two).

## 22. Epochs: expiry and the boundary theorem (MEASURED + Lean)

The time of §21 is monotone: ground only arrives. Institutions live in
non-monotone time — confirmations lapse, registries are re-pledged,
facts are authoritatively changed. The anti-tick `expire` returns an
earned value to the mark, and with it the layer splits into two
chronologies that must never be conflated: the *knowledge* chronology
(verify — learning more about the same world) and the *validity*
chronology (expire — the world becoming different). A maximal
verify-only stretch is an **epoch**; an expiry opens a new one. A
composite event — authoritative revocation — is deliberately a
composition, expire + verify of the new value, so that one event
cannot hide two institutionally different facts.

**Measured** (`zexpire.py`): hereditary is a warranty against future
*verification*, not against the *loss of ground* — a fully verified
conjunction (T/hereditary) falls to F/until-verification on a single
expiry; and the "checks saved" of §21's early settlement are revealed
as a loan against the expirable ground: the settled verdict survives
the death of its shortcut iff the saved checks were verified before
the clock ran out — expiry-insurance, priced by the core.

**The Epoch Boundary Theorem** (`lean/EpochBoundary.lean`, empty axiom
list, structural). Call a verdict *epoch-blind* at a marking if it is
invariant along every finite chain of verify and expire events — i.e.
if the protocol refuses to distinguish epistemic refinement from
validity change. Then, within this model (markings over {T, F, Z}, the
greedy evaluation, the two event kinds):

> a verdict is epoch-blind **iff** it is constant over all markings
> whatsoever — iff the assertion reads none of its grounds.

Contentful conclusions cannot survive unrestricted epoch crossing; the
empirical census (2,906 formulas, 0 contentful survivors) is thereby
upgraded from evidence to a theorem for every formula of the language.
A separation witness (`epochs_matter`) completes the picture: a
hereditary verdict destroyed by one expiry — so intra-epoch warranty
and cross-epoch persistence are provably different notions, and the
epoch boundary is a logical necessity, not an administrative
convenience.

**The institutional reading.** For an admission formula over grounding
atoms the layer yields a three-coordinate cell — epistemic status
(the global supervaluation of §17: Z is *not established* and is never
conflated with falsity), operational decision (the greedy verdict:
default deny), and warranty grade — and an event ledger in which every
verification tick carries its source. The closed-world loan — "no
proof of revocation, hence not revoked" — cannot be taken inside the
logic at all: ¬R at R = Z evaluates F/until-verification, an argument
from absence never yields T. It can enter only as a tick without a
source, which the ledger exposes as an *ungrounded verification
event*. A worked, frozen artifact (admission condition; expiry branch;
revocation branch; the rejected ungrounded tick) ships in the
repository (`vrg/epoch_artifact.py`, deterministic JSON ledger).

## 23. The price of derivations: transport, not creation (MEASURED + Lean)

The price list of §3.1 concerns laws; it extends to *paths*. Take the
12 alive entailment rules of §3.2 as the only links, the 2 fallen ones
(¬¬-elimination and tautology-in-conclusion) as a loan library, and
close premise sets under chains, bounded to a 153-formula pool over
three atoms; every closure is cross-checked against the semantic
entailment of §3.2 (0 violations — the chains never lie;
`zderive.py`). Three facts emerge.

**From nothing, nothing — even on credit.** The closure of the empty
premise set is empty, with and without the loans: the battery has no
axiom rule. And yet ZTL-tautologies *exist* — the guarded forms
¬q → ¬q and ¬(p ⊕ p) are true under every assignment, because denial
is classical (¬Z = F; §3.1's "a denial is free") — and the battery
cannot mint even those. The alive rules are *transport, not creation*:
classical logic mints truth from form; ZTL's free truths must *enter*,
as verified premises.

**The one-way street, priced.** From {p} the ladder ¬¬p is earned
(¬¬-introduction is alive); from {¬¬p} the alive closure is {¬¬p}
itself, and the ¬¬-elimination loan unlocks fourteen formulas — the
first measured *on-credit derivations*, p among them. What
classical logic cannot even see (the step is invisible inside it) is
here a priced borrowing with a named creditor.

**The gap, honestly.** The rules are incomplete for the semantic
entailment even on the small pool ({p}: 24 entailed, 15 derivable) —
part pool-boundedness, part missing law-rewrite links, part genuine;
the split needs a bigger pool, not a claim.

**Kernel-checked** (`ZNoAxiom.lean`, empty axiom list), and in the general
form the 153-formula closure could only sample. Two halves that say something
only together.

*The tautologies exist under EVERY valuation, marks included.* `¬q → ¬q` and
`¬(p ⊕ p)` are T for every assignment, not merely across a pool — this is
where the greedy denial earns its keep, since `¬Z = F` is classical and no
mark can drag a formula built on denials down.

*And nothing is derivable from nothing — for ANY calculus whose every rule
demands a premise.* Not "these twelve rules happen not to derive it": no such
system can, whatever its rules are. Together: **there is a formula true under
every valuation that no premise-requiring calculus derives from the empty
set.** Truth of that shape has to be brought in, not minted — which is what
"transport, not creation" says.

*What is hypothesis and what is conclusion.* That the twelve alive rules of
§3.2 all have non-empty premise sets is a fact about the battery, recorded
and measured there; it is the HYPOTHESIS of the theorem, not its conclusion.
What is proved is that the hypothesis suffices, for every rule set at once.
The one-way street and the incompleteness gap in this section remain measured.

## 24. Identity: a `=` predicate on credit (MEASURED + Lean)

The first-order layer of §6 had quantifiers but no identity. We add it,
and the zero-trust principle turns the classical axioms of identity —
reflexivity and Leibniz's substitutivity — from free laws into *earned
verdicts*. The reading is the native one: a domain individual is a
*reference*, and a **marked** individual is one whose reference is not yet
verified — the individual-level face of Z (§10), a null pointer, an
unresolved description, `1/0`. Equality inherits the mark:

    Eq(a, b) = T   if a, b are grounded and denote the same object,
             = F   if a, b are grounded and denote different objects,
             = Z   if a or b is a marked (unverified) reference.

Four facts, all measured total in `zeq.py` over a domain of grounded and
marked individuals, and all kernel-checked in Lean (`ZEq.lean`, nine
theorems, **empty axiom list**) — on a fixed five-individual model (three
grounded, two marked), as instance certificates rather than structural
theorems over a class of models; the exhaustive statement is the
measurement. (Leibniz here is a one-line `congrArg`: once an equality is
earned, `=` is genuine identity, so substitution is congruence — the
content is in *when* it is earned, not in the substitution.)

- **Reflexivity is earned.** `Eq(a,a)` is T for a grounded reference but
  **Z** for a marked one — self-identity is not free; an unverified
  reference is not even certified equal to itself. This is the applied
  regularity R3 (§26), *identity is not earned*, now made a predicate: it
  is the same phenomenon as the uncertified `id` on a marked argument
  (§14), the non-registrable stream `x ≠ x` (§13), and `1/0 = 1/0 → Z`
  (§15). Reflexivity is therefore *not a law* (`refl_not_free`), the exact
  identity analogue of the fallen `¬¬p = p`.

- **The rule/law split (§3.2), on identity.** Symmetry holds as a rule
  (`Eq(a,b) ⊨ Eq(b,a)`, no violations) but the biconditional *law*
  `Eq(a,b) ↔ Eq(b,a)` fails wherever the equality is Z — because `↔` over
  Z is F (quarantine is detectable, `↔(Z,Z)=F`). Transitivity holds as a
  rule.

- **Leibniz substitutivity survives as a rule — salva veritate, not salva
  Z.** `Eq(a,b) ⊨ P(a) ↔ P(b)` for every generic predicate P (zero
  violations of the licensed substitutions): an earned equality means the
  two references are literally the same object (`eq_forces_same`), so
  substitution is congruence (`leibniz_congr` is a one-line `congrArg`).
  Where a reference is unverified the equality is never T, so the
  substitution is simply never licensed — you cannot launder a mark
  through identity (`no_laundering`).

- **Identity of indiscernibles fails on the mark.** Two distinct marked
  references are indiscernible — Z under every generic predicate — yet
  `Eq(m₁,m₂) = Z`, not T. Unverified references are not made equal by the
  mere absence of a distinguishing predicate.

So ZTL keeps the *consequence relation* of classical identity (Leibniz,
symmetry, transitivity as rules) and loses exactly the free half —
reflexivity-on-credit and indiscernibility-on-credit — by the same coin as
everywhere else. And the marked individual is the seed of the next
section: a non-denoting term is an unverified reference.

## 25. Free logic and definite descriptions: the mark as non-denotation (MEASURED + Lean)

Classical logic assumes every singular term denotes; *free logic* drops
that assumption. Its schools disagree on what an atomic statement about a
non-denoting term is worth — negative free logic says **false**, positive
says some are **true**, supervaluational leaves a **gap** (but keeps
excluded middle super-true), and the neutral school (Lehmann; weak-Kleene
on non-denoting atoms) gives it a **third value**. ZTL's answer is the
neutral one made operational — the atom takes the **mark** Z — with one
decisive difference: the mark is **greedy**. It does not propagate as a
gap and does not complete to a super-true middle; it evaporates at the
first operator, so excluded middle on a non-denoting atom is **F**, not a
gap and not super-true. Z was always the value of "unverified until
verification"; a description not shown to denote is precisely that.

The spine is a bridge back to §24, and it is Quine's *"no entity without
identity"* made literal:

        E!(t)  :=  Eq(t, t)          — existence *is* earned self-identity.

A grounded reference is equal to itself, so it exists (E! = T); an
unresolved reference is not, so E! = Z. Non-existence is therefore not
asserted through E! — `¬E!(τ) = ¬Z = F`, always — but it is still sayable:
a domain verified to be empty of φ earns `¬∃x.φ = T`, so "the F does not
exist" is asserted Russell's way, as a denied existential. E! and ∃ part
company on the negative side, and Russell's paraphrase is the honest way to
deny. A definite description
`ιx.φ(x)` — "the x such that φ" — denotes the unique grounded satisfier of
φ, uniqueness decided by the `=` of §24; with zero or several satisfiers
it is a marked reference. This is Russell's uniqueness, but failure lands
on the mark, not on falsity.

Measured in `zdesc.py`, with the first-order core in Lean (`ZDesc.lean`,
eight theorems, **empty axiom list**):

- **The sharp divergence: excluded middle.** For a non-denoting atom,
  `P(τ) ∨ ¬P(τ) = F` in ZTL, whereas supervaluational free logic makes it
  *super-true*. ZTL marks the gap rather than completing it; the mark is
  not a value, so the middle is not excluded (`lem_fails_nondenoting`).
- **Divergence from Russell.** "The present king of France is bald" is
  **F** on Russell's `∃x(Kx ∧ unique ∧ Bx)` and **Z** in ZTL: same
  sentence, Russell asserts falsity, ZTL refuses the assertion and marks
  it. (Compare §18, where Russell's *paradox* is contained rather than
  exploded — the same refusal to assert on unearned ground.)
- **Greedy propagation.** `P(τ)` alone is Z, but `P(τ) ∨ ⊤` is T
  (`mark_evaporates_in_compound`): a non-denoting term poisons only the
  atom, never a compound.
- **An internal witness.** `1/0 = ιx.(0·x = 1)` has no grounded x, so it is
  a marked reference and `1/0 = 1/0` is Z — dead-on with the arithmetic of
  §15. The construction reaches the same verdict the number line did.
- **Free universal instantiation.** The classical law `∀xφ ⊨ φ(t)` FAILS
  for a non-denoting t (`∀xφ` is T over what exists, `φ(τ)` is Z, and
  `T → Z = F`); the repaired free-logic law `∀xφ, E!t ⊨ φ(t)` holds, with
  existence the earned self-identity of the spine. Quantifiers range over
  what exists.

The nearest ancestor is Kleene's partial logic (an undefined term takes
the third value, motivated by partial recursive functions); ZTL's delta is
that the mark is **greedy**, so a non-denoting term inside a
tautology-shaped compound still collapses to a verdict rather than staying
undefined. *Where this stands:* the identity-of-indiscernibles failure and the
free instantiation law are now theorems in Lean on the empty axiom list
(`ZIndisc.lean`, `ZFreeUI.lean`), alongside the `ι` operator, the existence
bridge, and the excluded-middle divergence. Both were measurements until
2026-09-04; the gap was never the size of the domain but the order of the
quantifier — indiscernibility ranges over predicates, and a finite named
list of them keeps the check decidable where the function type would not
be. *Where the boundary now runs:* a falsified law needs one countermodel and
has it, so those failures hold generally. The positive half of identity is
no longer domain-bound either — `ZEqGeneric.lean` proves it for an arbitrary
type with decidable equality and an arbitrary choice of marked references:
an earned equality is genuine identity, substitution through it is
congruence, equality is never earned through a mark, reflexivity holds
exactly on the verified, and indiscernibility forces identity among grounded
references. The positive half of the instantiation schema went the same
way the next day — `ZFreeUIGeneric.lean` proves it for an arbitrary type
with decidable equality, an arbitrary marking, an arbitrary V-valued
predicate and an arbitrary range: wherever the premise `∀ᴳφ ∧ E!t` is earned
so is `φ(t)`; on a marked term the premise is never designated, so the schema
licenses nothing there; the repair is not vacuous; and an empty range is no
loophole, since the refusal comes from the mark rather than from the range
being inhabited. *What is still finite is the RANGE, not the domain*: a
strict universal has to be computed, and computing one over an unsurveyable
range would be exactly the survey this logic refuses to call an act. What
remains proved by exhaustion is now only the failures, and necessarily so:
over an arbitrary domain they are false, since a domain without marks is
classical and there the laws hold. A countermodel belongs in a witness, not
in a general theorem.

**The indefinite description, and choice as an act.** The definite `ι` has
a companion: Hilbert's ε, the choice term `εx.φ` — "*an* x such that φ".
Where `ι` demands uniqueness, ε demands only a witness and picks a
canonical one; where none exists, the choice is unearned and `εx.φ` is a
marked reference. Three facts (measured in `zeps.py`, core in `ZEps.lean`
on the empty axiom list). First, the **ε–∃ bridge**: `E!(εx.φ) = T` exactly
when `∃x.φ` — the choice term denotes precisely when the existential is
earned, and in ZTL the existential is itself the strict-T witness of §6, so
the two coincide. Second, `ι` and ε **divide the labour of reference**: on
a uniquely-satisfied φ they agree, but on a multiply-satisfied one `ιx.φ`
is marked (no unique referent) while `εx.φ` denotes a choice. Third, **the
empty choice is the mark** — `εx.(⊥)` earns Z, never a free F: to choose
from nothing is not an act. This is the operational reading of the
Hilbert operator — a choice is an act, and only an act grounds a term —
the same discipline the whole logic runs on, now at the level of singular
terms.

**Note (v1.4): three kinds of non-denoting are marked alike, and that is
the right answer at the level of value.** A description can fail to denote
in three ways — no satisfier, several satisfiers, or a satisfier whose
denotation is simply unverified — and `zdesc` gives all three the same
mark. The Lean theorems say so directly: `iota_empty_marked` and
`iota_multiple_marked` both return Z, and they are right to. Both are
non-denoting, neither earns existence, and *as a value* nothing separates
them. The distinction between the three is real, but it does not live in
the calculus.

We looked, because it seemed as though it should. Measured 2026-08-19
against the published code, imported and unmodified: **no verdict changes
anywhere.** `E` is a typed evaluation event, not a value; it does not
enter connectives; every compound answers exactly as before. So the
honest headline is the negative one — *the distinction buys no logical
power at all*, and nothing in the published semantics of this section
needs correcting.

**Where it does live is one floor up, in the work order.** The judge does
not only answer; it names the next check. In all three cases it named the
same one, and only one of the three can be carried out. With no
satisfier there is nothing to examine and never will be. With several
satisfiers examining does not help either, for a different reason: the
world is not missing anything, the claim is, and what is owed is a
*stipulation* rather than a check — the corpus already had the word and
was not using it here (`zpassport`: UNDERDETERMINED, several classical
models fit; stipulate one and the claim grounds). Only where the
denotation is merely unverified is "go and check" a real instruction.
Worse, the first two were marked OPEN — a status asserting the question
can be opened.

That is a defect of instruction, not of verdict, and the two are
different objects. It was invisible from inside the calculus precisely
because the calculus was behaving. The repair is in the disposition
layer: a fifth disposition for "this ground has no subject", a rule that
no order is issued which is already known to be unfillable, and — since a
declaration of absence is a premise rather than a discovery — a bill: on
declaring that a ground has no subject, the judge names which settlement
that declaration foreclosed. Where the ground would have decided the
matter, the bill is heavy and the declaration becomes contestable on the
world; where the matter stands on other grounds, the bill is empty. A
missing subject halts its own predicate, never the proceeding. None of this is an erratum against the published
record, and it is recorded here rather than quietly folded in, because
the temptation to inflate a correct verdict with a wrong instruction into
a semantic correction is exactly the kind of over-claim this paper spends
its caveats resisting.

## 26. Cross-cutting regularities

Three facts recurred in every applied chapter; we fix them once.

**R1. Two levels of equality.** On every floor (sets, functions,
arithmetic) the operations coincide at the representation level (the
machine sees equality), yet verdict-equality refuses: the very act of
recognizing identity is default deny. The engineering level serves the
solver, the verdict level serves assertions.

**R2. Two-registeredness reproduces itself.** The verdict and solver
variants of each construction (preimages, cardinalities,
probabilities) arise without special design — as consequences of the
generating principle and the §9 argument for the necessity of two
registers.

**R3. Apartness is earned, identity is not.** The difference of two
unverified objects is earned by a finite witness (diverged intervals,
diverged prefixes); identity is earned by nothing short of full
verification. Hence in one stroke: {Z,Z} ≠ {Z}, m−m ≠ 0, the
non-registrability of streams (§13), and the NaN signature x ≠ x.

## 27. Roadmap

a syntactic cut-elimination procedure with complexity bounds
(admissibility is settled — §5); the mining of the equivalent
quasivariety scouted in §3.7 (axiomatization, subquasivariety lattice,
a representation theorem replacing Plonka sums — a separate work);
a cheap characterization of the hereditary warranty grade of §19
(sound is one pass over completions; is hereditary computable without
enumerating refinements? — MEASURED narrowing, 2026-07-12/13: the
fence depth is exactly m−1 in the number of marks — sufficient for
every sound verdict (violations cannot hide in full completions) and
necessary by the guard family (b₁∧…∧b_{m−1}) → (a→a), checked at
m = 2,3,4,5 (`zverify` §§5–6); hence NO constant-depth
characterization exists and what remains open is a structural,
non-enumerative criterion);
A Lean port of the parameter (arbitrary-domain) tableaux of §6 — BEGUN,
and the two pieces done are the ones that decide what the rest costs.
`ZParamSound.lean` measures the tier of the four rules (see §6): three are
sound on the empty axiom list and the fourth is not. `ZParamSyntax.lean`
lays the ground BOTH quantifier rules stand on — the monadic syntax with
parameters, satisfaction as a RELATION rather than a computation (forced:
the greedy ∀ over an arbitrary domain is not decidable), and the two lemmas
without which neither rule is licensed. FRESHNESS: reassigning a parameter
that occurs nowhere in a formula leaves every verdict of it unchanged,
quantifiers included — this is what lets δ name a witness. INSTANTIATION:
putting a parameter into a formula is the same as putting its value on the
evaluation stack — this is what lets γ and δ instantiate at all. Every
soundness argument for these rules is those two plus bookkeeping. (The
instantiation lemma REPLACES a stack position rather than inserting one,
because `inst` does not shift the other indices; written the other way the
two sides disagree above the substituted depth, and the error would surface
only in the tableau, files later.) The RULE STEPS are then proved on branches
(`ZParamTableau.lean`): γ on T:∀ instantiates with any parameter already in
play and the model does not move at all; δ on T:∃ points a FRESH parameter at
the witness, and that this disturbs nothing else on the branch is exactly the
freshness lemma earning its place. Both preserve satisfiability, which is
what a sound step has to do. The third, γ on F:∃, is stated with an explicit
TOTALITY hypothesis about the model rather than proved outright: it needs a
value for the instance, and over an arbitrary domain the existence of a value
for a quantified formula is itself classical. The hypothesis is visible in
the statement instead of hidden in the definition of satisfaction, where
every other theorem would have paid for it — the same split measured in
`ZParamSound`, reappearing one level up. CLOSURE is proved too
(`ZParamClosure.lean`): a closed branch — two clashing signs on one formula —
has no model. That needed a lemma which is not a definition once satisfaction
is a relation: A FORMULA HAS ONE VALUE. Determinism is proved
constructively, and the quantifier case is where it could have failed — two
admissible values could differ only if one were T and the other F, and then
the T one forces the universal, which forces the other to T as well. The two
specifications are played against each other rather than deciding the
undecidable universal.

The PROPOSITIONAL steps are carried over to the quantified language too
(`ZParamProp.lean`), each read off a cover lemma of §5 rather than invented,
which is why the weak signs appear exactly where the tables put them:
`F:¬φ` yields P and not F, because `¬v = F` holds at T AND at Z, and writing
F there would claim more than the table allows. Branching and non-branching
steps are different theorems — a non-branching step says the extended branch
is satisfied, a branching one says AT LEAST ONE successor is, which is what
makes closure of every branch a proof.

So the soundness argument for the quantified calculus is complete IN ITS
PARTS, and now for the whole language rather than its quantifier fragment:
every rule carries satisfiability forward, closure denies it. THE SEARCH IS NOW
BUILT AND PROVED SOUND (`ZParamEngine.lean`, E48), on the layer E47 found
missing: nodes carry a TAG from a four-element inductive (`t f p n`) instead
of a function, a translation sends tags to signs, formulas have decidable
equality, and `closedB` decides closure — with `closedB_sound` proving that
what it calls closed is closed in the sense above, hence has no model. The
four tags are not four values: ZTL is two-valued with a mark, and a tag says
which VERDICTS a node admits (`n` = "not T": F, or the still unanswered Z);
P and N do not clash precisely because both admit the mark. The search runs
a fuel-bounded worklist: a closed branch is discharged, otherwise the first
node with a rule that adds something new is expanded and its successors
return to the list; running out of fuel claims nothing, as §6's
undecidability requires. It applies EXACTLY the rules proved sound on the
empty axiom list — the eight propositional steps, γ on T:∀ and F:∃, δ on
T:∃ — and F:∀, the rule that needs `¬∀ → ∃¬`, is deliberately absent. The
end-to-end theorems: `search_sound` (a run that closes every branch shows
no initial branch has a model, under any assignment, for a total
interpretation) and `entails_of_closed` (a closed run on Γ ⊢ φ, premises
tagged t and the conclusion n, proves that every total model making each
premise T makes φ T — constructively: the conclusion's value is PRODUCED by
totality and shown to be T, not obtained by refuting its negation). Three
runs are kernel-evaluated: ∀xP(x) ⊢ P(c) closes, P(c)∧Q(c) ⊢ Q(c) closes,
and ¬∀xP(x) ⊢ ∃x¬P(x) — the fallen bridge — returns `stuck`, not `closed`.
The fresh parameter is a theorem, not a side condition: it is a SUM of the
indices on the branch, and `freshFor_fresh` proves it occurs nowhere. E51,
the same day, gave the atoms any number of places (`atom : Nat → List Trm`,
with `trmVals_fresh` / `trmVals_inst` carrying the two load-bearing lemmas
over argument lists) and the two rules the first search lacked: in the
greedy register EVERY COMPOUND ANSWERS T OR F (`compound_two_valued` —
`evalF_classical` for the parameter language), so N on a compound is F and
P is T, and only atoms keep a weak sign; before that a compound conclusion
had no rule and `P(c) ⊢ P(c) ∨ Q(c)` was `stuck`. Three more runs close by
the kernel — `P(c) ⊢ P(c) ∨ Q(c)`, `∀x∀y R(x,y) ⊢ R(a,b)`, `∃x R(x,x) ⊢
∃x∃y R(x,y)` — and the VALID swap `∃x∀y R(x,y) ⊢ ∀y∃x R(x,y)` returns
`stuck` for the honest reason: its conclusion N:∀ promotes to F:∀, the one
rule this search does not have, because it is the classical one — the split
of `ZParamSound`, now visible in a whole run. Two repairs came from the
kernel runs and not from reading: γ's candidates are the parameters in play
(a bound growing with the branch made γ spawn instances forever), and δ
fires once (it re-fired with a fresh parameter every round). What remains of
the port: completeness, which §6 argues by Hintikka saturation and this
corpus does not measure;
**a fragment-embedding theorem for the remaining three traditions of
§1** — five are now done, and the entry is rewritten rather than deleted,
because what it asked for is larger than what has been delivered. The first
twin — IEEE 754's NaN, the first tradition of §1 — is embedded in `ZNaN.lean`
(E49, empty axiom list): the fragment as the standard states it (data, the
four mutually exclusive relations of §5.11, the predicates of Table 5.1, the
§6.2.3 propagation rule); their Boolean layer proved classical (`!=` is the
complement of `==` on every relation, the unordered one included); infection
proved to be the lazy register (`emb` is a homomorphism for `+` and `−`);
every ordered predicate proved to be `SignT` of a ZTL atom (`<=` and `>=` of
the GREEDY disjunction — `zor Z Z = F`, and IEEE's `<=` is false on a NaN too);
the unordered predicate proved to be `SignT (isZ …)` — quarantine detectable
from inside, §1, under IEEE's name; and `!=` proved to be `SignN` of the
equality atom and NOT the T-sign of the greedily negated one: off the mark
the two coincide, on the mark IEEE affirms `x != y` while ZTL's `¬(x = y)` is
`¬Z = F`. So the NaN signature "not equal to itself" is shared on `x == x` and
splits on its complement — one refusal and an affirmation against two
refusals (§18). The arithmetic boundary sits in the same file: `0 × NaN = NaN`
against the earned `0 · mark = 0` of §15, two `rfl`s. Not modelled: rounding,
signed zero, infinities, the signaling NaN — one algebraic core, not the
standard. Every `Int` order lemma measured carries propext, so both sides read
the order off one three-way comparison and no such lemma is used. The second
twin — SQL's NULL — is embedded in `ZNull.lean` (E50, empty axiom list): the
truth values TRUE/FALSE/UNKNOWN with the standard's three tables, the
comparison predicates, WHERE, CHECK and the <boolean test>. Proved: the
expression layer is a HOMOMORPHISM onto the lazy register `knot/kand/kor`,
cell for cell — and not onto the greedy one (`NOT NOT UNKNOWN` is UNKNOWN,
`¬¬Z` is T); the comparison with NULL is the SAME mark atom IEEE's `==`
landed on — two traditions, one ZTL atom; the boundaries are the four
signs — WHERE keeps iff `SignT`, CHECK passes iff `SignP` ("satisfied iff
not False": UNKNOWN passes), IS TRUE / IS FALSE / IS NOT TRUE / IS NOT FALSE
are `SignT / SignF / SignN / SignP`, IS UNKNOWN is the mark test `isZ`. So
SQL runs TWO boundaries with opposite defaults — `x < NULL` and `x >= NULL`
are both dropped by WHERE (§4's "false in both polarities") and both PASS a
CHECK — while ZTL's collapse is WHERE's alone: the mark falls to F, never to
T (`collapse_is_where`). At the WHERE boundary SQL and ZTL's greedy verdict
AGREE on every negation-normal search condition (`where_agrees_nnf`: the two
registers share their T-cells at every connective) and part exactly where a
negation stands over a compound — `¬¬Z`, the signature cell; at CHECK they
part already on `TRUE AND NULL`. And SQL's two equalities: `NULL = NULL` is
UNKNOWN while `NULL IS NOT DISTINCT FROM NULL` is TRUE (the rule DISTINCT
and GROUP BY run on) — ZTL has one equality and it withholds (§17's
"inconsistency not inherited", as `two_equalities`). Not modelled: tables,
joins, aggregates — the truth-value layer and its boundaries, not the
language. Fifth core; taint is the one worked case left. The
fifth twin went the same day: `ZDempster.lean` formalises Dempster–Shafer
as they define it (focal elements, Bel, Pl) and proves our verdict to be
their {0,1}-threshold in all three cells, for every finite frame and every
proper mass assignment — see §16, including the properness condition the
first draft got wrong. `ZProv.lean` (empty axiom list) formalises the ALGEBRA of
semiring provenance — the free commutative semiring on sources, `+`
for an alternative derivation, `·` for a joint requirement — and maps
it into ZTL: evaluation is a homomorphism into the LAZY register, which
satisfies every semiring law; withdrawal of a source never raises trust
along any derivation; a joint requirement dies with any one source
while an alternative survives; and on mark-free trust the two registers
coincide, so the Boolean case the 2007 paper starts from is recovered
exactly. The sharp half is negative and belongs to us: the GREEDY
operations carry no semiring structure at all — no constant whatever is
neutral for `zor`, none for `zand`, the obstruction being the mark
(`zor F Z = F`, `zand T Z = F`). So an algebra of trust in derivations
lives in the lazy register, and the verdict register is where it is
CASHED — cashing being provably not a homomorphism. That is why the two
registers had to be two. What is NOT formalised is their database
semantics: K-relations and the annotated relational operators. So one
tradition's algebraic core is mapped, not the tradition;
a practical zero-trust validation library (verdicts with warranties +
evidence combination + provenance); temporal operators over the
verification tree (□/◇/until against the grade semantics of §21) once
a concrete user forces them, and the grade automaton at scale; The interactive studio — natural
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
33. Martin, N. M. The Sheffer functions of 3-valued logic. *The
    Journal of Symbolic Logic* 19:1 (1954), 45–51.
34. Rosenberg, I. G. Über die funktionale Vollständigkeit in den
    mehrwertigen Logiken. *Rozpravy Československé Akad. Věd* 80
    (1970), 3–93 (the classification of maximal clones).
35. Finn, V. K. A criterion of functional completeness for B³.
    *Studia Logica* 33:2 (1974), 121–125 (abstract: *Bulletin of the
    Section of Logic* 2:1 (1973), 3–6). Remark 1 gives the seven
    pre-complete classes of the external class B³ₑₓ.
36. Łukasiewicz, J. *O logice trójwartościowej* (On three-valued
    logic). *Ruch Filozoficzny* 5 (1920), 170–171. English in: *Jan
    Łukasiewicz: Selected Works* (ed. L. Borkowski), North-Holland,
    1970. The first three-valued logic; its middle value "possible /
    not yet determined" is the meaning-ancestor of the mark Z, as
    Bochvar's external tables are of the {¬,∧,∨} fragment.
37. Suszko, R. The Fregean axiom and Polish mathematical logic in the
    1920s. *Studia Logica* 36 (1977), 377–380. Suszko's Thesis: every
    structural (Tarskian) logic is logically two-valued; the many values
    of a matrix are algebraic, the logical values only two (designated /
    undesignated). ZTL takes this as architecture — the mark is barred
    from the value of assertions by construction (greediness) — rather
    than recovering bivalence by the Suszko reduction after the fact.
38. Tomova, N. E. A lattice of implicative extensions of regular
    Kleene's logics. *Reports on Mathematical Logic* 47 (2012), 173–182;
    and *Estestvennye trekhznachnye logiki* [Natural three-valued
    logics], Moscow: IFRAN, 2012. The definition of a **natural
    implication** by four criteria (C-extension, Łukasiewicz–Tarski
    normality, the order condition p ≤ q ⇒ p→q designated, freedom
    elsewhere); see also Tomova, N. E. Natural implication and modus
    ponens principle. *Logical Investigations* 21 (2015), 138–143, where
    the normality criterion is weakened to the tautologousness-preserving
    form of modus ponens (a distinction due to Rescher, *Many-Valued
    Logic*, 1969, p. 70). ZTL meets criteria (1) and (2) and violates
    (3) in the single cell (Z, Z) — §4.

39. Łukasiewicz, J., Tarski, A. Investigations into the sentential
    calculus. In: J. Łukasiewicz, *Selected Works*, ed. L. Borkowski,
    Amsterdam & Warszawa: North-Holland & PWN, 1970, pp. 131–152. The
    normality of a logical matrix (p. 134): modus ponens preserves the
    designated value — criterion (2) of the natural-implication class.

40. de Kleer, J. An assumption-based TMS. *Artificial Intelligence*
    28:2 (1986), 127–162.

## Acknowledgements and AI disclosure

This work was carried out with the substantial participation of the AI
system Claude (Anthropic) in a dialogue setting: the system generated
the text, the test-bench code, and the Lean proofs. Across versions the
dialogue ran on two Claude models, and the attribution is kept honest:
Claude Opus 4.8 — the original corpus (v1.0) and the 2026-07-14/15
additions (the three-laws capstone §3.1, the Finn attribution and
reconciliation in §3.8, the paradox-engine synthesis opening §11, the
Łukasiewicz pedigree and the genetic order in §4); Claude Fable 5 —
the v1.1 same-day correction and the v1.2 assembly (the census of
sixteen and its Lean clone equalities, the fence-depth theorem, the
warranty ladder at scale, the naming of the lift, the temporal layer
§§21–23 with `ZTime.lean` and `EpochBoundary.lean`, the expiry and
derivation stands, and this PDF build); Claude Opus 5 — the receipt
results of §19 with `Receipt.lean`, `Linear.lean` and `LabelExact.lean`,
and the accompanying benches. All design
decisions, fork choices, hypotheses, and the final responsibility for
the content rest with the human author. In accordance with COPE/ICMJE
recommendations, the AI system is not listed as an author. The
reliability of the results does not depend on trusting the AI: every
numerical claim is checkable by the repository code (`run_all.py` —
full regression), and every Lean claim by the Lean 4 kernel (empty
axiom list, `#print axioms`).
