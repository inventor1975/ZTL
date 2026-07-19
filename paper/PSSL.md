# A Paradoxical, Self-Referential System of Logics

### Four non-classical logics as resolutions of one universal diagonal, with two machine-checked poles

**Vitaly Reznik**

*(v1.1 note: the publication text is `PSSL_EN_v1_1_0.tex` — it adds
Proposition C (the contextuality core, `lean/Contextuality.lean`: Mermin–Peres
0/512, GHZ 0/64, empty axiom list), the pair extension of the mirror
(the covering law falls in correlation form; the ladder of falls saturates),
and §7 "The world is not a corner (a reading)". This markdown mirrors v1.0.)*

---

**Abstract.** We propose a reading of four non-classical logics — classical, intuitionistic / type-theoretic, quantum (orthomodular), and Zero-Trust Logic (ZTL) — as four disciplined responses to a single self-referential construction: the universal diagonal underlying the liar, Russell, Cantor, Gödel and Tarski (Lawvere 1969; Yanofsky 2003). Each retains all classical structural principles *save one*, and each thereby houses the diagonal differently. Two features are invariant across all four: non-contradiction with its associated reductio (a retained *principle*), and the diagonal itself (a retained *obstruction*). We isolate the one part of this picture that is formal rather than expository — the complementary sacrifice made by ZTL and by orthomodular quantum logic — and record it as two propositions machine-checked in Lean 4 on the *empty axiom list* (no classical choice, no quotient, no propositional extensionality). We are explicit throughout about what is established (all four logics; the Lawvere–Yanofsky unification), what is the author's (ZTL; the arrangement; the two witnesses), and what is analogy carrying no proof (the "cycle" itself). This is a synthesis and a reading, not a theorem, a merger, a new foundation, or a new field.

**Keywords.** self-reference; Lawvere fixed point; diagonal argument; quantum logic; orthomodular lattice; three-valued logic; paracomplete logic; Zero-Trust Logic; universal logic; Lean 4; machine-checked proof.

**MSC 2020.** 03B50 (many-valued logic); 03B60 (nonclassical logic); 03G12 (quantum logic); 18C50 (categorical logic, diagonal arguments); 03B35 (mechanization).

---

## 0. Scope

The claim of this note is deliberately narrow. It is *not* that a new logic or a new foundation has been discovered, nor that the four logics below are amalgamated into one calculus — they are provably incompatible in the precise sense of §4. The unification of the classical antinomies under a single fixed-point schema is due to Lawvere (1969) and, in the concrete Set-theoretic form used here, to Yanofsky (2003); quantum logic is Birkhoff–von Neumann (1936); the intuitionistic corner is standard; the "general theory of logical systems" already exists as a field (universal logic, abstract model theory). The single component original to the author is **ZTL** [12], which appears here only as one corner. What this note adds is (i) the *arrangement* of the four as four resolutions of one diagonal, and (ii) two machine-checked propositions (§5) exhibiting the sharpest pair of them as complementary. Everything expository is marked as such; everything proved is in §5 and reproducible from zero.

## 1. The universal diagonal

The classical antinomies are one construction in several presentations. Lawvere's fixed-point theorem makes this exact.

> **Lemma (Lawvere 1969).** In a cartesian closed category, if there is a point-surjective morphism `φ : A → Y^A`, then every endomorphism `g : Y → Y` has a fixed point `y : 1 → Y` with `g ∘ y = y`.

Contrapositively: a **fixed-point-free** endomorphism of `Y` obstructs any point-surjection `A → Y^A`. Instantiating `Y` and `g`:

- `Y = 2`, `g = ¬` (no fixed point): no surjection `A → 2^A` — **Cantor**;
- the same schema, read in an internal truth object with a fixed-point-free negation, yields the **liar** and **Russell**;
- read in a provability/representation setting it yields **Gödel** and **Tarski's** undefinability (Yanofsky 2003, §§3–5).

The common core is *self-application against a fixed-point-free map*: an object that names its own maps, composed with a `g` that has no fixed point. Following Yanofsky, we call this schema **the diagonal**. It is *pre-classical*: it is not built by classical logic but is a construction that any logic expressive enough to talk about its own sentences must confront. A logic that ignores it does not escape it; it trivializes on it.

## 2. Four resolutions

A logic admitting self-reference must do something disciplined with the diagonal or collapse. There are (at least) four such disciplines in current use, and each is *classical logic minus exactly one structural principle*:

| Logic | Principle dropped | Resolution of the diagonal |
|---|---|---|
| **Classical** | none | explodes on the raw liar, then localizes truth one level up (**Tarski hierarchy**) |
| **Intuitionistic / type-theoretic** | excluded middle; unrestricted `Type : Type` | bans self-typing — the **universe hierarchy**; Girard's paradox is the diagonal of naïve type theory (Coquand; Hurkens 1995) |
| **Quantum (orthomodular)** | distributivity | the self-negating join lives as a genuine element; complementation stays total |
| **ZTL** | identity `p→p`, excluded middle, double negation | **pointwise quarantine**: the liar has no fixed value; it is flagged, not exploded [12] |

Two honesty points. First, only the ZTL row is the author's; the other three are the standard content of their fields, curated here, not discovered. Second, the classical row is the informative one: classical logic retains *every* structural principle, which is exactly why it is the system that must *explode* on the unlocalized liar and repair itself from the metalanguage. Retaining everything is paid for in the hierarchy.

## 3. Two invariants

Across the four, two things do not move — a dual pair, one positive and one negative.

**The floor (a retained principle).** Non-contradiction and the reductio it licenses, `(p → ¬p) → ¬p`, survive in every corner. In the quantum lattice `x ∧ x^⊥ = 0`; in the ZTL matrix `¬(p ∧ ¬p)` is designated for every value; both are among the propositions of §5.

**The ceiling (a retained obstruction).** The diagonal survives in every corner, precisely because each logic is expressive enough to state it. What differs is only the *manner of housing* it (§2).

The two are linked: **non-contradiction is the guard against the diagonal.** A logic that surrendered non-contradiction would not tame the diagonal but be trivialized by it (ex contradictione quodlibet). Where the obstruction persists, the floor stands; that is why both are invariant.

## 4. No consistent amalgamation

Why an irreducible plurality rather than a hierarchy or a common refinement?

Because the retained principles are *pairwise incompatible*. Quantum logic retains `x ∨ x^⊥ = 1`; ZTL withholds `p ∨ ¬p` at the mark — no single valuation structure validates both a total complementation law and its pointwise failure. Type theory demands strong normalization (every term terminates); the ZTL solver houses non-termination as the transient phase `N` (§5). Any system retaining *all four* families of principles at once would validate distributivity *and* its negation, hence be trivial — that system is classical logic, which pays for retaining everything with the raw diagonal it must then hierarchically contain. There is therefore no consistent common refinement; the four are genuinely incomparable.

We describe this informally as an *orbit* around classical logic — the unreachable centre that keeps all principles at the price of the liar. We stress that "orbit", "centre" and "cycle" are metaphor: the content is the pairwise incompatibility above and the concrete complementarity of §5. No claim of a formal cyclic structure is made.

## 5. The ZTL–quantum mirror, machine-checked

The one formalizable part of the picture is the *complementary sacrifice* made by ZTL and by orthomodular logic. Both are recorded below as propositions verified in Lean 4 over finite carriers by `decide`, on the **empty axiom list**, in bare Lean (no `mathlib`, no imports).

**Pole A (ZTL).** Let `M = {T, F, Z}`, with connectives generated by the *zero-trust lift*: for a Boolean `f`, `lift(f)(x⃗) = T` iff `f` returns `true` under every classical reading of the arguments (`Z` read as both `true` and `false`), else `F`. Then in `M`:

> **Proposition A** (`lean/ZTL.lean`, empty axiom list).
> (i) *non-contradiction* — `¬(p ∧ ¬p) = T` for all `p`;
> (ii) *distributivity in both directions* — `p ∧ (q ∨ r) = (p∧q) ∨ (p∧r)` and dually, for all `p,q,r`;
> (iii) *failure of identity, excluded middle and double negation* — `p → p`, `p ∨ ¬p`, `¬¬p → p` are not designated for all `p` (each is falsified at `p = Z`).

Here the third symbol `Z` is a **status mark, not a truth value**: verdicts are two-valued, `Z` marking an unverified input (greedy register) or, reused positionally in the solver, the transient phase `N = "not yet"` (Kleene's undefined), which never labels an input. ZTL is thus **paracomplete** (truth-value gaps, no gluts), not paraconsistent [12].

**Pole B (orthomodular).** Let `MO2` be the smallest non-distributive orthomodular lattice: `{0, 1}` together with two complementary pairs `(a, a^⊥), (b, b^⊥)`, all four proper elements mutually incomparable, with `x ∧ x^⊥ = 0`, `x ∨ x^⊥ = 1`. Then:

> **Proposition B** (`lean/QuantumWitness.lean`, empty axiom list).
> (i) *non-contradiction* — `x ∧ x^⊥ = 0` for all `x`;
> (ii) *excluded middle and double negation* — `x ∨ x^⊥ = 1` and `x^{⊥⊥} = x` for all `x`;
> (iii) *failure of distributivity* — `a ∧ (b ∨ b^⊥) = a ∧ 1 = a`, whereas `(a∧b) ∨ (a∧b^⊥) = 0 ∨ 0 = 0`.

**The mirror.** ZTL retains distributivity and surrenders excluded middle, double negation and identity; orthomodular logic retains excluded middle and double negation and surrenders distributivity; both retain non-contradiction. Informally: ZTL fails where a proposition meets *itself*; quantum logic fails where propositions *combine*.

**A required caveat (the honest mark).** The two "retentions of excluded middle" are not instances of one theorem in one system. In `MO2`, `x ∨ x^⊥ = 1` is a *lattice identity* and `x^{⊥⊥}=x` holds because the orthocomplement is involutive *by the choice of an ortholattice* — mild, structural. In `M`, the *failure* of `p ∨ ¬p` is a computation in a *logical matrix*, where validity means designation. These are facts in two different formalisms that rhyme; the "mirror" is an analogy made precise on each side, not a single cross-formalism theorem. This is the boundary between what is proved (each proposition) and what is read (their pairing).

**Reproduction** (Lean 4.29.1, measured 2026-07-18):

```
$ lean lean/ZTL.lean             # 13 objects: "does not depend on any axioms",  ~1.1 s
$ lean lean/QuantumWitness.lean  #  5 objects: "does not depend on any axioms",  ~0.5 s
```

Every `#print axioms` line reports *"does not depend on any axioms"*, definitions included: no `Classical.choice`, no `Quot.sound`, no `propext`. The intuitionistic and classical corners are, by contrast, *metatheorems* (underivability of excluded middle; failure of strong normalization for `Type : Type`; "classical as centre") and are not formalized here by design; the diagonal itself, ranging over four logics that are not objects of one theory, is likewise not a single formal object.

## 6. Provenance

| | Content | Status |
|---|---|---|
| **Established** | Lawvere's fixed-point theorem and the diagonal unification (Lawvere 1969; Yanofsky 2003); quantum logic and non-distributivity (Birkhoff–von Neumann 1936); intuitionism, the universe hierarchy, Girard's paradox (Martin-Löf; Coquand; Hurkens 1995); universal logic as a field (Béziau) | literature |
| **Author's** | ZTL, the zero-trust paracomplete logic [12]; the arrangement of the four as resolutions of one diagonal; the two Lean witnesses on the empty axiom list | synthesis + machine-checked |
| **Analogy (no proof)** | the "cycle / orbit / centre"; "the floor guards the ceiling"; "each logic pays one principle so none pays the whole diagonal" | structural metaphor, marked |

The defensible claim is narrow: four established non-classical logics align as four disciplined resolutions of one pre-classical diagonal, and the sharpest pair among them — ZTL and orthomodular logic — make complementary, machine-checkable sacrifices. The organizing picture is offered as a reading; its two poles are offered as proof.

---

## References

[1] G. Birkhoff, J. von Neumann. *The logic of quantum mechanics.* Ann. of Math. **37** (1936), 823–843.

[2] D. A. Bochvar. *On a three-valued logical calculus and its application to the analysis of the paradoxes of the classical extended functional calculus.* Mat. Sbornik **4** (1938); Eng. transl. Hist. Philos. Logic **2** (1981), 87–112.

[3] T. Coquand. *An analysis of Girard's paradox.* LICS 1986, 227–236.

[4] A. G. Hurkens. *A simplification of Girard's paradox.* TLCA 1995, LNCS 902, 266–278.

[5] S. C. Kleene. *Introduction to Metamathematics.* North-Holland, 1952 (strong three-valued connectives).

[6] S. Kripke. *Outline of a theory of truth.* J. Philos. **72** (1975), 690–716.

[7] F. W. Lawvere. *Diagonal arguments and cartesian closed categories.* In: Category Theory, Homology Theory and their Applications II, LNM 92, Springer, 1969, 134–145.

[8] J. Łukasiewicz. *On three-valued logic* (1920). In: Selected Works, North-Holland, 1970.

[9] P. Martin-Löf. *Intuitionistic Type Theory.* Bibliopolis, 1984.

[10] L. de Moura, S. Ullrich. *The Lean 4 theorem prover and programming language.* CADE 2021, LNCS 12699, 625–635.

[11] N. S. Yanofsky. *A universal approach to self-referential paradoxes, incompleteness and fixed points.* Bull. Symbolic Logic **9** (2003), 362–386.

[12] V. Reznik. *ZTL — Zero-Trust Logic.* Preprint, DOI 10.5281/zenodo.21318981 (concept).

[13] J.-Y. Béziau (ed.). *Universal Logic: An Anthology.* Birkhäuser, 2012.

---

*AI disclosure.* This note was written in dialogue with the AI system Claude (Anthropic); all design decisions, the framing and final responsibility are the human author's. The reliability of §5 depends on neither the author nor the AI: both Lean files verify against the Lean 4 kernel on the empty axiom list. Everything outside §5 is offered as a reading and marked as such.

*License.* Text CC BY 4.0; the accompanying Lean files are MIT-licensed (repository `ZTL`).
