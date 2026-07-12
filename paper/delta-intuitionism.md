# ZTL versus intuitionism: the honest delta

**VR Part II, step 1.** Companion note to *ZTL — Zero-Trust Logic*
(Zenodo, DOI 10.5281/zenodo.21318982). Every verdict below marked
MEASURED is produced by the stand `zipc.py` in the repository and
re-checked on every regression run.

## 1. Why this comparison is owed

ZTL's slogan — *truth is never granted on credit* — could be read as
Brouwer's. Intuitionism is the oldest and most respected logic that
refuses free classical truth; any newcomer with that slogan owes the
reader an explicit answer to "is this not just intuitionism,
rediscovered?" The debt is doubled in our case: the VR programme, whose
logic ZTL claims to be, built its continuum on Brouwer's side of the
street (choice sequences, apartness, potentialist infinity). If VR is
to be raised onto ZTL, the first thing to establish is that ZTL is not
IPC wearing a new coat — otherwise "VR Part II" would be a relabeling,
not a step.

The answer, measured: **it is not a coat. The two logics are
incomparable as sets of laws, agree exactly on a battery of premised
classical rules, and part ways on every structural signature that
defines intuitionism** — finite matrices, the disjunction property,
the behaviour of double negation, and the meaning of an unproved
sentence. Same slogan, different creditors: intuitionism refuses truth
without a *construction*; ZTL refuses truth without *certified input*.
Proof-debt versus data-debt.

## 2. Instruments

* **IPC side:** a real decision procedure — Dyckhoff's
  contraction-free sequent calculus **G4ip** (JSL 1992), sound and
  complete for intuitionistic propositional logic, so "IPC ✗" below
  means *non-theorem*, not "no proof found within a budget". The
  prover is calibrated against the canonical statuses of all 27
  battery laws (Troelstra–van Dalen; Gödel 1932); any disagreement
  turns the stand red. As an independent workout it also proves
  Glivenko's ¬¬-translation of all 27 classically valid laws (§7).
* **ZTL side:** the native entailment ⊨ of the keel (designated {T}),
  and the tableau-certified calculus behind it (preprint §5, Lean:
  zero axioms).
* **Shared language (honest scope):** {¬, ∧, ∨, →}, with ↔ read
  intuitionistically as (A→B)∧(B→A). ZTL's primitive ⊕ has no
  canonical intuitionistic reading and is left out of the comparison.

## 3. Laws: incomparable, both inside classical logic (MEASURED)

27 canonical laws, three judges (CPC / IPC / ZTL). Every law on the
battery is classically valid; each of IPC and ZTL keeps a strict
subset; the two subsets are incomparable:

**IPC-valid but ZTL-refused — 6 witnesses:**

| law | ZTL counterexample |
|---|---|
| identity p→p | p=Z |
| K q→(p→q) | p=T, q=Z |
| De Morgan ¬(p∨q)→(¬p∧¬q) | p=F, q=Z |
| ¬¬(p∨¬p) | p=Z |
| currying ((p∧q)→r)→(p→(q→r)) | p=T, q=Z, r=F |
| idempotence p→p∧p | p=Z |

**ZTL-valid but IPC-refused — 1 witness on the battery:**
the weak law of excluded middle **¬p∨¬¬p** (Jankov's axiom; the
axiom of the intermediate logic KC). ZTL earns it because ¬ evaporates
Z (¬Z=F, ¬¬Z=T: one disjunct is always classically true); IPC refuses
it because neither disjunct comes with a construction.

Three consequences worth stating plainly:

1. **ZTL is not an intermediate (superintuitionistic) logic.**
   Intermediate logics live between IPC and CPC; every one of them
   proves p→p. ZTL refuses p→p (an unverified input does not certify
   itself), so ZTL is not above IPC at all — it sits *beside* it,
   inside CPC. The tabular kin of ZTL remain the Bochvar family
   (preprint §4), not the Heyting family: the three-valued logics that
   *are* intermediate (Gödel's G3, Dummett's LC₃) all validate
   identity.
2. **Both directions of non-inclusion are witnessed**, so the
   incomparability is an existential fact, immune to battery choice.
3. A nuance the preprint's price list makes easy to misread:
   **contraposition survives as a law-formula** — ⊨ (p→q)→(¬q→¬p)
   (MEASURED) — while contraposition as a *table identity*
   (p→q ≡ ¬q→¬p pointwise) fell (preprint §3.5). These are different
   claims; the incompatibility mini-theorem concerns the identity, not
   the implication.

## 4. Rules: exact agreement on the premised battery (MEASURED)

The keel's 14 classical premised inferences, judged as Γ ⊢ φ by G4ip
and Γ ⊨ φ by ZTL: **verdicts coincide 14 of 14** — including both
casualties. The two rules that fall in ZTL are exactly the two that
fall in IPC:

* **¬¬-elimination** ¬¬p ⊬ p. IPC: a proof of ¬¬p carries no
  construction of p. ZTL: the premise launders the mark — ¬¬Z = T, so
  the premise is true while p itself is still unverified.
* **tautology-in-conclusion** p ⊬ q∨¬q. IPC: q∨¬q is not a theorem.
  ZTL: premises about p earn nothing for the fresh atom q.

The diagnoses differ; the casualty list is the same. The shared
denominator is relevance of certification: *the conclusion's
certificate must come from somewhere* — either a construction (IPC) or
a verified input (ZTL); both systems refuse inference moves that mint
a certificate out of nothing.

**Do not overclaim this agreement.** As full consequence relations the
two differ already at empty Γ: ∅ ⊢ p→p in IPC, ∅ ⊭ p→p in ZTL (§3).
The coincidence is battery-relative and premised; it is a resonance,
not an identity.

## 5. The three structural chasms

These are not battery facts; they are architecture.

1. **Verdicts are two-valued; Z is not a truth value.** IPC's
   "values" are proof-contents — potentially infinitely many, ordered
   by construction. ZTL asks a Boolean question — *is T forced under
   every classical reading of the unverified input?* — and therefore
   legitimately lives in a 3-cell table where the third cell is an
   input mark, not a value (preprint §10). This is why ZTL can be
   tabular at all.
2. **Tabularity.** Gödel (1932): IPC has no finite characteristic
   matrix. ZTL is a finite matrix by construction. So no finite-valued
   logic — ZTL included — can *be* intuitionistic logic; conversely,
   intuitionism can never enjoy ZTL's decidability-by-table. This is a
   theorem-level separation, independent of any battery.
3. **Refusal is an answer with a passport.** In ZTL the solver
   provably terminates (lazy grounding stabilizes in ≤ n+1 steps —
   Lean, zero axioms), and an unresolved sentence receives a *final*
   verdict-with-genesis: PARADOX / UNDERDETERMINED / INTRINSIC / INPUT
   / DOWNSTREAM (preprint §9). In intuitionism an unproved sentence is
   an *open potentiality* — no verdict, no passport, openness forever.
   (Revision theory is a third posture: the process itself is eternal.
   ZTL: the process ends, the refusal is eternal. Intuitionism: the
   question stays open. Gupta–Belnap: the answer keeps changing.)

## 6. The disjunction property: ZTL is not BHK (MEASURED)

IPC has the disjunction property — ⊢ A∨B forces ⊢ A or ⊢ B (Gödel) —
the formal shadow of BHK: a proof of a disjunction contains a decided
disjunct. ZTL **loses** it, and the loss is measured, not argued:
⊨ ¬p∨¬¬p while ⊭ ¬p and ⊭ ¬¬p; a census over all ∨-pairs of the
one-atom depth-2 pool finds 924 such disjunctions (simplest:
p ∨ ¬(p∧p)). ZTL's ∨ earns T when every classical reading forces it,
not when a disjunct is certified — a supervaluational, not a BHK,
disjunction.

The honest counterpoint: ZTL's witness discipline lives one floor up.
The existential quantifier demands a strict T-witness (∃ = a
certified instance; `quantifiers.py`, preprint §6), and apartness on
streams is earned by an explicit finite index (E6). ZTL is not a BHK
logic of connectives; its constructivity is concentrated in the solver
and the quantifiers, where certificates are physical.

## 7. Double negation: transparent versus load-bearing (MEASURED)

In ZTL, ¬¬ changes no verdict: ⊨ A ⟺ ⊨ ¬¬A, checked totally on a
786-formula pool (0 mismatches). In IPC, ¬¬ is the load-bearing wall:
Glivenko (1929) — CPC ⊢ A iff IPC ⊢ ¬¬A — verified here by G4ip on
all 27 classically valid battery laws (27/27, including ¬¬Peirce).

The embeddings therefore run in opposite directions. IPC is "bigger
inside": it contains all of classical logic as its ¬¬-fragment. ZTL is
"smaller inside": it is a sublogic of CPC whose verdict algebra is
already classical, with no hidden classical shadow to unfold. A critic
who wants ZTL to "recover classical reasoning" does it by
verification of inputs (Z→T/F, preprint §19), not by a translation.

## 8. Persistence: what Kripke bakes in, ZTL sells separately

Kripke semantics for IPC is built on heredity: truth, once earned,
persists along all future information states. ZTL's greedy verdicts
violate heredity by design — a verdict can die under further
verification (the Frege cell, E12) — and ZTL buys persistence back as
an explicit *warranty bit* (stability = global supervaluation; the
90/90 theorem: stable ⟺ invariant under all verifications). The
intuitionism-resonant half of ZTL is the lazy register: Kleene
grounding is monotone and stabilizes (Knaster–Tarski, Lean-checked) —
that is where "growth of knowledge" lives. In short: intuitionism
fuses information-growth and truth into one semantics; ZTL splits them
into two registers and prices the fusion (verdict = pair (value,
warranty)).

## 9. What VR Part II carries across this delta

The delta tells us exactly which planks may be carried from the
Brouwerian shore onto the ZTL deck, and which must not:

* **Witnessed identity → earned T.** VR-Sets' identity-by-witnessed-
  bisimulation is verbatim "T is earned by a certificate" — it lands
  on ZTL's R3 atoms without translation.
* **Apartness/equality asymmetry.** Constructive analysis: apartness
  is positive, equality is its negation. ZTL, measured (E6): apartness
  of streams is *earnable* at a finite stage and persists; stream
  equality is never-T (Z-permanent). The VR continuum's apartness
  discipline transfers as a theorem about earnability, not as a
  borrowed axiom.
* **Choice sequences → the lazy register** (step б of the programme).
  Brouwer's distinction between a sequence-in-growth and what is
  assertable at a stage maps onto lazy/greedy: the lazy register is
  the growing object, the greedy register is the stage-assertion. The
  two-register theorem (quarantine architecture) is the formal home
  the distinction never had in a tabular setting.
* **Potentialism.** Yablo's paradox lives only on actual infinity
  (E-expeditions: every finite truncation grounds) — rhyming with VR's
  potentialist infinity. This plank carries.
* **What must NOT be carried:** BHK disjunction (ZTL provably lacks
  DP), truth-as-provability (verdicts are bivalent), and any hope of
  Kripke heredity for free (it is a purchasable warranty, not a
  semantic axiom).

## 10. Verdict

ZTL is a third posture in the foundations landscape, not a variant of
the second:

* not classical — 15 of 27 classical laws fall (the price list was
  paid knowingly);
* not intuitionistic — incomparable law-sets (both directions
  witnessed), tabular where IPC provably cannot be, no disjunction
  property, verdict-transparent ¬¬, bivalent verdicts, and refusal as
  a terminating answer with a passport rather than an eternal
  openness;
* yet rule-resonant with intuitionism exactly where certification
  matters: on the premised classical battery the two logics accept
  and refuse the same inferences, 14 of 14.

Brouwer built mathematics and Heyting wrote out its logic. VR was
built first, and ZTL is its logic written out — and the delta measured
here says the second pair is not a photocopy of the first.

## Honest caveats

* The comparison lives on the {¬,∧,∨,→,(↔)} fragment; ⊕ is out of
  scope by declared translation policy.
* "IPC ✗" is a completeness-backed non-theorem (G4ip is a decision
  procedure), not a failed search.
* The 14/14 rule agreement is battery-relative (the keel's classical
  battery); the full consequence relations differ at empty Γ.
* Law incomparability is existential (witnesses) and hence robust;
  the *counts* (6 vs 1, 15 of 27) are battery-relative and carry no
  weight beyond illustration.
* Structural claims cited, not re-proved here: Gödel 1932 (no finite
  matrix), Gödel/Kleene DP for IPC, Glivenko 1929 (verified on the
  battery as a prover workout, which is a check, not a proof).

## References

1. L. E. J. Brouwer, *Over de grondslagen der wiskunde*, 1907.
2. A. Heyting, *Die formalen Regeln der intuitionistischen Logik*,
   1930.
3. V. Glivenko, *Sur quelques points de la logique de M. Brouwer*,
   Bull. Acad. Sci. Belgique 15, 1929.
4. K. Gödel, *Zum intuitionistischen Aussagenkalkül*, Anzeiger Akad.
   Wiss. Wien 69, 1932.
5. R. Dyckhoff, *Contraction-free sequent calculi for intuitionistic
   logic*, J. Symbolic Logic 57(3), 1992.
6. S. A. Kripke, *Semantical analysis of intuitionistic logic I*,
   1965.
7. A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*,
   North-Holland, 1988.
8. M. Dummett, *A propositional calculus with denumerable matrix*,
   J. Symbolic Logic 24, 1959.
9. V. A. Jankov, *The calculus of the weak "law of excluded middle"*,
   Math. USSR Izvestija 2, 1968.
10. A. Chagrov, M. Zakharyaschev, *Modal Logic*, Oxford UP, 1997
    (intermediate logics).
11. A. Gupta, N. Belnap, *The Revision Theory of Truth*, MIT Press,
    1993.
12. *ZTL — Zero-Trust Logic*, Zenodo, DOI 10.5281/zenodo.21318982
    (the system, the price list, the passport).

## Acknowledgements and AI disclosure

This note was prepared with the substantial participation of the AI
system Claude (Anthropic) in a dialogue setting, under the direction
of the human author, who owns all design decisions and the final
responsibility for the content. The AI system is not an author
(COPE/ICMJE). The reliability of the results does not depend on
trusting the AI: every MEASURED claim is reproduced by `zipc.py` in
the repository on every regression run.
