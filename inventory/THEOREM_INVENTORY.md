# ZTL — theorem inventory

Every claim the ZTL corpus makes, with the evidence that backs it and
nothing stronger. Required by the Research Gravity Program §4.8; written
so that a referee can check any single row without reading the
repository history.

**State: 2026-07-20.** Corpus at preprint v1.2 (DOI
[10.5281/zenodo.21440066](https://doi.org/10.5281/zenodo.21440066)).
Reproduced on a clean build the same day.

Reproduce the two mechanical tiers:

```
cd lean && lake build              # 35 jobs, green
python3 inventory/axiom_audit.py   # 338 theorems, empty axiom list
python3 run_all.py                 # 40 stands + Lean, ALL GREEN
```

---

## The four tiers

Nothing in this repository is called "proved" unless it sits in tier A.
The tiers are ordered by what would have to be wrong for the claim to
fail.

| tier | name | what it means | what it does NOT mean |
|---|---|---|---|
| **A** | machine-proved | a Lean 4 kernel proof, `#print axioms` empty | — |
| **B** | totally measured | exhaustive over a space that is *complete for the claim* (e.g. all 3ⁿ assignments of a fixed formula) | — |
| **C** | measured on a bounded pool | exhaustive over a *stated finite fragment* (e.g. all depth-≤2 formulas over two atoms) | that it holds for all formulas |
| **D** | argued in prose | reasoning, positioning, literature comparison | that any machine checked it |

The distinction between **B** and **C** is the one a referee will hunt
for, so it is drawn explicitly in every row. "Exhaustive" alone is not a
tier: exhaustive *over what* is the whole question.

---

## Tier A — machine-proved (338 theorems, empty axiom list)

Lean 4.29.1, no mathlib, no imports outside the corpus. Measured
2026-07-20 by `inventory/axiom_audit.py`: **338 of 338 theorems return
"does not depend on any axioms"** — not the 125 hand-placed prints, but
every theorem in every module, generated and checked.

| module | thms | what it establishes |
|---|---:|---|
| `ZTL.lean` | 78 | the core: lift-generated connectives, anchor cells as theorems, 12 alive + 14 fallen laws, semantic MP, greediness, liar homelessness (∀v, ¬v ≠ v), `no_gluts`, the lazy Kleene register with monotonicity, the 12 tableau `cover_*` preimage theorems |
| `TableauCert.lean` | 35 | `closes_iff` — tableau soundness **and** completeness; `tproves_iff` — the entailment certificate |
| `ZClone.lean` | 34 | single-operator completeness: the census of sixteen, clone equalities, reachability and non-reachability results |
| `ZGround.lean` | 25 | Knaster–Tarski over the whole language: monotonicity, least fixed point by bounded iteration, absoluteness of the grounded part |
| `ZAlgebra.lean` | 25 | the algebraic passport: J-indicators, unary expressive completeness, `ddt_E` (full deduction theorem for E), all Blok–Pigozzi witnesses, failure of self-extensionality, structurality of ⊨ |
| `ZQuant.lean` | 19 | finite-domain quantifiers as strict folds, n-ary signed rules as coverage theorems, UI alive / EG fallen in membership form |
| `ZSets.lean` | 17 | marked sets: a mark earns membership nowhere, {Z,Z} ≠ {Z}, a marked set not provably a subset of itself |
| `Facts.lean` | 17 | domain-2 quantifier battery and the dynamics zoo (liar period 2, carousel period 4, Curry, Yablo-3, the crocodile) |
| `ZExped.lean` | 16 | streams and apartness, Cantor diagonal, injectivity collapse under one mark, □/◇ thresholds, Russell's grounding half |
| `TableauCertN.lean` | 12 | the native engine: `closesN_iff`, `tprovesN_iff`, and `engines_agree` |
| `EpochBoundary.lean` | 11 | `epoch_boundary_iff` (epoch-blind ⟺ constant over all markings) and `epochs_matter` |
| `JunctionWitness.lean` | 9 | the junction: a true pair whose every local disjunct fails |
| `ZTime.lean` | 8 | logical time: `hereditary_absorbing`, `grounded_hereditary`, `hereditary_sound`, `strict_ladder` |
| `ZSequent.lean` | 7 | `cut_admissible`, admissible weakening, derivable identity |
| `Frame.lean` | 17 | the §3.5 mini-theorems: contraposition dies at two named cells, the quarantine flag is outside the value layer, and the atom-collapse is classical term by term (Bochvar's B3□ fork) |
| `QuantumWitness.lean` | 5 | MO2: distributivity fails while LEM, DNE and non-contradiction hold — the quantum pole |
| `Contextuality.lean` | 3 | Mermin square and GHZ admit no valuation; the parity core |

**Boundary of tier A, stated once.** These theorems are about the
*formal system*. They establish nothing about the world, about whether a
natural-language sentence was encoded correctly, or about whether the
grounds fed to the kernel are true. That boundary is the subject of
Deliverable Two, not a gap in the proofs.

---

## Tier B — totally measured

Claims where the swept space is complete for the claim itself. A law over
a fixed formula has finitely many assignments; sweeping them all settles
it, and nothing about "all formulas" is being asserted.

| claim | stand | measurement |
|---|---|---|
| 12 laws alive, 14 fallen | `audit.py` | every assignment of each law |
| 12 entailment rules alive, 2 fallen | `entailment.py` | every assignment |
| ZTL is algebraizable; DDT two-way total | `zalgebra.py` | 512 of 512 external tables |
| Craig interpolation holds | `zinterp.py` | total on the stated pool |
| cut is admissible (semantic elimination) | `zsequent.py` | total |
| stipulation theorem; parity cross-check | `zpassport.py` | 62 of 62 |
| two engines agree | `bridge.py` | 141 kernel-computed answers, 0 divergences |
| Mermin–Peres 0/512, GHZ 0/64 | `dilemmas/quantum_ladder.py` | every valuation |
| ZTL ⊥ IPC: rule verdicts coincide 14/14 | `zipc.py` | every rule in the battery |
| hereditary never revoked | `zverify.py` | 0 revocations, invariant under every single verification |

---

## Tier C — measured on a bounded pool

**Exhaustive within a stated bound, and no further.** Every row here is a
census, not a theorem. Where a claim of this tier appears in the preprint
it must carry its bound in the same sentence.

| claim | stand | the bound — this is the ceiling |
|---|---|---|
| grade automaton: hereditary absorbing, 0 violations | `ztime.py` | all depth-≤2 formulas over 2 atoms — 2,906 formulas, 29,812 ticks |
| 130/130 traces end hereditary | `ztime.py` | curated pool, not a sweep |
| contentful survivors of unrestricted expiry: 0 | `zexpire.py` | the same 2,906-formula census |
| from ∅ nothing derivable even with loans; 6 guarded tautologies | `zderive.py` | forward chaining over a 153-formula pool on p,q,r |
| containment sweep, 0 violations | `pengine.py` | all 9,015 one-sentence nets of ≤6 symbols |
| ¬¬-transparency; the ZTL/IPC census | `zipc.py` | generated pool, depth 2 over p,q |
| the quasivariety is subdirectly irreducible | `zquasi.py` | the stated finite signature |

**The known gap, named.** `ztime.py`'s pool is depth ≤2. The conjecture
"sound is a birth grade" survived one hour in July 2026 precisely because
that pool cannot see the depth-3 shape that refutes it (the E21 cell).
A depth-≤2 census is evidence about depth-≤2 formulas. Nothing in this
tier should be written up as if it were tier A or B.

---

## Tier D — argued in prose

The honest residue: real claims of the preprint with no mechanical
backing. They are not weaker for being here — several are metatheoretic
and cannot be formalised inside the system — but none may be presented
as verified.

| claim | where | why it is prose, and what would upgrade it |
|---|---|---|
| the {¬,∧,∨} fragment coincides cell-by-cell with Bochvar's external layer | §4 | the coincidence itself is measured (`finn_reconcile.py`); the **historical** claim — found after the tables were generated, not taken from Bochvar — is testimony about our process. Unfalsifiable from outside; keep it as a dated statement of provenance, never as evidence of independence. |
| the six engineering traditions (NaN, SQL NULL, taint, abstract interpretation, imprecise probability, provenance semirings) **implement fragments of one logic** | §1, Abstract | each of the six is exhibited on a worked case with a stand — NaN and intervals `zarith.py`, NULL `zsets.py`/`zfuncs.py`, taint `zfuncs.py`/`zprob.py`, Dempster–Shafer `zprob.py`, provenance semirings `zcombine.py`. So the correspondences are demonstrated, not asserted. But **a worked instance is not an embedding**: no stand formalises a tradition's own semantics and proves a fragment map into ZTL. The evidence is "here is that tradition's central move, reproduced by our core", which is tier C by construction. **Upgrade path:** pick one — provenance semirings is the most tractable — define its semantics and prove the embedding. One such theorem would carry the whole §1 claim. |
| ZTL sits outside the Rosser–Turquette standardness conditions | §4 | argued against the definitions, not machine-checked |
| relative consistency / the position among three-valued logics | §4 | metatheory, cited to the literature |
| ~~the three §3.5 mini-theorems~~ | §3.5 | **PROMOTED to tier A on 2026-07-20** — `lean/Frame.lean`, 17 theorems, empty axiom list. Left in this table as a record of what tier D looked like before it was cleared. |
| R1–R3, the cross-cutting regularities | §24 | generalisations over the applied chapters; each instance is measured, the *pattern* is prose |
| the two-register architecture is **necessary** | §9, §24 | every *component* is tier A — lazy monotonicity (`evalK_mono`, `jumpL_mono`), the least fixed point (`kt_fixed`, `kt_least`), well-definedness of quarantine (`grounded_absolute`), greedy non-monotonicity (`eager_and_not_monotone`) — but **no Lean object states the necessity itself**. The conclusion is a composition of theorems by argument. §9's "the necessity of two registers is now a theorem end to end" therefore over-reads its own parts. Honest form: *each half of the necessity argument is machine-checked; the argument joining them is prose.* |
| ¬¬Z = T is a design consequence, not a defect | §3, and the reply to VRG | the *value* is machine-checked (`ax_notnot_Z`); that it follows from the generating principle rather than being patched in is an argument about design intent. It is a good argument and it should be written out, not asserted. |

---

## Findings from building this inventory

**F1 — the corpus claim is true, and now measured rather than argued.**
The preprint says `#print axioms` over "the whole corpus" is empty. That
rested on 103 hand-placed prints against 321 theorems; the defence (a
dirty lemma infects its consumers) is sound but is an argument, and an
orphan theorem would escape it. Measured exhaustively: **321 of 321
clean.** The claim survived contact with its own audit. This is a
strengthening and should be stated in Deliverable One with the method,
not just the result.

**F2 — `QuantumWitness.lean` was in nobody's build. FIXED 2026-07-20.**
Five theorems, real content (the MO2 quantum pole, load-bearing for
PSSL); it compiled clean and printed an empty axiom list, but was absent
from `defaultTargets` in `lean/lakefile.toml`, so `lake build` never
touched it and CI had never seen it. It was passing on nobody's
authority. Added to the targets (build: 33 jobs, 108 axiom prints), and
`axiom_audit.py` now **fails on any orphan module carrying theorems**, so
the class of bug cannot recur silently. A zero-theorem generator
(`BridgeGen.lean`, which feeds `bridge.py` by `#eval`) is noted, not
failed — there is nothing in it to audit.

**F6 — the stands ran in no CI at all. FIXED 2026-07-20.** The sharpest
finding of this pass, and it was not about a theorem. Two workflows
existed: `blueprint.yml` and `lean.yml`, the latter triggered only on
`paths: lean/**`. **`run_all.py` was invoked by neither.** Every tier-B
and tier-C claim above — the 12/14 price list, the algebraic passport,
interpolation, cut admissibility, the temporal layer, the quantum stands
— was green on the curator's machine and nowhere else.

Worst of it: `bridge.py`, the stand that checks the Python core and the
Lean corpus still answer identically (141 answers, cell by cell), never
ran either. A change to `ztl.py` could drift from `ZTL.lean` without any
automation noticing, because a `lean/**` path filter would not even wake
the workflow. That drift is the one failure that would invalidate the
machine-verification claim itself.

Also: the zero-axiom gate read `test "$clean" -ge 60` against a corpus
producing 108. Forty prints could be deleted with CI still green.

Fixed: threshold set to the measured 108; `inventory/axiom_audit.py`
added as a CI step; new `regression.yml` runs `run_all.py` on every push
with **no path filter**, deliberately. `tool/USING_THE_CORE.md` tells an
external agent that "the same build runs on every push under GitHub
Actions, executed by a third party, publicly logged" — that sentence was
true of the Lean half and not of the stands. It is true of both now.

**F3 — the abstract's MEASURED tag sits on the wrong claim.** The
abstract reads: "We show **(MEASURED)** that all six implement fragments
of a single logic." Checked: each of the six does have a stand, and each
reproduces that tradition's central move on a worked case. So this is not
an unsupported claim — it is tier C wearing a tier-B label. What is
measured is *six worked correspondences*; what is claimed is *six
implementations of fragments*, a general statement about each tradition's
semantics that no stand touches. The gap is exactly one quantifier wide,
and a referee who knows provenance semirings will find it in the first
reading.

Recommended wording, which costs the paper nothing it can defend: "Each
of the six is shown (MEASURED) to reproduce, on worked cases, the
behaviour generated by this principle." Then the honest ambition goes in
the roadmap: prove one embedding properly.

This is the largest single gap between what the paper says and what the
repository can show — and it sits in the abstract, the one paragraph
every referee reads.

**F4 — §9 over-reads its own parts.** The text closes: "the necessity of
two registers is now a theorem end to end." Checked against the code:
every component is genuinely tier A — `evalK_mono`, `jumpL_mono`,
`kt_fixed`, `kt_least`, `grounded_absolute` on the lazy side,
`eager_and_not_monotone` on the greedy side. But **no Lean object states
that two registers are necessary.** That step is a composition made by
argument: the greedy register has no fixed point on the liar, the lazy
one cannot pass verdicts, therefore both are required. The argument is
good; "a theorem end to end" is one notch above it. Honest replacement:
*both halves of the necessity argument are machine-checked; the
inference joining them is prose.* Two words, and the claim ceiling is
correct.

(Recorded also as a correction to my own first draft of this inventory,
which filed the §9 claim as unbacked prose. It is not unbacked — its
parts are the most thoroughly checked material in the corpus. The defect
is narrower and more interesting than "no evidence": it is a true
composition described with a stronger word than composition earns.)

**F5 — the three §3.5 mini-theorems were prose. FIXED 2026-07-20.**
They were the only place in the paper where the word "theorem" sat on
unformalised reasoning about the core itself. Now `lean/Frame.lean`, 17
theorems, empty axiom list:

* MT1 `mt1_contraposition_impossible`, plus `mt1_from_the_cells` stating
  the failure as an implication from the two named cells — so the cost
  of a rescue is explicit;
* MT2 `mt2_quarantine_irremovable` — no ¬-fixed point exists, and at Z
  it is pessimism that excludes it;
* MT3 turned out to be the real work. "Restores all classical laws"
  deserved the strong reading, so what is proved is agreement with
  Boolean evaluation term by term (`mt3_collapse_is_classical`), with
  "every classical tautology returns" as a corollary
  (`mt3_every_tautology_returns`). `mt3_the_fork` exhibits the same
  `p→p` at F in ZTL proper — the fork is one step wide.

Corpus now 338 theorems in 17 modules, all clean.

---

## What this inventory does not establish

It does not establish that the preprint's prose is accurate everywhere,
that the encodings in the stands mean what their names say, or that the
Lean statements formalise the intended informal claims. A theorem is only
as good as its statement, and reading statements against intentions is
the curator's step, not the machine's.
