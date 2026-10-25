# Zenodo sheet — PSSL **v1.1.0 PUBLISHED 2026-07-20**

**Published history**
- **v1.1.0** — 2026-07-20, version DOI
  [10.5281/zenodo.21455696](https://doi.org/10.5281/zenodo.21455696).
  Verified against the API: 9 pages, CC BY 4.0, ORCID in the creator, the
  three related identifiers as entered — and the **concept DOI unchanged**
  at 21452735, so the New-version flow held and the lineage is intact.
- **v1.0.0** — 2026-07-20, version DOI
  [10.5281/zenodo.21452736](https://doi.org/10.5281/zenodo.21452736).
  Verified against the API after publication: 8 pages, CC BY 4.0, ORCID in
  the creator, three related identifiers as entered.
- **Concept DOI (always latest):**
  [10.5281/zenodo.21452735](https://doi.org/10.5281/zenodo.21452735)

**This file prepared the v1.1.0 upload. Claude never publishes; the curator
did. Kept as the record of what was entered.**

Source: `paper/PSSL_EN_v1_1_0.tex` → **`paper/PSSL_EN_v1_1_0.pdf` (9 pages,
lualatex, 2026-07-20)** = the file to upload. English only: the Russian
reading copy was removed in v1.1.0 (see the foot of this sheet).
Verifiable anchor: `lean/ZTL.lean` + `lean/QuantumWitness.lean` +
`lean/Contextuality.lean` + `lean/JunctionWitness.lean` (all empty axiom list,
re-measured 2026-07-20: 13 + 11 + 3 + 8 = 35 objects).

**Upload flow — NOT a new record.** Open the existing record
https://zenodo.org/records/21452736 → **New version** → replace the file with
`paper/PSSL_EN_v1_1_0.pdf` → set Version to **1.1.0** → paste the block below
over the old description → Publish → paste the new version DOI back here.
Going through "New version" keeps the concept DOI 21452735 and the lineage;
a fresh record would orphan v1.1.0 from v1.0.0.

**File to upload:** `paper/PSSL_EN_v1_1_0.pdf` (9 pages)

---

**Resource type:** Publication → Preprint

**Title:** A Paradoxical, Self-Referential System of Logics (PSSL)

**Subtitle / in-text:** Three non-classical logics as resolutions of one
universal diagonal — a synthesis with five machine-checked components.

**Authors:** Reznik, Vitaly

**Version:** 1.1.0

**License:** Creative Commons Attribution 4.0 International (CC BY 4.0)

**Description (paste as-is):**

This essay offers a way to see three non-classical logics — type theory /
intuitionism, quantum logic, and Zero-Trust Logic (ZTL) — as three
disciplined answers to a single self-referential paradox. The paradox is the
one construction behind the liar, Russell's set, Cantor's diagonal, and
Gödel's undecidable sentence, made exact by Lawvere's fixed-point theorem
(1969): self-application with no fixed point. Each keeps all of classical logic
except one law and thereby houses the paradox differently FROM WITHIN — type
theory by the universe hierarchy (Girard's paradox), quantum by
superposition, ZTL by pointwise quarantine to the mark Z. Classical logic
itself is stated once as the BASELINE and set aside: it keeps every
structural principle and therefore has nothing to house the paradox with, so
it explodes and is repaired from the METALANGUAGE — Tarski's hierarchy sits
above the logic, not inside it. Its "resolution" is of a different kind, and
nothing about the classical corner is proved here.

Two invariants do not move: non-contradiction with its reductio
(the shared floor, a law kept by all) and the self-referential paradox itself
(the shared ceiling, a monster tamed by all); the floor is the guard posted
against the monster. The three do not merge, and the paper states exactly how the three pairs
fail to: two pairs clash at the level of what is validated (total excluded
middle against its pointwise failure; strong normalization against housed
non-termination), while the third — quantum and intuitionistic — CAN merge,
and the merge is exactly classical logic (distributivity plus excluded middle,
double negation and total complementation is a Boolean algebra). Merging
expels the pair from the family: the result resolves nothing from within. So
the three are incomparable AS RESOLUTIONS — two pairs cannot share a valuation
structure, and the third can share one only by ceasing to resolve.

The formal components are machine-checked on the EMPTY axiom list,
verifiable from zero with a bare Lean 4 (no mathlib, no imports): the
mirror between ZTL and quantum logic, the combinatorial
core of quantum contextuality — the Mermin-Peres magic square admits no
bivalent valuation (0 of 512) and GHZ none (0 of 64), by kernel
enumeration. On two quanta the mirror sharpens: at the singlet, pair
propositions are true while every local proposition is empty — ontic
vacancy, not our ignorance: by Bell no consistent local values exist to be
looked at — the covering law falls in correlation form — and the seam itself is
kernel-checked (the junction theorem: the singlet lies in the join of two
product atoms yet in neither atom and in no local plane of either factor,
exact integer arithmetic, empty axiom list); the falls saturate along the
ladder. A closing section, explicitly marked as a reading, draws the
consequence: the corners are descriptions and it is descriptions that pay
the laws; at the level of states the diagonal's premise itself fails (the
self-negating fixed point exists physically), so for the world the paradox
dissolves rather than being tamed. ZTL keeps distributivity and loses
excluded middle, double negation, and identity p→p (they fall at the mark);
quantum logic (witnessed on MO2, the smallest non-distributive ortholattice)
keeps excluded middle and double negation and loses distributivity; both keep
non-contradiction. ZTL breaks where a thing equals itself; quantum breaks where
things combine. That second clause is sharpened into a necessity and
machine-checked: MO2 keeps modus ponens under the Sasaki hook but admits NO
implication at all — no binary operation on the lattice — satisfying the
deduction theorem: such an arrow would have to be a relative
pseudocomplement, which would make the lattice Heyting and
therefore distributive. So what the quantum corner cannot do is discharge a
premise while a context still stands, and no choice of connective repairs it;
the claim is not "MO2 under the Sasaki hook lacks the deduction theorem" but
"MO2 cannot have one". The mirror is shown to be an analogy, not a lattice duality:
the obstruction is the involution asymmetry (ZTL's negation is not involutive,
double negation being one of the laws it drops), which is also what locates
ZTL as the paracomplete relative that breaks the involution its Lukasiewicz
ancestor and its quantum cousin both keep (the known bridge from orthomodular
to many-valued logic runs through Lukasiewicz, Pykacz 2010).

What changed in version 1.1.0. Classical logic is no longer listed as a
fourth resolution. Version 1.0.0 tabled it beside the other three, which
counted classical logic among the "non-classical logics" of its own subtitle,
and suggested a symmetry that does not hold: none of the five machine-checked
components concerns the classical corner — every witness is about ZTL, MO2, or
their pair. Classical logic is now stated once as the baseline and set aside,
with the difference in kind made explicit (its repair is metalinguistic, the
other three resolve the diagonal from within). Section 4 is restated exactly: two pairs are valuation-incompatible, and the
third pair (quantum–intuitionistic) can merge — into classical logic itself,
which is precisely the baseline and resolves nothing from within. The old
argument through the baseline was muddled in form (classical logic is not
trivial) but was gesturing at this true fact, and the repair states it rather
than deleting it: the baseline is where the mergeable pair lands. The metaphor
of an orbit around an unreachable centre is gone; it was marked as metaphor
and did no work. No formal content is added or removed: the five
machine-checked components, their axiom profiles and their statements are
unchanged from 1.0.0.

Honest scope. This is a synthesis and a reading, not a theorem, a merger, a new
foundation, or a new field. Its components are established (Lawvere 1969;
Birkhoff–von Neumann 1936; intuitionism; universal logic). What is the author's:
ZTL itself (its own preprint), the curation of the three as resolutions of one
diagonal, and the five Lean witnesses (the impossibility result among them). The formal components are machine-checked;
the cycle between them, and the metatheoretic corners (intuitionistic
underivability of LEM), are prose, marked as such. The
reliability of the machine-checked components does not depend on trusting the
author or the AI: all four Lean files verify against the Lean 4 kernel on the
empty axiom list, 35 objects in about a second in total.

AI disclosure: written in dialogue with the AI system Claude (Anthropic); all
design decisions, framing, and final responsibility rest with the human author.

**Keywords:**
non-classical logic; self-reference; Lawvere fixed point; paradox; liar paradox;
Russell's paradox; Cantor diagonal; Gödel incompleteness; quantum logic;
orthomodular lattice; distributivity; excluded middle; type theory; intuitionism;
Girard's paradox; Zero-Trust Logic; paracomplete logic; bivalent verdicts; three-valued matrix; universal logic;
deduction theorem; Sasaki hook; relative pseudocomplement; Heyting algebra;
Lean 4; machine-checked proofs; empty axiom list

**Related/alternate identifiers:**
- https://doi.org/10.5281/zenodo.21318981 — references (ZTL, Zero-Trust Logic — the ZTL corner)
- https://doi.org/10.5281/zenodo.21419290 — references (Choice as an Act — verify-from-zero precedent)
- https://github.com/inventor1975/ZTL — isSupplementedBy (the four Lean files + the measured stands)

**Additional notes (paste into "Additional notes"):**
The essay text is CC BY 4.0; the accompanying Lean files are MIT-licensed.
Reproduce the machine-checked components from zero, no mathlib:
`lean lean/ZTL.lean` (13 objects, "does not depend on any axioms", ~0.3 s),
`lean lean/QuantumWitness.lean` (11 objects, ~0.2 s),
`lean lean/Contextuality.lean` (3 objects, ~0.3 s) and
`lean lean/JunctionWitness.lean` (8 objects, ~0.2 s), Lean 4.29.1.
Timings re-measured 2026-07-20 on the curator's machine.

---

**On the Russian reading copy.** `paper/PSSL-RU.md` was removed with v1.1.0
rather than carried forward. It had fallen a generation behind twice in two
days — four corners after the English went to three, and no Proposition B′
after the impossibility landed — and a second-language copy that misdescribes
the work is worse than none, since nothing in the record marks it as stale to
a reader who finds it. The English `.tex` is the single source. It remains in
git history (last at `0729be8`) if it is ever wanted back.
