# Zenodo upload sheet — PSSL v1.0.0 (PREPARED; the curator publishes)

**This file only prepares the manual upload. Claude never publishes.**
Source: `paper/PSSL_EN_v1_0_0.tex` → **`paper/PSSL_EN_v1_0_0.pdf` (6 pages, BUILT
2026-07-18, pdflatex)** = the file to upload. RU reading copy: `paper/PSSL-RU.md`.
Verifiable anchor: `lean/ZTL.lean` + `lean/QuantumWitness.lean` (both empty axiom
list, measured 2026-07-18).

**Upload flow:** new Zenodo record → upload `paper/PSSL_EN_v1_0_0.pdf` → paste the
block below → Publish → paste the version DOI back here.

**File to upload:** `paper/PSSL_EN_v1_0_0.pdf` (6 pages)

---

**Resource type:** Publication → Preprint

**Title:** A Paradoxical, Self-Referential System of Logics (PSSL)

**Subtitle / in-text:** Four non-classical logics as tamings of one
self-referential fixed point — a synthesis with two machine-checked poles.

**Authors:** Reznik, Vitaly

**Version:** 1.0.0

**License:** Creative Commons Attribution 4.0 International (CC BY 4.0)

**Description (paste as-is):**

This essay offers a way to see four non-classical logics — classical, type
theory / intuitionism, quantum logic, and Zero-Trust Logic (ZTL) — as four
disciplined answers to a single self-referential paradox. The paradox is the
one construction behind the liar, Russell's set, Cantor's diagonal, and
Gödel's undecidable sentence, made exact by Lawvere's fixed-point theorem
(1969): self-application with no fixed point. Each logic keeps all of classical
logic except one law and thereby houses the paradox differently — classical by
explosion plus the Tarski hierarchy, type theory by the universe hierarchy
(Girard's paradox), quantum by superposition, ZTL by pointwise quarantine to
the mark Z. Two invariants do not move: non-contradiction with its reductio
(the shared floor, a law kept by all) and the self-referential paradox itself
(the shared ceiling, a monster tamed by all); the floor is the guard posted
against the monster. The four do not merge — their kept laws conflict at the
seams — so they orbit classical logic (the unreachable center that would keep
every law at the price of the raw liar) rather than fusing.

The formalizable half of the picture is machine-checked on the EMPTY axiom
list, verifiable from zero with a bare Lean 4 (no mathlib, no imports): the
mirror between ZTL and quantum logic. ZTL keeps distributivity and loses
excluded middle, double negation, and identity p→p (they fall at the mark);
quantum logic (witnessed on MO2, the smallest non-distributive ortholattice)
keeps excluded middle and double negation and loses distributivity; both keep
non-contradiction. ZTL breaks where a thing equals itself; quantum breaks where
things combine.

Honest scope. This is a synthesis and a reading, not a theorem, a merger, a new
foundation, or a new field. Its components are established (Lawvere 1969;
Birkhoff–von Neumann 1936; intuitionism; universal logic). What is the author's:
ZTL itself (its own preprint), the curation of the four as tamings of one
monster, and the two Lean witnesses. Two poles are concrete and machine-checked;
the cycle between them, and the metatheoretic corners (intuitionistic
underivability of LEM, "classical as center"), are prose, marked as such. The
reliability of the machine-checked half does not depend on trusting the author
or the AI: both Lean files verify against the Lean 4 kernel on the empty axiom
list.

AI disclosure: written in dialogue with the AI system Claude (Anthropic); all
design decisions, framing, and final responsibility rest with the human author.

**Keywords:**
non-classical logic; self-reference; Lawvere fixed point; paradox; liar paradox;
Russell's paradox; Cantor diagonal; Gödel incompleteness; quantum logic;
orthomodular lattice; distributivity; excluded middle; type theory; intuitionism;
Girard's paradox; Zero-Trust Logic; paracomplete logic; bivalent verdicts; three-valued matrix; universal logic;
Lean 4; machine-checked proofs; empty axiom list

**Related/alternate identifiers:**
- https://doi.org/10.5281/zenodo.21318981 — references (ZTL, Zero-Trust Logic — the ZTL corner)
- https://doi.org/10.5281/zenodo.21419290 — references (Choice as an Act — verify-from-zero precedent)
- https://github.com/inventor1975/ZTL — isSupplementedBy (the two Lean witnesses, ZTL.lean + QuantumWitness.lean)

**Additional notes (paste into "Additional notes"):**
The essay text is CC BY 4.0; the accompanying Lean files are MIT-licensed.
Reproduce the two machine-checked poles from zero, no mathlib:
`lean lean/ZTL.lean` (13 objects, "does not depend on any axioms", ~1.1 s) and
`lean lean/QuantumWitness.lean` (5 objects, ~0.5 s), Lean 4.29.1.
