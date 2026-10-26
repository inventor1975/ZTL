# Zenodo sheet — The Gettier Case File

## v1.1 — PREPARED 2026-10-26 (the dirty Z). Draft 23663277, reserved DOI 10.5281/zenodo.23663277. Claude never publishes; the curator does.

- **Flow:** open https://zenodo.org/records/21877469 → **New version** (keeps the concept DOI and the lineage).
- **File:** replace with `publications/gettier/Gettier-case-file-EN-v1.1.pdf` (10 pages). Build: `pandoc gettier-docket-EN-build.md -o Gettier-case-file-EN-v1.1.pdf --pdf-engine=lualatex -V mainfont=FreeSerif -V monofont=FreeMono -V geometry:margin=1in -V papersize=letter` (run in `publications/gettier/`; same letter page and fonts as v1.0).
- **Version:** `1.1`. **Publication date:** 2026-10-26. Title, authors, license, keywords — unchanged.
- **Description:** keep the v1.0 text below and put this paragraph first:

> **New in v1.1.** Z is named for what it is — a **dirty** parameter, following ZTL v2.1.3 (DOI 10.5281/zenodo.23648237): not ours, its owner may change it between two reads, so each occurrence is read on its own, and verification cleans it. v1.0 called Z an "unverified" tag, one of three statuses of the data — wording that suggested one hidden value merely not yet known. §2.1, the glossary and the phrases naming a Z-marked link are corrected. No verdict, carrier or measurement changes.

- **Related identifiers (add):** `isNewVersionOf` 10.5281/zenodo.21877469 (v1.0); keep the v1.0 relations.
- **AI disclosure:** v1.1 corrections with Claude Opus 5.5 (Anthropic), Variant A, curator Vitaly Reznik — already in the PDF.

---

## v1.0 — record of what was entered (published 2026-08-10)


**PUBLISHED 2026-08-10: DOI 10.5281/zenodo.21877469** (relations used:
Derived from 10.5281/zenodo.21318981; References 10.5281/zenodo.21864082 —
note: `isRelatedTo` is not in the Zenodo/DataCite vocabulary).

## Title

The Gettier Case File: Knowledge as an Earned Verdict

## Version

v1.0 (2026-08-10)

## Upload file

`paper/Gettier-case-file-EN-v1.0.pdf` (10 pages)

## Resource type

Preprint

## Authors

Reznik, Vitaly — ORCID 0009-0002-4103-6387

## Description (paste into Zenodo)

For twenty-four centuries knowledge was defined as justified true belief
(JTB). In 1963 Edmund Gettier showed, in three pages, that a belief can be
justified, true — and still not knowledge; epistemology has been hunting a
"fourth condition" ever since. This paper runs both of Gettier's canonical
cases (the sheep in the field; the ten coins) through an executable logical
instrument — the ZTL judge, which returns not a bare verdict but the pair
verdict + warranty, together with a named list of weak links.

Findings: (1) a Gettier case is not a defect of inference but contraband at
admission — the "justification" of JTB is a T admitted on a witness that
testifies about a different atom; the logic, handed a poisoned marking,
honestly answers "earned", because the fraud happens before it; (2) the
case has a measurable signature — the set of atoms carrying the verdict
under the naive marking and the set carrying it after the world's
correction are disjoint, so "the truth arrived by a different road than the
justification" turns from metaphor into a checkable condition on two sets;
(3) the passport office of the ZTL corpus confirms that no paradox is
present — only a conditional refusal with a named culprit.

The diagnosis is credited where it belongs: Sergei Artemov formalized
Gettier's case in Justification Logic in 2008, and his formulation is
quoted verbatim. The contribution here is an independent corroboration in a
foreign formalism (the convergence between formal methods that Williamson
explicitly recommends), executability (every claim of the paper re-checks
with one command: python3 zgettier.py, expedition E36 of the ZTL
repository), and three deltas along cracks Artemov himself named: a
mechanical admission gate instead of post-hoc analysis, a warranty ladder
instead of a timeless factivity axiom, and epochs instead of absent time.
The jurisdiction boundary is measured and declared: fake-barn cases are not
caught by the signature, and the paper shows why that refusal is correct.

Reproducibility: the reference bench zgettier.py (asserts pinned; a failing
assert refutes the paper) ships in the public repository
https://github.com/inventor1975/ZTL; the appendix is the verbatim output of
the bench at the publication commit. The interactive studio
(https://ztl.vitalyreznik.com) runs the same core in the browser.

AI disclosure: this work was carried out with the substantial
participation of the AI system Claude Fable 5 (Anthropic) under the
Variant A collaboration model — the human sets the tasks, verifies the
results, and answers for the content. Per COPE/ICMJE recommendations the
AI system is not listed as an author; the human author bears full
responsibility.

## Keywords

Gettier problem; epistemology; justified true belief; justification logic;
zero-trust logic; three-valued logic; machine-checked philosophy;
executable philosophy

## License

CC BY 4.0 (text); code MIT (in repository)

## Related identifiers

- References / isDerivedFrom: 10.5281/zenodo.21318981 (ZTL — Zero-Trust
  Logic, concept DOI)
- isRelatedTo: 10.5281/zenodo.21864082 (The Paradox Docket v1.0)

## Notes for the manual upload (curator)

1. New upload (new concept — this is a separate work, not a ZTL version).
2. Paste title/description/keywords from above; license CC BY 4.0.
3. Related identifier to the ZTL concept DOI as "References" or
   "Is derived from".
4. Publish; then bring the DOI back — I will stamp it into the paper
   header (v1.0.1 metadata touch or keep for v1.1), the repository README
   and the memory.
