# Zenodo upload sheet — The Paradox Docket v1.1 (PREPARED, NOT UPLOADED)

**v1.0 PUBLISHED 2026-08-09: version DOI 10.5281/zenodo.21864082**
(https://zenodo.org/records/21864082). Concept DOI 10.5281/zenodo.21864081
resolves to the latest version. This sheet prepares **v1.1**; the upload and
the publish button are the curator's.

Source of truth: `paper/paradox-docket-EN-draft.md` (v1.1 header, 2026-08-13).
Assembled file with Appendix A substituted: `paper/paradox-docket-EN-build.md`.
No PDF toolchain exists in this environment — the PDF is produced on the
curator's side from the build file.

---

## Title (unchanged)

The Paradox Docket: A Computable Classification of the Classical Paradoxes

## Version

1.1

## Publication date

2026-08-13

## Upload type

Publication → Preprint

## Description (Zenodo abstract field)

Use the paper's abstract verbatim, then append the version note below as its
own paragraph:

> **New in v1.1.** A ninth verdict: Agrippa's dogmatic horn splits under this
> paper's own count — a self-supporting foundation is UNDERDETERMINED with two
> admissible settings, so the stop was a real choice with a coherent rival
> (the fifth postulate, the axiom of choice, propositional extensionality),
> while a self-forcing one is INTRINSIC with exactly one setting, a terminus
> nobody chose. A nullary ground — an operation with no arguments — is a
> terminus of the second kind, and Agrippa's argument, being about the
> justification of statements, does not reach it; no priority is claimed for
> the philosophical move (Wittgenstein, the pragmatists, and nearest of all
> Brouwer), only for the exhibit: a foundation whose axiom cost is zero and
> machine-confirmed. Four jurisdiction edges declared in v1.0 are now crossed
> rather than merely named — the sorites, the surprise exam, the lottery and
> Berry — plus Moore's paradox, which never appeared on the list. A second
> genre of defect is added: the empty description and the status E. The docket
> table is re-measured row by row against the machine on every regression run.
> Two corrections are recorded in the text rather than silently applied: the
> count of crossed edges, and a claim about where robustness comes from, which
> the Agrippa case refuted.

## Version notes (Zenodo "Additional notes", optional)

v1.1 supersedes v1.0 (10.5281/zenodo.21864082). No verdict published in v1.0
is withdrawn; the docket table is unchanged and re-measured. One sentence of
v1.0's supporting material is corrected in §4.9 and marked as such.

## Related identifiers

- `isNewVersionOf` — 10.5281/zenodo.21864082 (v1.0, the prior version)
- `isSupplementedBy` — https://github.com/inventor1975/ZTL (the corpus; every
  verdict reproducible with one command)
- `cites` / `isDerivedFrom` — 10.5281/zenodo.21318981 (ZTL concept DOI, the
  canonical preprint of the logic)

## Keywords (unchanged from v1.0, plus)

Agrippa's trilemma; Münchhausen trilemma; regress; nullary operation; Moore's
paradox; foundations of mathematics

## Checklist before upload

- [ ] `python3 run_all.py` green (83 stands + Lean) — the paper's claims are
      pinned by `inventory/docket_claims.py`, which fails the run if one cell
      of the published table stops matching the machine
- [ ] Appendix A in the build file is the CURRENT `zclassify.py` output
- [ ] Figures 1–3 present in the PDF (placeholders in the markdown)
- [ ] AI disclosure paragraph names the model of the session that wrote the
      version, Variant A, curator Vitaly Reznik
- [ ] DOI of v1.0 cited in the header of the new version
