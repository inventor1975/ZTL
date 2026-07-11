# ZTL — remaining work (revision 2026-07-11, order: hard to easy)

## Gaps (substantive)

1. ✅ DONE (E12, zverify.py): stability bit = global supervaluation;
   the 90/90 theorem; verdict = pair (value, warranty).
   **The "verify" operation** — the act Z→T/F outside the system: who
   sanctions it, how it is recorded, what happens to already-issued
   verdicts after further grounding. NARROW PLACE: greedy verdicts are
   non-monotone under verification (can flip) — a stability bit is
   needed. → zverify.py (E12).
2. ✅ DONE (E13, zcombine.py): intersection of constraints; verify =
   special case; Zadeh → Smets; twin #6 Green–Tannen.
   **Evidence combination** — two sources about one value: fusion of
   intervals/masses (they have Dempster's rule, we don't). Candidate
   for twin #6: provenance algebra (Green–Tannen semirings).
3. **Z is blind to the kinds of ungroundedness** — the liar and the
   truth-teller are both Z; revision theory distinguishes them by
   patterns. Enrich the mark with a "passport" without killing
   greediness?
4. **Proof theory is thin** — no sequents/cut-elimination/
   interpolation; no algebraic semantics; first order only on finite
   domains. For v1 — an honest caveat; for completeness — a gap.

## Seams

5. Lean lags behind the expeditions: E6–E11 have no Lean twins; no
   general lazy-grounding theorem (finite Knaster–Tarski);
   C-extension of sets is examples only.
6. Python and Lean are not stitched (no auto-check against the Lean
   reference).
7. ✅ DONE: run_all.py — 19 stands + Lean, markers, exit code.

## Cosmetics before the port (Zenodo)

8. ✅ DONE: "References" in the preprint — 30 entries.
9. ✅ DONE: LICENSE (MIT), CITATION.cff, README; language decided —
   everything public is English (Russian originals archived locally
   in OLD/, untracked).
10. The prover is naive (exponential, no heuristics) — not urgent,
    matters for the tool.

Order of movement (curator's decision): hard to easy, narrow places
first: 1 → 2 → (publishing hygiene 7–9) → port; 3–6, 10 — after v1.
