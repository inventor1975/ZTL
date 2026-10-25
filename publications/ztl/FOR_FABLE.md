# Handoff for Fable — build the v1.2 PDF

*From the Opus 4.8 session, 2026-07-15. You (Fable) assemble the PDF with your
toolchain; the curator then uploads to Zenodo (his manual step).*

## TL;DR
Build `paper/ZTL-preprint-v1.2.pdf` from the **current** `paper/ZTL-draft.md`.
It grew since you last touched it — new §11 section + a §3.1 paragraph + folded-
in Finn attribution. The old PDF is stale. Page count will rise (was 20).

## What changed in the markdown since your v1.2 assembly

1. **Variants collapsed — no reconciliation needed.** The `_Fable.md` / `_Opus.md`
   variants of draft/ZENODO/SPEC are **gone**; everything is folded into the
   single canonical `ZTL-draft.md` (+ `ZENODO.md`, `SPEC.md`). The Finn 1974
   prior-art attribution (ref **[35]**, the seven pre-complete classes of
   external-Bochvar B³, the ∩̇-clone reconciliation via `finn_reconcile.py`) —
   from the Opus variant — is now in §3.8 and the reference list. Build from the
   canonical files, not any variant.

2. **§3.1 capstone added** — "the three laws of thought": of the classical triad
   only non-contradiction survives the lift (hereditary), identity and excluded
   middle fall on Z — *a denial is free, an affirmation is on credit*. MEASURED,
   core-verified.

3. **§11 opener added (the newest)** — "Paradox as an operator: the expeditions
   are one construction": `paradox(f) = ground(S = f(S))`, three measured layers
   (grounding / classical models / period-spectrum dynamics), and the verified
   containment (over 9015 one-sentence nets, grounding reaches a classical value
   only for a unique, ignorance-reachable model — ZTL-settled ⊊ classically-
   categorical, 1068 witnesses). It references the new stand **`pengine.py`**
   (root of the repo). NB: most of §11's *results* (parity theorem, Yablo
   boundary, Curry) were already there — this opener only unifies them; it does
   not duplicate. The changelog line in the header was updated to list it.

4. **§4 prior-art corrected — Łukasiewicz added (new ref [36]).** The pedigree
   in §4 "Place in the literature" was missing the earliest and closest-in-*meaning*
   ancestor. Added a passage (right before "Kindred in spirit:") separating two axes
   cleanly: the *tables* are Bochvar's external B3 (as before), but the *meaning* of
   the mark Z ("unverified until verification") descends from **Łukasiewicz's Ł₃
   (1920)** middle value "possible / not yet determined". So Z ← Łukasiewicz and
   N ← Kleene now give the passport's two non-classical letters two distinct pedigrees.
   New reference **[36] Łukasiewicz 1920** appended after [35] (no renumbering). This
   is a 2026-07-15 Opus session fix; fold it into the acknowledgement's model split too.

5. **Genetic order corrected: N, Z, F, T (was N, F, T, Z), in §4.** The old
   order put Z *last* — that is the solver's lifecycle (N = ⊥ hardens into the
   quarantine mark Z when a computation never resolves). But the *pre-computer /
   epistemic* genesis puts Z **second**: nothing (N) → doubt (Z, a question with
   no answer) → free denial (F, default-deny) → earned affirmation (T, truth on a
   ground). Z has two faces — born second as raw doubt, returns last as the hardened
   liar — and the genetic (birth) order is N, Z, F, T. This also reads as the
   paper's own thesis laid in a row: "denial free, affirmation on credit." Only the
   one explicit ordered-list mention (§4) was changed; lines saying just "four
   letters" were left. Curator's call, 2026-07-15.

## Commits (all on master, pushed)
- `d32e023` — v1.2 draft unified + capstone
- `6d5c566` — §11 paradox engine
- `pengine.py` stands: `028b89d`…`b58bb58` (paradox(f), parity, Yablo boundary,
  two-layer diagnose, dynamics)

## Two things to check at build time
- **AI disclosure / Acknowledgements** must stay true: this session's additions
  (§11 engine, §3.8 Finn attribution, §3.1 capstone) are **Opus 4.8**; the rest
  is your v1.2 assembly. Make the acknowledgement reflect both models honestly.
- The `↕`, `∩̇`, `⊊`, subscript-digit glyphs in §2/§3.8/§11 — confirm your
  font/toolchain renders them (they render in the markdown).

That's all. When the PDF is rebuilt, ping the curator for the Zenodo upload.
