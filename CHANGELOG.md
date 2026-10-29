# Changelog — the judge's public surface

Changes to what a client of `ztljudge` receives. Announced here before anything is retired.

## 2026-10-29 (evening) — `IF STABLE` decided by completions

- `EARNED` and `REFUTED` are now exactly strong Kleene T and F (the lazy register), nothing else.
- `EARNED IF STABLE` (`REFUTED IF STABLE`): not settled read by read, but T (F) in every completion of the dirty
  atoms, i.e. if each dirty atom reads the same at all its occurrences. The afternoon definition used the grade's
  refinements, which keep Z among their values, so the label followed ZTL's own verdicts on dirty atoms: `p -> p`
  was `OPEN` while `~(p & ~p)` was `EARNED IF STABLE`, though both are true in every completion. Found by two cloud
  reviews of preprint 2.1.6 and the journal draft.
- `ON CREDIT` / `OPEN`: T now / not T now, and the completions disagree.
- MEASURED on the regression pool (14,530 cells with a dirty atom): `EARNED IF STABLE` 950 → 2,440, `REFUTED IF
  STABLE` 1,014 → 1,470, `ON CREDIT` 2,788 → 2,296, `OPEN` 6,054 → 4,600; `EARNED` 2,450 and `REFUTED` 1,274 unchanged.
  Checked against brute force on every cell: 0 disagreements.
- **Effect on clients.** Some claims move from `OPEN` or `ON CREDIT` to an `IF STABLE` disposition (e.g. `p -> p`,
  `p | ~p`, `~(p -> p)`). A client that accepts only `EARNED` is unaffected.
- Cost: only the REPEATED dirty atoms are enumerated (2^r strong Kleene passes); with them fixed every other dirty
  atom occurs once, where strong Kleene is exact. Past 16 repeated atoms the search is skipped and said so.
- Lean (`lean/ZSpeaks.lean`, empty axiom list): the six dispositions defined this way, each a ZTL formula over the
  atoms (`judge_speaks_ztl`), covering every case (`dispositions_partition`); the judge's grant is exactly "T in
  every completion" (`grant_iff_enum`), right wherever a classical substitution is right
  (`grant_right_where_substitution_right`).

## 2026-10-29 — two new dispositions: `EARNED IF STABLE`, `REFUTED IF STABLE`

- `judge()` now returns seven dispositions instead of five. What used to be `EARNED` splits:
  - `EARNED` — T, survives every verification, AND T under every read of every occurrence (the lazy, Kleene register agrees);
  - `EARNED IF STABLE` — T and survives every verification, but only if each atom in the new field `if_stable` reads the
    same at every occurrence. Read each occurrence on its own and the claim is not established.
  
  `REFUTED` splits the same way. `if_stable` lists the dirty atoms that occur more than once; it is empty on every claim
  where each dirty atom occurs once.
- **Why.** The judge's "survives every verification" refines each dirty atom to one value, so it presumes that every
  occurrence of an atom reads the same. ZTL's own premise is that two reads may differ (time of check vs time of use).
  Running every stand under `dilemmas/` found 19 claims where the two disagree, all argument forms (Cogito, Hume's
  guillotine, Plato's third man, Bell, Agrippa's critics): valid only if the atom means the same in premise and
  conclusion. The presumption is now named instead of silent.
- **Effect on clients.** A client that accepts only `EARNED` now refuses the `IF STABLE` cases — the safe direction. A
  client that buckets dispositions must add the two new keys (`ztljudge.DISPOSITIONS` lists all seven).
  `next_check` treats `IF STABLE` as not settled and orders verification of `if_stable`.
- The Lean predicate `Earned` (`lean/ZDirty.lean`) and the dominance theorems of preprint 2.1.5 are about the
  refinement notion, i.e. `EARNED` and `EARNED IF STABLE` together; they are unchanged.

## Announced, not yet done

- The field `unverified` will be retired in favour of `dirty` (same content, both returned now).
