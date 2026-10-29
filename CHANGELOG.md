# Changelog — the judge's public surface

Changes to what a client of `ztljudge` receives. Announced here before anything is retired.

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
