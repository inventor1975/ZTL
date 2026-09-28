# FORECAST — fixing the uncovered-core findings (frozen BEFORE the change)

**Date:** 2026-09-28. **Written by:** Claude (Opus 5.5), curator Vitaly Reznik («Да»).
**Source:** PR #5, `inventory/probes/REDTEAM-UNCOVERED-2026-09.md`. Reproduced on master
1af886b first, by direct calls (not the cloud's stand):
`what_to_check('p | q', p=T)` → `already: True` beside `guaranteed [['q']]`;
`order(a&b&c&d&e, all Z, EARNED)` → «НЕТ НАБОРА … недостижима» (search cut at 4 of 5);
`order(g0&…&g9, all Z, REFUTED)` → «недостижима», while `g0 = F` alone gives REFUTED.

## Exact changes
- **B1** `zbackward.backward`: when the target is already met, the minimal family is {∅}:
  `possible = guaranteed = []`, `possible_none = guaranteed_none = False`, no search.
- **B2** a cut search (`limit < n`) does not claim "none": the `*_none` flags are `None`
  (not searched), and `order()` says the search was cut instead of «НЕТ НАБОРА» / «ГАРАНТИИ НЕТ»
  when nothing was found below the cut.
- **B3** a refusal at the cap: `*_none` are `None`, and `order()` returns the refusal, not
  «недостижима».
- **E1** the epoch floor's `survives` compares the DISPOSITION (EARNED / REFUTED / OPEN), not
  the bare verdict letter; the comment is rewritten: one crossing survived says nothing about
  grounds — only survival of EVERY crossing reads none of them (EpochBoundary). `~p` is the
  witness: F before (REFUTED), F after (¬Z = F, OPEN).
- **P1** the parser's precedence and associativity stated in SPEC.md, ONBOARDING.md and the
  studio's operator reference (`zfldoc.py`): `&` > `|` > `^` > `->` > `=`, all left-associative;
  `a -> b -> c` is `(a -> b) -> c` — write the brackets.

## Predictions
- **F1** `test_redteam_uncovered.py`: 11 FAIL → 0, every sweep still PASS.
- **F2** `inventory/test_backward.py` GREEN unchanged (its cases are neither cut nor at the cap
  nor already met — to be confirmed by running it, not by this sentence).
- **F3** `zfl.what_to_check` in the studio: the `refused` path and the ≤ 3-input path cannot be
  cut (`BACKWARD_CAP` 3 < `MAX_K` 4), so only B1 moves there: `already` rows lose their lists.
  The studio's rendering already shows «already» first — the visible page does not change.
- **F4** `survives` flips only where the verdict letter is equal and the disposition is not;
  on the cloud's 118 epoch documents: counted after, reported, not guessed here.
- **F5** run_all ALL GREEN with the new stand registered (163 stands + Lean).
