# The width of an inquiry — measured 2026-08-19

Predictions frozen in `PREDICTIONS.md` first.

## The quantity

For an unsettled claim, **width** = the size of the smallest set of unverified
grounds that, filled together, moves the verdict. Width 1 is ordinary
incremental inquiry. Width ≥ 2 means no partial progress is possible at all.

## Result

**P1 held.** Width 1 dominates: 93% of unsettled cells over the exhaustive
depth-2 pool, 91% over random depth-5 formulas across five atoms. For most
claims inquiry is incremental, and the judge's one-ground order is honest.

**P2's conclusion held; its witness was invented.** I predicted width would grow
with xor chains. It does not: `p ⊕ q ⊕ r` with all three unverified has width
**1**, because the inner xor collapses to a definite value and the outer one is
sensitive to the last ground alone. My hand-calculation had tested two atoms of
three. The wide cases are irregular mixed formulas, and the hunt found width
reaching the number of available grounds — **4 of 4 at four atoms, 5 of 5 at
five**, over ~24,000 unsettled cells.

So the honest statement, and it is a limit rather than a bug:

> **Step-by-step inquiry is not always possible.** There are claims of any size
> for which nothing moves until every unverified ground is filled at once.

**P3 held.** The label cannot see width. `p ⊕ q ⊕ r` names all three grounds and
has width 1; `p ⊕ q` names both and has width 2. The receipt answers "which
grounds could matter", never "how many at once" — the over-approximation half
showing its operational face again.

## What was changed in the judge

`judge(...)["joint"]`: when no single ground moves the matter, it names the
grounds that must be filled together, and `why` says a one-at-a-time order would
be empty work. Two kernel calls per ground; no recursion (it asks `ev` and
`grade` directly rather than `what_if`, which calls `judge`).

Deliberately NOT computed: the exact width. That search is exponential in the
number of marks, and what a reader needs is the difference between "go check
this" and "no single check will move this".

## Cost of the whole Meno thread, honestly

Two defects found and fixed — orders on settled matters (27–30% of settled
cells), and one-ground orders where no one ground helps (6–7% of unsettled).
One limit established by measurement. Two of my three predictions were wrong in
their mechanism while right in their number or conclusion, which is the ratio
worth remembering before the next one.

---

## Перенесено в репозиторий 2026-08-30

Лежало в `lab/`, который **намеренно** в `.gitignore` — там рабочий материал
ветки интроспекции, специально не отгружаемый. Ширина дознания — не рабочий
материал, а измерение, и её место в `inventory/`, рядом с остальными
промерами. Копия в `lab/` удалена: `bench.py` в двух каталогах — ровно тот
ДВОЙНИК, который ловит `tool/deploy_stamp.py`.

Прибор проверен НА НОВОМ МЕСТЕ, а не просто переложен: прогон
`python3 inventory/width/bench.py` из корня репозитория воспроизводит
число 91% (ширина 1 на случайных формулах глубины ≤5 по пяти атомам),
записанное выше.
