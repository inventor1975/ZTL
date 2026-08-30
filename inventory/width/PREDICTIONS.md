# The width of an inquiry — frozen 2026-08-19, before the bench

## The quantity

The judge orders ONE ground checked at a time. The Meno bench found ~3% of
orders individually worthless: `p ⊕ q` with both grounds unverified moves for
neither atom alone, only for both together.

So define, for an unsettled claim:

> **width** = the size of the smallest set of unverified grounds that, filled
> together, moves the verdict or the disposition.

Width 1 is ordinary incremental inquiry. Width ≥ 2 means no partial progress is
possible: you must produce the whole configuration before anything at all
happens. The judge cannot currently report this, and its order is misleading
exactly there.

## Why it is worth an hour

Not the 3%. The question behind it: **is width bounded?** If some fixed number
covers every claim, inquiry is always nearly-incremental and the fix is a label.
If width grows without bound, then there are claims for which step-by-step
inquiry is impossible in principle — the strongest form of Meno's second horn,
and a real limit on what any evidence-gathering procedure can promise.

## Predictions

**P1 — width 1 dominates**, well over 90% of unsettled cells.

**P2 — width is UNBOUNDED**, and the witnesses are xor/xnor chains. Worked by
hand before the bench: `p ⊕ q ⊕ r` with all three unverified reads `F`; filling
one leaves `F`, filling two leaves `F`, and only `p=T, q=F, r=F` moves it. So
width 3 exists at three marks, and I expect width to track the number of marks
in a chain — one more mark, one more unit of width.

**P3 — width is invisible to the label.** All the atoms of such a chain are ON
the label (the lazy register keeps every hole of an undecided xor), so the
receipt cannot distinguish width 1 from width 3. This is the over-approximation
half showing its operational face, and it means the fix is a NEW computation,
not a filter over an existing one.

**Cut-offs.** If P2 is wrong and width never exceeds 2, the finding is small and
the honest output is a warning flag on the order, nothing more. If width turns
out unbounded, the result is a limit statement worth its own paragraph — and I
must then say plainly what it costs to compute, because the naive search is
exponential in the number of marks.
