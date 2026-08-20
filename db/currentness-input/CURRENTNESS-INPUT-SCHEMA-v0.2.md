# Currentness measurement — what a dataset must supply

**v0.2, 2026-08-20.** Specification, not a result. Frozen at this version; a
change gets a new version and a new hash. v0.1 is left intact beside it.

*Change in v0.2:* one condition added — **A9, Threshold Governance Record
Completeness** — designed by Ignacio Adrián Lerer, together with the third
verdict it requires. Nothing else moved.

## What this is for

A conclusion can be correct when it is made and stop being fit to rely on later,
because something it rested on changed. The question we made measurable is
whether the exposure that follows is carried by **how long** the organisation was
out of date, or by **what it did** while it was. On a synthetic corpus, elapsed
time turned out to be a poor proxy in every run: the window of false containment
is exactly the update lag, and the acts taken inside it are lag × action rate.

That is a statement about the instrument. Whether it holds of any real
institution is a **separate empirical claim** and has not been tested.

This document specifies what a body of real records must contain for that
separate claim to be testable at all — so that "is this dataset adequate?" can be
answered **before** anyone negotiates access, rather than after.

## The honest starting point

The existing probe (`db/probe_currentness.py`) consumes no data. It generates its
own world and measures inside it. So this is not documentation of an input format
that exists; it is the specification of what a records-consuming version would
require. Saying otherwise would be the first thing a reader should catch us on.

## The three quantities, and what each needs from the records

**The lag** — the interval between a change taking effect and the organisation's
own records reflecting it. This needs **two timestamps per change**, and it is
where most audit logs fail: they record when the organisation learned something,
not when it became true. One timestamp yields no lag at all, and a lag inferred
from the recording time is not a measurement, it is a restatement.

**The window** — the interval during which the recorded state satisfies the
organisation's containment requirement and the actual state does not. This needs
the requirement itself, **declared by the record holder**. An analyst who picks
the threshold picks the result.

**The acts** — what was done in reliance during the window. This needs each act
tied to a conclusion, each conclusion tied to a basis, and each act carrying a
**type**. Without types the finding collapses to a count, and the claim was
"number and type", not "number".

## The eight adequacy conditions

Checked mechanically by `check_dataset.py`, which refuses rather than degrades.
Five are hard: failing one means the measurement must not be run. Three cap what
a run may claim.

| id | what it protects | hard |
|----|------------------|:----:|
| A1 | lag is computable at all — both timestamps present | yes |
| A2 | lag is not silently inferred from the recording time | yes |
| A3 | the run is not vacuous — some change was recorded late | |
| A4 | exposure is attributable — every act reaches a basis | yes |
| A5 | "number **and type**" is supported, not just the count | |
| A6 | "blind" is defined by the institution, not by the analyst | yes |
| A7 | an absent change means "no change", not "not recorded" | |
| A8 | the measured lag is not clock skew wearing a lag's clothes | yes |
| A9 | the threshold declaration is documented enough to **be** evaluated | *neither* |

**A7 deserves its own sentence**, because it is the condition most likely to be
waved through. If the scope does not state what it is complete over, a missing
change event is ambiguous three ways: nothing happened, something happened and
was not recorded, or this basis was never in scope. Those are different facts,
and a measurement that treats them alike is measuring the record-keeping rather
than the institution. The schema therefore demands a closure statement, and
accepts `UNKNOWN` — which is not a defect, but does cap the claim.

**A9 is neither hard nor soft, and that is the point.** A6 asks who declared the
containment threshold; it cannot ask whether they had the standing to. A9 asks
for the materials a competent reviewer would need in order to judge that:
the asserted mandate, the procedure followed, the evidentiary basis, the review
conditions, and the conflict safeguards.

Passing A9 **establishes nothing about legitimacy.** It does not establish the
declarant's competence, does not validate the procedure, and does not make the
threshold legally sufficient for reliance. It establishes only that the
institutional claim is documented well enough to become evaluable by someone who
is competent to evaluate it. The condition's own text says so, in the code as
well as here, because a check named for authority that tests only form is exactly
the kind of thing that gets quoted later as though it had certified competence.

So failing A9 is **not invalidity**. The dataset is not defective; the question
cannot yet be asked. The checker returns a third verdict for it —
`INDETERMINATE_PENDING_COMPLETION` — and the cure is to supply the materials and
ask again.

**Two gates remain outside this test, and their being outside it is part of the
result rather than a gap in it.** *Competence*: whether the asserted mandate and
procedure are institutionally sufficient, and whether the resulting threshold may
govern this class of decisions at all. *Situated admissibility*: whether a
particular output may be relied upon for a particular use under the facts,
authority, jurisdiction, evidence and review conditions then in force. The first
conditions the second without determining it, and neither is computable.

The reason to keep them separate is not tidiness. The threshold governs a state
of the system; admissibility governs the permitted disposition of the resulting
output. Collapsing them would turn evidence of compliance into a certificate of
legitimate use — a system would report conformance while doing something it was
not entitled to do.

**A8 is the one that would embarrass us.** If clocks are unsynchronised and the
skew is larger than the smallest observed lag, then what the probe reports as a
lag may be an artefact of the clocks. The check compares the declared skew
against the smallest lag actually present, and refuses when they are not
separable.

## Custody

The probe should run **inside the custody of whoever holds the records**. Neither
the designer nor the implementer needs to see the data, and we would prefer not
to. `check_dataset.py` is written to be run by the record holder and to emit a
report that can be shared without the underlying records.

## What adequacy is not

It says the measurement can be computed from these records. It says nothing about
whether the result generalises beyond them, and nothing about permission to use
them. Both are decisions for the record holder and for counsel; neither is a
property of the data.

And one discipline that belongs here rather than in a later apology: **before any
real dataset is examined, the predictions and the refutation conditions get
written down and frozen** — including what result would refute the hypothesis.
The danger with a first real dataset is not measurement, it is that one dataset
gets read as a statement about institutions in general.

## Attribution

The experiment is **Arkadiy Miteiko's** design. The implementation and this
specification are **Vitaly Reznik's**. The legal research question — on what
basis a conclusion remains fit to be relied upon — is **Ignacio Adrián Lerer's**.
**Condition A9, its name, its three-way outcome, and the two gates it hands
outward are his design as well**, and are implemented here as he specified them.
Each contribution is separable, and none of them is a claim about the other two.

## Files

    currentness-events-v0.2.schema.json   the machine-readable input contract
    currentness-events-v0.1.schema.json   the previous version, left intact
    check_dataset.py                      the checks; accepts either version
    example-adequate.json                 a minimal v0.1 dataset that passes
    example-inadequate.json               the same one broken in two ways
    example-v02-documented.json           a v0.2 dataset whose threshold is documented
    example-v02-undocumented.json         the same one, indeterminate pending completion

AI disclosure: drafted with Claude Opus 5; every condition above is checked by
the accompanying code, and the code is the arbiter.
