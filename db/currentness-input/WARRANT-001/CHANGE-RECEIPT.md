# Change receipt — ADMISSIBILITY-CONSEQUENCE BOUNDED WARRANT 001

**What changed.** In `measure.py`, the emitted record carried
`"admissibility_consequence": None` plus a prose `admissibility_note`. It now
carries a typed `admissibility_determination` and **no** consequence field.

**Why.** A field present with `null` is still *carried* by the record, and `null`
is ambiguous four ways at once — not computed, not applicable, false, absent.
Arkadiy demonstrated this to me earlier; my own corpus records that I had cited
this exact construction as an example of *compliance* and that the assessment was
withdrawn. The warrant prohibits both `null` and a manufactured consequence used
to encode a refusal.

**Under whose authority.** Arkadiy Miteiko, artifact owner,
`ADMISSIBILITY-CONSEQUENCE BOUNDED IMPLEMENTATION WARRANT — 001`, 2026-08-29.

**Which frozen reference governed.** Temporal Typing and Institutional Interval
Selection v0.6 non-drift boundary. Not modified; not touched.

## The case, named

The admissibility question **arises** — these acts may or may not be relied upon —
and **cannot presently be answered**, because no institutional authority is
supplied to this layer. That is the warrant's **case B**.

## A fork I announced and then withdrew

I first reported to the curator that the warrant leaves open whether the
`admissibility_consequence` key may be dropped. **On rereading the warrant whole,
it does not.** Two clauses close it together: the refusal must sit *"outside the
target-plane result itself"*, and the implementation *"must not manufacture an
admissibility consequence merely to encode refusal"*. A refusal token written into
the consequence slot violates both. So the key is absent and the refusal has its
own field.

I record the withdrawal rather than quietly dropping it: I inflated a fork by
reading one clause at a time.

## What made the omission legal — and what had to be built for it

The warrant permits omission only where **a schema declares the field
conditional**. There was no schema to declare it in: `currentness-events-v0.1` and
`v0.2` describe the **input** event dataset; the **output** record had none.

So `currentness-record-v0.3.schema.json` was created. It declares
`admissibility_consequence` conditional, forbids `null` for it explicitly, and
makes `admissibility_determination` required. This is the minimum schema change
strictly necessary; nothing else was added.

**This is itself a finding.** The warrant's mechanism for making an absence
readable presupposed an artifact that did not exist.

## Record-by-record partition

One record class is emitted by this layer, and every record of it falls in case B
for the same structural reason — the layer has no authority to compute a
consequence, ever, not merely today.

| record | treatment | justification |
|---|---|---|
| `CURRENTNESS_EPISTEMIC_CLASSIFICATION` (every instance) | **B — typed refusal** | question arises; unanswerable at this layer by construction, not by accident |

No record was found that fits neither treatment, so warrant §6.1 did not trigger.

## Verification (§4) — consumer-side, not only schema-side

`consumer_check.py`, output in `evidence/consumer-output.txt`. **9 checks, 0 failures.**

Four institutionally distinct situations are separately recognised downstream:

| situation | recognised state | disposition |
|---|---|---|
| typed refusal (after) | `REFUSED_NO_WARRANT` | `HOLD_PENDING_WARRANT` |
| the old `null` (before) | `UNREADABLE` | `REJECT_RECORD` |
| omission, field conditional | `OMITTED_NOT_APPLICABLE` | `PROCEED_WITHOUT` |
| omission, field mandatory | `UNREADABLE` | `REJECT_RECORD` |
| false | `FALSE_NOT_ADMISSIBLE` | `DENY` |
| genuine consequence | `CONSEQUENCE_PRESENT` | `APPLY` |

No operational collapse: the four institutions the warrant names are four distinct
recognised states.

**Two controls, because a battery of only must-differ cases is satisfied by a
consumer that differentiates everything:**

- the untouched part of the record survives the change with **zero** changes
  (14 fields compared field by field) — warrant §3.7;
- two identical records receive the identical state, so the consumer does not
  manufacture distinctions.

## Digests

    BEFORE  measure.py                        7772f76e8bb092e6…
    AFTER   measure_v03.py                    3a7464a4feac96d4…
            currentness-record-v0.3.schema.json b3bb34f7e4531602…
            record-AFTER.json                 379c44c5960233a1…
            consumer_check.py                 b2d66db9d3f32ebd…

Full lists in `evidence/BEFORE.sha256` and `evidence/AFTER.sha256`.
The preserved artifact is `evidence/measure-PRESERVED-v0.2.py`, byte-unchanged.

## Stopping conditions (§6) — none triggered

No record fitted neither treatment; scope stayed within
`admissibility_consequence` plus the minimum schema and consumer work; no frozen
invariant was touched; no consumer collapses the four states; the control record
did not change; the circulated artifact is preserved; and no institutional or
legal determination was required of me — the whole point of the typed refusal is
that this layer declines to make one.

## Ceiling

This establishes that **this** layer's record now distinguishes refusal from
omission, falsity and non-computation to **this** consumer, on these digests. It
establishes nothing about other producers, other consumers, or whether the
completion condition named in the refusal is the institutionally correct one.

`independent_review_claim = FALSE`.
