# Interval-sensitivity experiment — predeclared before the run

**v0.1, 2026-08-20, frozen before any result was seen.** Everything below was
written first; the run comes after. A change gets a new version and a new hash.

## What is being measured, and what is NOT

Adrián Lerer's analysis holds that the five temporalities are not interchangeable
timestamps, and therefore that the stale window has no single legally correct
definition independent of the proposition being tested. This experiment measures
**how much the classification of acts changes when the interval definition
changes**, on one evidence universe.

Arkadiy Miteiko's boundary, adopted verbatim as a constraint on the output:

> The experiment may measure how classification changes under alternative
> predeclared interval definitions, but it must not infer from either divergence
> or convergence which interval is institutionally correct, whether
> authorization is necessary, or what disposition follows.

So the run yields a number and stops. It does not select an interval, does not
argue that a declaration requirement is warranted, and does not attach a
consequence to any classification. Those are questions of warrant and
admissibility and are outside this instrument.

And the two directions are not symmetric in what they license:

- **divergence** demonstrates that a hidden interval selection is consequential;
- **convergence** shows only that it was not consequential **in this evidence
  universe** — never that interval choice does not matter.

## The evidence universe

The emitted dataset from `emit_dataset.py` at `lag = 5`, `drift = 20`,
`rate = 10`, seed 20260816: 200 steps, 20 000 subjects, 5 sources, 4 000 changes,
2 000 acts. Synthetic throughout.

**The receipt timestamp in it is invented and is declared as invented.** The
simulation never had one. It is emitted at `effective_at + 2`, strictly between
effectiveness and recording, so that two intervals exist to compare at all.
Nothing here is a claim about when real institutions receive notice.

## The two predeclared interval definitions

    A  NORMATIVE CURRENTNESS
       opens   when the change became effective
       closes  when the change was incorporated into the operative record
       (in this dataset: effective_at -> recorded_at)

    B  RESPONSE DUTY
       opens   when the change was received by the institution
       closes  when it was incorporated into the operative record
       (in this dataset: received_at -> recorded_at)

B is a subinterval of A by construction here. That is a property of this
synthetic world, not a general relation between the two propositions: in real
records an institution may receive notice before a change becomes effective,
which would make them overlap without nesting.

## Treatment of the unresolved state

Declared uncertainty is **zero** for this run, so under each definition
separately every act is either certainly inside or certainly outside and none is
unresolved. The comparison is therefore between two complete classifications and
is not confounded by unresolved acts. An act that changes state between A and B
is counted as a change; it is not reported as unresolved, because under each
definition taken alone it is settled.

## The comparison metric

Two numbers, both fixed now:

    M1  the share of acts assigned a different state under B than under A
    M2  the relative change in the count of acts certainly inside the window,
        |inside_B - inside_A| / inside_A

## The material-divergence condition

Declared before the run so that it cannot be chosen afterwards:

    MATERIAL if M1 >= 0.05 or M2 >= 0.10
    NOT MATERIAL otherwise

There is no third outcome and no interpretation clause. If the run lands just
under the line, it is not material and will be reported as not material.

## What would make this experiment worthless

Stated in advance, in the same spirit: if the invented receipt offset were the
only thing driving the divergence, the result would be an artefact of my choice
of offset rather than a property of interval selection. The run therefore repeats
at three offsets (1, 2, 3) and reports all three. If the verdict flips between
them, that is reported as instability rather than smoothed into a headline.
