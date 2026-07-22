# Independent reproductions

This directory holds versioned independent reproduction reports for the ZTL
artifact. Each is a copy of
[`INDEPENDENT-REPRODUCTION-REPORT-TEMPLATE.md`](INDEPENDENT-REPRODUCTION-REPORT-TEMPLATE.md),
filled and committed verbatim, named
`INDEPENDENT-REPRODUCTION-REPORT-0NN.md`. The reproduction instructions
themselves are in [`../REPRODUCE.md`](../REPRODUCE.md).

The purpose is to turn reproduction from a one-off letter into a research
artifact that can be pointed at, versioned, and counted.

## How much a reproduction counts — independence tiers

A reproduction is a **mechanical** check: it confirms that the stated
commands produce the stated output on a machine that is not the author's.
Disclosing a relationship makes a report *honest*; it does not make it
*weightier*. Evidential weight comes from **arm's length** — from the
reproducer having no stake in the outcome.

- **Tier 1 — maximal weight.** An engineer or researcher with no prior
  connection to ZTL or Veraxis, who received nothing beyond the public
  `REPRODUCE.md`.
- **Tier 2.** An acquaintance who discloses the connection and did not take
  part in development.
- **Tier 3.** The author's own self-check, and checks by family or
  co-authors.

All three are useful; only **Tier 1** strengthens external conviction.

**The first independent report must be Tier 1.** It must NOT come from a
relative, a spouse, a co-author, anyone who took part in development, or
anyone who received instructions beyond the public `REPRODUCE.md`. (The
author's green self-check on 2026-07-21 is explicitly **Tier 3** and is not
recorded here as an independent reproduction.)

## Target set

Reproducibility matures with independent, diverse confirmations:

1. **#001** — an unconnected engineer. Requirements: no prior connection to
   ZTL, Veraxis, or the authors; given only the public `REPRODUCE.md`; runs
   the **full terminal Path B** on a clean machine or VM (Path B is what
   exercises the whole stand suite, the full axiom audit, and the paper-claims
   measurement — Path A may be done additionally, but the first weighty report
   must include Path B); returns the **raw output regardless of result**; if
   paid, paid **for time, not for a green result**. Records `target_commit`
   and `recipe_blob` (see the template) plus OS, Lean version, exact commands,
   and any deviation.
2. **#002** — a different engineer, on a different OS.
3. **#003** — a Lean / formal-methods specialist.

A failed or partially-successful reproduction is as useful as a clean one — the
report certifies execution reproducibility only, never mathematical
correctness, significance, or correspondence between the formal statements and
the prose.

## The claim ladder

What may honestly be said scales with what has actually happened:

- With the recipe alone: *"the author provided a reproduction recipe, and
  self-checked it."*
- After **three** successful **Tier 1** reproductions: *"independent parties
  reproduced the claimed computational results, using the published recipe,
  without author involvement."*

No claim may run ahead of the reports in this directory. This is the same
governing principle as everywhere else in the programme: no external claim
should be stronger than the artifact supporting it.

## Submitting a report

1. Copy the template to the next free `INDEPENDENT-REPRODUCTION-REPORT-0NN.md`.
2. Fill every field; paste raw output rather than summarising.
3. Open a pull request, or send it to the author to commit verbatim.
