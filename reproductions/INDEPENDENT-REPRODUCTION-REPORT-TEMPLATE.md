# Independent reproduction report — TEMPLATE

Copy this file to `INDEPENDENT-REPRODUCTION-REPORT-0NN.md` (next free
number), fill every field, and submit it (pull request, or send it to the
author to commit verbatim). Leave a field blank only if it genuinely does
not apply, and say so rather than deleting it. Raw output beats a summary:
paste what you actually saw.

The instructions you followed are in [`../REPRODUCE.md`](../REPRODUCE.md).
See [`README.md`](README.md) for how much a report counts (independence
tiers) and why the first independent report should be Tier 1.

---

- **report number**:
- **identity** (real name, or a stable pseudonym you will answer to):
- **relationship disclosure** — your connection, if any, to ZTL, Veraxis,
  the author (Vitaly Reznik), or A. Miteiko. Write "none" only if there is
  none. State if you received any instruction beyond the public
  `REPRODUCE.md`.
- **self-assessed tier** (1 / 2 / 3 — see `README.md`):
- **exact OS** (name and version):
- **browser** (name + version) **and/or terminal / shell**:
- **Lean version** (as reported by the tool you used):
- **commit reproduced** (the SHA you actually checked out or whose blob
  links you opened; the document pins `82a0f6a`):
- **date / time** (with timezone):
- **path taken**: Path A (browser only) / Path B (full terminal run) / both

## Path A result (if run)

| file | lines expected | lines you saw saying "does not depend on any axioms" | any line NOT saying that? | any red error? |
|---|---:|---:|---|---|
| ZTL.lean | 13 | | | |
| QuantumWitness.lean | 11 | | | |
| Contextuality.lean | 3 | | | |
| JunctionWitness.lean | 8 | | | |
| ZTime.lean | 7 | | | |
| EpochBoundary.lean | 5 | | | |

## Path B result (if run)

Expected final lines:

```
ALL GREEN: 59 stands + Lean.
ALL CLEAN: 371 theorems across 21 modules, every one on the empty axiom list.
PAPER CLAIMS GREEN — every numeric claim checked matches a measurement taken now.
```

What you actually saw (paste the final lines and any FAIL):

```
(paste here)
```

## Deviations

Anything that differed from the stated expectations — different counts, a
step that failed, an instruction that was unclear, a message you could not
interpret, time that ran much longer than stated. "None" is a valid answer.

## Raw console output

Paste the relevant raw output (or attach it). For Path A, the tail of the
InfoView. For Path B, the tails of `run_all.py`, `axiom_audit.py`,
`paper_claims.py`.

```
(paste here)
```

## Verdict

Exactly one:

- [ ] **reproduced** — every stated command produced the stated output
- [ ] **reproduced with deviations** — the substance held, but see Deviations
- [ ] **failed** — a stated command did not produce the stated output (describe)

---

*This report certifies one thing only: that the stated commands produced the
stated output on a machine that is not the author's. It does not certify that
the theorems are the right theorems or that the work is any good — that is a
different task for a logician.*
