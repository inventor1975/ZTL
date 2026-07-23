# Independent reproduction — instructions

You have been asked to check that this repository does what it says. You
need no knowledge of logic, and you are not being asked to judge whether
the mathematics is interesting or correct. **You are checking one thing:
that the stated commands produce the stated output on a machine that is
not the author's.**

That is a real and useful thing to establish, and it is deliberately
small. Please do not sign anything broader.

---

## What this does and does not establish

**Does:** the artifact runs; the instructions are complete enough for
someone outside the project to follow; the numbers printed here match
the numbers claimed in the papers.

**Does not:** that the theorems are the right theorems, that the formal
statements say what the prose says they say, or that the work is any
good. Those need a logician and are somebody else's task.

---

**Start with Path A — it needs nothing installed and IS the real check. Path B
is a heavier optional cross-check, only for people who want the full terminal
build. (A skilled admin who jumps straight to a terminal can trip on Path B's
toolchain install and miss that Path A was the easy, sufficient route.)**

## Path A — browser only, about 10 minutes, nothing installed

The Lean files below have **no imports and no library dependencies**.
They can be pasted into Lean's official web editor and will compile
there.

The links are pinned to commit `82a0f6a` so the counts in the table
below match exactly. A newer state of the repository will show larger
counts — that is the corpus growing, not a failure; reproduce this
commit to match this document.

The web editor may offer a newer Lean than the `v4.29.1` this repository
pins (pick any version in its dropdown — these files have no imports, so
they compile against Lean core alone). If it compiles without a red error,
the `does not depend on any axioms` lines are what matter; that result does
not hinge on the exact version. To reproduce against the paper's exact
toolchain instead, use Path B, where `elan` installs `v4.29.1` for you.

1. Open **https://live.lean-lang.org** (if it shows a version chooser first,
   pick any entry — the default is fine — to reach the editor).
2. Open one of these files on GitHub, click the "copy raw file" button:
   - https://github.com/inventor1975/ZTL/blob/82a0f6ac61e0ddf9a927a70e04a0018989ef316d/lean/ZTL.lean
   - https://github.com/inventor1975/ZTL/blob/82a0f6ac61e0ddf9a927a70e04a0018989ef316d/lean/QuantumWitness.lean
   - https://github.com/inventor1975/ZTL/blob/82a0f6ac61e0ddf9a927a70e04a0018989ef316d/lean/Contextuality.lean
   - https://github.com/inventor1975/ZTL/blob/82a0f6ac61e0ddf9a927a70e04a0018989ef316d/lean/JunctionWitness.lean
   - https://github.com/inventor1975/ZTL/blob/82a0f6ac61e0ddf9a927a70e04a0018989ef316d/lean/ZTime.lean
   - https://github.com/inventor1975/ZTL/blob/82a0f6ac61e0ddf9a927a70e04a0018989ef316d/lean/EpochBoundary.lean
3. Paste it into the editor, replacing whatever is there. Wait for the
   right-hand panel to finish (a few seconds; a spinner or "Processing"
   may show first).
4. Scroll the right-hand panel to the bottom.

**What you should see.** A block of lines, each of the form

```
'SomeName' does not depend on any axioms
```

**What to record for each file:**

| file | lines expected | any line NOT saying "does not depend on any axioms"? | any red error? |
|---|---:|---|---|
| ZTL.lean | 13 | | |
| QuantumWitness.lean | 11 | | |
| Contextuality.lean | 3 | | |
| JunctionWitness.lean | 8 | | |
| ZTime.lean | 7 | | |
| EpochBoundary.lean | 5 | | |

The counts matter less than the two questions after them. **A single
line that says anything other than "does not depend on any axioms", or
any red error marker, is a finding — please report it exactly as shown.**

That is the whole of Path A. Nothing is installed, nothing is trusted:
the checking is done by Lean's own kernel, running in your browser, on a
server that has nothing to do with this project.

---

## Path B — full run, needs a terminal (optional)

Only if you are comfortable at a command line (Mac/Linux; on Windows use WSL).

**Copy and paste the whole block at once** — it does everything itself:

```bash
git clone https://github.com/inventor1975/ZTL &&
cd ZTL &&
git checkout 82a0f6ac61e0ddf9a927a70e04a0018989ef316d &&
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y &&
source "$HOME/.elan/env" &&
(cd lean && lake build) &&
python3 run_all.py &&
python3 inventory/axiom_audit.py &&
python3 inventory/paper_claims.py &&
echo "
============================================================
  ✅ REPRODUCED — everything matched.  59 stands / 371 theorems / 21 modules.
  Copy THIS line into your report — you are done.
============================================================"
```

Installing Lean can take a few minutes — that is normal, and `run_all.py` prints
a `N/59 stands finished…` counter so you can see it is working, not stuck.

**You will see a lot of technical output — that is the evidence; you do not need
to read it.** You only need the **very last line**:

- if it says **✅ REPRODUCED** with the numbers **59 / 371 / 21** — it matched;
  copy that line into your report and you are done;
- if that line **does not appear** (or you see `FAIL` or red anywhere) — that is
  the finding: copy the last lines of the terminal into your report.

(The `git checkout` pins the exact documented state; if you skip it and run the
moving tip, larger counts are expected and worth recording, not a failure.)

---

## What to send back

Whatever you actually saw, including anything confusing. A reproduction
report is more useful when it records the friction — an instruction that
was unclear, a step that took much longer than stated, a message you
could not interpret — than when it is a clean "worked fine". The
instructions are as much on trial as the code.

Please file your report as a copy of
[`reproductions/INDEPENDENT-REPRODUCTION-REPORT-TEMPLATE.md`](reproductions/INDEPENDENT-REPRODUCTION-REPORT-TEMPLATE.md)
— a fixed structure (identity, relationship, OS, versions, commit, raw
output, verdict) so reproductions accumulate as a versioned record rather
than scattered emails. A quick note is also fine if that is all you have time for — just fill these in:

```
My connection to the ZTL / Veraxis project:  none  (or: acquaintance / relative / colleague)
Date:
OS:                                (e.g. Ubuntu 24.04 / Windows 11 + WSL / macOS)
Path:  A (browser)  or  B (terminal)
Saw the "✅ REPRODUCED" line and the numbers 59 / 371 / 21?   yes  /  no (then: what you saw)
Anything different from what the instructions promised?       no  /  describe
Where was it hard or confusing?                               no  /  describe
Name or handle (a real name gives the report more weight):
```

---

## How much your reproduction counts (independence tiers)

Disclosing a relationship makes a report honest; it does not make it carry
more weight. Weight comes from **arm's length**. Reports are graded:
**Tier 1** — a reproducer with no prior connection to ZTL or Veraxis (maximal
weight); **Tier 2** — a disclosed acquaintance who did not take part in
development; **Tier 3** — the author's self-check, or checks by family or
co-authors. All are useful, but only Tier 1 strengthens external conviction,
and **the first independent report should be Tier 1**. The full policy and
the target set are in [`reproductions/README.md`](reproductions/README.md).

---

## Please state the relationship

If you are connected to anyone working on this project — related,
married, employed, or friends — **say so in the report**. It costs
nothing here: this test is mechanical, you are reporting what a compiler
printed, and there is no room for judgement to bend. But a reproduction
whose provenance is discovered later reads as concealed, while the same
reproduction with the relationship stated in the first line reads as
exactly what it is.

The governing principle of the programme this belongs to is that no
external claim should be stronger than the artifact supporting it. A
disclosed relationship keeps the claim honest; an undisclosed one makes
every other claim in the record suspect.
