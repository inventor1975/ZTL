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

## Path A — browser only, about 10 minutes, nothing installed

The Lean files below have **no imports and no library dependencies**.
They can be pasted into Lean's official web editor and will compile
there.

The links are pinned to commit `82a0f6a` so the counts in the table
below match exactly. A newer state of the repository will show larger
counts — that is the corpus growing, not a failure; reproduce this
commit to match this document.

1. Open **https://live.lean-lang.org**
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
| ZTL.lean | 14 | | |
| QuantumWitness.lean | 11 | | |
| Contextuality.lean | 3 | | |
| JunctionWitness.lean | 8 | | |
| ZTime.lean | 8 | | |
| EpochBoundary.lean | 6 | | |

The counts matter less than the two questions after them. **A single
line that says anything other than "does not depend on any axioms", or
any red error marker, is a finding — please report it exactly as shown.**

That is the whole of Path A. Nothing is installed, nothing is trusted:
the checking is done by Lean's own kernel, running in your browser, on a
server that has nothing to do with this project.

---

## Path B — full run, needs a terminal (optional)

Only if you are comfortable at a command line. Needs `git`, `python3`,
and Lean (via `elan`).

```bash
git clone https://github.com/inventor1975/ZTL
cd ZTL
git checkout 82a0f6ac61e0ddf9a927a70e04a0018989ef316d   # the documented state
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # installs Lean
cd lean && lake build && cd ..
python3 run_all.py
python3 inventory/axiom_audit.py
python3 inventory/paper_claims.py
```

**Expected final lines:**

```
ALL GREEN: 59 stands + Lean.
ALL CLEAN: 371 theorems across 21 modules, every one on the empty axiom list.
PAPER CLAIMS GREEN — every numeric claim checked matches a measurement taken now.
```

Note the counts (59, 371, 21) as you see them. The `git checkout` above
pins the repository to the state these numbers were taken from; if you skip
it and run the moving tip instead, larger counts are expected and are worth
recording rather than a failure.

`run_all.py` takes a few minutes. If a stand fails it prints `FAIL` with
the name; that line is the finding.

---

## What to send back

Whatever you actually saw, including anything confusing. A reproduction
report is more useful when it records the friction — an instruction that
was unclear, a step that took much longer than stated, a message you
could not interpret — than when it is a clean "worked fine". The
instructions are as much on trial as the code.

A template, to be edited freely:

> On [date] I followed [Path A / Path B] on [OS, browser or terminal].
> I ran [what], and saw [what]. Deviations from the stated expectations:
> [list, or "none"]. Difficulties: [list, or "none"].
> — [name]

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
