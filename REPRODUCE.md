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

## How to reproduce — one terminal command

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
