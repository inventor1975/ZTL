# zhunt — the ZTL warranty hunter (corpus saved)

A search project, self-contained in this folder. It imports the ZTL core from
the parent directory (`ztl.py`, `zmodal.py`, `zverify.py`) and **never modifies
it**.

## The idea (two clean parts)

- **HUNTER *gives*.** `gen_formulas` enumerates every distinct formula tree up
  to a node budget over N atoms, and crosses each with every marking
  `{T, F, mark}`. It decides nothing.
- **The CORE *judges*, exactly like the studio.** For each candidate the core
  (`ztl.ev` + the warranty grade from `zverify.py`) returns a value (T/F) and a
  warranty **grade**. Everything caught is written to disk — nothing dropped.

The overnight hunt of 2026-07-12 streamed ~151.8M pairs, asserted, and **threw
the list away** — only counts and one trophy survived. Its exact enumeration
parameters were not saved and cannot be reproduced to the digit; this project
uses a **clean, stated** enumeration instead and reports its real size.

## The three files (by warranty grade)

| `results/…` | grade | meaning | curator's words |
|---|---|---|---|
| `clean.jsonl` | **hereditary** | verdict never revoked under any verification | «всё ровно» |
| `suspect.jsonl` | **sound, not hereditary** | honest in every completion, yet a hidden break exists — the `kill` field says why | «как с той лемкой, вот почему» |
| `unverified.jsonl` | **until-verification** | alive only until the first check, then flips | «не проверено, на всякий случай» |

Each line: `{f, m, v, g}` plus `kill` + `depth` when it breaks. `depth` = how
many marks must be verified before the break shows — **depth ≥ 2 = survives
every single check, dies only on a combination** (the fallen-lemma class).

## Run

    python3 zhunt.py --max-nodes 8 --cores 30      # ~36M pairs, ~2 min
    python3 zhunt.py --regression                  # pin to zverify's facts
    tail -f results/progress.log

`--max-nodes` scales the hunt: ≤7 = 5.2M pairs, ≤8 = 35.8M, ≤9 = 481M (the last
needs a streaming refactor — 15M formulas won't fit in memory as a list).

## Result of the ≤8 run (2026-07-14, MEASURED)

35,788,896 pairs in 104s on 30 cores:

- **clean**: 19,866,136
- **suspect**: 47,280 — of which **depth 1: 45,072**, **depth 2: 2,208**
  (survive every single verification, die only on a pair)
- **unverified**: 15,875,480

A depth-2 exhibit: `a → ((b∧c) → a)` — value T at all marks, invariant under
every single verification, killed only by `b=T, c=T`.

The `results/` dump is git-ignored (GBs, reproducible); the code is the artifact.
