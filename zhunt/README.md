# zhunt — the ZTL warranty hunter (save the catch, count the rest)

A search project, self-contained in this folder. It imports the ZTL core from
the parent directory (`ztl.py`, `zmodal.py`, `zverify.py`) and **never modifies
it**.

## The idea (two clean parts)

- **HUNTER *gives*.** It streams every distinct formula tree up to a node budget
  over N atoms, crossed with every marking `{T, F, mark}`. Decides nothing.
  Generated layer by layer, so the formula list is never fully materialised.
- **The CORE *judges*, exactly like the studio.** For each candidate the core
  (`ztl.ev` + the warranty grade from `zverify.py`) returns a value and a grade.

## Buckets

**SAVED** — one file only, written with WHY (`kill` = the refinement that flips
it, `depth` = how many marks must be verified first):

| file | grade | meaning | curator's words |
|---|---|---|---|
| `results/suspect.jsonl` | **sound, not hereditary** | a genuine classical law (a tautology when the value is T) that breaks ONLY under ZTL uncertainty — the fallen-lemma class | «как с той лемкой, вот почему» |

**COUNTED** — everything else, statistics only (bucket totals + depth histograms
in `summary.json`, never dumped):

| bucket | grade | why not saved |
|---|---|---|
| **dangerous** | until-verification, value T | NOT sound ⇒ it has a classical countermodel ⇒ **classical logic already refutes it**. Not unique to ZTL, so counted only. |
| clean | hereditary | never revoked. «всё ровно» |
| deny | until-verification, value F | a refusal now that verification would GRANT. Safe pessimism. |
| atom_z | value Z | a bare marked atom: the unverified datum itself. «Или Z» |

The point: **only `suspect` is broken *only* in ZTL.** Everything else is either
fine (clean), a safe refusal (deny), or already broken classically (dangerous).

`summary.json` keeps full bucket totals + depth histograms for every grade, so
the counted mass is never lost — only its line-by-line dump is.

## Run

    python3 zhunt.py --regression                        # pin to zverify's facts
    python3 zhunt.py --atoms a,b,c,d --max-nodes 8       # a quick slice
    tail -f results/progress.log

The night run (reaches depth-4, only 5+ atoms can): billions of pairs, ~2–3 h,
DP table ~1 GB, catch stays small at depth ≥ 3:

    python3 zhunt.py --atoms a,b,c,d,e --max-nodes 9 --cores 30 --save-min-depth 3

`depth = m − 1` is the deepest a break can hide over `m` marks (zverify §6), so
depth-4 needs ≥5 atoms — that is why the night run adds the fifth.

## Depth is the prize

`depth ≥ 2` = survives every single verification, breaks only on a combination.
That is the fallen-lemma phenomenon: a law that fools any one-at-a-time check.
The `results/` dump is git-ignored (reproducible); the code is the artifact.
