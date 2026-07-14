# The broken-law catalogue — what the ZTL hunter actually found

The distilled result of the overnight hunt (2026-07-14). The raw corpus
(`results/suspect.jsonl`, 2.76M records, 364 MB) is reproducible and
git-ignored; this file is the выжимка.

## The run

5 atoms, formulas ≤ 9 nodes, every marking — **1,963,653,285 candidate
pairs** judged by the ZTL core in 1 h 47 m (30 cores).

| bucket | count | meaning |
|---|---:|---|
| clean (hereditary) | 1,040,209,120 | never revoked — «всё ровно» |
| **suspect (sound, not hereditary)** | **2,756,520** | **a classical tautology broken ONLY under ZTL** |
| dangerous (T-until-verification) | 277,374,535 | classically refutable already (has a countermodel) |
| deny (F-until-verification) | 643,313,105 | a refusal verification would grant |
| atom_z | 5 | the bare unverified atoms |

Only `suspect` is unique to ZTL. Its depth histogram (marks that must be
verified before the break shows):

    depth 1: 2,576,820      depth 2: 177,540      depth 3: 2,160

No depth-4 suspect appears: a 5-mark sound guard needs `(b∧c∧d∧e)→(a→a)` = 11
nodes, beyond the ≤9 budget. So the deepest hiders here survive **two** checks.

## The sift

The 2.76M records, filtered to v=T & depth ≥ 2 and canonicalised by atom
renaming, collapse to **1,341 distinct laws**. Every one reduces to **three
mechanisms** — and all three are the classic constructivist targets:

| # | skeleton | example (with the verification that kills it) | max depth | what it is |
|---|---|---|---:|---|
| 1 | **guarded identity** `G → (a→a)` | `(a ∧ (b↔c)) → (d→d)` — kill `a=T, b=T` | 3 | a vacuous identity hidden behind a guard |
| 2 | **guarded weakening** `a → (G → a)` | `a → (((b⊕c)∧d) → a)` — kill `c=F, d=T` | 3 | re-deriving the premise from itself |
| 3 | **guarded excluded-middle** `(G→c) ∨ ¬c`, `a ∨ (G→¬a)` | `((a∧b)→c) ∨ ¬c` — kill `b=T, c=T` | 2 | LEM / material implication on one atom |

Family sizes among the 1,341: identity-gap **706**, LEM/material **552**,
weakening **83**.

**The deepest class (depth 3, survives two checks) is only #1 and #2** — 2,160
laws, all 9-node. The LEM family (#3) never gets past depth 2.

## The honest verdict

**No new class of "law that crept into mathematics."** Every ZTL-fragile
tautology at depth ≥ 2, up to renaming and packaging, is one of *identity*,
*weakening*, or *excluded middle* — exactly the three patterns constructivism
(Brouwer, Bishop) has flagged for a century. The diamond is, in the main, the
known stone — precisely re-cut and machine-confirmed at scale.

**What is genuinely ZTL's own** is not a broken law but a *measure*: a
known-broken pattern can be **guarded to survive `k` verifications** — the fence
depth is `(#marks − 1)` (zverify §6). "How many one-at-a-time checks a vacuous
or circular lemma can pass before it is exposed" is a ZTL quantity; classical
constructivism does not state it.

So the result is a solid **negative** one plus one own metric: *within ≤9
nodes, ZTL-fragile classical tautologies are exhausted by three constructive
mechanisms, and their masking depth is exactly measured.* Not a sensation — an
honest census.

*Method: `zhunt.py` (hunter → core) + `sift.py` (canonical-law catalogue).
Reproduce the run with `python3 zhunt.py --atoms a,b,c,d,e --max-nodes 9`.*
