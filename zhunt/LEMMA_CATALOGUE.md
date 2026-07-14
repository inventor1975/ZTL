# The broken-law catalogue — what the ZTL hunter actually found

The distilled result of the overnight hunt (2026-07-14), **corrected** after a
rigorous intuitionistic check. The raw corpus (`results/suspect.jsonl`, 2.76M
records, 364 MB) is reproducible and git-ignored; this file is the выжимка.

## The run

5 atoms, formulas ≤ 9 nodes, every marking — **1,963,653,285 candidate pairs**
judged by the ZTL core in 1 h 47 m (30 cores).

| bucket | count | meaning |
|---|---:|---|
| clean (hereditary) | 1,040,209,120 | never revoked — «всё ровно» |
| **suspect (sound, not hereditary)** | **2,756,520** | **a classical tautology broken ONLY under ZTL** |
| dangerous (T-until-verification) | 277,374,535 | classically refutable already (has a countermodel) |
| deny (F-until-verification) | 643,313,105 | a refusal verification would grant |
| atom_z | 5 | the bare unverified atoms |

`suspect` depth histogram (marks that must be verified before the break shows):

    depth 1: 2,576,820      depth 2: 177,540      depth 3: 2,160

No depth-4 suspect: a 5-mark sound guard needs 11 nodes, beyond the ≤9 budget.
The deepest hiders here survive **two** checks.

## The sift + the intuitionistic test

The 2.76M records, filtered to v=T & depth ≥ 2 and canonicalised by atom
renaming, collapse to **1,341 distinct laws**. Each was then run through a real
IPC decision procedure (`zipc.ipc_valid`, Dyckhoff G4ip) to ask the decisive
question: *is this a law that intuitionistic logic also keeps?*

| | count | depth 2 | depth 3 |
|---|---:|---:|---:|
| **IPC-VALID — broken ONLY by ZTL (beyond constructivism)** | **817** | 799 | **18** |
| IPC-invalid — the constructivist overlap (excluded middle) | 524 | 524 | 0 |

**61% of the catalogue, and 100% of the deepest laws, are accepted by BOTH
classical and intuitionistic logic — and refused only by ZTL.**

## The three skeletons

| # | skeleton | example (with the kill) | IPC | what it is |
|---|---|---|---|---|
| 1 | **guarded identity** `G → (a→a)` | `(a ∧ (b↔c)) → (d→d)` — kill `a=T, b=T` | **valid → ZTL-unique** | a vacuous identity behind a guard |
| 2 | **guarded weakening** `a → (G → a)` | `a → (((b⊕c)∧d) → a)` — kill `c=F, d=T` | **valid → ZTL-unique** | re-deriving the premise from itself |
| 3 | **guarded excluded-middle** `(G→c) ∨ ¬c` | `((a∧b)→c) ∨ ¬c` — kill `b=T, c=T` | invalid → constructivist | LEM / material implication |

Families 1–2 are the 817 ZTL-unique laws; family 3 is the 524 constructivist
overlap. The deepest class (depth 3, survives two checks) is entirely #1 and #2.

## The honest verdict (corrected)

A first, structural reading said "all three are the classic constructivist
targets — nothing new." **That was wrong.** Identity and weakening are theorems
of intuitionistic logic; a constructivist keeps them. The rigorous IPC test
shows the opposite of the first verdict: **the majority of ZTL-fragile
tautologies — and every one of the deepest — are laws that classical AND
intuitionistic logic both accept, and only ZTL refuses.**

This is the concrete, measured content of **ZTL ⊥ IPC** (the two logics are
incomparable, established earlier as E20): here are 817 distinct witnesses of
the direction "ZTL strictly refuses what intuitionism grants," at ≤9 nodes,
with their exact masking depth. These are not hidden bugs in real theorems —
they are the universally-used inferences (identity, weakening) that ZTL's
zero-trust discipline uniquely denies on *unverified* inputs. That denial is
the philosophical core of ZTL — now a census, not a slogan.

The one quantity that is ZTL's alone throughout: the **fence depth** — a
known-shape law can be guarded to survive `(#marks − 1)` verifications
(zverify §6). "How many one-at-a-time checks a credit-dependent inference passes
before exposure" is measured here for the first time at scale.

*Method: `zhunt.py` (hunter → core) + `sift.py` (canonical catalogue) +
`zipc.ipc_valid` (the intuitionistic screen). Reproduce with
`python3 zhunt.py --atoms a,b,c,d,e --max-nodes 9`.*
