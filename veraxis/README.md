# `veraxis/` — downstream integration artifacts

Everything in this directory exists because a **consumer** asked for it. None of it is part
of the logic. ZTL is a logic with a machine-checked corpus and a preprint; this folder is the
paperwork one particular integration requires, kept here so it does not clutter the project.

**Consumer:** Veraxis / Open Institutional Compiler (TDD-OIC-001), where ZTL is module M6,
the dependency and warrant engine.

## Contents

| File | What it is |
|---|---|
| `VERAXIS-ZTL-CONFORMANCE-input-v0.1.md` | 28 declarations of the agreed subset, 13 fields each, with per-declaration claim ceilings |
| `VERAXIS-ZTL-fixtures-v0.1.json` | 28 typed fixtures across 8 `subject_kind`s |
| `VERAXIS-ZTL-deps-v0.1.json` | transitive dependency closure from the Lean kernel — 826 edges over 169 corpus objects, no mathlib leakage |
| `VERAXIS-ZTL-DOSSIER-v0.1.md` | dependency verification dossier (13 fields required by the consumer) |
| `oic_fixtures.py` | generates the consumer's conformance fixtures from **live kernel runs**, and marks unreachable states `NOT_REACHABLE` instead of inventing them |

## The pins are not affected by this move

The frozen references point at commits, not paths:

| Tag | Commit | Note |
|---|---|---|
| `veraxis-ztl-input-v0.1` | `e819dec` | annotated; **accepted upstream 2026-07-21 and never rewritten** |
| `veraxis-ztl-input-v0.1.1-signed` | `e819dec` | GPG-signed provenance for the same commit |

At `e819dec` these files sit in the repository **root**. That snapshot is immutable and remains
valid; the relocation applies to `master` going forward. A consumer pinning the tag sees the old
layout and is unaffected. A consumer following `master` finds them here.

Artifact digests are unchanged by the move:

```
33de416110be748a647216ef97b246e925b2dcde95e95cbefdd13cf51f69bb8c  VERAXIS-ZTL-CONFORMANCE-input-v0.1.md
717853cf2a84ede0cb0472192d2e4fac4303acf29775f0d41d972e15c3652f93  VERAXIS-ZTL-fixtures-v0.1.json
efe05b396cdb4a8731f51b5cc927a8fc998e01a789a2a6dff5657e5a2b5971a5  VERAXIS-ZTL-deps-v0.1.json
```

## Boundary — worth restating, since this folder is where it gets forgotten

ZTL judges **logic over supplied grounds**. It does not validate source authenticity, determine
authority, interpret prose, create institutional admission, or decide ALLOW/DENY. Those belong to
the consumer. Nothing in this directory extends the logic; it only describes it to an integrator.

The logic itself lives in `ztl.py`, `ztljudge.py`, `zverify.py` and `lean/` — 371 theorems across
21 modules, all on the empty axiom list — and is documented in `paper/`, not here.
