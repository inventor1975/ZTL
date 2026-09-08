# code2zfl — code → atoms → ZFL2 → the judge

A model cannot lay a text out into atoms without losing some. Code is
different: a parser lays it out exactly. So here the atomizer is an
**algorithm** — `atoms.php` on `nikic/php-parser` — and the only judge is
the **ZTL core** (`tool/zfl2.py`, the same `run` the studio calls). No model
is called anywhere; a run costs milliseconds and no key.

## What it answers

For every **sink** (a query, a shell call, an include…) one question:

> can an attacker drive this call?

as one ZFL2 document, three rows, one claim:

    tainted     an attacker-controlled value reaches the sink          — from source facts
    sanitized   on EVERY path it was substituted by a verified value   — E40: no function launders a mark
    safe        := ~Tr(tainted) | Tr(sanitized)                        — claim: safe

and the judge answers with a **disposition and a weak link**, not a score:

| disposition | meaning |
|---|---|
| **REFUTED** | attacker-controlled value reaches the sink and nothing on the path substitutes it — an injection |
| **EARNED** | grounded: on the named substitution (`san-intval-L12`), or nothing attacker-controlled arrives |
| **OPEN** | the path crosses something this file cannot see; the weak link is **named** (`clean_input()@L4`, `param:$id`) |
| **E** | the file does not parse — *not judged*, never "clean" |

## Why per-sink documents lose nothing

Evaluation reads the marking only at the atoms of the formula:
`lean/NoGift.lean` `evalF_congr`, `lean/ContextClosure.lean` `eval_indep`,
`lean/Receipt.lean` `receipt_complete` — all with empty axiom lists. Cutting
one big table into per-claim tables changes no verdict. The `3^names` cost of
the passport office never enters: these documents have three names.

## What is proved, what is measured, what is a boundary

- **Proved** (Lean, `[]`): a chain of functions never removes a mark; the only
  sanitizer is a *substitution* of the element — `lean/ZTaint.lean`
  `no_laundering`, `sanitizer_is_substitution`. The catalog encodes exactly
  that: `intval` substitutes for every context, `mysqli_real_escape_string`
  only for the quoted SQL context, `htmlspecialchars` only for HTML;
  `addslashes`, `substr`, `str_replace` substitute nothing.
- **Measured** (`test_code2zfl.py`): 14 fixture sinks — planted injections
  REFUTED, clean code EARNED, opaque code OPEN with the weak link named — and
  two **vacuity controls**: with the sanitizer catalog emptied `f02` flips to
  REFUTED, with the source catalog emptied `f01` flips to OPEN. The catalog is
  load-bearing; the verdicts are not the frame talking.
- **Boundaries** (named in the ledger, not hidden):
  - *intra-procedural*: a parameter, a global, an include, a DB row are Z;
  - escaping **without quotes** is refuted, not credited (`ast-unquoted`);
  - a transformation after escaping **drops** it (`substr` can end in a lone backslash);
  - a sanitizer of the **wrong context** is refuted (HTML escaper before SQL);
  - the catalog carries `measured` per sink context — only `sql` is exercised by the stand so far.
- **Never emitted**: literal values. A string literal contributes two bits
  (does it begin / end with a quote). Secrets in config files cannot leak
  through this tool's output.

## Run

    composer install                                   # or: export CODE2ZFL_AUTOLOAD=/path/to/vendor/autoload.php
    python3 code2zfl.py path/to/code [--overlay project.json] [--ctx sql|all] [--md ledger.md] [--json facts.json]
    python3 test_code2zfl.py

`catalog.json` is the base PHP catalog — sources, sinks by context,
substitutions by context, transparent functions. A project **overlay** adds
its own wrapper (`$db->query`, `$db->escape`, `get_var`): see
`fixtures/overlay-wrapper.json`. Overlays for live sites stay private.

## Prior art, named once

Taint analysis exists — Psalm, PHPStan, Semgrep, Phan. What they do not give
is the **warrant**: their "clean" is unwarranted, ours is `EARNED on
san-intval-L12`; where they either assume or shout, ours says **Z** and names
the link to verify. Independent comparison on the same files is the next
measurement, not a claim made here.
