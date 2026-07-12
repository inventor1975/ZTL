# ZTLStudio

A local studio: a human states a claim or a paradox in **natural
language** (any language), the AI only **translates** — it never
judges — and the measured **ZTL core judges**: verdicts with
warranties, quarantine passports, stipulation options.

```
human ──meta-chat──► understanding (negotiated, you sign off)
      ──AI emits──► ZFL ──validator──► errors ──AI repairs──► valid ZFL
                     │
                     ▼ deterministic back-reading (no AI — the second auditor)
                     ▼
               the ZTL core (AI-free, measured, kernel-backed)
                     ▼
               verdict · warranty · passport · stipulations
```

The pipeline embodies the logic it serves: the LLM's output is an
**unverified input** (the mark Z), and the deterministic core is the
customs — truth is never granted on credit, not even to the
translator.

## Run

```
python3 tool/ztlstudio.py        # → http://localhost:8190
```

No dependencies (Python stdlib only; the core is imported from the
repository root). The AI is optional: without a Groq key the studio
runs in **pro mode** — write ZFL by hand in the middle panel. To
enable the AI, set `GROQ_API_KEY` or put the key into `tool/.groq_key`
(gitignored). Model override: `ZTL_GROQ_MODEL` (default
`llama-3.3-70b-versatile`).

## The three panels

1. **Meta-chat** — negotiate the meaning with the AI in your language.
   The AI produces a structured understanding (atoms, what is
   verified, genre, the question) and may ask clarifying questions —
   but only when formalization is blocked. It knows its boundary:
   arithmetic, quantities and numeric wordplay get an honest "does not
   formalize into propositional ZTL" instead of an invented encoding.
   When you agree — press **Agree → ZFL**.
2. **ZFL** — the emitted formal document, hand-editable (pros can skip
   the chat entirely). **Validate** checks it; **AI repair from
   errors** feeds the validator's machine-readable errors back to the
   AI; the **back-reading** (template-generated, no AI) verbalizes
   what is *actually* written, so the translation is audited by a
   component that cannot hallucinate.
3. **Results** — validator issues and the core's report, followed by
   an **AI explanation chat**: the AI retells the formal verdict in
   plain language and answers follow-up questions. The report is the
   authority — the explainer is forbidden to re-judge, and its panel
   is labeled *unverified by definition*: the pipeline applies its own
   logic to itself.

## ZFL — the Zero-trust Formal Language

Design goal: **everything valid in ZFL loads into the ZTL core with no
further questions.** A ZFL document is strict JSON:

```json
{
  "genre": "statement",
  "atoms": {
    "overheat": {"status": "Z", "note": "sensor unverified"},
    "shutdown": {"status": "Z", "note": "not observed"}
  },
  "assert": "imp(overheat, shutdown)",
  "ask": ["verdict", "warranty"]
}
```

```json
{
  "genre": "system",
  "sentences": {"R": "Tr(M)", "M": "not(Tr(R))"},
  "ask": ["passport", "stipulations"]
}
```

* `genre: "statement"` — a verdict question about a claim over
  (un)verified atoms. `atoms` declare the inputs: `status` is
  `"T"` (verified true), `"F"` (verified false) or `"Z"` (unverified);
  `assert` is the formula.
* `genre: "system"` — a self-referential system: each sentence is
  defined by a formula over `Tr(name)` references (and constants
  `T`/`F`). Declared atoms enter the system as unverified/verified
  inputs. Bare atom names inside system formulas are forbidden —
  references go through `Tr(...)` only.
* Formulas: `not(x)`, `and(x,y)`, `or(x,y)`, `imp(x,y)`, `xor(x,y)`,
  `xnor(x,y)`, constants `T`/`F`, atom names (any language). `Z` is
  not a constant — the mark lives on atoms.
* `ask` (optional): any of `verdict`, `warranty`, `passport`,
  `stipulations`.

The validator emits machine-readable issues (`E_UNDEF_ATOM`,
`E_TR_IN_STATEMENT`, `E_BARE_ATOM`, `E_TYPE`, …) with hints — the same
list the AI repair loop consumes.

## What the core reports

* **Statements:** the verdict (T/F — verdicts are always two-valued),
  its **warranty** (stable / until-verification, §19 of the preprint),
  the passport of unverified inputs, and the completion table showing
  how the verdict behaves under every reading of the unverified atoms.
* **Systems:** the grounded part (identical in every fixed point —
  kernel-checked), the quarantine set, and a **passport** per
  component: PARADOX (no classical solutions — refusal permanent, with
  the oscillation period), UNDERDETERMINED (refusal until stipulation,
  with the available choices), INPUT (until verification), DOWNSTREAM
  (inherited, culprits listed). §9/§18 of the preprint, measured and
  kernel-backed.

## Files

| file | role |
|---|---|
| `zfl.py` | ZFL parser, validator, deterministic back-reading, core converters — AI-free |
| `engine.py` | the arbiter: runs validated ZFL on the measured core — AI-free |
| `translator.py` | the only AI component: understanding ↔ emission ↔ repair (Groq) |
| `ztlstudio.py` | local server (stdlib), three-panel UI, examples |
| `static/` | the UI (HTML/CSS/JS) |
| `test_zfl.py` | the foundation stand (24 checks), wired into `run_all.py` |

*AI participation: designed and written in a dialogue between the
curator (Vitaly Reznik) and Claude (Anthropic); all fork decisions are
the curator's.*
