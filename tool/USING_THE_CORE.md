# Using the ZTL core — a guide for an AI agent

You are about to send a claim through a logic engine that refuses to grant
truth on credit. This page is everything you need. It is written for a
machine reader; a human can follow it too.

---

## 0. What it judges — and what it does not

The core judges **the propositional structure of a formalized claim**. It
answers: does this follow from these grounds, what is the verdict worth,
which unverified inputs decide it.

It does **not** judge: whether your facts are true, arithmetic, quantities,
dates, deadlines, modality, degree, relevance, or value. It has no opinion
about the world — only about the formula you hand it.

Therefore the weak link is never the core. It is **your formalization**.
Everything below is arranged around that fact.

---

## 1. Call it

No key, no account, no rate limit on the core routes (the limits apply only
to the optional AI-translation routes, which you do not need — you are the
translator).

```
POST https://ztl.vitalyreznik.com/api/assert
Content-Type: application/json
{"zfl": "assert !revoked impl guilty"}
```

Routes:

| route | what it gives |
|---|---|
| `/api/validate` | parse + machine-readable errors + the back-reading |
| `/api/assert` | **the logic map** — currency, decisive checks, derivation audit |
| `/api/run` | verdict + warranty + completion table (and paradox passports) |
| `/api/refute` | for a claimed LAW: exhaustive check over all assignments |

Offline instead: `git clone https://github.com/inventor1975/ZTL`, then
`python3 tool/ztlstudio.py` (stdlib only, no dependencies), or call
`zfl.validate` / `engine.logic_map` directly.

---

## 2. Input

**Quick form** — one line, atoms default to unverified:

```
assert !revoked impl guilty
a=F assert (d iff !c) impl ((b impl a) impl (b iff c))
```

Operators: `!` `not` `and` `or` `impl` `xor` `iff`/`nxor`. A leading
`name=T` / `name=F` marks an atom as verified with that value; anything
unmarked is unverified (the mark `Z`).

**Full form** — JSON, and the form you should prefer, because it carries
the glosses:

```json
{
  "genre": "statement",
  "atoms": {
    "revoked": {"status": "Z", "means": "the ground was revoked"},
    "guilty":  {"status": "Z", "means": "the person is guilty"}
  },
  "assert": "imp(not(revoked), guilty)"
}
```

`status`: `"T"` verified true, `"F"` verified false, `"Z"` **unverified**.

### `means` is not decoration — it is the polarity auditor

An atom is a bare string to the core. Nothing stops you from writing
`not(fresh)` while you meant "not revoked" — and if `fresh` already MEANS
"no revocation occurred", your formula now asserts the opposite of your
intent. This exact error shipped in this repository on 2026-07-19 and was
caught by a human reviewer, not by any machine.

So: **state what T of each atom means**, and the validator will warn you —

* `W_DOUBLE_NEGATION_MEANING` — you negated an atom whose gloss is already
  negative; `not X` therefore asserts a *positive* fact. Check the polarity.
* `W_NO_GLOSS` — no gloss; the polarity cannot be audited at all.

And the **back-reading** will verbalize your formula *by meaning*:
`not ([the ground was revoked])`. Read that line before you trust your own
encoding. It is the only auditor in the pipeline that cannot hallucinate.

---

## 3. Output, and how to read it

### The verdict is a pair: value + warranty

* `T` / `F` — the verdict. Verdicts are always two-valued; `Z` is a mark on
  an *input*, never a verdict.
* warranty ladder:
  * `until-verification` — true **now**, on credit; a check may revoke it;
  * `sound` — agrees with every completion of the unknowns, but may wobble
    mid-verification;
  * `hereditary` — **no verification path can revoke it** (machine-checked
    licence, `lean/ZTime.lean`, empty axiom list). This is the only grade
    on which a third party may rely without rechecking.

### The logic map (`/api/assert`)

* **currency** — what the claim's truth is made of:
  * `free-truth` — true under every assignment *including* unverified
    inputs; costs nothing;
  * `on-credit` — classically valid, yet **breaks when an input is
    unverified** (the witness marking is returned): truth minted from form;
  * `contingent` — depends on the facts; a countermodel is returned.
* **decisive** — which single verifications flip the verdict (what to check
  first, and what not to pay for).
* **audit** (for `if … then …` shapes) — `earned` (a chain of the twelve
  alive rules, with provenance), `on-credit` (naming the borrowed fallen
  rule), `rules-gap`, or `does-not-follow` (with a counterexample).

### Three traps in reading the output

1. **`F` is not "false".** It is *default deny*: not earned. "Unverified"
   and "refuted" are different states — the first has grade
   `until-verification`, the second can be `hereditary`.
2. **`T` can be vacuous.** `assert !revoked impl guilty` returns `T` — but
   only because the antecedent `!revoked` was itself refused (`¬Z = F`), and
   a false antecedent makes any implication true. Always read the currency
   and the completion table, never the bare verdict.
3. **A constant completion table means a frame.** If the verdict is the same
   under every completion, the claim reads none of its own grounds: a test
   that cannot fail is not a test. The engine says so explicitly.

---

## 4. The discipline (this part is not optional)

1. **Show your formalization.** Atoms, glosses, formula, back-reading — beside
   the verdict, always. Your reading is a step someone may dispute; make it
   disputable. A verdict without its encoding is worthless.
2. **Do not formalize the unformalizable.** Vague, open-textured, metaphoric,
   quantitative or value-laden claims do not enter. Say "this does not
   formalize into propositional ZTL" — that is a correct answer, not a
   failure. Inventing an encoding to have something to run is the one
   unforgivable move here.
3. **Refute, do not certify.** The core earns denial cheaply and truth
   sparingly. Its natural work: "this step is on credit", "these two clauses
   contradict", "this condition can never fire", "this term is used but never
   grounded". It cannot tell anyone that a document is sound.
4. **Report the warranty, not just the verdict.** "T" alone misleads.
   "T, until-verification, decided by atom X" is the truth.
5. **The core is a measuring instrument, not a certifier** — it measures
   whether a conclusion is logically warranted by the grounds offered. Whether
   the grounds are admissible, current or authoritative is somebody else's
   question, and it is not answered here.

---

## 5. Verify the engine itself

You do not have to trust this repository. The Lean corpus is import-free and
mathlib-free by design: paste `lean/ZTime.lean` or `lean/EpochBoundary.lean`
into the web editor at `live.lean-lang.org` and read the `#print axioms`
output in your own browser — every line must say *"does not depend on any
axioms"*. The same build runs on every push under GitHub Actions (workflow
`lean`, step "zero-axiom ledger"), executed by a third party, publicly logged.

An empty axiom list is precisely a verdict that two parties who share no
axioms and no trust can both confirm. That is the point of the whole thing.
