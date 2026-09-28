# ZTL against classical logic — the card

One page, four columns, every number produced by `python3 zledger.py`
(part of `run_all.py`). Quote from here; do not improvise the comparison.

| | |
|---|---|
| **Shared** | On Z-free markings ZTL **is** classical logic. Not sampled — **proved**: `lean/ClassicalAgreement.lean`, `evalF_agrees`, structural induction over the whole formula language, empty axiom list. (The 2906 × 4 measurement that preceded it stands as the sanity check.) |
| **Nothing lost** | **All 26 classical laws hold here on verified data — not one falls, ever** (measured: on mark-free valuations classical and ZTL have the same 584 validities of the depth-≤2 pool, the same set element for element — 588 counting the pool list's repeated entries; see the erratum below). Of the 26, **12 keep working when an atom carries the mark**; the other **14 do not extend to it** — both De Morgans, contraposition, `¬¬p = p`, excluded middle, `p → p`, idempotence (`audit.py`) — and there ZTL proves the **refutation with a witness** instead, with zero undecided outcomes. The 212 counts validities over the WIDER domain: beside the 584 it is the price of admitting unverified input (fewer formulas hold on every valuation), not a loss on verified data (corrected 2026-09-28). Against the classical default on that wider domain the comparison is external Bochvar's 548. |
| **Gained (laws)** | **Zero, and now machine-checked:** `ztl_taut_is_classical` — every ZTL tautology is a classical one, for every formula, empty axiom list. And the inclusion is **strict** (`not_conversely`: `p → p` is classically valid and fails here at a mark), so "conservative" never reads as "the same logic". This column can never fill. |
| **Gained (sight)** | Classical logic sorts two-variable formulas into **16** equivalence classes; we sort them into **195**, and **all 16** classical classes are split. Twelvefold refinement: same truths, finer eyes. |
| **Order of birth** | Under pure doubt (every atom Z, no constants) **F is born first and T only through an F** — proved over the whole language: `lean/ZOrigin.lean`, `T_through_F`, `birth_order`, empty axiom list. Classical logic has no such order: its negation is an involution, and the question does not arise. Not a gain in laws (row above) — a fact about where ZTL's values come from. |
| **Only here** | `¬(p ↔ p)` answers F, F, **T** on T, F, Z — the mark is sayable *inside the object language*. A two-valued logic has no words for the question, not merely no proof. |

## "So you abolished De Morgan?" — the schedule

No. A classical law costs exactly the verification of its atoms, and the
toolbox returns as they are paid for (measured, `zledger.py` §1):

| verified | classical tautologies that hold |
|---|---|
| both atoms | 584 / 584 — **100%**, and this one is a theorem, not a sample |
| one of two | 379 — 64% |
| nothing | 212 — 36% |

De Morgan itself: `p=T, q=T → T`; `p=T, q=Z → F`. The licence is per
FORMULA and needs EVERY atom in it verified — not most of them.

**Expiry is a WORLD problem, not a proof problem.** A verification can
lapse (§E25), and the licence lapses with it — but only for empirical
grounds: invoices, measurements, inspections, certificates. In
mathematics a proof does not expire, so the temporal layer never fires
there; what mathematics has instead is refutation, which is a different
transition. Audit needs both; proof needs only one.

## The instance to quote

```
p -> p     T->T  F->T  Z->F      can fail, honestly
~p -> ~p   T->T  F->T  Z->T      cannot fail — negation burns the mark
```

Classically one class, one truth. Here, two fates — which is why proving
`p → p` through `¬p → ¬p` is a forgery (the counterfeit test from the Job
dilemma).

## Why refusing free truth is the point

Nothing is lost on verified atoms: there every classical law holds, these
two included. What ZTL refuses is to apply them to an atom nobody checked
— and those two moves are exactly the engines of the paradoxes:

* `¬(p → q) ≡ p ∧ ¬q` — classically valid, and valid here on verified
  atoms; **not** at an unchecked one. This is the sorites' engine: it
  turns "this step failed" into "here is the cliff".
* `p ∨ ¬p` at an unchecked `p` — **F** here. Asserting the excluded
  middle about the undecided is what launches the surprise-exam
  elimination.

Modus ponens is **untouched**, and so is the rest of the working kit —
syllogism, reductio, and **proof by cases** `((p→q) ∧ (¬p→q)) → q`, which
is ZTL-valid (measured in `zprove.py`; an earlier claim in this corpus
that case analysis was lost was simply wrong). What is refused at an
unchecked atom is Peirce's law — the one that separates classical from
intuitionistic logic — and the excluded middle. The resolutions were not
bought by breaking inference; what is refused is truth on credit.

## Two traps in our own numbers

* **Vacuous validity.** Under default deny an unverified antecedent is
  F, so *every* conditional over unchecked atoms is ZTL-valid for free.
  "ZTL-valid" for a conditional must always be read with "and its
  antecedent is earnable at all" (`zprove.py`, section 2).
* **Validity is not derivability.** From an empty ledger nothing is
  derivable, not even a guarded tautology (E26); the twelve rules are
  incomplete. Inference *transports* verification into compound claims —
  the pigeonhole conclusion is earned with three of six atoms still
  unverified — but never mints the first coin.

## What a theorem costs

The pigeonhole principle (3 pigeons, 2 holes) is ZTL-valid, and valid
non-vacuously: of 729 markings, 125 earn the antecedent and all 125 give
the conclusion. The **verification bill is exactly 3 atoms** — one
witness per pigeon, the price of the theorem's own subject matter. That
is the currency here: not steps, witnesses.

## The honest boundary

This makes a good **auditor** and a **mathematician that pays for its
premises**: equal to classical logic in strength on verified data — on
verified premises every classical proof goes through — and never cheaper than its data.
Real theorems go through and cost their own data; what cannot be done is starting from nothing, or reasoning by
excluded middle about something nobody checked. Narrow search is a virtue
when judging claims and a constraint when building proofs.

## The first objection from a logician: "p → p fails, that is not a logic"

Nobody in the literature says that. What exists is Tomova's class of
**natural implications** (Reports on Mathematical Logic 47, 2012), four
criteria: (1) classical on {0,1}; (2) Łukasiewicz–Tarski normality —
modus ponens preserves the designated value; (3) `p ≤ q ⇒ p→q`
designated; (4) free elsewhere. **We meet (1) and (2)** — (1) is now a
Lean theorem — **and violate (3) in exactly one cell: (Z, Z)** (measured,
`zledger.py` §6).

`p → p` is not a primitive of that definition; it is the diagonal of (3),
and (3) presupposes a linear order on the values — the middle one being a
*degree* of truth (Łukasiewicz's ½, "possible, not yet determined").
Ours is a status mark barred from compounds: `Z ≤ Z` does not say
"equally true", it says "neither side examined", and designating the
conditional there is exactly granting truth on credit. So we are outside
the family the classification is built for, not in breach of a law.

The constitutive test of logicality is elsewhere and we pass it: the
consequence relation is Tarskian — reflexive, monotone, closed under cut
— so **`p ⊨ p` holds where `⊨ p→p` fails**. The price, named: the
deduction theorem holds left to right only (→-elimination works,
→-introduction does not). Ł3 lacks the deduction theorem too, so this is
a family trait, not an exile.

## What NOT to say

* ~~"ZTL is weaker than classical logic"~~ — misleading, and
  ~~"strictly fewer validities is false"~~ — WRONG, corrected 2026-09-28
  (Logik2's hostile review, re-checked): by our own `ztl_taut_is_classical`
  and `not_conversely` (`p → p`), over its own valuations ZTL has strictly
  fewer validities. Say instead: equal to classical logic in strength ON
  VERIFIED DATA (the same set, 584 = 584); fewer validities only over
  unverified input, where classical logic cannot take the input at all —
  the price of admitting it (paper §3.2, §10), nothing lost on verified
  data; strictly more expressive than any classical default (binary clone
  2 + 512 against 2 + 16 for "unverified := false", and 2 + 16 for ":= true";
  every default yields a two-valued function of the three-valued inputs, ZTL
  defines every such function as a DNF over its detectors p ∧ p, ¬p,
  ¬(p ↔ p), and no default defines isZ; external Bochvar is NOT such a
  default — its negation reads ¬Z = F, the default's ¬Z = T — and its clone
  is the same 2 + 512 as ZTL's: they part in seven cells, not in
  expressiveness; measured 2026-09-28); dominant as a solver.
  The 212 against the 584 is that price, measured — not a category error
  (see "Can classical logic replace ZTL?" below).
* ~~"ZTL can express everything"~~ — false on three values: 515 of 19683
  binary functions are expressible (2.6%), a consequence of greediness
  (compound formulas never take Z).
* ~~"we solved the paradoxes"~~ — we priced them. The diagnoses have
  prior art (Quine 1953 and Sorensen 1988 for the surprise exam;
  paracomplete treatments for the sorites); what is ours is that each
  diagnosis is a reproducible run with a warranty and a named cure.
* ~~"Lean proves our choices are right"~~ — Lean proves our theorems have
  no holes (405, empty axiom list). The adequacy of `¬Z = F` is not a
  theorem and cannot be one.

## Ethics and deontic logic — what is theirs, measured 2026-08-30

Asked whether the ethical question is ours at all. It is not, and the
precedent is old. **Cite this, do not re-derive it.**

**von Wright, 1951** — the founding move of deontic logic is exactly our
observation: *not every act that is a performance-function of other acts is
also a deontic function of them.* The moral value is not computed from the
truth table; that is why the field went modal rather than truth-functional.
So the impossibility half of "no truth-functional extension carries ethics"
is **75 years old and not ours.** Never claim it.

**Benzmüller, Parent, van der Torre — a deontic logic reasoning
infrastructure.** Deontic logics are shallow-embedded into classical HOL and
run on Isabelle/HOL with Leo-III and SMT; case study on GDPR. Their pitch is
that there is no consensus on the best deontic formalism, so candidates can
be swapped and compared — which is an open invitation for ZTL to be one more
candidate. **The catch to state before anyone gets attached:** the workbench
is classical HOL, and our whole discipline is the axiom tiers with `[]` and
no `Classical.choice`. Embedding puts our logic *inside* the axioms we
refuse. The verdicts would likely agree; the claim "proved on an empty axiom
list" would not survive the move.

**What their "uncertainty" and "epistemic" actually are** — checked, because
both words sound like our `Z` and neither is:

- *Uncertain Machine Ethics Planning* (Kolker, Dennis, Pereira, Xu, 2025):
  probability over **outcomes** — a multi-moral MDP and stochastic shortest
  path — plus moral uncertainty across conflicting theories. Full-text scan:
  `unverified`, `not checked`, `unknown`, `refuse`, `abstain`,
  `three-valued` — **zero occurrences**. Not our object.
- *Epistemic Reasoning for Machine Ethics with Situation Calculus*
  (Pagnucco, Rajaratnam, Limarga, Nayak, Song, AIES 2021): the knowledge
  modality `K(s',s)` of Scherl & Levesque in the situation calculus,
  implemented in ASP. "What the agent knows", not "was this input checked".

**The honest boundary on this section.** The Manchester paper was read as
full text. The UNSW one was **not**: ACM returns 403 and no preprint was
reachable — that entry rests on the conference **poster**, which is a
summary. Three searches, not a survey. The nearest neighbours **not read**
are Governatori and the defeasible / argumentation-with-deontic line, where
a typed refusal may well already exist.

**Corrected in the same pass:** the LLM normative-reasoning benchmark
(NeuBAROCO line, arXiv 2510.26606) was first called a neighbour of our
formalizer-stability measurement. It is not — by its own abstract it tests
how well LLMs *reason with* normative and epistemic modals and reports
inconsistencies and cognitive biases; it does not measure translation into a
formal representation, nor run-to-run stability. Read: abstract and the
repository landing page, not the paper.

**The defeasible / argumentation line — first paper read, 2026-08-30.**
Yu & Lu, *Explaining Non-monotonic Normative Reasoning using Argumentation
Theory with Deontic Logic* (arXiv 2409.11780), the LeSAC system for legally
compliant design. The find worth quoting, verbatim:

> "This should be ensured by the epistemic reasoning process before being
> input into LeSAC."

They **name our slot and assign it upstream**: the normative reasoner
requires beliefs already justified and consistent, and whether they are is
another system's job. A full-text scan of that paper finds no `undecided`,
no `abstain`, no `refuse`, no `unverified` — the vocabulary of unsettledness
is simply not in it.

**But the slot is not vacant, and this is the live objection to us.** They
say who does the upstream job: **ASPIC+**, structured argumentation, where a
claim can come out *undecided*. So "a typed non-verdict" already exists in
the field. The distinction that would have to be ours is narrower: their
undecided arises from **conflict between arguments** (defeat); our `Z`
arises from **absence of a check**, and we additionally bill the declaration
of absence. **ASPIC+ itself has NOT been read or run** — until it is, this
distinction is argued, not established.

**What may still be ours, narrowly:** the verification status of a
**premise** — not of an outcome, not of the agent's knowledge, not of a
defeat relation — plus a typed refusal and a bill for declaring absence.

**Access note:** the UNSW/AIES 2021 paper is definitively closed — Semantic
Scholar reports open-access status CLOSED with no PDF. That entry rests on
the poster and the abstract and cannot be improved without a library.

---

## Can classical logic replace ZTL? — measured 2026-09-18

Asked by the curator, answered by running rather than arguing. Pool throughout:
the depth-≤2 pool of `paper/core_logic_checks.py` §5, 2926 formulas over `p, q`.

**On grounded input, classical and ZTL are THE SAME — not close, identical.**

| | validities on grounded inputs only |
|---|---|
| classical | 584 (588 list entries) |
| ZTL | 584 (588 list entries) — *and the sets are equal, element for element* |

**Laws that work classically and fail in ZTL: zero.** Every one of the 584 holds
here whenever the atoms are verified.

### The 212 against the 584 is the price, measured — name it, do not hide it

212 is ZTL's validity count over the *extended* input domain, where an atom may
be unverified. A law is a claim about every valuation; admitting the unverified
ones means fewer formulas hold on all of them. That IS "fewer validities" in the
logician's sense (`ztl_taut_is_classical` + `not_conversely`), and it is the
price of admitting unverified input — named in the paper (§3.2: the deduction
theorem runs one way only). Nothing is lost on verified data (584 = 584).
(Corrected 2026-09-28: this section used to call the comparison a "category
error"; it is not — same formulas, a wider set of valuations.) The comparison
that separates ZTL from the classical DEFAULT on the extended domain is **ZTL
212 against external Bochvar 548**: both are defined on three values, and those
336 are what Bochvar grants on ignorance.

### "Classical with unverified := false" is external Bochvar

Measured cell by cell: they agree on **every** binary connective (0 divergences
of 45) and part only at `¬`. So the substitution approach is not a naive
shortcut — it is Bochvar's external layer, available since 1938. ZTL parts from
it in exactly **7 cells**: `→` at (Z,F),(Z,Z); `↔` at (F,Z),(Z,F),(Z,Z); `⊕` at
(T,Z),(Z,T). Against the substitution itself the count is 8 — those seven plus
`¬Z`. Every one of the eight is a place where the substitution **manufactures a
verdict out of ignorance**: `¬Z = T`, `Z→F = T`, `Z↔Z = T`.

### What the mark buys, in numbers

* **1840 of 2924 compound formulas (63%) distinguish "unverified" from "false"**
  while still returning a two-valued verdict. Call a compound *mark-sensitive*
  when, on **some** valuation, replacing **every** mark by false changes the
  verdict — that is the definition behind the figure, and the figure means
  nothing without it. Under substitution: **0** — `Z` and `F` become one input,
  so nothing can separate them. Shortest separators are ordinary: `¬p`, `¬¬p`,
  `(p→p)`, `(p⊕q)`, `(q↔p)`. Run: `python3 marksens.py`.

  **Correction, 2026-09-19.** This line read "1263 of 2924 (43%)" from
  2026-09-18 until today. That number is not wrong, but it answers a *narrower*
  question: it counts the compounds that separate the two inputs when the mark
  sits on **one designated atom** and the other atom is verified (1263 for `p`,
  1263 for `q`, 1830 for the union). The remaining 10 need **both** atoms
  unverified at once — e.g. `((p→p)∨(q→q))`, which is F when both carry the
  mark and T as soon as either one is verified — so marking one atom at a time
  cannot reach them. The sentence above claimed the general fact and quoted the
  narrow count, which understated the result by twenty points; and no script in
  the tree produced either number, which is why the error survived a day.
  `marksens.py` now prints all three readings.
* The mark is sayable inside the language: `isZ(x) = ¬(x↔x)` gives T on Z and F
  on both T and F.
* **On unverified input ZTL decides all 26 classical laws: 12 hold, 14 are
  REFUTED with a witness value, 0 undecided.** The fourteen are not a hole; they
  are fourteen theorems about unverified data. Classical decides 0 of 26, because
  it cannot accept the input at all.

### How to say this without being refuted in one line

"ZTL is stronger than classical logic" invites the standard reading — *proves
more* — and our own machine-checked `ztl_taut_is_classical` refutes it instantly.
The wording that survives:

> **On verified valuations ZTL is classical logic — the two-element Boolean
> algebra, with T designated, is a submatrix of the ZTL matrix; over a wider
> input domain it is strictly more expressive and strictly more applicable,
> and it adds no theorem about the old domain.**
>
> (Until 2026-09-28 this read "a conservative extension of classical logic".
> Wrong term: an extension keeps every theorem of the original, and ZTL does
> not validate `p → p` over its own valuations.)

And the sharper claim, the one the exhibit below actually proves — say this when
someone asks whether ZTL is *stronger*, because it is the strength without the
word that invites the wrong reading:

> **There are problems ZTL answers correctly that classical logic answers
> correctly under NO choice of default. There are no problems the other way
> round. As a decision procedure, ZTL strictly DOMINATES classical logic.**

Both halves are measured, neither is argued: *no problems the other way round* —
on grounded input the two are identical, 584 and 584, the same sets, zero laws
lost; *problems ours only* — the `$_GET` exhibit, where both classical defaults
grant a pass and no conservative default exists at all.

Keep the two relations apart and nothing here can be attacked: **as a system of
proofs the two are exactly equal on classical's own domain; as a solver ZTL
dominates.** Saying "stronger" without naming which relation is what loses the
argument, not the facts.

Every word of that is measured: *extension* (the domain gains the unverified
state), *conservative* (unique validities: exactly zero, machine-checked), and
nothing lost (584 = 584, same sets).

### The operational exhibit: a `$_GET` parameter reaching a SQL sink

The cell counts above say what differs. This says what it costs. The shape is the
live one `php2zfl` builds for every sink — three rows, judged by `zfl.run`:

    tainted    the parameter comes from $_GET and reaches the sink
    sanitized  it passed through escaping on the way
    safe  :=  ~Tr(tainted) | Tr(sanitized)

**ZTL returns three outcomes, not two** (measured on `zfl.run`):

| what is known | verdict | disposition |
|---|---|---|
| tainted verified, sanitized verified | `T` | EARNED, hereditary |
| tainted verified, sanitized refuted | `F` | REFUTED, hereditary |
| **neither established** | `Z` | **OPEN, until-verification, naming `safe` as unverified** |

The third row is the whole point: a *decided* verdict that safety is not
established, with the address of what is missing.

**Classical has no third row, and both of its defaults grant a PASS:**

    unverified := false   ->  safe = ¬F ∨ F = T    PASS
    unverified := true    ->  safe = ¬T ∨ T = T    PASS

Read that twice. The "cautious" default is the dangerous one here, because the
atom is named `tainted`: assuming *not tainted* is assuming safety. Whether a
substitution is cautious depends on the **polarity** of the atom, not on the
intent of the person choosing it.

**And choosing per polarity does not rescue it.** Take a formula where one atom
occurs under a negation and without one — ordinary in real rules:

    safe = (¬tainted ∨ sanitized) ∧ (tainted ∨ logged)
           "clean, or escaped"     and  "dirty, or we logged it"

For the first conjunct not to come out true for free, `tainted` must be T. For
the second, it must be F. One atom, two incompatible demands: **no conservative
substitution exists.** The choice classical is forced to make has no safe
setting — which is precisely why ZTL does not make it.

---

**Erratum, 2026-09-27 (the cloud red team, PR #3, re-checked here).** The depth-≤2 pool
is a LIST of 2926 entries that repeats 20 formulas, four of them tautologies (`p→p`, `q→q`,
`p↔p`, `q↔q`). Counted over the list, classical logic and ZTL both validate 588; as a SET,
2906 formulas and **584 = 584** — the figure `zledger.py` asserts. The equality never
depended on the duplicates; "the same set" has 584 elements. The published v2.0.0 text
(`paper/ZENODO.md`, the 2.0.0 preprint) says "588 … the same set": that record is frozen
and is corrected here and from 2.1.0 on. `paper/core_logic_checks.py` still counts the list
(588), and says so.

