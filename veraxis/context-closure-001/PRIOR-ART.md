# Prior-art crosswalk — claim by claim, before anyone builds on this

Requested by Arkadiy 2026-08-19, and it exists because the first framing of
this artifact leaned on novelty it does not have. The rule of this repository
is that a claim of the form "nobody has X" is the shape that dies fastest; four
such died here in a single day. So every prospective claim is listed with a
verdict, and the verdicts are deliberately unkind.

**Verdicts:** `KNOWN` — established elsewhere, do not claim ·
`DIFFERENT SEMANTICS` — same shape, another calculus · `ZTL-SPECIFIC` — a fact
about this logic · `LEGAL EXTENSION` — outside the computational literature ·
`OPEN` — not settled, and not claimed.

## The line of work this sits in

    PTaCL (Crampton & Morisset)                             POST 2012
      attribute-hiding attacks; three-valued targets {1,0,⊥}
    ATRAP / policy resistance (Griesmayer & Morisset)            2013
      resistance formalised; counterexamples in Maude, proofs in Isabelle
    Monotonicity and Completeness in ABAC (Crampton & Morisset) 2014
      monotonicity as a structural property
    On Missing Attributes in Access Control                      2015
      missing attributes as nondeterministic retrieval
    Extended evaluation + query constraints (Morisset et al.) 2018/2019
      evaluate all extensions of the observed query, inside an
      admissible query space Q(A|C) fixed by domain constraints;
      "critical pairs" and "attribute value power"

## The crosswalk

| # | prospective claim | verdict | why |
|---|---|---|---|
| 1 | hidden information can turn an unfavourable decision into a favourable one | **KNOWN** | attribute-hiding attacks, PTaCL 2012 |
| 2 | a system can be checked for resistance to such withholding | **KNOWN** | policy resistance, ATRAP 2013 |
| 3 | check it by evaluating all completions/extensions of what was shown | **KNOWN** | extended evaluation 2019; nondeterministic retrieval 2015 |
| 4 | do that check by machine, with proofs | **KNOWN** | ATRAP 2013 — Maude search plus Isabelle proof |
| 5 | monotonicity is a sufficient structural property | **KNOWN** | Crampton & Morisset 2014 |
| 6 | restrict the completion space by declared constraints | **KNOWN** | query constraints, `Q(A|C)`, 2019 |
| 7 | identify which hidden values could change the decision | **KNOWN** | critical pairs / attribute value power, 2019 |
| 8 | our "boundary receipt" as an audit artifact | **KNOWN (idea)** | the idea is 7 above; only its packaging is ours |
| 9 | the kernel's verdict is NOT completion semantics, witness `¬¬Z = T` | **ZTL-SPECIFIC** | a fact about the greedy connective-local lift, verified against PTaCL's own table, not its name |
| 10 | the positive fragment where the two coincide, proved | **ZTL-SPECIFIC** | `closure_coincides`, empty axiom list |
| 11 | no purely syntactic condition can be exact | **ZTL-SPECIFIC** | `no_syntactic_characterisation` |
| 12 | normalisation removes every credit-verdict, and costs honest ones | **ZTL-SPECIFIC** | `normal_form_sound` / `normal_form_incomplete` |
| 13 | an empty admissible space must not yield a vacuous grant | **KNOWN (shape)** | XACML separates NotApplicable from Indeterminate and makes the disposition an explicit combining algorithm |
| 14 | requiring that disposition to be source-grounded and auditable in an institutional compiler | **LEGAL EXTENSION** | Veraxis' contribution, not this artifact's |
| 15 | what makes a constrained completion space *institutionally* warranted | **OPEN** | the question for the legal side — see below |

## The one correction the sources forced on us

The contrast with PTaCL is **not** that its logic is immune. Read from its own
table (Fig. 1(e)): `¬⊥ = ⊥`, and a separate unary `∼` with `∼⊥ = 0`. Collapsing
an unverified ground into a false one **exists there too** — as an explicit
operator (`opt`) the policy author writes, locally and on purpose.

Under the greedy lift that collapse is the semantics: everywhere, always,
unwritten. So the honest sentence is *the exposure is bounded in PTaCL by where
`opt` appears and unbounded here* — it is the price of a default, not someone's
oversight and not our discovery.

## Where the legal question actually stands

It is **not** "nobody has asked who fixes the completion space". The 2019
authors say plainly that query constraints encode domain-specific requirements
and assumptions about which worlds are plausible. Computer security can say
`q' ∈ Q(A|C)` because the constraint declares it so.

The open question is the next one, and it is Arkadiy's formulation:

> What converts a **computational** constraint on admissible completions into
> an **institutionally warranted** constraint on legally permissible
> interpretations or factual states? Who had authority to establish it, for
> what purpose, under which source of law, at what time; may a defeating
> completion lawfully be excluded; and what happens to reliance when the
> constraint is later challenged?

Which is the corpus's own doctrine in another dress: *evaluation establishes
the property; issuance creates the reliance*. Resistance inside a constrained
state space is established. That an institution was entitled to choose that
state space as the operative one is not.

## Held back on purpose: E, and the case that will call for it

`E` is not in the brief for the legal side, and should not be added until a
legal distinction actually needs it. The distinction it would carry is between
*no proposition established* and *no proposition presented for adjudication* —
and the curator's example shows the difference is operational, not academic:

> **The murder weapon.** "The weapon has not been identified" — the object
> exists, the question is open, the case proceeds: examination, search, burden
> of proof. That is `Z`. "No weapon was entered into the case" — there is
> nothing to judge on that point at all. That is `E`.

The hazard is the one this artifact keeps meeting: **a vacuum reads in either
direction.** An unpresented object can be read silently as *the link is not
proven* or as *the prosecution's account stands unrefuted*, and both readings
come from the quantifier's default rather than from the case.

Note also that `E` attaches to a PREDICATE, not to a proceeding. A case may
stand without the weapon; then the predicate "the weapon carries trace X" is
`E` while the case rests on other grounds. `E` does not void the process — it
says this statement has no subject, so do not read its silence as an answer.

## Standing of this document

The PTaCL operator table was read from the paper itself. Everything else here
rests on abstracts, secondary description and Arkadiy's reading of the primary
sources — **not on our own full reading of each paper**. Before publication the
line-by-line check belongs to whoever signs the text.
