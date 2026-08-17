# Eight Questions to a Provenance System

### What a working lineage engine answers, and two answers an auditor should not accept

**Vitaly Reznik** · Independent researcher · 2026-08-17

> **STATUS: NOT FOR PUBLICATION — kept as a record.** Adversarial review on
> 2026-08-17 refuted the last claim this note made for itself: the earned/credit
> grade is a shipped ProvSQL built-in (`sr_maxmin`), as is the permission
> dimension (`sr_minmax`). Three rounds of checking each withdrew a claim and
> kept a remainder, and each next round found the remainder was also available.
> The document is corrected rather than deleted, and the corrections are left
> visible, because the sequence is the only thing here worth reading. See
> `paper/PROVSQL-REVIEW-FINDINGS.md`.

---

## Abstract

Database provenance answers *which tuples produced this row*. An auditor asks
something adjacent and not identical: *how much rests on this document, and how
sure am I allowed to be*. This note takes eight questions from the second
vocabulary, puts them to the leading free implementation of the first —
**ProvSQL** [17], the PostgreSQL realisation of provenance semirings [12] —
and reports what came back.

**It answered all eight.** Two of those answers were written here as failures
before review corrected them, and the corrections are the substance of what
follows. `expected(sum(amount))` returns the correct post-withdrawal total
directly — predicted impossible, in writing, before the run. The earned/credit
grade propagates through `sr_maxmin`, a shipped built-in over any enum, for the
price of a type declaration. The permission dimension is its shipped dual
`sr_minmax`, which ProvSQL's own documentation demonstrates as *Minimum
Security Clearance*.

One observation survives, and it is smaller than a finding. Two grounds named
`inv-17` and `invoice-17`, each at probability 0.9, come back as **0.9900 with
probability bounds of zero width** — a confident number that assumes the two
names are two pieces of paper. That is not a defect and not a property of the
formalism: ProvSQL's manual states tuple-independence as a **default** and
ships `repair_key` for correlated annotation. The other reading is one
statement away — point the second row's token at the first's and the same query
returns 0.9000.

So what separates this author's ledger from the engine is a **default**, not a
capability, and this note claims nothing beyond that. Every figure here is
printed by a script in a public repository; where an earlier draft printed one
that was not, §6 says so.

---

## 1. Why these questions, and whose they are

A provenance system and an auditor are interested in the same graph for
different reasons. The first wants to explain a result. The second wants to
know what a lie would cost.

The eight questions below are a day's ordinary work on a small ledger: three
invoice lines, a quoted figure nobody has documented, a contractual ceiling, a
payment. Two lines rest on one invoice.

| | question |
|---|---|
| 1 | What was spent in total? |
| 2 | What is the whole ledger's total? |
| 3 | Are we inside the ceiling? |
| 4 | Which figures have never been documented? |
| 5 | What rests on invoice inv-17? |
| 6 | inv-17 is forged. What falls? |
| 7 | What do the numbers become once it is withdrawn? |
| 8 | May I quote the margin in the report? |

**The list is the author's, and a list one writes oneself is a list one wins.**
It was drawn from the vocabulary of the ledger described in §6, which is the
strongest objection available to everything below: a differently-drawn list
would very likely leave nothing standing. The next measurement worth making is
against somebody else's list, and it has not been made.

---

## 2. What ProvSQL answers

PostgreSQL 16.14 with ProvSQL 1.13.0-dev, built from source; the ledger is one
table of seven rows with `add_provenance` applied and a token→document mapping
made by `create_provenance_mapping`. The transcript is `db/provsql_ledger.sql`
and runs end to end.

| question | answer |
|---|---|
| 1–3 | **yes** — arithmetic; provenance is not what answers them |
| 4 | **yes**, once the mapping is pointed at the right thing — see §3 |
| 5 | **yes**, cleanly: the formula for each line is the document's name |
| 6 | **yes** — withdrawal is `set_prob(token, 0)` |
| 7 | **yes, and exactly** — `expected(sum(amount))` returns the correct total |
| 8 | **yes** — `sr_minmax`, shipped, demonstrated in their docs as Minimum Security Clearance |

Question 7 deserves emphasis because it went against the prediction. ProvSQL
carries magnitudes through aggregation — `expected`, `variance`, moments — and
`support(sum(amount))` returns a genuine interval over the total. An earlier
draft of this note asserted that provenance systems annotate results without
carrying magnitudes. That was reasoning where a measurement was available, and
installing the package took under an hour.

There is one thing `support()` is worth separating from the bracket of §4: it
is the **unconditional** range across all possible worlds and ignores the
probabilities, so it does not narrow to a scenario. It brackets a total. It
does not bracket an assumption.

---

## 3. The first answer: a figure standing on nothing

Question 4 asks which figures have never been documented. In the test ledger
two of them have not: a quoted price and a payment, neither of which points at
any paper.

Under the **default** mapping, ProvSQL returns a token for each — a bare
identifier, structurally identical to the token of a line that stands on a real
invoice. Every base row is its own variable, so a fact supported by a document
and a fact supported by nothing but its own presence in the table arrive
looking the same.

That is where this section stopped, and stopping there was the error. The
default is not the formalism. What follows is the correction.

A grade that propagates is itself a semiring: a two-element lattice, EARNED
above CREDIT, with minimum for multiplication. An earlier version of this
section said that ProvSQL supports user-defined semirings and that **nobody
had written this one**.

**It ships.** `provsql.sr_maxmin(token, token2value, element_one anyenum)` is
a compiled built-in with ⊕ = enum-max and ⊗ = enum-min over any PostgreSQL
ENUM — that lattice exactly, generic over its carrier. Instantiating it on
this ledger costs a type declaration and no semiring code at all:

```
CREATE TYPE zgrade AS ENUM ('credit','earned');
SELECT sr_maxmin(provenance(),'zgmap','credit'::zgrade) ...
  line_a x line_c -> earned
  line_a x quoted -> credit
  line_c x quoted -> credit
```

The premise this section opened with — that the distinction "has nowhere to
live" — is false with it. It lives in the leaf annotation, and
`create_provenance_mapping` builds that from any column *or expression*, so
`(ground IS NOT NULL)` with `sr_boolean` carries documented-ness to derived
rows, which `WHERE ground IS NULL` cannot do.

---

## 4. The second answer: a point where there should be a width

Two grounds named `inv-17` and `invoice-17`, each believed at probability 0.9,
supporting one conclusion that stands if either does. ProvSQL renders the
provenance as `inv17 ⊕ invoice17` and evaluates it:

```
formula              probability   bounds
inv17 ⊕ invoice17    0.9900        [0.99, 0.99]
```

The number is right and the bounds are honest about what they are — they report
the precision of the *computation*, which is exact here. What neither reports
is that the whole result rests on an assumption nobody checked: that two names
are two pieces of paper. If they are one document filed twice, the conclusion
stands at 0.9, not 0.99, and **nothing in the output distinguishes the case**.

For a reader from data management this is unremarkable: independence is the
stated premise of the probabilistic model, and a model is entitled to its
premises. For a reader whose subject is evidence it is the whole problem. Two
photographs from one camera are one photograph; two orders under one commander
are one order; two copies of one invoice buy no redundancy whatsoever. An
instrument that prices such a pair at 0.9900 without remark is not lying, but
it is answering a question about *data* while being asked a question about
*the world*.

### 4.1 The objection to this note's own claim, run rather than argued

The obvious reply is that the bracket is no achievement, because ProvSQL can
compute both ends itself. **That reply is correct**, and it was tested rather
than conceded on argument. Encoding the same scenario twice — once with two
rows, once with one — the same engine returns:

```
reading A, two names are two papers    inv17 ⊕ invoice17    0.99
reading B, two names are one paper     inv17                0.90
```

So `[0.90, 0.99]` is available in ProvSQL to anyone who thinks to ask for it.

**And even this concession was too generous to us**, as review then showed. Two
encodings are not needed and nothing has to be combined by hand: one `UPDATE`
pointing the second row's `provsql` column at the first row's token expresses
"two names, one paper" inside a single table, and the identical query returns
0.9000 directly. ProvSQL's manual states the independence assumption as a
default in so many words — *"correlations between tuples are not modelled. To
model correlated probabilities, derive them explicitly with queries"* — and the
extension ships `repair_key` for block-independent-disjoint annotation, with
its own tests. §4 above called it a premise of the model; it is a setting.

What remains is therefore a **default and not a capability**. One instrument
prints 0.9900 unless the reader knows to ask otherwise; the other computes both
readings unasked, prints the width, and has no function that returns the cost
as a bare figure. The difference is entirely in what happens to the reader who
does *not* already know the question.

That is a very modest claim, and it is the only one this note still makes.

---

## 5. What the eight questions actually established

Stated compactly, because the tally moved three times during the writing and
each position was less flattering than the last.

**ProvSQL answers the lineage questions, and answers them better than this
author's alternative.** The cascade, the alternatives, the exposed set and the
post-withdrawal magnitudes are its subject; it is a compiled extension inside a
real database, and anyone who needs those should use it.

**And it answers the other four too.** The earned/credit grade: `sr_maxmin`,
shipped. Permission as a second grade: `sr_minmax`, shipped, with a worked
example in their documentation. The bracket: a default, one `UPDATE` from the
other reading. The single remaining difference — that a magnitude carries a
unit and refuses to be added to an incommensurable one; `sum()` over 2000 EUR
and 40 hours returned 2040 without complaint — is a property of a type system
and owes nothing to provenance.

**So nothing here is this author's**, and the useful part of the note is the
shape of how that was discovered. Three rounds. Round one withdrew a novelty
claim and kept four properties. Round two installed the package and lost two of
them. Round three read the function list and lost the rest. Every time, the
sentence that failed had the same form — *the tool does not do X* — and every
time it had been reached by reasoning rather than by typing `\df provsql.sr_*`.

That is worth recording as a measurement of distance rather than a list of
mistakes: on this subject the frontier is far enough ahead that an hour of
checking keeps finding another shipped feature, and there is no reason to
expect a fourth round to end differently.

---

## 6. The other default, briefly

The alternative referred to above is a small ledger the author maintains, and
it is described here only as far as is needed to say what "the other default"
means. It holds claims and grounds and **never verdicts** — a verdict is
recomputed on every reading, because a stored one is a judgement taken on credit
from a past moment.

Asked what a ground costs it returns both readings and the width between them.
`zbook.py` §12, complete and unedited:

```
   inv-17                 [0, 2]
   inv-17-photocopy       [0, 2]
   performed/zero         [0, 1]
   plain-deed             [1, 1]   <- zero width: nothing taken on trust
```

An earlier draft of this note printed that block with the third row removed
and no ellipsis — and it was the awkward row, whose low end of 0 is a refused
question coded as an integer rather than a measured cost. It is restored, and
the flaw it exposes is left visible: an integer low end cannot distinguish
"costs nothing" from "the question does not apply".

There is deliberately no function returning that cost as a bare figure, and
where the book takes something on trust it says so by name. §12 again:

```
   ASSUMED, and unverifiable: the 4 external names below denote 4 distinct grounds
   ['inv-17', 'inv-17-photocopy', 'performed/zero', 'plain-deed']
```

and, nine lines later and about a different pair, it prices a coincidence it
cannot resolve:

```
   if inv-17 and invoice-17 are one paper: 2 + 2 -> 4
```

The earlier draft ran those two together as one block, which put names into
the assumption line that were not in it. Both are quoted here as they print.

Exposure is reported by unit and never summed across incommensurable ones: a
ground carrying both a fee and an area returns two lines and no grand total,
and the refusal names both culprits. A ground records whether it *supports* a
conclusion or *permits* it, because a conclusion needs evidence to be supported
and authority to be permitted and falls when either fails — a distinction a
reader from law meets daily, since a fact survives the repeal of a statute and
a statute survives the discrediting of a witness.

None of that is a new mechanism, and §7 says where each was done first. It is
offered here as the worked example of a different default, not as a tool a
reader is urged to adopt.

---

## 7. What this note does not do

**It does not find a defect in ProvSQL.** Every behaviour in §§3–4 follows
correctly from the model's stated premises. The note is about what those
premises cost a reader who brought a different question.

**It does not detect a lie.** Every ground is a name taken on trust. Measured
against the Wirecard collapse, where €1.9bn rested on forged bank letters:
both instruments would have found the ground present and reported it clean, for
years. Against an adversary who controls the input, neither is weak — both are
**inert**.

**It does not discover a dependency.** Citations are honoured, never found. A
dependence nobody recorded is invisible to both, so a measured blast radius can
be understated and never overstated by this omission.

**It does not verify independence** — §4 — and therefore cannot be trusted
about redundancy. Declared redundancy resting on a shared origin reports a
safety it does not provide. Naming the assumption is not resolving it, and the
note claims only the naming.

**It does not compare a formula to an intention.** A spreadsheet dividing by a
sum where the author meant an average is well-formed, grounded, and returns a
clean verdict on a figure that is half of what was meant.

**And the finding is audience-dependent.** To a database researcher §§3–4 are
restatements of the model's premises and are not news. Their value, if any, is
to a reader who reaches for a provenance engine to answer an evidential
question and would otherwise take 0.9900 at face value.

---

## 8. Where this has been done before

The retraction cascade is the central operation of a **truth-maintenance
system** [1, 2] and no priority is claimed over it. Separating authority from
evidential support is older than this work by three decades: a modal `says` and
a `speaks-for` relation [3, 4], authorization certificates with k-of-n
threshold subjects [5], credential-chain discovery [6, 7]; withdrawal and
staleness of a credential are the subject of [8, 9, 10]. **Belief revision**
[11] studies what to give up when a new fact contradicts an old one.
**Provenance semirings** [12] and lineage systems [13] are the subject of this
note's measurement. **Argumentation frameworks** [14] compute which claims
survive attacks between them. Redundancy defeated by a shared dependency is
**common-cause failure**, standardised in reliability engineering [15, 16] —
where the unverifiable-independence problem of §4 has a name, a β-factor, and
sixty years of practice behind it.

That last citation was called, in an earlier draft, the strongest objection to
this note's framing. It is not, and the real one was missing entirely: **this
note's reference list contained no probabilistic-database entry at all.**

Tuple-independence is the standing assumption of that field and the standing
subject of its criticism. Dalvi & Suciu [18] and Fuhr & Rölleke [19] are the
model ProvSQL implements; **Sen & Deshpande [20]** exists because "current
probabilistic databases make simplistic assumptions about the data (e.g.,
complete independence among tuples)" — §4's observation, as a paper's opening
motivation, in 2007. **Trio/ULDB [21]** computes confidence through lineage
precisely because derived tuples are correlated. And most directly of all,
**Beskales et al. [22]** treat record identity as an unresolved decision and
return **min/max counts and confidence intervals instead of point values** —
which is this note's bracket, for this note's problem, in a database venue,
seventeen years before it.

Naming [22] is not a formality. It means the "different default" of §4.1 is
not even a different default: it is a published one, in the field the
measurement was made in. What survives is the narrow observation that the
default *shipped* in ProvSQL is the un-bracketed one, which is checkable in a
few lines and is a fact about a package rather than about a subject.

---

## 9. Reproduction

The ledger and its probes need the standard library only:

```
python3 zbook.py                    the ledger of §6
python3 db/probe_provenance.py      the semiring comparison
python3 db/probe_ledger.py          the same facts with and without warrants
python3 run_all.py                  the full suite and the Lean corpus
```

The measurements of §§2–4 need PostgreSQL with ProvSQL loaded
(`shared_preload_libraries = 'provsql'`, then `CREATE EXTENSION provsql
CASCADE` and `SELECT provsql.setup_search_path()`):

```
psql -d provtest -v ON_ERROR_STOP=1 -f db/provsql_ledger.sql
```

The logic underneath the ledger is machine-checked in Lean 4 and prints an
empty axiom list. That result concerns the calculus, not the ledger built on
it, and the two are separate contributions.

---

## References

1. Doyle, J. A truth maintenance system. *Artificial Intelligence* 12(3),
   1979, 231–272.
2. de Kleer, J. An assumption-based TMS. *Artificial Intelligence* 28(2),
   1986, 127–162.
3. Abadi, M., Burrows, M., Lampson, B., Plotkin, G. A calculus for access
   control in distributed systems. *ACM TOPLAS* 15(4), 1993, 706–734.
4. Lampson, B., Abadi, M., Burrows, M., Wobber, E. Authentication in
   distributed systems. *ACM TOCS* 10(4), 1992, 265–310.
5. Ellison, C., et al. SPKI certificate theory. RFC 2693, IETF, 1999.
6. Blaze, M., Feigenbaum, J., Lacy, J. Decentralized trust management. *IEEE
   S&P*, 1996.
7. Li, N., Mitchell, J., Winsborough, W. Design of a role-based trust
   management framework. *IEEE S&P*, 2002.
8. Burrows, M., Abadi, M., Needham, R. A logic of authentication. *ACM TOCS*
   8(1), 1990, 18–36.
9. Stubblebine, S. Recent-secure authentication. *IEEE S&P*, 1995.
10. Rivest, R. Can we eliminate certificate revocation lists? *Financial
    Cryptography*, 1998.
11. Alchourrón, C., Gärdenfors, P., Makinson, D. On the logic of theory
    change. *Journal of Symbolic Logic* 50(2), 1985, 510–530.
12. Green, T., Karvounarakis, G., Tannen, V. Provenance semirings. *PODS*,
    2007, 31–40.
13. Cheney, J., Chiticariu, L., Tan, W.-C. Provenance in databases.
    *Foundations and Trends in Databases* 1(4), 2009, 379–474.
14. Dung, P. M. On the acceptability of arguments. *Artificial Intelligence*
    77(2), 1995, 321–357.
15. IEC 61508-6:2010, Annex D.
16. NUREG/CR-5485. US NRC, 1998.
17. Senellart, P., Jachiet, L., Maniu, S., Ramusat, Y. ProvSQL: provenance and
    probability management in PostgreSQL. *PVLDB* 11(12), 2018, 2034–2037.
18. Dalvi, N., Suciu, D. Efficient query evaluation on probabilistic databases.
    *The VLDB Journal* 16(4), 2007, 523–544.
19. Fuhr, N., Rölleke, T. A probabilistic relational algebra for the
    integration of information retrieval and database systems. *ACM TOIS*
    15(1), 1997, 32–66.
20. Sen, P., Deshpande, A. Representing and querying correlated tuples in
    probabilistic databases. *ICDE*, 2007, 596–605.
21. Benjelloun, O., Das Sarma, A., Halevy, A., Widom, J. ULDBs: databases with
    uncertainty and lineage. *VLDB*, 2006, 953–964.
22. Beskales, G., Soliman, M., Ilyas, I., Ben-David, S. Modeling and querying
    possible repairs in duplicate detection. *PVLDB* 2(1), 2009, 598–609.

Author, venue and year were checked for each; page ranges and annex structure
were not independently verified against printed sources. The search behind §8
was LLM-assisted and is not a systematic review — and [18]–[22] are there
because an adversarial review found that the first version of this list had no
probabilistic-database entry at all, while making a claim about probabilistic
databases. The absence of a field from such a list is not weak evidence of
anything; it is evidence about the list. Reference [17] is a further exception:
it was not only cited but installed and run, and doing so refuted four claims
earlier versions of this note had made.

---

## Acknowledgement

Built with Claude (Opus 5) as architect and implementer, under Variant A, with
Vitaly Reznik as human curator. Every figure above is printed by a program in a
public repository and re-checked by its regression suite.
