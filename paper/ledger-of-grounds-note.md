# A Ledger of Grounds

### What falls when a ground falls, and what the machine refuses to tell you

**Vitaly Reznik** · Independent researcher · 2026-08-17

---

## Abstract

A conclusion rests on grounds: a document, an act, an authority, another
conclusion. When a ground is withdrawn — a paper turns out to be forged, a
certificate lapses, a delegation is revoked — some conclusions stop standing
and others do not, and which is which is normally something a person
remembers. This note describes a small machine that computes it instead, and
spends most of its length on what the machine refuses to do.

Three properties are the subject. Withdrawal **propagates prospectively**
through the dependency structure, reaching conclusions that never named the
withdrawn ground. The cost of a withdrawal is reported as a **bracket, never
as a single number**, because part of it rests on a declaration the machine
cannot check. And a ground carries a **dimension** — whether it *supports* a
conclusion or *permits* it — because losing permission and losing support are
different failures and a conclusion needs both.

None of the mechanisms are novel and §7 says where each was done first. What
is offered is narrower and, for some readers, more useful: a working ledger in
which a withdrawal is computed rather than remembered, in which the
unverifiability of a declared independence is a **first-class output** rather
than a footnote — a bracket, an itemised assumption, a priced coincidence —
and in which support and permission are held apart so that losing one is not
mistaken for losing the other. It is a few hundred lines over a calculus
machine-checked on an empty axiom list, and every figure below is printed by
a program a reader can run.

---

## 1. The ledger

The store holds claims and grounds and **never verdicts**. A verdict is
recomputed on every reading, because a stored one is a judgement taken on
credit from a past moment, when the ground may since have expired and the
judge may since have changed.

A quantity's ground may be:

| form | meaning |
|---|---|
| `inv-17` | an opaque external name — the machine never looks inside |
| `claim/c1` | another claim in the same ledger |
| `expiring/cert-9` | a ground carrying a clock |
| `performed/x` | an act with no inputs, which cannot be withdrawn |
| `authority/order-4` | a permission rather than a support (§4) |
| `inv-17\|inv-18` | two grounds declared independent, either sufficing |

Three operations follow from that shape without further rules.

**Warranty is inherited.** A citation is honoured exactly as far as the cited
claim currently stands. Cite anything short of EARNED and the citing quantity
drops to credit.

**Retraction travels.** Withdraw one ground and the whole subtree moves,
including claims that never mentioned it. In the corpus's own example, a
correction to a spreadsheet moves three storeys and reaches a recommendation
that never named the spreadsheet.

**Exposure is measured by unit.** The ledger reports *how much* rests on a
ground rather than how many claims do — and never sums across incommensurable
units. One ground carrying both a fee and an area returns two lines and no
grand total; adding metres to roubles is refused outright, and the refusal
names both culprits.

This last is worth a sentence for a reader from law rather than engineering.
The machine's answer to an ill-posed comparison is not an error and not a
guess: it is a fourth verdict, computed, meaning *these two cannot be
compared and here is why*.

---

## 2. Cost is a bracket, never a number

Asked what a ground costs, the ledger returns **both readings and the width
between them**: the low end believes every declaration of independence in the
book, the high end assumes each one false, and the truth lies between.

```
inv-17                 [0, 2]
inv-17-photocopy       [0, 2]
plain-deed             [1, 1]   <- zero width: nothing taken on trust
```

There is deliberately **no function that returns this cost as a bare
figure**. A number quoted without its width is a number quoted without the
thing that makes it trustworthy, and the omission is a design decision rather
than an oversight — the raw event list remains available and its
documentation says, in so many words, that its length is not the cost.

The width has a precise meaning: it is the **price of the author's
unverifiable word**. A ledger that took nothing on trust has zero-width
brackets throughout.

Where a book takes something on trust it also says so by name, and prices the
possibility it cannot resolve:

```
ASSUMED, and unverifiable: the 4 external names below denote 4 distinct grounds
if inv-17 and invoice-17 are one paper: 2 + 2 -> 4
```

The machine cannot determine whether those two names are one document. It can
state the assumption, list the names it applies to, and compute what a
coincidence would cost — which is a different thing from resolving it, and is
said to be.

---

## 3. Alternatives, and a confirmation from outside

`inv-17|inv-18` declares that two grounds are independent, so that losing one
leaves the claim standing. **The machine cannot verify the declaration.** Two
photocopies of one invoice buy the same immunity as two documents, and nothing
here detects it. Where both alternatives are claims *inside* the ledger the
shared ancestor is computed and named by name; between external papers it is
not, and the line is drawn rather than blurred.

That ceiling is not peculiar to this work. A dependency graph on the machine
this note was written on — a Debian package database, 2,444 packages and
12,266 requirement groups — uses **the same notation for the same idea**:
`Depends: libfoo | libbar`, a requirement satisfied by either. Measured there:

- **2.6%** of requirement groups offer an alternative at all;
- `libgcc-s1` and `libc6` each carry **86.8%** of the installed system;
- and an alternative is defeated in exactly the way described above if both
  branches rest on the same library underneath — which a package manager
  forty years old does not detect either.

The notation was arrived at here independently, from a philosophical problem
about regress rather than from software distribution. That two fields reached
the same mark for the same idea, and stopped at the same wall, is the reason
the wall is described in this note rather than apologised for.

---

## 4. The dimension of a ground

`earned:inv-17` and `earned:order-4` were, until recently, the same kind of
thing to this ledger — though the first attests a fact and the second confers
a right. They are not the same. A conclusion needs evidence to be *supported*
and authority to be *permitted*, and it falls when **either** fails.

The ledger now records which, and computes the consequence a reader from law
will recognise:

```
mission.advance  both grounds are authority  ['authority/order-4', 'authority/order-9']
survey.width     both grounds are evidence   ['photo-a', 'photo-b']
```

`supply.fuel`, which stands on a document *and* an order, is not listed:
losing either leaves it standing. The two listed claims carry declared
redundancy that buys nothing against the failure that matters — two orders
under one commander are one order, two photographs from one camera are one
photograph.

For a normative memory this is the ordinary case rather than the exotic one.
An interpretation rests on evidence about the world and on the authority of
the norm it reads, and those lapse independently: a fact survives the repeal
of a statute, and a statute survives the discrediting of a witness.

The ceiling here is exact and worth stating beside the function: this checks
that two grounds are of different **kinds**, never that they are
**independent**. Two orders from two commanders under one general are still
one order, and nothing here sees it.

---

## 5. What this does do

Stated plainly, because the two sections that follow are about limits and
about other people's work, and a reader is entitled to know what is left.

**It answers, by computation, a question normally answered from memory.**
Given a ledger and a withdrawn ground, it names what stops standing —
including claims that never mentioned that ground. The mechanism is a
truth-maintenance system's [1, 2]; what is offered is that it is *in a
ledger of ordinary claims*, that the answer is recomputed on every reading
rather than stored, and that it costs nothing to run.

**It refuses to compress an unverifiable declaration into a number.** This is
the part with no equivalent in the systems of §6. A TMS returns the
assumption set behind a conclusion; it does not price the fact that
"assumption A and assumption B are independent" is itself unchecked. Here
that unverifiability is a first-class output: a bracket whose width is the
cost of the author's word, an itemised list of which names the assumption
covers, and a computed price for the coincidence the machine cannot rule out.

**It keeps support and permission apart in the same store.** Authorization
logics separate them for access control [3, 4, 5]; ledgers of claims do not
separate them at all. Holding both, with retraction travelling through each,
is what lets the ledger say that two orders under one commander are one
order.

**It holds six kinds of ground in one structure and retracts them
uniformly** — an opaque document, another claim, a clock, an act with no
inputs, an authority, and a declared alternative. Adding a kind did not
require a new rule for retraction; that is a property of the shape rather
than an achievement, and it is why the dimension of §4 could be added in an
afternoon without disturbing anything.

**And it is small.** The core is machine-checked in Lean 4 on an empty axiom
list, the ledger is a few hundred lines of standard-library Python, and every
figure in this note is printed by a program that a reader can run.

What it is NOT is a discovery. Everything above is either an old mechanism
put in a new place or a design decision about what to refuse. Whether that is
worth having depends entirely on whether the refusals are the ones a
particular reader needs.

---

## 6. What this does not do

Stated at length because the mechanisms of §§1-4 are simple and their
limits are where most of the interest lies.

**It does not detect a lie.** Every ground is a name taken on trust. Measured
against the Wirecard collapse, where €1.9bn rested on forged bank letters: the
ledger would have found the ground present and printed a clean EARNED for
years. Against an adversary who controls the input this machine is not weak,
it is **inert**.

**It does not discover a dependency.** Citations are honoured, never found. A
dependence nobody recorded is invisible, so a measured blast radius can be
understated and never overstated by this omission.

**It does not verify independence.** §3. Nor, therefore, can it be trusted
about redundancy: declared redundancy resting on a shared origin reports a
safety it does not provide.

**It does not compare a formula to an intention.** A spreadsheet dividing by a
sum where the author meant an average is well-formed, grounded, and returns
EARNED on a figure that is half of what was meant. There is no second copy of
the intention to compare against.

**It does not establish permission.** The dimension of §4 records that a
ground is an authority; whether that authority holds, and whether anyone may
act on the result, is decided outside. This work computes the consequences of
authority and does not confer it.

---

## 7. Where this has been done before

The retraction cascade of §1 is the central operation of a **truth-maintenance
system** [1, 2], and no priority is claimed over it. The separation of
authority from evidential support in §4 is older than this work by three
decades: a modal `says` and a `speaks-for` delegation relation [3, 4],
authorization certificates with k-of-n threshold subjects [5], credential-chain
discovery [6, 7]. Withdrawal and staleness of a credential are the subject of
[8, 9, 10]. **Belief revision** [11] studies what to give up when a new fact
contradicts an old one; **provenance semirings** [12] and lineage systems [13]
annotate results with what produced them; **argumentation frameworks** [14]
compute which claims survive attacks between them. Redundancy defeated by a
shared dependency — §3 — is **common-cause failure**, standardised in
reliability engineering [15, 16].

What this note offers is not a new mechanism but a small implementation in
which the ceilings are first-class: the bracket that refuses to collapse, the
assumption printed with the names it covers, the dimension that says which
kind of loss a ground protects against. Whether that is worth having is for a
reader with a normative memory to judge.

---

## 8. Reproduction

Standard library only, no dependencies:

```
python3 zbook.py                 the ledger, sections 1-16
python3 db/probe_real.py         the Debian measurement of §3
python3 db/probe_ledger.py       the same facts with and without warrants
python3 run_all.py               115 stands and the Lean corpus
```

The logic underneath is machine-checked in Lean 4 and prints an empty axiom
list. That result concerns the calculus, not the ledger built on it, and the
two are separate contributions.

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

Author, venue and year were checked for each; page ranges and annex structure
were not independently verified against printed sources. The search behind §7
was LLM-assisted and is not a systematic review, so the absence of a field
from that list is weak evidence of anything.

---

## Acknowledgement

Built with Claude (Opus 5) as architect and implementer, under Variant A, with
Vitaly Reznik as human curator. Every figure above is printed by a program in
a public repository and re-checked by its regression suite.
