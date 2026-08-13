# Known limits — what this instrument cannot do, and what is not finished

Two different lists, kept apart on purpose. A **ceiling** is something the
instrument cannot do by its nature; naming it is not an apology and it will not
be closed by more work. A **gap** is unfinished work with a known shape. A
classification that does not know its own borders is one more total theory, and
the same applies to a judge.

Revision 2026-08-13. Add to this file rather than to a commit message when
something is found and not fixed the same day.

---

## Ceilings — permanent, by the nature of the thing

**Independence between documents cannot be verified.** Writing
`earned:inv-17|inv-18` asserts that two grounds are independent, so that losing
one leaves the claim standing. Two photocopies of one invoice buy the same
immunity and nothing here detects it (`dilemmas/agrippa_book.py` §7). Where both
grounds are CLAIMS the graph does check it and a shared ancestor refutes the
declaration by name — that half is closed. Between external documents it is not,
and cannot be.

**Nullarity cannot be verified — for OPAQUE grounds only.** Narrowed
2026-08-13 on the curator's question, "can the descent not catch it?" It can.
Where the book can descend into a ground, nullarity is COMPUTED: a claim with no
quantities demanded nothing, so there is nothing anyone could withdraw, and
claims resting on it inherit the perpetuity as a checked property (`zbook` §13).
`earned:performed/x` remains a declaration, and remains unverifiable, only for
grounds the book cannot see into — an act performed outside it. The rule is
exact: transparent grounds are checked, opaque grounds are declared. It is also
why VR's machine-confirmed `[]` is stronger than any label here could be, since
the elaborator walks the whole construction and reports what it leans on.

**Citations are honoured, never discovered.** The book computes what falls when
a ground goes, but only along links a human wrote down. A dependence nobody
recorded is invisible, so a measured blast radius can be UNDERSTATED and never
overstated. Stated in `inventory/corpus_book.py` as that file's own ceiling.

**No premise selection.** Nothing finds the relevant stored claims for a new
question. That is a crowded field with strong tools (Sledgehammer and its kin)
and this corpus would lose there; declined rather than postponed
(`zbook.py`, last section).

**Numbers, not prose.** Every claim can be re-measured and match while the
sentence interpreting it in a paper is false. `inventory/paper_claims.py` and
`docket_claims.py` compare tables to code and read nothing around them. This is
exactly where Frege's mistake lived and nothing in this corpus closes it.

**One warranty is not one number.** `epochs_matter` (lean/EpochBoundary.lean,
empty axiom list) proves that invariance under learning and invariance under
world-change are different properties, so "how well is this earned" cannot
collapse to a single grade. Three axes are read through one frame instead
(`zbook`, section 11) — the frame is the fix; the merger is impossible.

### The reporting discipline

`cost(book, ground)` is the only way to ask what a ground costs, and it cannot
answer with a single number: it returns both ends and the width. `fallout`
remains as the raw event list of ONE reading, with a docstring saying in
so many words that its length is not the cost. This closes the possibility of
quoting the optimistic figure without the thing that makes it trustworthy — it
does not close the ceiling above, and is not meant to.

### How the ceilings are handled rather than hidden

The two unverifiable declarations above are not left to rot inside a verdict.
Every ground carries a **trust bracket** (`zbook.trust_interval`): the low end
reads the book believing every declaration, the high end assumes each one
false, and the true cost lies between. The WIDTH of the bracket is exactly the
price of the author's unverifiable word, and a book that took nothing on trust
has zero-width brackets throughout — which `inventory/corpus_book.py` now
checks of this corpus rather than promising.

This is the corpus's own habit turned on itself. The numeric floor never drops
an unknown and never guesses it; it returns an interval and a theorem that the
answer is inside. A ledger built on declarations owes the same. The point is
worth stating precisely: the judge's guarantee was always conditional AND total
— given this marking, this verdict, nothing claimed outside its jurisdiction —
and the book was the first component here whose output could be wrong in a way
its input did not show. With the bracket it no longer reports a number it might
miss; it reports a range it cannot.

---

## Gaps — unfinished, with a known shape

**Three built cases are placed nowhere.** `dilemmas/lifeline.py`,
`ought_can.py`, `closure.py` run green in the suite and appear in no paper. Not
a defect, but they are findings sitting in a drawer.

**The docket borrows a term it did not earn.** §5 of the paradox docket calls
Moore and the surprise exam instances of "the epoch boundary of §§21-23".
Measured 2026-08-13 (`dilemmas/epoch_line.py`): Moore is a constraint inside a
single marking and the surprise exam is monotone time; only Berry needs an
expire. v1.1 is published (DOI 10.5281/zenodo.21916017), so this is a v1.2 line.
The Berry sentences are correct as they stand.

**The docket's glossary overstates one ceiling.** It says the machine "records
and cannot verify" both declarations. Since the shared-ancestor check went in,
that is true only between documents. Also a v1.2 line.

**The §5 through-line has no successor.** The five non-loop cases were expected
to share a mechanism; the epoch half of that was tested and refused. Whether
the lottery and the sorites share the OTHER proposed mechanism — credit is not
a witness — has not been tested, and should not be written up before it is.

---

## Closed, so that the list stays honest

Things that appeared on a list like this and are now done, kept for one
revision so a reader can see the difference between a ceiling and a gap:

- declarations hidden inside a bare EARNED — closed 2026-08-13, the verdict
  carries the assurance frame and inherits it along citations;
- independence undetectable *between claims* — closed the same day, the shared
  ancestor is computed and named;
- retraction unrelated to E25's expiry — closed the same day: the correspondence
  is named and the declared scope added;
- the five philosophical case stands outside the regression suite — wired the
  same day, after three months of holding by luck.
