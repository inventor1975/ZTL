# Review of the ProvSQL note — the last remainder was also shipped

**2026-08-17.** Fifteen agents, five lenses, each finding put to a refuter that
defaults to "refuted" unless the objection can be run. Ten findings, six
survived. Every load-bearing one below was then **re-verified by hand** against
the running database before being written down, because a review is a claim
like any other.

## The blocking finding, found independently by three lenses

The note said, of a fact graded EARNED or ON CREDIT:

> A grade that propagates is itself a semiring: a two-element lattice, EARNED
> above CREDIT, with minimum for multiplication. ProvSQL supports user-defined
> semirings and its own test suite writes one. **Nobody has written this one.**

**That semiring ships.** `provsql.sr_maxmin(token uuid, token2value regclass,
element_one anyenum)` is a compiled built-in with ⊕ = enum-max and ⊗ =
enum-min, generic over any PostgreSQL ENUM — which is exactly "a lattice with
minimum for multiplication". Verified here, on the note's own ledger:

```sql
CREATE TYPE zgrade AS ENUM ('credit','earned');
SELECT create_provenance_mapping('zgmap','zg','grade');
SELECT sr_maxmin(provenance(),'zgmap','credit'::zgrade) ...
  line_a x line_c -> earned
  line_a x quoted -> credit
  line_c x quoted -> credit
```

One `CREATE TYPE` and zero lines of semiring code. The grade propagates today.
Its dual `sr_minmax` ships too, and ProvSQL's documentation demonstrates it
under the heading **Minimum Security Clearance** — which is question 8, the
authority dimension, also answered.

So the tally that the note reported as "two and a half things" and then as
"no capability gap, but nobody has written it" is now simply: **nothing.**
Every property the ledger claimed is in the shipped extension.

## What else the review found, all re-checked by hand

**The version figure is wrong.** The note says PostgreSQL 16.10 throughout.
This machine runs **16.14** and never ran 16.10. It is the first line a
replicator checks, in a note whose whole standing is "measured, not argued" —
and it escaped the repo's own orphan-figure scan because the exemption list
added the same morning exempts the string `16.10` as "a version string". The
exemption was introduced to stop a false alarm and it created a blind spot in
the same commit. That is the second time in one day an instrument built to
catch errors introduced one.

**Two code blocks in §6 are not program output.** The bracket listing silently
drops the third of four rows (`performed/zero [0, 1]`) with no ellipsis — and
the dropped row is the awkward one, whose low end of 0 is a refused question
coded as an integer rather than a measured cost. The `ASSUMED, and
unverifiable` block splices lines from two different ledgers. In a note whose
Acknowledgement says every figure is printed by a program, these are the worst
defects on the list, and they are ours alone.

**Independence is documented as a default, not a limitation.** ProvSQL's own
manual: *"correlations between tuples are not modelled. To model correlated
probabilities, derive them explicitly with queries"* — and it ships
`repair_key` for block-independent-disjoint annotation, with tests. The note's
§4 presented tuple-independence as a property of the formalism. The note's own
thesis (a default, not a capability) was right; §4's framing of it was wrong.

**Even §4.1 understated it.** The note said the two readings need two
encodings combined by hand. They need one statement: point the second row's
`provsql` column at the first row's token and the same query returns 0.9000
directly.

**The reference list has no probabilistic-database entry at all.** Missing and
on-point: Sen & Deshpande, *Representing and Querying Correlated Tuples in
Probabilistic Databases* (ICDE 2007) — whose stated motivation is that
probabilistic databases assume complete tuple independence; Trio/ULDB
(Benjelloun et al., VLDB 2006), whose reason for computing confidence through
lineage is precisely that derived tuples are correlated; Dalvi & Suciu; Fuhr &
Rölleke. And most directly, **Beskales et al., PVLDB 2(1), 2009**, which
treats record identity as an unresolved decision and returns **min/max counts
and confidence intervals instead of point values** — the note's bracket, for
the note's problem, in a database venue, seventeen years earlier.

## The verdict this forces

Three rounds of withdrawal, and each round found that the remainder was also
available:

| round | what was claimed | what checking found |
|---|---|---|
| survey | four properties, novel | mechanisms all old (TMS, authorization, CCF, semirings) |
| installing ProvSQL | four properties, unavailable | magnitudes shipped; bracket computable |
| this review | one lattice, unwritten | **it ships, and so does the authority dual** |

That is no longer a sequence of corrections. It is a **measurement of
distance**: on this subject we are far enough from the frontier that every
hour of checking finds another shipped feature, and there is no reason to
believe a fourth round would end differently.

What is untouched by any of this is the logic — a new matrix, machine-checked
on an empty axiom list, provably identical to classical logic on Z-free
valuations (`lean/ClassicalAgreement.lean`). Nothing in three rounds has
touched it, because none of this was ever about it.
