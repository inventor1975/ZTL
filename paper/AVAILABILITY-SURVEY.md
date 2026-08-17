# Availability survey — the mechanisms are old; where are the implementations?

**2026-08-17.** Adversarial review established that every mechanism in the
ledger note has a literature: truth-maintenance systems for the cascade,
common-cause failure analysis for pricing an unverifiable independence,
authorization logic for separating permission from support, provenance
semirings for lineage. The note withdrew its novelty claim in consequence.

That leaves a different and checkable question, and it was the curator's:
**a mechanism described in a paper is not a thing you can run.** Where a
predecessor exists in the literature, does it exist as free working software
that does what this ledger does?

## Method, and its weakness

PyPI queries for installable packages; web searches for maintained projects;
public documentation for licensing. Roughly thirty minutes, conducted with LLM
assistance on 2026-08-17. **This is not a systematic review.** A short search
finding nothing is weak evidence that nothing exists, and a single link from a
reader would overturn any row below. It is recorded so that it can be
overturned.

## What was found

| field | free working implementation? | notes |
|---|---|---|
| TMS / ATMS | **none found installable** | `pip index` finds no TMS package (`tms` on PyPI is a test-assertion matcher, `tweety` is a Twitter scraper). Implementations are research code from the 1980s–90s or embedded inside diagnosis and CAD systems. |
| argumentation, belief revision | **yes** — TweetyProject | Java, actively maintained, v1.28 (Jan 2025). Broad AI library. Does not price an unverified independence declaration. |
| provenance semirings | **yes** — ProvSQL | MIT, PostgreSQL extension, maintained. This row said "provenance annotation, not warrant withdrawal" before the package was installed. Withdrawal is `set_prob(token, 0)`, and it answers the post-withdrawal figure exactly. See the measured section below. |
| authorization / delegation | **yes** — OPA/Rego, Cedar, Zanzibar-style | Free, widely deployed. Zanzibar walks a relationship graph. None returns a bracket, and none records that a delegation's independence is unchecked. |
| common-cause failure | **none found free** | Isograph Reliability Workbench, ITEM iQRAS. Commercial, licence-locked per seat. The β-factor methodology is public (IEC 61508-6 Annex D); the tooling is not. |

## What this does and does not license us to say

**Not licensed:** any claim about speed. Measured on this machine, the cascade
runs 100,000 nodes and 1,000,000 edges in **117 ms of pure Python**. That is
adequate and it is not a selling point; nothing here has been optimised once,
and an engine written for the purpose would beat it comfortably. Speed is not
our argument and should not be made one.

**Licensed, and modestly** — *and REFUTED the same day; the two sections below
are the retraction, left after this paragraph rather than replacing it because
the sequence is the point*: the combination appears not to be available in one
free runnable object. Cascade with inheritance, a bracket that refuses to
collapse an unverifiable independence, exposure reported by unit, and a
support/permission distinction — each exists somewhere, two of them only
inside commercial reliability tooling, and no free artefact found does more
than one of them.

That is an **availability** claim, not a novelty claim, and the difference
matters: it is falsifiable by a link, it does not require anyone to have
failed to think of something, and it decays the moment someone packages the
same combination. It is worth exactly as much as the search behind it, which
is thirty minutes.

**Also licensed:** the honest framing for a citing reader. This is a small
free implementation of mechanisms that are individually old and collectively
scattered, with its ceilings computed rather than asserted. Whether that is
useful depends on whether the reader needs the combination and cannot buy it.

## Done since: the comparison, and it went against us

`db/probe_provenance.py` implements provenance semirings directly and runs the
same scenario through both formalisms.

**The semiring already does three of the ledger's four operations.** The
cascade is not a cascade there at all: set a variable to zero and evaluate.
Alternatives are addition. The exposed set is the polynomial's support. All
published in 2007, with a maintained free PostgreSQL implementation. Anyone
who needs those three should use ProvSQL and not this.

## Then the package was installed, and it took a fourth

The paragraph above compared the **formalism**, because Postgres was not on
this machine. That is a weaker thing to do than it sounds, and it produced an
error in our favour. PostgreSQL 16.14 and ProvSQL 1.13.0-dev were built from
source on 2026-08-17 and the eight auditor questions asked of the running
tool: `db/provsql_ledger.sql`, reproducible end to end.

| auditor question | ProvSQL 1.13, measured |
|---|---|
| 1–3. the plain figures | yes (arithmetic; provenance is not what answers them) |
| 4. which figures were never documented | **yes** — the DEFAULT mapping gives an undocumented row a bare token like any document, but `create_provenance_mapping` takes any column *or expression*, so `(ground IS NOT NULL)` with `sr_boolean` carries documented-ness to derived rows |
| 5. what rests on inv-17 | **yes**, cleanly |
| 6. inv-17 is forged, what falls | **yes** — withdrawal is `set_prob(token, 0)` |
| 7. what do the numbers become | **yes, and exactly**: `expected(sum(amount))` returns **2000** |
| 8. may I quote it | **yes** — `sr_minmax`, a shipped built-in, demonstrated in ProvSQL's documentation as *Minimum Security Clearance* |

**Question 7 is the one that was predicted wrongly, and the prediction was
written down first.** ProvSQL carries magnitudes through aggregation —
`expected`, `variance`, moments, and `support(sum(amount))` = **[0, 6500]**, a
genuine interval over the total. The claim that "semirings annotate, they do
not carry magnitudes" was false about the shipped tool, and the probe has been
corrected. Reasoning about what a package does not do is not a substitute for
installing it; a bare thirty minutes of building saved a false claim from
reaching a citing reader.

**What survived the run** was recorded here as "two and a half things": a
graded fact, a bracketed independence, and units. **Adversarial review the same
day took the first two.** They are shipped:

- **the earned/credit grade** — `sr_maxmin(token, token2value, element_one
  anyenum)`, a compiled built-in with ⊕ = enum-max and ⊗ = enum-min over any
  PostgreSQL ENUM. That is the lattice, generic over its carrier. Verified on
  this corpus's own ledger: one `CREATE TYPE`, zero lines of semiring code, and
  `line_a × quoted → credit`;
- **permission as a second grade** — `sr_minmax`, the shipped dual, which
  ProvSQL's documentation demonstrates under *Minimum Security Clearance*: the
  clearance needed to have inferred a derived fact. That is auditor question 8;
- **the bracket** — a default, not a capability. Their manual states
  tuple-independence as a default and ships `repair_key` for correlated
  annotation; one `UPDATE` pointing a row's token at another's yields the
  0.9000 reading directly;
- **units** — `sum()` over 2000 EUR and 40 hours returned **2040**, silently.
  Real, and a type-system property owing nothing to provenance. Worth little.

`support()` deserves its own line because it is nearly the bracket and is not:
it is the **unconditional** range over all worlds and stayed [0, 6500] after
conditioning, because it ignores the probabilities. ProvSQL brackets a total;
it does not narrow the bracket to a scenario.

**The verdict this survey was built to reach, reached.** The question it opened
with was whether a mechanism described in a paper exists as software one can
run. For this corpus's four properties the answer is yes, in one package, free,
maintained, and compiled. The survey's own closing warning — "an availability
fact with a shelf life" — turned out to have a shelf life of about six hours.
See `paper/PROVSQL-REVIEW-FINDINGS.md`.
