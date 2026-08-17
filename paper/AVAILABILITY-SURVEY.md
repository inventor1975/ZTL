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
| provenance semirings | **yes** — ProvSQL | MIT, PostgreSQL extension, maintained. Excellent at what it does; provenance annotation, not warrant withdrawal. |
| authorization / delegation | **yes** — OPA/Rego, Cedar, Zanzibar-style | Free, widely deployed. Zanzibar walks a relationship graph. None returns a bracket, and none records that a delegation's independence is unchecked. |
| common-cause failure | **none found free** | Isograph Reliability Workbench, ITEM iQRAS. Commercial, licence-locked per seat. The β-factor methodology is public (IEC 61508-6 Annex D); the tooling is not. |

## What this does and does not license us to say

**Not licensed:** any claim about speed. Measured on this machine, the cascade
runs 100,000 nodes and 1,000,000 edges in **117 ms of pure Python**. That is
adequate and it is not a selling point; nothing here has been optimised once,
and an engine written for the purpose would beat it comfortably. Speed is not
our argument and should not be made one.

**Licensed, and modestly:** the combination appears not to be available in one
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

`db/probe_provenance.py` implements provenance semirings directly — Postgres
is not on this machine, so the FORMALISM is compared rather than the package —
and runs the same scenario through both.

**The semiring already does three of the ledger's four operations.** The
cascade is not a cascade there at all: set a variable to zero and evaluate.
Alternatives are addition. The exposed set is the polynomial's support. All
published in 2007, with a maintained free PostgreSQL implementation. Anyone
who needs those three should use ProvSQL and not this.

What is left is narrower and checkable rather than novel: magnitudes carried
with units and refused when incommensurable; a fact graded earned or on credit
rather than only supported or unsupported; evidence kept apart from authority;
and the unverifiability of an independence declaration reported as a bracket
instead of left implicit in the choice of variable names.

**And the warning that goes with it.** Four of those are things a semiring
could be extended to do — units and grades in a richer semiring, dimensions in
a product of two. That nobody has packaged the extension is an availability
fact with a shelf life, not a limit of the formalism.
