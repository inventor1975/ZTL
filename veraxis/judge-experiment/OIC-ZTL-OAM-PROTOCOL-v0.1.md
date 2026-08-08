# OIC–ZTL–OAM Protocol v0.1

**Document ID:** `OIC-ZTL-OAM-PROTOCOL-v0.1`
**Status:** REVISED CANDIDATE (revision 2) — returned for owner/adjudicator review after `REVISION_REQUIRED_BEFORE_FREEZE`; not frozen; not executable authority.
**Steering:** Vitaliy Reznik (post-M1 protocol phase, per owner authorization of 2026-08-09).
**Drafted:** 2026-08-09, by Claude (Fable 5) under the steering role's direction (Variant A: the human owns decisions and answers for the result).
**Governing predecessor state:** Review Ledger `main` = `060efa2cc295e0d7d9960f725aece264fc471935` (M1 `CLOSED_BY_ACCEPTED_FALSIFICATION`; falsification basis F1+F3+F6+F7; F4 not sustained as labeled; no replacement causal hypothesis).
**Prior candidate:** commit `3c6a8cf`, SHA-256 `e207a243…`; the semantic core of that candidate was ACCEPTED and is preserved here; the changes of this revision are accounted in Appendix D.

---

# PART I — THE SEMANTIC CONTRACT

## 0. Purpose and scope

This protocol defines the semantic contract between three layers of an institutional
computation stack:

- **OIC** (Institutional Computation): the layer that **preserves and compiles**
  institutional meaning. The institution — the authorized institutional actor — is the
  source of authoritative meaning; OIC preserves authoritative source anchors, exposes
  ambiguity and conflict, records admission, represents stipulated institutional
  meaning, and compiles admitted/stipulated meaning into formal formulas and
  projections. OIC does not originate institutional meaning, authority, or warrant.
- **ZTL** (Zero-Trust Logic): the layer that mechanically evaluates what follows from
  admitted grounds — the judge.
- **OAM** (the audit/reconstruction layer): the layer that lets an independent party
  later reconstruct why a transition was permitted.

It is **implementation-ready at the semantic level and implementation-neutral**: it
fixes meanings, records, transitions and their falsification conditions, and does not
prescribe transports, storage layouts, process boundaries, or languages.

Two distinctions are frozen throughout, in the shared terminology already agreed:

> **D1.** A judge establishes a **contemporaneous logical-warrant record (CLWR)**.
> Institutional warrant is broader and is **not** created by the judge; it includes the
> relevant authority, admissibility, sufficiency, and reliance conditions.

> **D2.** **Evaluation establishes the property. Issuance creates the reliance.**

Every normative rule in this document (`R-xx`) is stated with five fields —
*input state; condition evaluated; permitted output/transition; observable evidence of
compliance; falsifying counterexample* — so that conformance to this protocol is itself
a checkable, falsifiable property (§16).

Part II defines the preregistered experiment by which the mechanical-judge role is to
be tested before any implementation reliance.

## 1. Actors and roles

| Role | Owns | May not |
|---|---|---|
| **Institution / authorized institutional actor** | authoritative meaning; stipulations; institutional determinations; issuance decisions; phase boundaries | mark atoms as earned; alter a CLWR |
| **OIC (compilation layer)** | preserving source anchors; exposing ambiguity/conflict; recording admission of meaning; compiling stipulated meaning into formulas/projections | originating meaning, authority, or warrant; issuing reliance |
| **Evidence custodian (admission layer)** | admitting atoms into markings, with witnesses; provenance discipline; marking succession (§3.2) | authoring formulas; issuing reliance |
| **Judge (ZTL)** | computing dispositions, grades and weak links over a JudgeContext; emitting CLWRs | originating authority or admission; upgrading its own output's institutional status |
| **Independent reviewer** | verifying records against evidence; adjudicating conformance to frozen texts | repairing evidence; converting review acceptance into owner acceptance |
| **Relying party** | acting on **issued, currently active** claims | acting on bare CLWRs |

One natural person or system may hold several roles only where the governing
institutional rules explicitly allow it; the **judge role is never combined** with the
institutional-actor or admission roles for the same evaluation.

## 2. Definitions

- **Atom** — the smallest evaluable proposition; carries exactly one status in a
  marking.
- **Status** (of an atom in a marking) — `T` (earned: a completed verification act
  supports it), `F` (refuted: a completed verification act stands against it), `Z`
  (**unverified/unknown marked ground; default-deny**). `Z` is not a probability and
  not a permission: it is the absence of an admitted act, and nothing qualifying may
  be built on it.
- **Witness** — the hash-bound evidence artifact (or artifact set) produced by the
  verification act that grounds a `T` or `F` status **for that specific atom and
  status** (R-02/R-03).
- **Marking** — an immutable, versioned finite map atom → status, together with
  witness references for every non-`Z` status. Markings change only by succession
  (§3.2), never in place.
- **Formula** — a finite composition of atoms under the frozen connective semantics of
  the judge implementation; the formal content of a claim.
- **Claim** — a formula together with its stipulating authority and intended
  institutional reading.
- **JudgeContext** — the hash-bound triple: **formula identity + marking identity +
  judge semantics/implementation identity**. The judge computes over JudgeContexts and
  over nothing else.
- **ClaimContext (institutional envelope)** — the hash-bound tuple: **stipulation
  identity + authority identity + institutional reading/scope + JudgeContext
  identity**. The ClaimContext belongs to the institutional layer; the judge has no
  authority over it.
- **Disposition** (kernel-exact) — the judge's output kind:
  - `EARNED` = verdict `T` **with grade `hereditary`**;
  - `REFUTED` = verdict `F` **with grade `hereditary`**;
  - `ON CREDIT` = verdict `T` with a non-`hereditary` grade;
  - `OPEN` = otherwise non-established under the current marking.
  `ON CREDIT` names a **disposition**, never an atom status. Note: `EARNED` does
  **not** require every atom in the marking to carry `T`; irrelevant `Z` atoms may
  exist under a hereditary result (the grade quantifies over their completions).
- **Grade** — the judge's stability qualifier over the verdict; `hereditary` means the
  verdict survives every completion/refinement of the current marking **within the
  same JudgeContext**.
- **Weak links** — the named atoms whose status blocks or conditions the disposition.
- **CLWR** — contemporaneous logical-warrant record (§6).
- **Issuance** — the explicit act of an institutional authority that converts an
  evaluated property into a claim others may rely on, with a lifecycle (§11).

## 3. Admitted grounds

### 3.1 Admission

**R-01 — Admission is an act.**
*Input state:* an atom not present in the current marking version.
*Condition:* an admission act by the evidence custodian, recording status and (for
`T`/`F`) witness references.
*Permitted transition:* the atom enters the marking version created by that act with
exactly that status.
*Observable evidence:* the admission record (atom, status, witness hashes, actor,
time reference, marking version).
*Falsifying counterexample:* an atom present in any evaluated marking without an
admission record.

**R-02 — Provenance for `T`.**
*Input state:* an admission act proposing status `T` for a specific atom.
*Condition:* at least one admissible witness reference resolves to a hash-bound
artifact of a completed verification act **whose recorded content supports that
specific atom at that specific status** — not merely some completed act.
*Permitted transition:* status `T` admitted; otherwise the atom is admitted as `Z`.
*Observable evidence:* resolvable witness hashes whose artifacts name or entail the
atom's proposition.
*Falsifying counterexample:* a `T` atom whose witnesses are absent, unresolvable, or
resolve to artifacts that do not support that atom at that status (including witnesses
borrowed from a different atom or a different status).
**Corollary (frozen):** *T without admissible witness → Z.* An adapter's bare
assertion is itself only an unverified input.

**R-03 — Provenance for `F`.**
*Input state:* an admission act proposing status `F` for a specific atom.
*Condition:* at least one admissible witness reference resolves to a hash-bound
artifact of a completed verification act whose recorded content stands against that
specific atom.
*Permitted transition:* status `F` admitted; otherwise the atom is admitted as `Z` —
refutation is also an act, never a default.
*Observable evidence:* resolvable witness hashes supporting the refutation.
*Falsifying counterexample:* an `F` admitted because verification was merely absent.

**R-04 — Marking immutability.**
*Input state:* a marking version in existence.
*Condition:* none — this is a prohibition.
*Permitted transition:* no change of any kind to that marking version; all change is
succession (R-25).
*Observable evidence:* marking hash stability across every citation.
*Falsifying counterexample:* two artifacts citing the same marking identity with
different content.

### 3.2 Marking succession

**R-25 — Status change is succession, never mutation.**
*Input state:* an existing (immutable) marking version and a proposed status change
(`Z→T`, `Z→F`, or a later correction of any status).
*Condition:* a new admission act for each changed atom, with witness binding per
R-02/R-03, producing a **new marking version** that cites its predecessor.
*Permitted transition:* the successor marking comes into existence; the predecessor
remains preserved and citable; any evaluation over the successor is a **new
JudgeContext** (R-06).
*Observable evidence:* the successor marking's predecessor reference; per-atom new
admission records; both marking hashes preserved.
*Falsifying counterexample:* a status change without a new admission act; a
predecessor marking discarded or overwritten; a CLWR citing a "changed" marking under
the predecessor's identity.

## 4. The claim under evaluation

**R-05 — Formulas are stipulated, not judged into being.**
*Input state:* a formula proposed for evaluation.
*Condition:* an identified institutional authority has stipulated the formula as the
formal content of an institutional condition, before evaluation; OIC's compilation of
that stipulation preserves the source anchor.
*Permitted transition:* the formula becomes evaluable in JudgeContexts cited by
ClaimContexts that reference that stipulation.
*Observable evidence:* the stipulation record (authority identity, formula hash,
institutional reading, source anchor).
*Falsifying counterexample:* a CLWR whose formula has no prior stipulation record, or
whose stipulation post-dates the evaluation.
**Note.** The judge never authors, amends, or reinterprets formulas. A dispute about
what the institution *meant* is an institutional-layer dispute; the judge holds only
the frozen formal content.

## 5. The two contexts

**R-06 — The JudgeContext is the triple, and the CLWR binds both contexts.**
*Input state:* a stipulated formula and an admitted marking version.
*Condition:* formula hash, marking hash, and judge semantics/implementation identity
are each recorded (the **JudgeContext**); the relevant stipulation/ClaimContext
identity is recorded alongside.
*Permitted transition:* evaluation may run; the CLWR must cite exactly this
JudgeContext **and** the ClaimContext identity it was evaluated for — without thereby
granting the judge any authority over the institutional envelope.
*Observable evidence:* both identities inside the CLWR.
*Falsifying counterexample:* a CLWR citing an unversioned judge, an unhashed formula,
an unhashed marking, or no ClaimContext identity; or any artifact treating the judge's
output as determining institutional-envelope content.

Everything the judge asserts is asserted **relative to a JudgeContext**. Institutional
lifecycle events — expiry, revocation, supersession, authority change — modify
**institutional reliance state** (the ClaimContext/issuance layer, §11) and **never
retroactively modify a logical result**. A changed institutional envelope does not
falsify an old CLWR; it changes what may currently be relied upon.

## 6. The contemporaneous logical-warrant record (CLWR)

**R-07 — Every evaluation emits a CLWR at evaluation time.**
*Input state:* a JudgeContext (§5) with its ClaimContext identity.
*Condition:* the judge computes over the JudgeContext.
*Permitted transition:* exactly one CLWR is created, containing at minimum:

1. formula and formula hash;
2. marking and marking hash;
3. judge semantics/implementation identity;
4. verdict and disposition (kernel-exact, §2);
5. grade;
6. named weak links (possibly empty);
7. atom provenance references (as admitted);
8. relevant input artifact hashes;
9. invocation time/context reference;
10. the ClaimContext identity this evaluation was performed for.

*Observable evidence:* the CLWR itself, hash-bound as one artifact.
*Falsifying counterexample:* an evaluation whose disposition is cited anywhere without
a corresponding CLWR, or a CLWR missing any of the ten fields.

**R-08 — CLWR immutability.**
*Input state:* a CLWR emitted and identified (hash-bound).
*Condition:* none — this is a prohibition.
*Permitted transition:* no edit, amendment, or re-emission under the same identity;
corrections are new records citing the old.
*Observable evidence:* stable content under the CLWR's identity across all citations.
*Falsifying counterexample:* two artifacts presenting the same CLWR identity with
different content.

**R-09 — Determinism.**
*Input state:* a fixed JudgeContext.
*Condition:* none — property of the judge.
*Permitted transition:* the judge's output is a pure function of the JudgeContext;
repeated evaluation reproduces the CLWR's verdict, grade and weak links exactly.
*Observable evidence:* replay records (§14).
*Falsifying counterexample:* two evaluations of the identical JudgeContext with
differing outputs — this falsifies either the judge's conformance or the context's
integrity, and is a protocol breach finding in both cases.

## 7. The institutional-warrant boundary

**R-10 — A CLWR is not institutional warrant.**
*Input state:* any CLWR, including `EARNED / hereditary`.
*Condition:* none — this is a prohibition.
*Permitted transition:* no **reliance-bearing transition governed by this protocol**
occurs by force of a CLWR alone. The CLWR establishes a **property**; authority,
admissibility, sufficiency and reliance conditions live outside the judge (D1).
Institutional operations that are not reliance-bearing under this protocol —
revocation, correction, escalation, administrative acts — are governed by the
institution's own rules and are **not** required to present an `EARNED` CLWR.
*Observable evidence:* every reliance-bearing transition record cites both a CLWR
**and** an issuance act (§11).
*Falsifying counterexample:* a reliance-bearing transition record citing only a CLWR
as its basis.

## 8. Evaluation semantics

### 8.1 Dispositions (kernel-exact)

Given a JudgeContext, the judge returns exactly one disposition:

| Disposition | Kernel definition | Meaning |
|---|---|---|
| `EARNED` | verdict `T` + grade `hereditary` | the claim holds and no completion of the current marking can revoke it within this JudgeContext |
| `REFUTED` | verdict `F` + grade `hereditary` | the claim fails and no completion of the current marking can rescue it within this JudgeContext |
| `ON CREDIT` | verdict `T` + non-`hereditary` grade | the claim currently computes true, but unverified ground is load-bearing: truth is being asked for on credit |
| `OPEN` | otherwise non-established | the current marking does not establish the claim; the weak links name what verification would have to settle |

`EARNED` does not require an all-`T` marking: atoms irrelevant to the verdict may
remain `Z` under a hereditary result.

### 8.2 Conformance mapping (frozen canon)

| Judge disposition | Conformance reading |
|---|---|
| `EARNED` | eligible to map to **PASS** |
| `REFUTED` | **FAIL** |
| `OPEN` | **CANNOT** (unknown) |
| `ON CREDIT` | **CANNOT / NON-QUALIFYING** |

**R-11 — Only `EARNED` qualifies.**
*Input state:* a qualifying predicate consuming a judge output.
*Condition:* disposition is `EARNED`.
*Permitted transition:* the predicate may read **PASS**; under any other disposition it
must read **CANNOT** or **FAIL** per the table.
*Observable evidence:* the consuming record cites the CLWR and its disposition.
*Falsifying counterexample:* any record in which `ON CREDIT` or `OPEN` is treated as
qualifying — including by default, by timeout, or by repetition (§12).

**Institutional consumption of non-PASS readings.** `REFUTED`/FAIL and `CANNOT`
create **no positive reliance of any kind** by themselves: FAIL is not an issued
denial, and CANNOT is not an issued anything. Any affirmative act consuming them —
denial, escalation, suspension, notification — is a separate institutional decision
under governing authority, recorded as such.

### 8.3 Grades and the hereditary boundary (frozen canon)

> **ZTL `hereditary` = logical stability under the stated semantics and the fixed
> JudgeContext — not institutional persistence of authorization.**

**R-12 — Grade semantics are JudgeContext-bounded.**
*Input state:* a CLWR with grade `hereditary`.
*Condition:* refinements/completions of the **current marking** (verification of
currently-`Z` atoms) within the **same** JudgeContext.
*Permitted transition:* the disposition may be relied upon as logically stable under
exactly those refinements — nothing more.
*Observable evidence:* the CLWR's JudgeContext triple.
*Falsifying counterexample:* any artifact citing a `hereditary` grade as grounds that
an authorization cannot expire, be revoked, or be superseded. Those are lifecycle
events of the institutional envelope (§11); they change current reliance state and
leave the logical record untouched.

**R-13 — Weak-link disclosure.**
*Input state:* any non-`EARNED` disposition.
*Condition:* none.
*Permitted transition:* the CLWR must name the blocking atoms (weak links) — the
protocol's diagnostic obligation.
*Observable evidence:* non-empty weak-link field, or an explicit empty-set record for
`REFUTED` on fully earned grounds.
*Falsifying counterexample:* a non-`EARNED` CLWR whose weak links are absent where the
judge semantics define them.

## 9. Authority prerequisites

**R-14 — Issuance has prerequisites in both layers.**
*Input state:* an institutional authority contemplating issuance over a claim.
*Condition:* (a) a CLWR for the claim's JudgeContext with disposition `EARNED`, bound
to the claim's ClaimContext; **and** (b) the institutional conditions — authority
competence, admissibility of the grounds, sufficiency for the intended reliance —
each satisfied under the governing rules, outside the judge.
*Permitted transition:* issuance (§11) may proceed; absent either leg, it may not.
*Observable evidence:* the issuance record cites the CLWR and the institutional
determinations separately.
*Falsifying counterexample:* an issuance citing logical grounds for the institutional
leg, or institutional discretion in place of the `EARNED` CLWR.

## 10. Evidence references

**R-15 — Everything resolves to hashes.**
*Input state:* any record defined by this protocol (admission, stipulation, marking
succession, CLWR, issuance, lifecycle event, replay).
*Condition:* every reference inside the record is a content hash (with algorithm
identified) or a typed identity that resolves to one.
*Permitted transition:* the record is admissible as protocol evidence.
*Observable evidence:* successful independent resolution of every reference.
*Falsifying counterexample:* a load-bearing reference that is nominal only (a path or
title with no content identity).

## 11. The issuance / reliance transition and its lifecycle

**R-16 — Issuance is an explicit, separate act.**
*Input state:* R-14 prerequisites satisfied.
*Condition:* the institutional authority performs a distinct issuance act, producing
an issuance record containing at minimum: **issuance identity; the ClaimContext
binding (by hash); the CLWR reference (by hash); scope of reliance; effective
time/phase; expiry conditions where applicable; the issuing authority**.
*Permitted transition:* the claim becomes reliance-bearing **within the stated scope
and while the issuance is active** (R-26); relying parties may then act on it.
*Observable evidence:* the issuance record.
*Falsifying counterexample:* reliance recorded against a claim with no issuance
record, or issuance missing any of the seven minimum elements.

**R-26 — Issuance lifecycle and current status.**
*Input state:* an existing issuance record.
*Condition:* lifecycle events — activation, expiry, revocation, supersession — are
themselves explicit, hash-bound institutional records citing the issuance identity;
the **current status** of an issuance at any reliance event is determined from the
issuance record plus its recorded lifecycle events under the governing rules.
*Permitted transition:* status transitions occur only through such recorded events;
supersession records identify the superseding issuance.
*Observable evidence:* the lifecycle chain resolvable from the issuance identity.
*Falsifying counterexample:* an issuance treated as revoked/expired/superseded (or as
still active) with no corresponding lifecycle record; or lifecycle state asserted from
anything other than the recorded chain.

**R-17 — Reliance requires an ACTIVE issuance at the reliance event.**
*Input state:* a relying party contemplating action on a claim.
*Condition:* an issuance record exists for that claim; its current status per R-26 is
**active** at the time of the reliance event; and the intended action falls within its
stated scope.
*Permitted transition:* the action may proceed on the issued claim; absent an active
issuance, or outside its scope, it may not — regardless of the strength of the
underlying CLWR. A revoked, expired, or superseded issuance does not satisfy this rule
merely because its record still exists.
*Observable evidence:* the reliance record cites the issuance record and its
current-status determination, not the CLWR directly.
*Falsifying counterexample:* a relying party acting on a bare CLWR; or acting on an
issuance whose recorded lifecycle state was not active at the reliance event. (D2 in
operational form.)

## 12. Failure and non-decision semantics

**R-18 — `CANNOT` never decays into `PASS`.**
*Input state:* a predicate reading `CANNOT` (from `OPEN` or `ON CREDIT`).
*Condition:* passage of time, repetition of evaluation over the same JudgeContext,
system defaults, or operator convenience.
*Permitted transition:* **none** — the reading remains `CANNOT` until a **successor
marking** (R-25) yields a new JudgeContext and a new CLWR.
*Observable evidence:* absence of any PASS-consuming record citing a `CANNOT` CLWR.
*Falsifying counterexample:* a gate that passed on timeout, default, or retry-until-
green over unchanged grounds.

**R-19 — Adverse results are preserved, not repaired.**
*Input state:* a `REFUTED` disposition, or a falsified preregistered hypothesis.
*Condition:* none.
*Permitted transition:* the result enters the record as evidence with the same
standing as success. Successor work requires a **new, separately authorized context**;
a new stipulation is required **only when the formula or claim changes** — re-running
under new grounds within the same stipulated claim requires new authorization and a
successor marking, not a new stipulation. The original record remains controlling for
its context.
*Observable evidence:* the adverse record persisted unmodified; successor work citing
it as predecessor with its own authorization.
*Falsifying counterexample:* an adverse result edited, reclassified, or re-run within
its original context until favorable. (M1 methodological evidence: a falsified
hypothesis was persisted as the accepted closure of its mission — Appendix A.)

**R-20 — Non-decision is a first-class outcome.**
*Input state:* an evaluation attempt terminated before a result exists
(infrastructure failure, signal termination, unparseable output).
*Condition:* none.
*Permitted transition:* the attempt is recorded as a blocked non-decision of its own
kind, with the termination evidence preserved; counts remain unmeasured, the claim
remains unadjudicated, and any consumed one-shot authority is recorded as consumed.
*Observable evidence:* the blocked-state record (termination cause, preserved raw
streams, explicit UNMEASURED fields).
*Falsifying counterexample:* a blocked evaluation represented as a scientific result
in either direction — as `REFUTED`, as `EARNED`, as zero-counts, or by silent
omission.

## 13. Anti-overclaim boundaries

**R-21 — Recorded dispositions are ceilings, not floors.**
*Input state:* any recorded disposition or graded finding.
*Condition:* none.
*Permitted transition:* downstream citation may weaken, never strengthen: `NARROWED`
may not be cited as `IDENTIFIED`; `supported` may not be cited as `proven`; an
`EARNED` in one JudgeContext may not be cited as `EARNED` in another.
*Observable evidence:* claim-to-record equality under review.
*Falsifying counterexample:* any downstream artifact whose cited strength exceeds the
recorded disposition.

**R-22 — Interpretation is labeled.**
*Input state:* analysis extending beyond a recorded result (causal theories,
generalizations, design implications).
*Condition:* none.
*Permitted transition:* the analysis may be recorded only under an explicit
interpretation/proposal label, as a distinct artifact; it inherits none of the
record's evidentiary status.
*Observable evidence:* the interpretive artifact carries its own label and identity,
separate from the record it discusses.
*Falsifying counterexample:* downstream analysis presented under the record's hashes
or dispositions.

## 14. Replay and reproducibility

**R-23 — Replay is a new verification event.**
*Input state:* a preserved CLWR and its JudgeContext artifacts.
*Condition:* an independent party re-executes the judge over the identical
JudgeContext.
*Permitted transition:* the replay outcome is recorded as a **new** act that either
*confirms* the CLWR (byte-equal verdict/grade/weak links) or *impeaches* it.
*Observable evidence:* the replay record citing both context and original CLWR.
*Falsifying counterexample:* a replay outcome silently substituted for the
contemporaneous record, or treated as retroactively creating warrant at the original
time. **The CLWR is the contemporaneous logical-warrant record/act; replay is its
audit.**

**R-24 — Reconstruction must not require replay.**
*Input state:* an OAM reconstruction request over a past reliance-bearing transition.
*Condition:* the preserved records alone — stipulation, admissions and marking
succession, CLWR, **the institutional determination records of R-14(b)**, issuance,
**and the issuance lifecycle events of R-26**.
*Permitted transition:* the reconstruction succeeds from those records; replay is
available as an additional check, never as the missing link.
*Observable evidence:* a reconstruction trace citing only preserved artifacts,
including the institutional legs.
*Falsifying counterexample:* a transition whose basis cannot be reconstructed without
re-running the judge, or whose institutional determinations and lifecycle state are
absent from the preserved record.

## 15. What this protocol deliberately does NOT establish

1. **That ZTL is validated, or is the production engine of OIC or Authorized
   Autonomy.** That role must be earned empirically (Part II) and granted by separate
   issuance.
2. **Any causal theory from M1.** The M1 falsification contributes methodology only
   (Appendix A); no replacement hypothesis is stated or implied here.
3. **Transport, storage, process or language bindings.** Ledgers, files, services and
   schemas are implementation tranches under this contract, not parts of it.
4. **Institutional content.** What any institution ought to stipulate, admit or issue
   is outside scope; this protocol constrains only the records and transitions by
   which they do it.
5. **Truth outside contexts.** Every property established here is relative to a
   JudgeContext (and, for reliance, a ClaimContext); the protocol asserts nothing
   context-free.

## 16. Falsifiability of this protocol

This protocol is conformance-testable by construction: each rule `R-01 … R-26` names
its observable evidence and its falsifying counterexample. A conformance review of an
implementation consists of:

1. selecting and identifying a corpus of transactions (the corpus itself hash-bound);
2. for each rule, searching the corpus for the rule's counterexample pattern;
3. reporting, per rule: **conforms on the exercised corpus** (no counterexample found,
   evidence present), **violated** (counterexample exhibited, by hash), or **not
   exercised** (the corpus never reaches the rule's input state).

Conformance claims are always corpus-relative; no global conformance is asserted from
any finite corpus.

**Protocol-design falsification (operational).** The protocol *as a design* is
falsified if a corpus exhibits at least one transaction that (a) violates D1 or D2 —
an unissued reliance event, a reliance event on a non-active issuance, or a
qualification built on non-`EARNED` grounds — while (b) violating **no** rule
`R-01 … R-26` on that same transaction. Such a finding demonstrates that the rule set
under-implements its own frozen distinctions and requires a protocol revision, not a
reinterpretation (R-21 applies to this document's own claims).

---

# PART II — THE PREREGISTERED EXPERIMENT (MECHANICAL-JUDGE QUALIFICATION)

Part II defines the experiment that must run — and be independently reviewed — before
any implementation reliance on ZTL as the mechanical judge of Part I. Phase A is
retrospective and read-only; Phase B is prospective and shadow-only. Nothing in
Part II carries institutional authority.

## 17. Hypotheses

Preregistered, each falsifiable by the criteria of §24:

- **EH-1 (Representability).** The mechanical gate content of the corpus transactions
  can be represented as frozen formulas over harvestable atoms, with unrepresented
  mechanical residue below the tolerance of §24.6.
- **EH-2 (Known-seam detection).** Evaluated over honestly harvested markings, the
  judge flags every preregistered known seam of §22 as `REFUTED`, `OPEN`, or a
  provenance failure — none of them computes as clean `EARNED`.
- **EH-3 (Blinded detection).** Under the blinded-mutation methodology of §23, the
  judge pipeline detects planted defects at or above the thresholds of §24.2, with
  zero false `EARNED` (§24.3).
- **EH-4 (No false convictions).** On unmutated accepted transactions, gates that the
  governing record accepted evaluate `EARNED` — no false `REFUTED` against the
  independently established reference markings (§21).

## 18. Corpus

**Inclusion.** All eleven persisted ledger transactions of the M1 series
(PR #1–PR #11, by their exact reviewed heads/trees) **plus** the legacy M1-S1
measurement package (`m1-s1-measurement-001.zip`, 103189 bytes, SHA-256 `e9250d19…`),
its transport being the recorded final legacy exception.

**Exclusion.** Pre-ledger Stage-B0 packages other than the M1-S1 package (their gate
texts predate the frozen role/transport model); any artifact not hash-identified in
the persisted record. Every exclusion is listed with its identity and reason in the
corpus index.

**Corpus index.** A hash-bound `corpus-index` artifact enumerates every included
transaction: identity (head/tree or package hashes), its governing text(s), its
evidence tree, and its accepted disposition. The index is frozen with this protocol.

## 19. Atom harvesting and admission methodology

1. Harvesting rules are frozen before any evaluation and apply uniformly.
2. A harvester reads **only persisted evidence artifacts** from the corpus; every
   proposed `T`/`F` carries the witness reference (artifact path + content hash inside
   the identified tree) that supports the specific atom (R-02/R-03).
3. Whatever the harvester cannot support with a witness enters as `Z` — no exceptions
   and no manual patching.
4. Harvester outputs are marking documents, hash-bound, one per (transaction, gate).
5. **Provenance audit (separate from judging):** after harvesting, a distinct audit
   pass scans every marking for provenance-less `T`/`F`; any finding is a §24.5
   failure of the harvesting layer, scored independently of judge correctness.
6. Harvester implementation identity (version hash) is recorded in every marking.

## 20. Formula construction and freeze

1. Formulas are transcribed from the governing texts' own gate clauses (e.g., an
   activation predicate list, packaging accounting requirements, confinement
   counters), one formula per gate, composed of the atoms of §19.
2. Every formula records its source anchor: document identity + the quoted clause.
3. The complete formula set is frozen (hash + date) together with the harvesting
   rules **before** any evaluation or mutation run; after freeze, formula changes are
   prohibited for the duration of the experiment (a defective formula found later is
   an experiment *result* under §24.6, not a repair ticket).
4. The judge implementation is pinned by version/commit hash for the entire
   experiment; the pinned identity appears in every CLWR.

## 21. Ground truth

1. For each corpus gate, ground truth is the **accepted disposition of the persisted
   record**: the owner dispositions and the independent-review verdicts as persisted.
2. Reference markings for EH-4 are constructed from the accepted record's own
   identity claims (the recorded hashes and counters), independently of the
   harvester; where the record itself was later corrected (e.g., a not-sustained
   trigger label), the corrected owner disposition is ground truth.
3. Gates with ambiguous or contested ground truth are excluded and listed with
   reasons in the corpus index; exclusions are counted in the denominators (§24.1).

## 22. Known-seam test set (preregistered)

The retrospective corpus contains, at minimum, these already-adjudicated seams, each
identified by artifact and location:

| # | Seam | Location identity |
|---|---|---|
| S-1 | Expected-metric contradiction ("authorized functions changed = 7" vs seven sites in five functions) | M1-S1 order §5/§6, adjudicated B |
| S-2 | Transport-corrupted SHA-256 in a relayed review order | PR #9 order header (clean value in its §11) |
| S-3 | Transport-corrupted text blocks in a relayed order | PR #10 order (duplicated line; garbled token) |
| S-4 | Falsification-trigger mislabel | R1 adjudication F4, owner-ruled NOT_SUSTAINED_AS_LABELED |
| S-5 | Schema drift across packages | `bytes` vs `byte_length` member fields |

Expectation under EH-2: none of these computes as clean `EARNED` when honestly
harvested; each surfaces as `REFUTED`, `OPEN` (weak link naming the seam), or a
provenance/consistency failure. Detection of S-1…S-5 is scored as **known-seam
recall** and reported separately from blinded results (§23).

## 23. Blinded-mutation methodology

1. After the freeze of §20, a mutation controller **outside the implementation path**
   (owner side, or a sealed script accepted by the owner) produces N mutated copies
   of corpus transactions. The implementer does not know which transactions or
   classes were mutated.
2. Mutation classes (at minimum, per the accepted charter): missing witness/evidence;
   corrupted hashes; schema drift; counter inconsistency; contradictory gate facts;
   missing atoms; false-positive adapter markings; altered identity/environment
   evidence.
3. The mutation manifest (what was planted, where) is hash-committed **before** runs
   and disclosed only after the implementer's results are frozen.
4. Runs over mutated corpora use the same frozen harvester, formulas and judge as the
   unmutated runs.
5. Scoring after disclosure: per-class detection = flagged/planted; misses and false
   alarms enumerated by identity.

## 24. Preregistered failure and falsification criteria

The experiment **fails** (per hypothesis) if any of the following holds:

1. **Denominators.** All rates below use preregistered denominators: gates evaluated,
   atoms harvested, seams known (5), mutations planted per class (from the sealed
   manifest), qualifying evaluations. Excluded gates are reported in a separate
   line — never silently dropped from denominators.
2. **EH-3 thresholds.** Detection below **100%** for hash/identity/witness mutation
   classes, or below **90%** for any other class.
3. **False `EARNED`.** Any planted defect whose gate still evaluates clean `EARNED`:
   tolerance **zero**.
4. **False `REFUTED`.** Any unmutated accepted gate evaluating `REFUTED` against the
   reference markings (EH-4): tolerance **zero** after ground-truth adjudication.
5. **Provenance failure.** Any provenance-less `T`/`F` surviving admission into an
   evaluated marking (scored against the harvesting layer; EH-2/EH-3 results over
   such markings are void for the affected gates).
6. **Residue.** Mechanical disposition content of the governing texts that the frozen
   formalization cannot represent, exceeding **10%** of gates (per the discrepancy
   classification of §25); institutional and explanatory prose are not counted as
   mechanical residue.
7. **Non-qualification discipline.** Any `ON CREDIT` or `OPEN` output consumed as
   qualifying anywhere in the experiment pipeline.
8. **Reproducibility.** Failure of an independent party to reproduce the judge
   results from the frozen artifacts (corpus index, markings, formulas, pinned judge)
   per §26.

A failed hypothesis is a result. No criterion may be adjusted after the freeze; a
defective criterion discovered later is reported as a finding about the protocol,
under R-19 and R-21.

## 25. Discrepancy classification and outputs

**Discrepancy classes** for prose-vs-judge comparison, per gate:

- **mechanical** — content the judge should have represented (counts, identities,
  gate conjunctions): scored;
- **institutional** — authority/admissibility/sufficiency content outside the judge's
  jurisdiction by D1: recorded, not scored against the judge;
- **explanatory** — narrative with no dispositional content: recorded only.

**Exact outputs** (all hash-bound, manifested with a self-excluded manifest binding
path/bytes/SHA-256/SHA-512 per member):

1. corpus index (frozen);
2. harvesting rules + harvester identity (frozen);
3. formula set with source anchors (frozen);
4. marking documents per (transaction, gate);
5. provenance-audit report;
6. CLWR set (one per evaluation, ten fields per R-07);
7. per-gate comparison table: `governing disposition | judge disposition |
   discrepancy class`;
8. known-seam recall report (S-1…S-5, individually);
9. blinded-mutation scoring report (after manifest disclosure);
10. failure-criteria adjudication against §24, criterion by criterion;
11. reproduction procedure (§26);
12. final experiment return.

## 26. Reproduction procedure

An independent party must be able to reproduce every judge result from: the public
ZTL repository at the pinned commit; the frozen corpus index; the frozen harvesting
rules and formula set; and the persisted corpus artifacts — using one documented
command per phase, with no access to the implementer. Reproduction divergence is a
§24.8 failure. Replay semantics per R-23: reproduction audits the records; it does
not re-create them.

## 27. Phase boundaries

**Phase A — retrospective.**
*Authority:* **read-only; zero institutional authority.** No Phase A output changes
any disposition, ledger state, or governed artifact. Phase A comprises §§18–26 over
the unmutated corpus (known-seam recall, EH-1/EH-2/EH-4) and the blinded-mutation
runs (EH-3).
*Exit:* a frozen, manifested result bundle submitted for independent review and owner
adjudication.

**Phase B — prospective shadow.**
*Entry condition:* **only after Phase A review** and an explicit owner authorization
referencing it. Phase A success does not self-activate Phase B.
*Authority:* **shadow-only; no production consequence.** The judge runs alongside the
governing process; for every applicable gate the record is
`governing disposition | judge disposition | discrepancy`; all discrepancies are
retained and adjudicated. No consequence of any kind may depend on the judge's output
during Phase B.
*Exit:* a discrepancy ledger and adjudication submitted for review; any subsequent
role for the judge requires separate issuance per §15.1.

---

## Appendix A. Methodological evidence from M1 (admissible scope only)

M1 (`CLOSED_BY_ACCEPTED_FALSIFICATION`) contributes exactly four methodological
findings, each already demonstrated in persisted evidence, and nothing further:

| # | Finding | Where demonstrated | Encoded here as |
|---|---|---|---|
| 1 | Preregistration survives adverse results | H1 predictions/falsification conditions held fixed through a falsifying R1 | R-19, R-21, §24 |
| 2 | Conditional authority can be machine-activated from proven predicates | the 18-predicate Phase A→B activation, no discretionary step | R-06, R-11, R-15 (pattern), §9 |
| 3 | An evaluation result is distinguishable from authorization to rely on it | review-ACCEPT ≠ owner acceptance; CI PASS ≠ acceptance, throughout | D2, R-10, R-16, R-17, R-26 |
| 4 | A failed hypothesis is admissible evidence, not material for repair | the falsified R1 persisted as mission closure; no corrective iteration | R-19, R-20 |

No generalization beyond these four is made or licensed by this document.

## Appendix B. Frozen terminology imported by this protocol

- *Contemporaneous logical-warrant record (CLWR)* — §6; the judge's product; never
  institutional warrant by itself.
- *Evaluation establishes the property; issuance creates the reliance* — D2; §11.
- *ZTL hereditary = logical stability under the stated semantics and fixed
  JudgeContext, not institutional persistence of authorization* — §8.3.
- *`Z` = unverified/unknown marked ground, default-deny* (atom status); *`ON CREDIT` =
  verdict `T` with non-`hereditary` grade* (disposition) — §2; the two are never
  conflated.
- *T without admissible witness → Z* — R-02; harvesting is evaluated separately from
  judging (§19.5, §24.5).
- Disposition/conformance mapping table — §8.2.

## Appendix C. Rules index

| Rule | Section | One line |
|---|---|---|
| R-01 | §3.1 | admission is an act, recorded |
| R-02 | §3.1 | `T` requires a witness supporting that atom at that status; bare `T` → `Z` |
| R-03 | §3.1 | `F` requires an act too; absence of proof is not refutation |
| R-04 | §3.1 | marking versions are immutable |
| R-25 | §3.2 | status change is succession into a new marking/JudgeContext |
| R-05 | §4 | formulas are stipulated by the institution, never authored by the judge |
| R-06 | §5 | JudgeContext is the triple; the CLWR binds it plus the ClaimContext identity |
| R-07 | §6 | every evaluation emits a ten-field CLWR at evaluation time |
| R-08 | §6 | CLWRs are immutable; corrections are new records |
| R-09 | §6 | the judge is deterministic over a fixed JudgeContext |
| R-10 | §7 | a CLWR alone effects no reliance-bearing transition |
| R-11 | §8 | only `EARNED` qualifies as PASS |
| R-12 | §8 | `hereditary` is JudgeContext-bounded stability, not persistence |
| R-13 | §8 | non-`EARNED` dispositions name their weak links |
| R-14 | §9 | issuance requires both the `EARNED` CLWR and the institutional legs |
| R-15 | §10 | every load-bearing reference resolves to a content hash |
| R-16 | §11 | issuance is an explicit, scoped act with lifecycle elements |
| R-26 | §11 | issuance status is determined from recorded lifecycle events |
| R-17 | §11 | reliance requires an ACTIVE issuance at the reliance event |
| R-18 | §12 | `CANNOT` never decays into `PASS` |
| R-19 | §12 | adverse results are preserved; successor work is newly authorized |
| R-20 | §12 | blocked non-decisions are first-class outcomes |
| R-21 | §13 | recorded dispositions are ceilings, not floors |
| R-22 | §13 | interpretation is labeled and inherits no evidentiary status |
| R-23 | §14 | replay audits the contemporaneous record; it never creates warrant |
| R-24 | §14 | reconstruction succeeds from records — including institutional legs — without replay |

## Appendix D. Change account for this revision (keyed to the seven review items)

1. **Experiment protocol completed** — Part II added (§§17–27): hypotheses EH-1…EH-4;
   corpus with inclusion/exclusion and frozen index; harvesting/admission methodology
   with separate provenance audit; formula construction/freeze; ground truth;
   known-seam set S-1…S-5; blinded-mutation methodology with sealed manifest;
   discrepancy classes; explicit denominators; preregistered failure criteria with
   numeric thresholds; exact outputs; reproduction procedure; Phase A = read-only /
   zero institutional authority; Phase B = only after Phase A review, shadow-only /
   no production consequence. The Part I semantic contract is unchanged in substance.
2. **Two-level context model** — §2 and §5 rewritten: `JudgeContext` (formula +
   marking + judge identity) vs `ClaimContext` (stipulation + authority + reading/
   scope + JudgeContext identity); CLWR binds both (R-07 field 10) without granting
   the judge authority over the envelope; lifecycle events modify institutional
   reliance state and never retroactively modify logical results (§5, R-12).
3. **Issuance lifecycle** — R-16 extended (seven minimum elements incl. effective
   time/phase and expiry); new R-26 (lifecycle events and current-status
   determination); R-17 now requires an **active** issuance at the reliance event.
4. **Kernel-exact terminology** — §2: `Z` = unverified/unknown marked ground,
   default-deny (atom status); `ON CREDIT` = verdict `T` + non-`hereditary`
   (disposition); §8.1 table restated kernel-exactly (`EARNED` = T+hereditary,
   `REFUTED` = F+hereditary, `OPEN` = otherwise); explicit note that `EARNED` does not
   require an all-`T` marking. Appendix B updated to freeze the distinction.
5. **OIC authority boundary corrected** — §0 and §1: the institution/authorized actor
   is the source of authoritative meaning; OIC preserves anchors, exposes
   ambiguity/conflict, records admission, represents stipulated meaning, compiles
   into formulas; OIC originates no meaning, authority, or warrant.
6. **Marking succession defined** — new R-25 (§3.2): markings immutable; `Z→T`,
   `Z→F`, corrections only via new admission acts into a successor marking; the
   predecessor preserved; successor evaluations are new JudgeContexts; R-04 restated
   as pure immutability; R-18 re-pointed at successor markings.
7. **Bounded consistency corrections** — R-02: witness must support the specific
   atom/status; R-10: scoped to reliance-bearing transitions governed by this
   protocol, with non-reliance institutional operations exempted; §8.2: explicit
   institutional-consumption paragraph for FAIL/CANNOT (no positive reliance; any
   affirmative act is a separate institutional decision); R-19: successor work needs
   a new authorized context, new stipulation only when the formula/claim changes;
   R-23: "the CLWR is the contemporaneous logical-warrant record/act"; R-24:
   reconstruction includes institutional determination records and issuance-lifecycle
   events; §16: conformance is "on the exercised corpus", and protocol-design
   falsification is operationalized (a D1/D2 breach on a transaction violating no
   R-rule).

---

*End of Protocol v0.1 (revised candidate). Submitted for owner/adjudicator review. No
implementation work precedes that review.*
