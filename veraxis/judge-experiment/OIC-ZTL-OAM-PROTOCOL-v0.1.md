# OIC–ZTL–OAM Protocol v0.1

**Document ID:** `OIC-ZTL-OAM-PROTOCOL-v0.1`
**Status:** DRAFT CANDIDATE — submitted for owner/adjudicator review; not frozen; not executable authority.
**Steering:** Vitaliy Reznik (post-M1 protocol phase, per owner authorization of 2026-08-09).
**Drafted:** 2026-08-09, by Claude (Fable 5) under the steering role's direction (Variant A: the human owns decisions and answers for the result).
**Governing predecessor state:** Review Ledger `main` = `060efa2cc295e0d7d9960f725aece264fc471935` (M1 `CLOSED_BY_ACCEPTED_FALSIFICATION`; falsification basis F1+F3+F6+F7; F4 not sustained as labeled; no replacement causal hypothesis).

---

## 0. Purpose and scope

This protocol defines the semantic contract between three layers of an institutional
computation stack:

- **OIC** (Institutional Computation): the layer that states what institutional rules
  mean — the source of governing formulas.
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

## 1. Actors and roles

| Role | Owns | May not |
|---|---|---|
| **Authority (OIC side)** | stipulating formulas; defining institutional conditions; issuance decisions; phase boundaries | mark atoms as earned; alter a CLWR |
| **Evidence custodian (admission layer)** | admitting atoms into a marking, with witnesses; provenance discipline | author formulas; issue reliance |
| **Judge (ZTL)** | computing dispositions, grades and weak links from an admitted (formula, marking) pair; emitting CLWRs | originate authority or admission; upgrade its own output's institutional status |
| **Independent reviewer** | verifying records against evidence; adjudicating conformance to frozen texts | repair evidence; convert review acceptance into owner acceptance |
| **Relying party** | acting on **issued** claims | acting on bare CLWRs |

One natural person or system may hold several roles only where the governing
institutional rules explicitly allow it; the **judge role is never combined** with the
authority or admission roles for the same evaluation.

## 2. Definitions

- **Atom** — the smallest evaluable proposition; carries exactly one status in a
  marking.
- **Status** — `T` (earned: a completed verification act supports it), `F` (refuted: a
  completed verification act stands against it), `Z` (on credit: no completed act is
  admitted). `Z` is not "unknown probability"; it is the absence of an admitted act.
- **Witness** — the hash-bound evidence artifact (or artifact set) produced by the
  verification act that grounds a `T` or `F` status.
- **Marking** — a finite map atom → status, together with witness references for every
  non-`Z` status.
- **Formula** — a finite composition of atoms under the frozen connective semantics of
  the judge implementation; the formal content of a claim.
- **Claim** — a formula together with its stipulating authority and intended
  institutional reading.
- **Evaluation context** — the triple (formula identity, marking identity, judge
  implementation/version identity), each hash-bound (§5).
- **Disposition** — the judge's output kind: `EARNED`, `REFUTED`, `ON CREDIT`, `OPEN`.
- **Grade** — the judge's stability qualifier over the disposition, including
  `hereditary` (§8.3).
- **Weak links** — the named atoms whose status blocks or conditions the disposition.
- **CLWR** — contemporaneous logical-warrant record (§6).
- **Issuance** — the explicit act of an authority that converts an evaluated property
  into a claim others may rely on (§11).

## 3. Admitted grounds

**R-01 — Admission is an act.**
*Input state:* an atom not present in the marking.
*Condition:* an admission act by the evidence custodian, recording status and (for
`T`/`F`) witness references.
*Permitted transition:* the atom enters the marking with exactly that status.
*Observable evidence:* the admission record (atom, status, witness hashes, actor,
time reference).
*Falsifying counterexample:* an atom present in any evaluated marking without an
admission record.

**R-02 — Provenance for `T`.**
*Input state:* an admission act proposing status `T`.
*Condition:* at least one admissible witness reference resolves to a hash-bound
artifact of a completed verification act.
*Permitted transition:* status `T` admitted; otherwise the atom is admitted as `Z`.
*Observable evidence:* resolvable witness hashes in the admission record.
*Falsifying counterexample:* a `T` atom whose witness references are absent,
unresolvable, or resolve to artifacts that do not record a completed act.
**Corollary (frozen):** *T without admissible witness → Z.* An adapter's bare
assertion is itself only an unverified input.

**R-03 — Provenance for `F`.**
*Input state:* an admission act proposing status `F`.
*Condition:* at least one admissible witness reference resolves to a hash-bound
artifact of a completed verification act that stands against the atom.
*Permitted transition:* status `F` admitted; otherwise the atom is admitted as `Z` —
refutation is also an act, never a default.
*Observable evidence:* resolvable witness hashes in the admission record.
*Falsifying counterexample:* an `F` admitted because verification was merely absent.

**R-04 — Marking immutability inside a context.**
*Input state:* an evaluation context assembled (§5).
*Condition:* none — this is a prohibition.
*Permitted transition:* no change to the marking within that context; any change
creates a **new** context.
*Observable evidence:* marking hash equality across the CLWR and its cited inputs.
*Falsifying counterexample:* two artifacts citing the same context identity with
different marking content.

## 4. The claim under evaluation

**R-05 — Formulas are stipulated, not judged into being.**
*Input state:* a formula proposed for evaluation.
*Condition:* an identified authority has stipulated the formula as the formal content
of an institutional condition, before evaluation.
*Permitted transition:* the formula becomes evaluable in contexts citing that
stipulation.
*Observable evidence:* the stipulation record (authority identity, formula hash,
institutional reading).
*Falsifying counterexample:* a CLWR whose formula has no prior stipulation record, or
whose stipulation post-dates the evaluation.
**Note.** The judge never authors, amends, or reinterprets formulas. A dispute about
what the institution *meant* is an authority-layer dispute; the judge holds only the
frozen formal content.

## 5. Bounded evaluation context

**R-06 — The context is the triple, and nothing else.**
*Input state:* a stipulated formula and an admitted marking.
*Condition:* formula hash, marking hash, and judge implementation/version are each
recorded.
*Permitted transition:* evaluation may run; the CLWR must cite exactly this triple.
*Observable evidence:* the three identities inside the CLWR.
*Falsifying counterexample:* a CLWR citing an unversioned judge, an unhashed formula,
or an unhashed marking.

Everything the judge asserts is asserted **relative to a context**. No output of this
protocol floats free of its context triple.

## 6. The contemporaneous logical-warrant record (CLWR)

**R-07 — Every evaluation emits a CLWR at evaluation time.**
*Input state:* an evaluation context (§5).
*Condition:* the judge computes over the context.
*Permitted transition:* exactly one CLWR is created, containing at minimum:

1. formula and formula hash;
2. marking and marking hash;
3. judge implementation/version identity;
4. verdict and disposition;
5. grade;
6. named weak links (possibly empty);
7. atom provenance references (as admitted);
8. relevant input artifact hashes;
9. invocation time/context reference.

*Observable evidence:* the CLWR itself, hash-bound as one artifact.
*Falsifying counterexample:* an evaluation whose disposition is cited anywhere without
a corresponding CLWR, or a CLWR missing any of the nine fields.

**R-08 — CLWR immutability.**
*Input state:* a CLWR emitted and identified (hash-bound).
*Condition:* none — this is a prohibition.
*Permitted transition:* no edit, amendment, or re-emission under the same identity;
corrections are new records citing the old.
*Observable evidence:* stable content under the CLWR's identity across all citations.
*Falsifying counterexample:* two artifacts presenting the same CLWR identity with
different content.

**R-09 — Determinism.**
*Input state:* a fixed evaluation context.
*Condition:* none — property of the judge.
*Permitted transition:* the judge's output is a pure function of the context; repeated
evaluation reproduces the CLWR's verdict, grade and weak links exactly.
*Observable evidence:* replay records (§14).
*Falsifying counterexample:* two evaluations of the identical context with differing
outputs — this falsifies either the judge's conformance or the context's integrity, and
is a protocol breach finding in both cases.

## 7. The institutional-warrant boundary

**R-10 — A CLWR is not institutional warrant.**
*Input state:* any CLWR, including `EARNED / hereditary`.
*Condition:* none — this is a prohibition.
*Permitted transition:* no institutional state changes by force of a CLWR alone. The
CLWR establishes a **property**; authority, admissibility, sufficiency and reliance
conditions live outside the judge (D1).
*Observable evidence:* every institutional transition record cites both a CLWR **and**
an issuance act (§11).
*Falsifying counterexample:* an institutional transition record citing only a CLWR as
its basis.

## 8. Evaluation semantics

### 8.1 Dispositions

Given a context, the judge returns exactly one disposition:

| Disposition | Meaning (frozen) |
|---|---|
| `EARNED` | the claim holds and every load-bearing atom is earned; the property is established within the context |
| `REFUTED` | the claim fails on earned grounds within the context |
| `ON CREDIT` | the claim would hold, but load-bearing atoms are unverified: truth is being asked for on credit |
| `OPEN` | the claim is not decided by the current marking; the named weak links are what verification would have to settle |

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

### 8.3 Grades and the hereditary boundary (frozen canon)

> **ZTL `hereditary` = logical stability under the stated semantics and the fixed
> authority/formula context — not institutional persistence of authorization.**

**R-12 — Grade semantics are context-bounded.**
*Input state:* a CLWR with grade `hereditary`.
*Condition:* refinements of the **current marking** (verification of currently-`Z`
atoms) within the **same** formula/authority context.
*Permitted transition:* the disposition may be relied upon as logically stable under
exactly those refinements — nothing more.
*Observable evidence:* the CLWR's context triple.
*Falsifying counterexample:* any artifact citing a `hereditary` grade as grounds that
an authorization cannot expire, be revoked, or be superseded. Expiry, revocation and
supersession are institutional operations on the **context**, and a changed context
voids no logic — it simply requires a new evaluation.

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
*Input state:* an authority contemplating issuance over a claim.
*Condition:* (a) a CLWR for the claim's context with disposition `EARNED`; **and**
(b) the institutional conditions — authority competence, admissibility of the grounds,
sufficiency for the intended reliance — each satisfied under the governing rules,
outside the judge.
*Permitted transition:* issuance (§11) may proceed; absent either leg, it may not.
*Observable evidence:* the issuance record cites the CLWR and the institutional
determinations separately.
*Falsifying counterexample:* an issuance citing logical grounds for the institutional
leg, or institutional discretion in place of the `EARNED` CLWR.

## 10. Evidence references

**R-15 — Everything resolves to hashes.**
*Input state:* any record defined by this protocol (admission, stipulation, CLWR,
issuance, replay).
*Condition:* every reference inside the record is a content hash (with algorithm
identified) or a typed identity that resolves to one.
*Permitted transition:* the record is admissible as protocol evidence.
*Observable evidence:* successful independent resolution of every reference.
*Falsifying counterexample:* a load-bearing reference that is nominal only (a path or
title with no content identity).

## 11. The issuance / reliance transition

**R-16 — Issuance is an explicit, separate act.**
*Input state:* R-14 prerequisites satisfied.
*Condition:* the authority performs a distinct issuance act, producing an issuance
record that cites: the CLWR (by hash), the institutional determinations, the intended
scope of reliance, and the issuing authority.
*Permitted transition:* the claim becomes reliance-bearing **within the stated
scope**; relying parties may now act on it.
*Observable evidence:* the issuance record.
*Falsifying counterexample:* reliance recorded against a claim with no issuance
record, or issuance whose scope is silently exceeded by a relying party.

**R-17 — Reliance tracks issuance, not evaluation.**
*Input state:* a relying party contemplating action on a claim.
*Condition:* an issuance record exists for that claim and the intended action falls
within its stated scope.
*Permitted transition:* the action may proceed on the issued claim; absent issuance,
or outside its scope, it may not — regardless of the strength of the underlying CLWR.
*Observable evidence:* the reliance record cites the issuance record, not the CLWR
directly.
*Falsifying counterexample:* a relying party acting on a bare CLWR — however strong —
where the governing rules require issued claims. (D2 in operational form.)

## 12. Failure and non-decision semantics

**R-18 — `CANNOT` never decays into `PASS`.**
*Input state:* a predicate reading `CANNOT` (from `OPEN` or `ON CREDIT`).
*Condition:* passage of time, repetition of evaluation over the same context, system
defaults, or operator convenience.
*Permitted transition:* **none** — the reading remains `CANNOT` until a *new context*
(new admissions) yields a new CLWR.
*Observable evidence:* absence of any PASS-consuming record citing a `CANNOT` CLWR.
*Falsifying counterexample:* a gate that passed on timeout, default, or retry-until-
green over unchanged grounds.

**R-19 — Adverse results are preserved, not repaired.**
*Input state:* a `REFUTED` disposition, or a falsified preregistered hypothesis.
*Condition:* none.
*Permitted transition:* the result enters the record as evidence with the same
standing as success; subsequent work requires a **new** stipulation/authorization, and
the original record remains controlling for its context.
*Observable evidence:* the adverse record persisted unmodified; any successor work
citing it as predecessor.
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
`EARNED` in context A may not be cited as `EARNED` in context B.
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
*Input state:* a preserved CLWR and its context artifacts.
*Condition:* an independent party re-executes the judge over the identical context.
*Permitted transition:* the replay outcome is recorded as a **new** act that either
*confirms* the CLWR (byte-equal verdict/grade/weak links) or *impeaches* it.
*Observable evidence:* the replay record citing both context and original CLWR.
*Falsifying counterexample:* a replay outcome silently substituted for the
contemporaneous record, or treated as retroactively creating warrant at the original
time. **The CLWR is the warrant act; replay is its audit.**

**R-24 — Reconstruction must not require replay.**
*Input state:* an OAM reconstruction request over a past transition.
*Condition:* the preserved records (stipulation, admissions, CLWR, issuance) alone.
*Permitted transition:* the reconstruction succeeds from records; replay is available
as an additional check, never as the missing link.
*Observable evidence:* a reconstruction trace citing only preserved artifacts.
*Falsifying counterexample:* a transition whose basis cannot be reconstructed without
re-running the judge.

## 15. What this protocol deliberately does NOT establish

1. **That ZTL is validated, or is the production engine of OIC or Authorized
   Autonomy.** That role must be earned empirically (the chartered experiment) and
   granted by separate issuance.
2. **Any causal theory from M1.** The M1 falsification contributes methodology only
   (Appendix A); no replacement hypothesis is stated or implied here.
3. **Transport, storage, process or language bindings.** Ledgers, files, services and
   schemas are implementation tranches under this contract, not parts of it.
4. **Institutional content.** What any authority ought to stipulate, admit or issue is
   outside scope; this protocol constrains only the records and transitions by which
   they do it.
5. **Truth outside contexts.** Every property established here is relative to a
   context triple; the protocol asserts nothing context-free.

## 16. Falsifiability of this protocol

This protocol is conformance-testable by construction: each rule `R-01 … R-24` names
its observable evidence and its falsifying counterexample. A conformance review of an
implementation consists of:

1. selecting a corpus of transactions;
2. for each rule, searching the corpus for the rule's counterexample pattern;
3. reporting, per rule: *conforms* (no counterexample found, evidence present),
   *violated* (counterexample exhibited, by hash), or *not exercised* (the corpus
   never reaches the rule's input state).

A protocol version is **empirically falsified as a design** if conforming
implementations of it systematically fail to preserve D1/D2 — i.e., if a corpus shows
that following every rule still permits unissued reliance or credit-as-truth. Such a
finding requires a protocol revision, not a reinterpretation (R-21 applies to this
document's own claims).

---

## Appendix A. Methodological evidence from M1 (admissible scope only)

M1 (`CLOSED_BY_ACCEPTED_FALSIFICATION`) contributes exactly four methodological
findings, each already demonstrated in persisted evidence, and nothing further:

| # | Finding | Where demonstrated | Encoded here as |
|---|---|---|---|
| 1 | Preregistration survives adverse results | H1 predictions/falsification conditions held fixed through a falsifying R1 | R-19, R-21 |
| 2 | Conditional authority can be machine-activated from proven predicates | the 18-predicate Phase A→B activation, no discretionary step | R-06, R-11, R-15 (pattern), §9 |
| 3 | An evaluation result is distinguishable from authorization to rely on it | review-ACCEPT ≠ owner acceptance; CI PASS ≠ acceptance, throughout | D2, R-10, R-16, R-17 |
| 4 | A failed hypothesis is admissible evidence, not material for repair | the falsified R1 persisted as mission closure; no corrective iteration | R-19, R-20 |

No generalization beyond these four is made or licensed by this document.

## Appendix B. Frozen terminology imported by this protocol

- *Contemporaneous logical-warrant record (CLWR)* — §6; the judge's product; never
  institutional warrant by itself.
- *Evaluation establishes the property; issuance creates the reliance* — D2; §11.
- *ZTL hereditary = logical stability under the stated semantics and fixed
  authority/formula context, not institutional persistence of authorization* — §8.3.
- *T without admissible witness → Z* — R-02; harvesting is evaluated separately from
  judging.
- Disposition/conformance mapping table — §8.2.

## Appendix C. Rules index

| Rule | Section | One line |
|---|---|---|
| R-01 | §3 | admission is an act, recorded |
| R-02 | §3 | `T` requires an admissible witness; bare `T` → `Z` |
| R-03 | §3 | `F` requires an act too; absence of proof is not refutation |
| R-04 | §3 | markings are immutable inside a context |
| R-05 | §4 | formulas are stipulated by authority, never authored by the judge |
| R-06 | §5 | the evaluation context is the hash-bound triple |
| R-07 | §6 | every evaluation emits a nine-field CLWR at evaluation time |
| R-08 | §6 | CLWRs are immutable; corrections are new records |
| R-09 | §6 | the judge is deterministic over a fixed context |
| R-10 | §7 | a CLWR alone changes no institutional state |
| R-11 | §8 | only `EARNED` qualifies as PASS |
| R-12 | §8 | `hereditary` is context-bounded logical stability, not persistence |
| R-13 | §8 | non-`EARNED` dispositions name their weak links |
| R-14 | §9 | issuance requires both the `EARNED` CLWR and institutional legs |
| R-15 | §10 | every load-bearing reference resolves to a content hash |
| R-16 | §11 | issuance is an explicit, separate, scoped act |
| R-17 | §11 | reliance tracks issuance, never bare evaluation |
| R-18 | §12 | `CANNOT` never decays into `PASS` |
| R-19 | §12 | adverse results are preserved, not repaired |
| R-20 | §12 | blocked non-decisions are first-class outcomes |
| R-21 | §13 | recorded dispositions are ceilings, not floors |
| R-22 | §13 | interpretation is labeled and inherits no evidentiary status |
| R-23 | §14 | replay is a new act: audit of the CLWR, not its source of warrant |
| R-24 | §14 | OAM reconstruction must succeed from records without replay |

---

*End of Protocol v0.1. Submitted for owner/adjudicator review. No implementation work
precedes that review.*
