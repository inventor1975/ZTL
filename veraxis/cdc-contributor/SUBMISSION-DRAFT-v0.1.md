# CDC Submission Draft v0.1 — OIC–ZTL–OAM Institutional Architecture and Evidence Package

Status: DRAFT_FOR_OWNER_REVIEW. Assembled strictly from the owner-approved
permitted-claims surface. Not for publication or transmission.

```
claims_surface = SUBMISSION-PERMITTED-CLAIMS.md @ 2f3ec476a28953cfe0ec05e19ae197c54b44ce72
controlling_F = 4a388e261138f6e51b9261c4e91478bec622d3d2 (F-04/F-05, OWNER_APPROVED)
frozen_A_E = 973f9eba2dfe410efdadad132ce2348d3875e302 (CONTRIBUTOR_FROZEN, unchanged)
PUBLICATION_AUTHORIZED = FALSE
SUBMISSION_TRANSMISSION_AUTHORIZED = FALSE
SEMANTIC_IMPLEMENTATION_GATE = BLOCKED
GATE_SAR_05 = NOT_CLOSED
```

Bracketed tags ([PC-nn], [F-05], [01]–[05]) are traceability markers for
owner review, strippable at final typesetting. Every factual or comparative
sentence traces to the permitted-claims surface or the frozen A–E artifacts;
narrative compression preserves meaning at or below ceiling.

---

## 1. Executive summary

This package proposes to the CDC an institutional architecture — OIC–ZTL–OAM
— for turning authoritative institutional documents into governed,
inspectable computational processes, together with the evidence record of
what the architecture establishes today and what remains future release
work. The proposal is explicitly staged: its central claims are
**architectural**, supported by machine-checked logical foundations, partial
executable artifacts, and a preregistered adversarial evaluation record —
not claims of a completed production system. [PC-02, PC-05, PC-12]

Three commitments organize the design:

1. **Authority is never acquired by machinery.** External legal/regulatory
   sources remain attributable to their recognized issuers; the CDC retains
   institutional authority over adoption, review, reviewer standing,
   disposition, sign-off, and official record formation. Machine output
   never acquires either authority by being produced. [PC-01, PC-07]
2. **Meaning is admitted, recorded, and conserved — not reinterpreted.**
   The institution admits meaning; the system records, binds and versions
   its representation, and is required to conserve it — as meaning, not
   merely bytes — across component and supplier change. [PC-02, PC-10]
3. **Every verdict carries its warrant and its limits.** Logical
   consequence is machine-checked and separated from institutional
   judgment; adverse and incomplete evidence is preserved as such, never
   silently normalized. [PC-05, PC-12, PC-13]

## 2. Institutional architecture [01, 02, 05 — frozen narrative, compressed]

The architecture separates layers that institutional software commonly
conflates, along the frozen chain: authoritative source → candidate
representation of meaning → institutional admission of that exact
represented meaning → semantically conserved representation → logical
warrant → institutional disposition → issuance/official act → reliance,
with correction lineage throughout. Full detail is given in the frozen
artifacts 01 (architecture narrative), 02 (standing model), and 05
(end-to-end boundary with its three seams); this section summarizes their
content without amplification.

- **OIC** is designed as the boundary at which institutionally admitted
  meaning is represented, recorded and versioned; partial supporting
  artifacts exist. OIC software does not originate institutional authority,
  and the runtime layer must not silently reinterpret institutional
  meaning. [PC-02, PC-03]
- **ZTL** supplies the logical-warrant layer: whether a conclusion follows
  from admitted grounds under the represented logic. It does not by itself
  establish source authority, institutional admission, evidence
  sufficiency, reviewer authority, official-finding status, or reliance —
  a boundary whose conceptual form is established jurisprudential prior
  art, cited rather than claimed. [PC-05, PC-01]
- **OAM** owns mission execution: scope, population, evidence, control
  execution, candidate findings, review state, correction/replay,
  deliverable assembly — without owning what the institutional rule means.
  [PC-03]
- **Standing.** The OPEN model defines institutional standing as a bounded,
  non-transitive relation computed from the frozen input dimensions; role
  alone is insufficient. This is design-level: no runtime currently
  computes or enforces it, and authorization-as-such is established art.
  [PC-06]
- **Human authority.** The architecture prohibits machine candidates from
  silently becoming official findings: a separately recorded, authorized
  human act stands between candidate and official record.
  Human-in-the-loop governance as such is established practice and not
  claimed as a contribution. [PC-07]
- **Candidates and records.** The candidate model requires each material
  candidate to bind source, exact anchor, rule/version, expected condition,
  observed fact, uncertainty/contrary evidence, warrant state, reviewer,
  disposition, and artifact identity/digest; partial supporting artifacts
  exist, and binding-as-such is established art. Disposition records are
  required to remain connected to the exact candidate, evidence,
  rule/version, reviewer and consequence. [PC-04, PC-08]
- **Correction.** Correction preserves predecessor history and creates a
  successor state, recalculating downstream eligibility where implemented.
  Executable reliance claim: none. [PC-09]

## 3. Evidence base — what is established today

**Machine-checked logical foundations.** At the frozen evidence snapshot
(the veraxis input pin), the ZTL corpus comprises 371 theorems across 21
Lean modules, each on the empty axiom list — a machine-checked logical
foundation, cited as the snapshot figure, not the current repository state.
Lean verifies logic, not institutional legitimacy. [PC-05]

**Preregistered adversarial evaluation (Phase-A, frozen record).** In the
frozen Phase-A record, 50/50 mutations across six measured classes were
detected with zero observed misses; two classes were unmeasured, §24.5
failed, and the overall result was FAIL_AND_INCOMPLETE. The experiment's
governance value is that defects were preserved as non-measurements rather
than repaired or converted into favorable results. Adverse-evidence
non-promotion as a principle is established art and not claimed. [PC-12]

**Currentness.** Currentness/reliance semantics are represented in the
architecture, but the frozen Phase-A substrate could not construct
executable cases; the denominator was zero. Institutional currentness
remains a design requirement; runtime currentness as such is established
art and not claimed. [PC-13]

**Deployment posture.** The architecture and release plan target
CDC-controlled infrastructure and bounded offline/no-egress operation — a
preregistered release target, not yet measured. [PC-11]

## 4. Comparative positioning [03 — frozen; normalized statuses only]

The comparative record is an **external published-claim and specification
analysis** (papers, standards, formal models, reported architectures); it is
not independently verified competing-system capability:

```
EXTERNAL_IMPLEMENTATION_STATUS = NOT_SYSTEMATICALLY_ASSESSED
EXTERNAL_INDEPENDENT_REPRODUCTION_STATUS = NOT_ASSESSED
```

Established prior or concurrent art, used and cited rather than claimed:
runtime authorization primitives; generic semantic preservation; standing
as a general principle; the warrant-vs-authority distinction;
adverse-evidence non-promotion; runtime authorization currentness;
issuance/verification separation; record authenticity and history
preservation; human-in-the-loop governance. `NOVELTY_FINDING = NOT_CLAIMED`.

What the reviewed corpus does not document: full satisfaction of the S2
institutional-meaning-admission test (strong partial neighbors found; the
closest, W3C Verifiable Credentials 2.0, is a strong partial equivalent —
not a pass); and T1 semantic-conservation across heterogeneous
implementation substitution (semantic-preservation prior art found; no
reviewed source documents the T1 test across substitution). Their
conjunction has no full documented match in the reviewed corpus.

The residual proposition — architectural, design-level, held open to
falsification: **the system treats institutionally admitted meaning as a
distinct computational state and requires that state's meaning — not merely
its bytes — to remain conserved across heterogeneous implementation
change.** This is an architectural advancement claim, not an executable
achievement claim; the corresponding challenge record (SCR-16) remains
open under an owner-controlled withdrawal condition. [PC-02, PC-10, §2 of
the claims surface]

## 5. Limitations and open items (mandatory disclosures) [F-05]

The following are integral to this submission and bound its claims:

1. No frozen end-to-end OIC→OAM execution.
2. No full manifest-bound end-to-end candidate-binding execution.
3. No supplier-replacement execution (0 provider-replacement trials).
4. No measured R-CDC-04 offline/no-egress release-gate result.
5. Standing runtime not operationalized (standing-currentness deferred).
6. Phase-A v0.1 = FAIL_AND_INCOMPLETE (6/8 classes measured, 50/50, 0
   observed misses; 2 adapter/admission classes UNMEASURED; §24.5
   provenance-admission defect open, retained as an explicit product
   remediation item).
7. Currentness: denominator 0; 5 × BLOCKED_CASE_CONSTRUCTION; neither pass
   nor fail.
8. External implementation landscape not systematically assessed.
9. External independent reproduction not assessed.

Provenance caveat: the disposition-record connectivity requirement is
baseline-reflected; it has not been re-verified against the original
applicant-retained source. [PC-08] Definition-precedence status: the frozen
architecture's public coordinates and exact bytes are verifiable from the
freeze commit onward; public pre-review definition precedence is not
asserted (SCR-17 PARTIALLY_CLOSED). Open challenge records F02B-01/02/04/05
and SCR-16 remain open as listed in the frozen F-05.

## 6. Release gates and staging

Nothing in this package implies an open implementation gate:
`SEMANTIC_IMPLEMENTATION_GATE = BLOCKED`; `GATE_SAR_05 = NOT_CLOSED`.
Executable maturity beyond the recorded evidence — end-to-end OIC→OAM
execution, candidate-binding execution, supplier-replacement trials, the
offline/no-egress release gate, standing and currentness runtimes — is
future release work, each item gated by its own preregistered test and
separate authorization. [PC-02, PC-03, PC-09, PC-11, F-05]

## 7. Package provenance and claim discipline

The claims in this draft are bounded by the owner-approved
SUBMISSION-PERMITTED-CLAIMS surface (commit `2f3ec476…`, tree `e8723ded…`),
derived by intersection of an internal executable-evidence reconciliation
and an external published-claim analysis over the frozen architecture
artifacts 01–05 (freeze commit `973f9eba…`, SHA-256 manifest included in the
repository). Measured figures carry their denominators; snapshot figures
carry their snapshot context; blocked and unmeasured results are reported
as blocked and unmeasured. Any public statement exceeding this surface
requires separate owner adjudication.

---

*Assembly note (not part of the submission): the owner-side 14-section
submission structure was referenced in the contributor packet but its
template is not in the assembler's possession; if that template is binding,
this draft reflows into it mechanically — content is complete under the
permitted-claims surface, only sectioning would change.*
