# CDC Submission Draft v0.3 — OIC–ZTL–OAM Institutional Architecture and Evidence Package

Status: DRAFT_FOR_OWNER_REVIEW. Supersedes v0.2 (mechanical insertion of the
owner input packet into the frozen v0.2 scaffold; no semantic improvement,
compression or amplification; no new claims). Not for publication or
transmission.

```
claims_surface = SUBMISSION-PERMITTED-CLAIMS.md @ 2f3ec476a28953cfe0ec05e19ae197c54b44ce72
controlling_F = 4a388e261138f6e51b9261c4e91478bec622d3d2 (F-04/F-05, OWNER_APPROVED)
frozen_A_E = 973f9eba2dfe410efdadad132ce2348d3875e302 (CONTRIBUTOR_FROZEN, unchanged)
controlling_scaffold = SUBMISSION-DRAFT-v0.2 @ 53f4090d516061c834653fdb4eef3e355dc78969
owner_input = CDC-OWNER-INPUT-PACKET-v0.2-RECONCILED.md, SHA-256
  c745c54264db23a38a35e0562161856aa96674ff6f43e501005af631cd1e75f4
  (OWNER_INSERTION_AUTHORIZATION = GRANTED, owner message 2026-08-10;
  the packet's internal header retains its authoring-time labels
  "v0.1 / INSERTION_AUTHORIZED = FALSE" — superseded by the owner
  authorization bound to the exact SHA-256 above; noted, not normalized)
FINAL_SUBMISSION_APPROVED = FALSE
PUBLICATION_AUTHORIZED = FALSE
SUBMISSION_TRANSMISSION_AUTHORIZED = FALSE
SEMANTIC_IMPLEMENTATION_GATE = BLOCKED
GATE_SAR_05 = NOT_CLOSED
```

Bracketed tags ([PC-nn], [F-05], [01]–[05]) and the owner packet's
source-class tags (`CHALLENGE_SOURCE_FACT`, `OWNER_FRAMING`,
`ARCHITECTURAL_DESIGN`, `PROPOSED_POC_TARGET`, `OWNER_FACT`,
`UNRESOLVED_OWNER_FACT`) are traceability markers, strippable only at a
separately authorized final typesetting pass. All `UNRESOLVED_OWNER_FACT`
entries are carried verbatim and must not be filled by inference.

External-source reconciliation note (owner packet, verbatim): Claude's
independent challenge-source audit returned `PASS_WITH_EXACT_CORRECTIONS`;
the official live CDC page and Challenge Statement Version 3-1 were
independently re-checked on 2026-08-10. The official sources verify the
21 August 2026 deadline, CDC + twelve CRC beneficiaries, three procurement
phases, two complementary components, the published KPIs, listed risks, and
the eligibility criteria. The 2026 page's Terms link resolves to a 2025
Ghana instrument; no 2026 CDC Terms are treated as established here.

---

## 1. Executive Summary

This package proposes to the CDC an institutional architecture — OIC–ZTL–OAM
— for turning authoritative institutional documents into governed,
inspectable computational processes, together with the evidence record of
what the architecture establishes today and what remains future release
work. The proposal is explicitly staged: its central claims are
**architectural**, supported by machine-checked logical foundations, partial
executable artifacts, and a recorded adversarial evaluation — not claims of
a completed production system. [PC-02, PC-05, PC-12]

Three commitments organize the design:

1. **Authority is never acquired by machinery.** External legal/regulatory
   sources remain attributable to their recognized issuers; the CDC retains
   institutional authority over adoption, review, reviewer standing,
   disposition, sign-off, and official record formation. Machine output
   never acquires either authority by being produced. [PC-01, PC-07]
2. **Meaning is admitted, recorded, and conserved — not reinterpreted.**
   The institution admits meaning; the system records, binds and versions
   its representation, and the architecture defines a requirement to
   conserve it — as meaning, not merely bytes — across component and
   supplier change. [PC-02, PC-10]
3. **Every verdict carries its warrant and its limits.** Logical
   consequence is machine-checked and separated from institutional
   judgment; adverse and incomplete evidence is preserved as such, never
   silently normalized. [PC-05, PC-12, PC-13]

## 2. Challenge Fit and Customer Outcome

The owner frames the CDC/CRC challenge as an institutional production
problem rather than an absence of audit authority or methodology. The
underlying challenge facts are that the CDC and twelve CRCs already operate
formal procurement-control processes, use structured PMP data and
standardized mission deliverables, while current control work remains
substantially manual: tender dossiers and PMP data are reconciled manually,
controls are generally applied to samples, semantic analysis of contractual
documents is rarely practised for lack of appropriate tools, probity checks
are manual, and formal deliverables consume significant controller time.
`OWNER_FRAMING + CHALLENGE_SOURCE_FACT`

The proposed PoC therefore targets the two components named by the
challenge as one governed workflow. For **compliance analysis and
predictive detection**, it would combine read-only PMP/dossier
reconciliation, a bounded CDC-approved control pack across competitive
tendering, bid evaluation and contract award, separately labelled
semantic/irregularity proposals, probity-coverage checks, and
source-rule-expected-observed traceability. For **deliverable generation**,
it would assist preparation of the five named mission deliverables while
preserving CDC/CRC review, editing, validation, sign-off and official
record formation. `CHALLENGE_SOURCE_FACT + ARCHITECTURAL_DESIGN`

The customer outcome is not "more alerts." The owner-defined PoC objective
is **more defensible procurement-control work completed per CDC/CRC
auditor-day, with evidentiary and procedural quality held constant or
improved**, measured on a fixed pilot population rather than assumed at
proposal stage. `OWNER_FRAMING + PROPOSED_POC_TARGET`

The institutional boundary remains explicit: AI may organize evidence,
execute approved tests and propose bounded issues; CDC/CRC controllers
retain authority over methodology, investigation, institutional
disposition, finalization and official follow-up. `ARCHITECTURAL_DESIGN`

## 3. Technical Solution

The architecture deliberately separates layers along the frozen chain:
authoritative source → candidate representation of meaning → institutional
admission of that exact represented meaning → semantically conserved
representation → logical warrant → institutional disposition →
issuance/official act → reliance, with correction lineage throughout. Full
detail is given in the frozen artifacts 01 (architecture narrative), 02
(standing model), and 05 (end-to-end boundary with its three seams); this
section summarizes their content without amplification. [01, 02, 05]

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
- **Correction.** Correction is designed to preserve predecessor history,
  create successor representation, and recalculate downstream eligibility
  where implemented. Executable reliance claim: none. [PC-09]

## 4. Implementation Methodology

The delivery method is the same governed-transition discipline that
produced this package's own claims record: architecture is frozen before
evidence is claimed against it; evidence carries its class and denominator;
measured, blocked and unmeasured results are reported as such; adverse
results are preserved rather than repaired; and public claims are bounded
by an owner-adjudicated ceiling. The recorded adversarial evaluation
(Section 5) was governed this way: defects were preserved as
non-measurements rather than converted into favorable results. [PC-12, §7]

## 5. Expected Impact and Measurement

The proposed impact follows the challenge's own success indicators: move
from sample-based control toward comprehensive coverage within the agreed
PoC scope; reduce time spent executing selected controls; assess the
relevance of compliance and ethics alerts with control teams; preserve full
source/rule traceability; and reduce time spent producing mission
deliverables while maintaining institutional quality and template
compliance. These are PoC objectives, not current performance claims.
`CHALLENGE_SOURCE_FACT + PROPOSED_POC_TARGET`

Impact will be established only through a fixed-denominator, paired
current-versus-assisted evaluation agreed with CDC/CRC. The measurement
contract should report at least:

1. mission-population coverage and evaluability;
2. controller time for selected control-test tasks;
3. deterministic alert relevance and disposition distribution;
4. semantic/probity proposal relevance, reported separately from
   deterministic controls;
5. source-locator and traceability completeness;
6. reviewer workload, dismissal/qualification/escalation burden and
   correction burden;
7. time and edit burden to reach a review-ready version of each selected
   deliverable;
8. template/content quality under CDC/CRC review;
9. unauthorized-transition and silent-failure negative-test outcomes where
   those release gates are executable; and
10. CDC/CRC user acceptance of the source → rule → evidence → candidate →
    disposition chain.

No percentage improvement, ROI, staffing saving, recovery amount or
detection-rate improvement is asserted in this packet. Numeric targets may
be introduced only as explicitly preregistered PoC targets after Gate 0
baseline/corpus agreement; they cannot be reported as achieved until
measured. `PROPOSED_POC_TARGET`

**Impact acceptance rule.** The PoC should not be called impactful merely
because it processes documents or generates alerts. An impact claim
requires a signed measurement record showing a fully accounted denominator,
comparable current and assisted tasks, improved defensible throughput or
reduced effort, maintained/improved evidentiary and deliverable quality,
manageable review workload, and successful human use of the exact
source-rule-candidate-disposition chain.
`OWNER_FRAMING + PROPOSED_POC_TARGET`

The measurement record established to date:

- **Machine-checked logical foundations.** At the frozen evidence snapshot
  (the veraxis input pin), the ZTL corpus comprises 371 theorems across 21
  Lean modules, each on the empty axiom list — a machine-checked logical
  foundation, cited as the snapshot figure, not the current repository
  state. Lean verifies logic, not institutional legitimacy. [PC-05]
- **Recorded adversarial evaluation (Phase-A, frozen record).** In the
  frozen Phase-A record, 50/50 mutations across six measured classes were
  detected with zero observed misses; two classes were unmeasured, §24.5
  failed, and the overall result was FAIL_AND_INCOMPLETE. The evaluation's
  governance value is that defects were preserved as non-measurements
  rather than repaired or converted into favorable results.
  Adverse-evidence non-promotion as a principle is established art and not
  claimed. [PC-12]
- **Currentness.** Currentness/reliance semantics are represented in the
  architecture, but the frozen Phase-A substrate could not construct
  executable cases; the denominator was zero. Institutional currentness
  remains a design requirement; runtime currentness as such is established
  art and not claimed. [PC-13]

## 6. Sovereign Architecture, Security and Operations

The architecture and release plan target CDC-controlled infrastructure and
bounded offline/no-egress operation — a preregistered release target, not
yet measured. Tools come to the CDC; normal PoC operation is designed
around CDC-approved infrastructure and CDC-controlled
sources/roles/rules/evidence. No production deployment, certified sovereign
environment, hardware-compatibility, HA/DR or accreditation evidence is
claimed. [PC-11]

## 7. Acceptance Tests and Definition of Done

Acceptance is bounded to what can be tested under the applicable
frozen/preregistered gates; nothing recorded here is represented as already
done. Currently unmeasured acceptance surfaces, each future release work,
subject to the applicable frozen/preregistered gates and separate
authorization: end-to-end OIC→OAM execution; manifest-bound
candidate-binding execution; the R-CDC-04 offline/no-egress release gate;
the supplier-replacement release test; standing and currentness runtimes.
`SEMANTIC_IMPLEMENTATION_GATE = BLOCKED`; `GATE_SAR_05 = NOT_CLOSED`.
[PC-02, PC-03, PC-09, PC-10, PC-11, F-05]

## 8. Scaling to the CRC Network

The first scaling question is institutional scale inside Morocco, not
international replication. The challenge beneficiary is the CDC together
with twelve CRCs. The proposed scaling architecture therefore uses a common
governed core while keeping mission authority, local scope and disposition
bounded to the relevant CDC/CRC context.
`CHALLENGE_SOURCE_FACT + ARCHITECTURAL_DESIGN`

The design target is:

- a CDC-approved base control/template package with versioned CRC overlays
  rather than hard-coded software forks;
- mission-scoped CRC users, evidence and dispositions;
- common source/evidence schemas and governed transition semantics;
- institution-controlled portable records that do not require
  reconstruction when a conformant implementation or provider changes; and
- local mission responsibility without implying transfer of institutional
  authority through shared infrastructure.
  `ARCHITECTURAL_DESIGN + PROPOSED_POC_TARGET`

A bounded transfer test should require one selected CRC to complete an
agreed scenario using the common deployment/profile, followed by an
adaptation dry run in which selected controls, connectors and templates
change without changing the core evidence/transition schemas or
invalidating frozen historical records. This is a proposed PoC transfer
test, not demonstrated CRC scalability. `PROPOSED_POC_TARGET`

International/jurisdictional transfer is outside the current capability
claim. The transferable design unit is the common evidence/transition
interface plus a jurisdiction-owned control pack, language/model pack,
source connectors, authority/workflow configuration, institutional
templates/record adapter and sovereign deployment profile. Each new
institution or jurisdiction requires fresh authority, source, control,
standing and currentness inputs; Moroccan institutional authority is not
portable. `ARCHITECTURAL_DESIGN`

## 9. Risks and Mitigations

The open-items record (Section 13; F-05) is the honest risk surface of this
proposal; it is disclosed rather than mitigated by wording:

- Executable maturity risks: no frozen end-to-end OIC→OAM execution; no
  full manifest-bound candidate-binding execution; no supplier-replacement
  execution; no measured offline/no-egress release-gate result; standing
  and currentness runtimes not operationalized. [F-05]
- Evaluation risks: two adversarial classes unmeasured; one open
  provenance-admission defect (§24.5), retained as an explicit product
  remediation item. [PC-12, F-05]
- Provenance risk: the disposition-record connectivity requirement is
  baseline-reflected, not re-verified against the original
  applicant-retained source. [PC-08]
- Comparative-knowledge risks: external implementation landscape not
  systematically assessed; external independent reproduction not assessed.
  [F-05]

The challenge identifies document quality, semantic complexity,
ethics-alert precision, deliverable completeness, POD variability,
confidentiality and ethics-follow-up as material risks. The PoC mitigation
plan is deliberately staged; a mitigation is not represented as operating
until its corresponding gate is executed.

- **Aged scans, handwriting, proprietary or poor-quality documents:**
  preserve originals and source locators; stratify evaluability by
  language/format/quality; route unsupported or low-confidence material to
  explicit human-review/not-evaluable states. No production-grade Arabic
  handwriting capability is assumed before representative corpus testing.
  `CHALLENGE_SOURCE_FACT + PROPOSED_POC_TARGET`
- **Semantic complexity:** limit semantic use cases to a bounded
  CDC-approved scope; require source-cited proposals and explicit
  method/version; keep semantic proposals separate from deterministic
  breach results and institutional findings.
  `ARCHITECTURAL_DESIGN + PROPOSED_POC_TARGET`
- **False positives / sensitive ethics signals:** report relevance and
  workload by risk class; require a CDC-approved restricted follow-up
  protocol before operational use; never interpret missing POD evidence as
  absence of risk. `CHALLENGE_SOURCE_FACT + PROPOSED_POC_TARGET`
- **Incomplete or non-conforming deliverables:** use controlled CDC
  templates, explicit completeness checks, tracked human edits and
  required sign-off; machine generation cannot create an official record.
  `ARCHITECTURAL_DESIGN + PROPOSED_POC_TARGET`
- **POD format/storage variability:** perform Gate 0 discovery and
  maintain explicit coverage/evidence states rather than silently dropping
  unavailable declarations. `CHALLENGE_SOURCE_FACT + PROPOSED_POC_TARGET`
- **Confidentiality/data sovereignty:** target CDC-approved local
  infrastructure, mission-scoped access and bounded no-egress operation;
  target-environment no-egress, backup/restore and access-isolation
  evidence remain release tests, not current achievements.
  `ARCHITECTURAL_DESIGN + PROPOSED_POC_TARGET`
- **Known internal maturity gaps:** no end-to-end OIC→OAM execution, no
  full candidate-binding execution, no supplier-replacement execution, no
  measured offline/no-egress release gate, standing runtime not
  operationalized, Phase-A remains FAIL_AND_INCOMPLETE, and currentness
  has executable denominator zero. Each remains a separately governed
  release item; none is mitigated by wording. `F-05 BOUNDARY`

## 10. Team, Governance and Delivery Responsibilities

**Arkadiy Miteiko — Owner / design authority.** Existing project records
assign Arkadiy responsibility for system intent, scope authority, product
boundary, challenge claims and owner decisions. For this submission, that
supports the role of accountable architecture/product owner and final
claim/submission authority. `OWNER_FACT`
Provenance binding: `Open_Audit_Mission_TDD_v1.0_CDC_Submission_Baseline.docx`,
SHA-256 `cf795f408fd5adf618756f7509d8826a26a3b0c058d61a89b610bed91cac5635`
(owner/design authority record); `OAM_System_Architecture_Review_SAR_v1.0.pdf`,
SHA-256 `f6f26fdcbcd89d3a4ca02f2ec77c1ecde17af00b1aa388aacc002736d3ab516f`
(system intent/scope/product-boundary/challenge-claim/owner-decision
responsibility record).

**Vitaliy Reznik — Core research/architecture and verification
contributor.** Existing project records assign Vitaliy responsibility for
ZTL warrant semantics, T/F/Z correctness, the logical boundary and
conformance review; current CDC standing is active core contributor, not
independent assurance on the same object. `OWNER_FACT`
Provenance binding: `OAM_System_Architecture_Review_SAR_v1.0.pdf`, SHA-256
`f6f26fdcbcd89d3a4ca02f2ec77c1ecde17af00b1aa388aacc002736d3ab516f`
(ZTL/T-F-Z/logical-boundary/conformance responsibility record); frozen
contributor artifact `03-ADVANCEMENT-BEYOND-STATE-OF-ART.md` @ commit
`973f9eba2dfe410efdadad132ce2348d3875e302`, canonical package SHA-256
`70bebe3a963ac93f2eded55fcf3df58a94f59fa11aa9f15d8239881583957545`
(CORE_RESEARCH_AND_ARCHITECTURE_CONTRIBUTOR standing). Same-object
independent assurance remains prohibited by the frozen standing model.

**CDC/CRC institutional role.** The proposal does not transfer source,
methodology, reviewer, disposition or official-record authority to the
applicant. CDC/CRC must supply or approve the mission scope, authoritative
controls/interpretations, reviewer standing, permitted dispositions,
templates and official handoff process. `ARCHITECTURAL_DESIGN`

Governance surface derivable from the permitted claims: institutional
authority over adoption, review, reviewer standing, disposition, sign-off
and official record formation remains with the CDC [PC-01]; a separately
recorded, authorized human act stands between machine candidate and
official record [PC-07]; public claims about the system are themselves
governed by the owner-adjudicated claim ceiling (Section 13).

### Official eligibility and deadline gates

The current official CDC challenge page states that applications are due
**21 August 2026** and that incomplete applications will not be evaluated.
`CHALLENGE_SOURCE_FACT`

The current official eligibility criteria include: legal incorporation;
fewer than 75 employees; at least one fluent-French team member; under
USD 5 million in annual revenue; relevant technical expertise; and
capacity to develop on-premise solutions. `CHALLENGE_SOURCE_FACT`

Current owner-evidence state:

```text
APPLICATION_DEADLINE = 2026-08-21 / VERIFIED_OFFICIAL_SOURCE
EMPLOYEE_COUNT_LT_75 = UNRESOLVED_OWNER_FACT / SUBMISSION-BLOCKING ELIGIBILITY INPUT
ANNUAL_REVENUE_LT_USD_5M = UNRESOLVED_OWNER_FACT / SUBMISSION-BLOCKING ELIGIBILITY INPUT
FRENCH_FLUENT_TEAM_MEMBER = UNRESOLVED_OWNER_FACT / SUBMISSION-BLOCKING ELIGIBILITY INPUT
ON_PREMISE_CAPACITY = ARCHITECTURAL_DESIGN / CURRENT ORGANIZATIONAL ELIGIBILITY EVIDENCE NOT YET SEPARATELY BOUND
```

The packet must not treat architecture-level on-premise design as proof
that the applicant satisfies the organizational eligibility criterion.
Applicant evidence must be bound separately before submission.

### Blocking roster facts — do not infer

```text
FRENCH_FLUENT_TEAM_MEMBER = UNRESOLVED_OWNER_FACT / SUBMISSION-BLOCKING ELIGIBILITY INPUT
PUBLIC_PROCUREMENT_AUDIT_SME = UNRESOLVED_OWNER_FACT / TEAM-CAPABILITY INPUT
DOCUMENT_AI_NLP_DELIVERY_LEAD = UNRESOLVED_OWNER_FACT / TEAM-CAPABILITY INPUT
SOVEREIGN_ON_PREM_SECURITY_LEAD = UNRESOLVED_OWNER_FACT / TEAM-CAPABILITY INPUT
MOROCCO_ARABIC_SUPPORT = UNRESOLVED_OWNER_FACT / BOUNDED GAP OR NAMED SUPPORT
```

The current official challenge page requires at least one fluent-French
team member and technical capacity for on-premise solutions. No admissible
project source retrieved for the owner packet names the French-fluent
member or the other domain leads above. They must remain unresolved until
owner evidence is supplied; they may not be assigned to Arkadiy, Vitaliy or
another person by inference.
`CHALLENGE_SOURCE_FACT + UNRESOLVED_OWNER_FACT`

## 11. Data Ownership, Openness and Supplier-Replacement Test

OPEN defines a cross-supplier preservation and semantic-conservation
requirement (T1) for institution-controlled artifacts: the architecture is
required to permit replacement of model, provider, database, UI, adapter,
deployment operator, and ultimately supplier without requiring the
institution to surrender or reconstruct its admitted control
representations, evidence, dispositions, mission history, correction
lineage, or other institution-controlled portable artifacts — with
institutional meaning semantically conserved across the transition. This is
a design requirement; actual provider-replacement performance remains a
separate unexecuted release test. In the reviewed published corpus no
source documents T1 satisfaction across heterogeneous implementation
substitution. [PC-10, 03]

## 12. Challenge Requirement Coverage

| Official challenge requirement / outcome | Proposed response | Current epistemic state |
|---|---|---|
| Regulatory compliance across competitive tendering, bid evaluation and contract award | Bounded CDC-approved Control Pack; OIC-admitted controls consumed by OAM | DESIGN / END-TO-END NOT YET EXECUTED |
| Systematic use of structured PMP + unstructured tender dossiers | Read-only PMP/dossier reconciliation with source preservation and explicit missing/non-evaluable states | DESIGN / PARTIAL ARTIFACT |
| Move from sample-based work toward comprehensive PoC coverage | Frozen mission population and population-accountability requirement | DESIGN / POC TARGET |
| Semantic analysis for qualitative irregularities | Bounded source-cited semantic proposals, separately labelled from deterministic controls/findings | DESIGN / POC TARGET |
| Ethics/probity signals | Member-level POD coverage and bounded risk proposals with restricted follow-up | DESIGN / POC TARGET |
| Alert traceability: source, control rule, expected vs observed | Evidence-bound candidate model and traceability requirement | DESIGN + PARTIAL ARTIFACT; FULL END-TO-END BINDING NOT EXECUTED |
| Cross-reference PMP and tender files | Procedure-centred reconciliation and exception queue | DESIGN / POC TARGET |
| Five standard mission deliverables + review interface | Assisted drafts of orientation note, provisional report, final report, findings summary and transmittal letter; human finalization | DESIGN / POC TARGET |
| Compatibility with official circulation / mission tools | Controlled export/record-adapter seam with authoritative receipt as end-state target | DESIGN / POC TARGET |
| Reduce control-test time | Paired current-vs-assisted measurement with fixed task boundaries | UNMEASURED POC TARGET |
| Alert relevance assessed with control teams | Blinded/structured disposition and workload/yield measurement, deterministic and probabilistic classes separated | UNMEASURED POC TARGET |
| Reduce deliverable-production time | Paired time/edit-burden measurement under CDC templates | UNMEASURED POC TARGET |
| On-premise / data sovereignty | CDC-controlled infrastructure and bounded offline/no-egress release target | PREREGISTERED/DESIGN TARGET; NOT MEASURED |
| Twelve CRC beneficiary network / scalability | Common governed core + CRC-scoped mission overlays and transfer scenario | DESIGN / UNEXECUTED TRANSFER TEST |
| Remote/satellite verification for relevant project types | Preserve as an optional challenge capability surface for infrastructure/construction/agricultural/environmental cases; no current implementation claim | OFFICIAL CHALLENGE CONTEXT / NOT CURRENTLY CLAIMED OR IMPLEMENTED |
| Corruption/fraud detection standards and good-practice sources in criteria/costing evaluation | Maintain a CDC-approved, versioned external-reference register and use only where institutionally admitted; no claim that public standards themselves establish a finding | OFFICIAL CHALLENGE EXPECTATION / DESIGN RESPONSE / NOT MEASURED |
| French-language eligibility | Name and evidence for at least one fluent-French team member | BLOCKING OWNER INPUT |

This table is a requirement-to-response map. It is not evidence that the
mapped capability has been implemented or accepted. The maturity column is
controlling.

## 13. Claim Boundaries and Submission Conditions

**Comparative positioning (published-claim analysis only).** The
comparative record is an external published-claim and specification
analysis (papers, standards, formal models, reported architectures); it is
not independently verified competing-system capability:

```
EXTERNAL_IMPLEMENTATION_STATUS = NOT_SYSTEMATICALLY_ASSESSED
EXTERNAL_INDEPENDENT_REPRODUCTION_STATUS = NOT_ASSESSED
NOVELTY_FINDING = NOT_CLAIMED
```

Established prior or concurrent art, used and cited rather than claimed:
runtime authorization primitives; generic semantic preservation; standing
as a general principle; the warrant-vs-authority distinction;
adverse-evidence non-promotion; runtime authorization currentness;
issuance/verification separation; record authenticity and history
preservation; human-in-the-loop governance.

What the reviewed corpus does not document: full satisfaction of the S2
institutional-meaning-admission test (strong partial neighbors found; the
closest, W3C Verifiable Credentials 2.0, is a strong partial equivalent —
not a pass); and T1 semantic-conservation across heterogeneous
implementation substitution. Their conjunction has no full documented match
in the reviewed corpus. The residual proposition — architectural,
design-level, held open to falsification: the system treats institutionally
admitted meaning as a distinct computational state and requires that
state's meaning — not merely its bytes — to remain conserved across
heterogeneous implementation change. This is an architectural advancement
claim, not an executable achievement claim; challenge record SCR-16 remains
open under an owner-controlled withdrawal condition. [PC-02, PC-10, §2]

**Mandatory disclosures (integral to this submission).** (1) No frozen
end-to-end OIC→OAM execution. (2) No full manifest-bound candidate-binding
execution. (3) No supplier-replacement execution (0 trials). (4) No
measured R-CDC-04 offline/no-egress release-gate result. (5) Standing
runtime not operationalized. (6) Phase-A v0.1 = FAIL_AND_INCOMPLETE (6/8
classes measured, 50/50, 0 observed misses; 2 adapter/admission classes
UNMEASURED; §24.5 provenance-admission defect open). (7) Currentness:
denominator 0; 5 × BLOCKED_CASE_CONSTRUCTION; neither pass nor fail.
(8) External implementation landscape not systematically assessed.
(9) External independent reproduction not assessed. [F-05]

**Precedence and provenance.** The frozen architecture's public coordinates
and exact bytes are verifiable from the freeze commit onward; public
pre-review definition precedence is not asserted (SCR-17
PARTIALLY_CLOSED). Open challenge records F02B-01/02/04/05 and SCR-16
remain open as listed in the frozen F-05. The claims in this draft are
bounded by the owner-approved SUBMISSION-PERMITTED-CLAIMS surface (commit
`2f3ec476…`), derived by intersection of an internal executable-evidence
reconciliation and an external published-claim analysis over the frozen
architecture artifacts 01–05 (freeze commit `973f9eba…`). Measured figures
carry their denominators; snapshot figures carry their snapshot context;
blocked and unmeasured results are reported as blocked and unmeasured. Any
public statement exceeding this surface requires separate owner
adjudication.

**Terms status (owner packet, verbatim).**

```text
2026_TERMS_STATUS = AMBIGUOUS
LIVE_2026_PAGE_TERMS_LINK = resolves to TV_IC_TermsConditions_2025.pdf
LOCATED_TERMS_SCOPE = GovTech Innovation Challenge 2025 / Ghana Revenue Authority
2026_CDC_IP_OR_PARTICIPATION_TERMS = NOT_ESTABLISHED_BY_THIS_PACKET
```

No IP, open-source, post-programme procurement, participation, branding,
or data-sharing obligation is asserted from the 2025 instrument for the
2026 CDC challenge. A binding 2026 instrument, if later supplied through
the application portal or official communication, must be separately
admitted before reliance.

## 14. Conclusion

The package offers the CDC a deliberately staged proposition: an
institutional architecture whose boundary commitments — authority never
acquired by machinery; meaning admitted, recorded and conserved by
requirement; verdicts carrying their warrants and limits — are frozen and
publicly verifiable; an evidence record that reports exactly what has been
established, with denominators, and exactly what has not; and a release
path in which every remaining capability is future work subject to the
applicable frozen/preregistered gates and separate authorization. The
claims made here are bounded by an adjudicated ceiling, and the package
discloses its own open defects and unmeasured surfaces as part of the
proposal itself. [§1, §7, §13]

## References

### External official sources

1. World Bank GovTech Innovation Challenge 2026 — Morocco CDC/CRC, Public
   Procurement Control, Challenge Statement Version 3-1, last updated
   25 June 2026:
   https://govtech.trustvalley.swiss/assets/uploads/2026/CDC/en/2026-GIC-challenge-statement-public-procurement-control-EN-1.pdf
2. GovTech Trust Valley — Morocco Supreme Audit Institution (Cour des
   Comptes / CDC) challenge page, current retrieval 10 August 2026:
   https://govtech.trustvalley.swiss/challenges/cdc-morocco/

### Owner/application sources

3. `01_Veraxis_CDC_Flagship_Proposal_Completion_Candidate.docx` — July 2026
   completion-candidate owner material. Used only for owner framing,
   proposed PoC measurement/scaling design and prior requirement crosswalk;
   bracketed applicant facts remain non-evidence.
4. `Open_Audit_Mission_TDD_v1.1_Core_and_CDC_Reference_Profile.docx` —
   owner-controlled development baseline and requirement traceability.
5. `OAM_System_Architecture_Review_SAR_v1.0.pdf` — project role assignments
   and architecture review record.

### Frozen claim/control surfaces

6. Frozen CDC contributor A–E, commit
   `973f9eba2dfe410efdadad132ce2348d3875e302`.
7. Owner-approved F reconciliation, commit
   `4a388e261138f6e51b9261c4e91478bec622d3d2`.
8. Owner-approved `SUBMISSION-PERMITTED-CLAIMS`, commit
   `2f3ec476a28953cfe0ec05e19ae197c54b44ce72`.
9. Controlling submission scaffold v0.2, commit
   `53f4090d516061c834653fdb4eef3e355dc78969`.

Prior-art citations named in Sections 3 and 13 (jurisprudential
warrant/authority formalization; W3C VC 2.0; further items per owner
reference list): pending the separately authorized final typesetting pass.
