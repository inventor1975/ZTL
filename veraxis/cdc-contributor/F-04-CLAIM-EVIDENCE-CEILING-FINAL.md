# F-04-CLAIM-EVIDENCE-CEILING-FINAL

From: Vitaly Reznik (`inventor1975`), integration owner for F. Date: 2026-08-10.
Method: **intersection, not average.** For each frozen `CDC-CLAIM-01..13`
(artifact 04, sha256 `696354b0…`, the sole authoritative register) three
independent surfaces are held apart and the final permitted claim is
constrained by the **lower applicable ceiling**:

- `INTERNAL_EVIDENCE_CEILING` — from F-02B (accepted controlling internal
  reconciliation; `tests_executed=0`; evidence classes and denominators
  verbatim), traceability closed where possible by
  `F-02B-TRACEABILITY-SUPPLEMENT.md` (existing artifacts only).
- `EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING` — from F-03D under the owner
  delta (`OWNER-ADJUDICATION-AND-SOTA-EVIDENCE-CLASS-DELTA.md`); epistemic
  class `EXTERNAL_PUBLISHED_CLAIM_AND_SPECIFICATION_ANALYSIS` only.
- `EXTERNAL_VERIFIED_SYSTEM_CAPABILITY` — **`NOT_ASSESSED` for every claim**
  (no independent execution of competing systems was performed).

Governing rules honored: published claim about a neighbor ≠ observed
competitor capability; internally implemented property ≠ advancement claim
by mere existence; S2/T1 are **architectural advancement claims, not
executable achievement claims**; blocked=BLOCKED, unmeasured=UNMEASURED,
denominator 0 is neither pass nor fail; A–E untouched.

Global external constraints applying to all claims (from F-01 §2):
`EXTERNAL_IMPLEMENTATION_STATUS = NOT_SYSTEMATICALLY_ASSESSED`;
`EXTERNAL_INDEPENDENT_REPRODUCTION_STATUS = NOT_ASSESSED`; the withdrawn-
novelty list (runtime authorization primitives; generic semantic
preservation; standing as a general principle; warrant-vs-authority as a
general principle; adverse-evidence non-promotion; runtime authorization
currentness; issuance/verification separation; record authenticity/history
preservation as generic properties) is binding on final wording.

---

## CDC-CLAIM-01 — source authority / CDC mission authority

- INTERNAL_EVIDENCE_CEILING: `DESIGN + EXTERNALLY_SOURCED_CHALLENGE_BOUNDARY`;
  observation `NO_EXECUTION`; denominator N/A. Max wording (F-02B): "The
  architecture preserves source-authority and CDC mission-authority
  boundaries."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: authority-non-transferability
  and warrant-vs-power distinctions are established prior art (Hohfeld
  second-order relations with modern formalizations — SCR-15; CXI
  manifest-bound authority, `REPORTED_ARCHITECTURE`). Cite as prior art;
  no contribution claim on the distinction itself.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: The architecture preserves source-authority and
  CDC mission-authority boundaries, applying a boundary whose conceptual
  form is established jurisprudential prior art (cited), to the CDC
  institutional pipeline. Design-level; no pilot authority configuration
  executed.
- PROHIBITED: CDC authority operationally configured/validated/conferred by
  machine output; the warrant-vs-authority distinction presented as our
  contribution.

## CDC-CLAIM-02 — OIC admitted-meaning boundary

- INTERNAL_EVIDENCE_CEILING: `DESIGN_BASELINE + PARTIAL_EXECUTABLE_ARTIFACT`;
  `ARTIFACT_INSPECTION`; no frozen end-to-end OIC→OAM execution denominator
  (CHALLENGE_RECORD-F02B-01 preserved). Max wording (F-02B): "OIC is
  designed as the admitted-meaning representation boundary; partial
  supporting artifacts exist."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: S2 territory.
  `S2_PUBLISHED_CLAIM_PRIOR_ART_STATUS = STRONG_PARTIAL_NEIGHBORS_FOUND;
  NO_REVIEWED_PUBLICATION_OR_SPECIFICATION_DOCUMENTS_FULL_S2_TEST_SATISFACTION`.
  `VC_2_0 = STRONG_PARTIAL_EQUIVALENT` (`FORMAL_SPECIFICATION`), not PASS —
  the reviewed spec does not establish the source→candidate-represented-
  meaning→institutional-admission/refusal transition (owner S2 8-point
  operationalization controls). SCR-16 candidate deltas (non-subject-claim
  content; conservation under transformation; reliance correction on
  supersession) remain open challenge probes — secondary discriminators,
  not exhaustive necessary conditions — carried in F-05.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: OIC is designed as the boundary at which
  institutionally admitted meaning is represented, recorded and versioned;
  partial supporting artifacts exist. In the reviewed published
  claim/specification corpus, no source documents full satisfaction of the
  S2 admission test; the closest neighbor (W3C VC 2.0) is a strong partial
  equivalent. Architectural advancement claim only; end-to-end executable
  admission not demonstrated.
- PROHIBITED: OIC fully compiles/admits meaning end-to-end; runtime
  enforcement proven; "no system can admit meaning" (implementation
  landscape not systematically assessed); S2 as executable achievement.

## CDC-CLAIM-03 — OAM execution ownership without meaning authority

- INTERNAL_EVIDENCE_CEILING: `DESIGN_BASELINE + PARTIAL_ARTIFACT`;
  `ARTIFACT_INSPECTION`; denominator 0 institutionally admitted end-to-end
  missions; semantic gate BLOCKED, golden mission NOT_ADMITTED. Max wording
  (F-02B): "OAM's frozen design assigns mission execution and
  candidate-management responsibilities without assigning rule-meaning
  authority."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: runtime
  execution/authorization primitives heavily anticipated (XACML, SAB/SEB,
  CXI — `FORMAL_SPECIFICATION`/`REPORTED_ARCHITECTURE`); no novelty claim
  on the runtime side.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: OAM's frozen design assigns mission execution and
  candidate-management responsibilities without assigning rule-meaning
  authority; runtime execution primitives as such are established art and
  not claimed.
- PROHIBITED: OAM presently executes an admitted end-to-end mission;
  runtime-enforces the boundary; runtime primitives claimed as novel.

## CDC-CLAIM-04 — material candidate binding

- INTERNAL_EVIDENCE_CEILING: `DESIGN + PARTIAL_ARTIFACT`;
  `ARTIFACT_INSPECTION`; no frozen end-to-end candidate-binding execution
  denominator (CHALLENGE_RECORD-F02B-02 preserved). Max wording (F-02B):
  "The candidate model requires the enumerated evidence and identity
  bindings; partial supporting artifacts exist."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: record/provenance binding is
  established art (VC 2.0 data model, SACM, records-management lineage);
  no novelty claim on binding as such.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: The candidate model requires the enumerated
  evidence and identity bindings; partial supporting artifacts exist;
  binding-as-such is established art.
- PROHIBITED: every candidate currently bound end-to-end; any candidate
  constitutes an official finding.

## CDC-CLAIM-05 — ZTL scope: logic, not authority

- INTERNAL_EVIDENCE_CEILING: `MACHINE_CHECKED_FORMAL + MEASURED_DETECTION +
  ARCHITECTURAL/THEORETICAL_BOUNDARY`; `ARTIFACT_INSPECTION +
  RECORDED_PRIOR_MEASUREMENT`; denominators: 371 Lean theorems / 21 modules
  (frozen snapshot figure at the veraxis input pins e819dec7/56e1ff05 —
  supplement §D; never the current state) and Phase-A 50/50 across 6
  measured classes. Traceability: CHALLENGE_RECORD-F02B-03/06 raw-bundle and
  commit gaps CLOSED by the supplement (raw d5bd9e17/4d8f87bd, scored
  40712058, adjudication 9f5a9adf, member hashes); environment record
  NOT_RECORDED stands. Max wording (F-02B): "ZTL supplies machine-checked
  logical properties and recorded bounded detection evidence; it does not
  establish institutional authority."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: warrant ≠ institutional
  judgment is prior art at the conceptual level (Hohfeld — SCR-15;
  CXI enforcement-vs-policy `PARTIAL_EQUIVALENT`); the machine-checked
  empty-axiom kernel is internal evidence, not an external novelty claim.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: ZTL supplies machine-checked logical properties
  (snapshot: 371 theorems / 21 modules, empty axiom lists) and recorded
  bounded detection evidence (50/50 over 6 measured classes; 2 classes
  unmeasured; §24.5 admission defect open); it does not establish
  institutional authority — a boundary whose conceptual form is prior art
  (cited).
- PROHIBITED: Lean proves institutional legitimacy/authority/admission/
  official status/sufficiency/reliance; 371/21 cited as current ZTL state;
  Phase-A framed as pass.

## CDC-CLAIM-06 — standing as bounded relation

- INTERNAL_EVIDENCE_CEILING: `DESIGN`; `NO_EXECUTION`; denominator N/A;
  standing-currentness not operationalized. Max wording (F-02B): "The OPEN
  model defines standing as a bounded relation computed from the listed
  inputs; role alone is insufficient."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: standing as a general
  principle — novelty withdrawn (attribute/role/context authorization =
  established art, XACML et al.); the frozen bounded institutional-standing
  relation remains design-level architecture.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: The OPEN model defines institutional standing as a
  bounded, non-transitive relation computed from the listed inputs; role
  alone is insufficient. Design-level; no runtime computes or enforces it;
  authorization-as-such is established art.
- PROHIBITED: the system currently computes/enforces valid institutional
  standing; standing claimed as a novel general principle.

## CDC-CLAIM-07 — AI may / may not

- INTERNAL_EVIDENCE_CEILING: `DESIGN + OPERATING_RULE`;
  `ARTIFACT_INSPECTION`; denominator 0 frozen end-to-end enforcement runs.
  Max wording (F-02B): "The architecture prohibits machine candidates from
  silently becoming official findings."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: HITL delegation-chain and
  human-governance literature = `PARTIAL_EQUIVALENT`, adjudicated
  `HITL_ROW = CONTEXTUAL_NON_LOAD_BEARING` — not a basis for any residual
  novelty/advancement claim.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: The architecture prohibits machine candidates from
  silently becoming official findings (SEAM-2 discipline); human-in-the-loop
  governance as such is established practice and not claimed.
- PROHIBITED: runtime enforcement demonstrated; HITL used as advancement
  basis.

## CDC-CLAIM-08 — disposition record connectivity

- INTERNAL_EVIDENCE_CEILING: `DESIGN + BASELINE_REFLECTED_CLARIFICATION`;
  `ARTIFACT_INSPECTION`; PROVENANCE_CAVEAT open — original
  applicant-retained source not re-read (CHALLENGE_RECORD-F02B-04). Max
  wording (F-02B): "The frozen baseline reflects a requirement that
  disposition remain connected to the exact candidate, evidence,
  rule/version, reviewer and consequence."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: record connectivity /
  authenticity = records-management prior art; no novelty claim.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: The frozen baseline reflects the connectivity
  requirement (candidate + evidence + rule/version + reviewer + disposition
  + consequence). Provenance caveat stands until the original source is
  re-read.
- PROHIBITED: independently verified against the original applicant
  communication; framed as an executable measured property.

## CDC-CLAIM-09 — correction: history + successor; reliance NONE

- INTERNAL_EVIDENCE_CEILING: `DESIGN + PARTIAL_ARTIFACT`;
  `ARTIFACT_INSPECTION`; no frozen reliance/currentness propagation
  denominator; OAM-EXEC-CURRENTNESS-001 deferred/unauthorized. Max wording
  (F-02B): "Correction is designed to preserve predecessor history, create
  successor representation, and recalculate downstream eligibility where
  implemented."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: record history/authenticity
  preservation as a generic property = established art (ISO 15489 lineage,
  `CONCEPTUAL_PRIOR_ART`); no novelty claim.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: Correction is designed to preserve predecessor
  history, create successor representation, and recalculate downstream
  eligibility where implemented; executable reliance claim: NONE.
- PROHIBITED: reliance recalculated; rollback-resistant currentness
  operating end-to-end; correction propagation measured.

## CDC-CLAIM-10 — OPEN / supplier replacement with semantic conservation

- INTERNAL_EVIDENCE_CEILING: `DESIGN / OPEN-EXIT TARGET`; `NO_EXECUTION`;
  denominator 0 provider-replacement trials. Max wording (F-02B): "OPEN
  defines a cross-supplier preservation and semantic-conservation
  requirement for institution-controlled artifacts."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: T1 territory.
  `T1_PUBLISHED_CLAIM_PRIOR_ART_STATUS = SEMANTIC_PRESERVATION_PRIOR_ART_
  FOUND; NO_REVIEWED_PUBLICATION_OR_SPECIFICATION_DOCUMENTS_T1_TEST_
  SATISFACTION_ACROSS_HETEROGENEOUS_IMPLEMENTATION_SUBSTITUTION` (Catala,
  ISO 15489 = INDETERMINATE; SEB/CXI = FAIL by their own scope statements).
  `S2_PLUS_T1 = NO_FULL_DOCUMENTED_MATCH_FOUND_IN_REVIEWED_CORPUS`.
  Generic semantic preservation novelty withdrawn.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: OPEN defines a cross-supplier preservation and
  semantic-conservation requirement (T1) for institution-controlled
  artifacts; in the reviewed published corpus no source documents T1
  satisfaction across heterogeneous implementation substitution.
  Architectural advancement claim only; actual provider replacement is a
  separate unexecuted release test.
- PROHIBITED: supplier replacement/semantic equivalence/lossless migration
  demonstrated or guaranteed; "no working system preserves semantics"
  (implementation landscape not systematically assessed); T1 as executable
  achievement.

## CDC-CLAIM-11 — CDC-controlled infrastructure / offline target

- INTERNAL_EVIDENCE_CEILING: `DESIGN + PREREGISTERED_RELEASE_TARGET`;
  `ARTIFACT_INSPECTION`; denominator 0 frozen offline/no-egress release runs
  (CHALLENGE_RECORD-F02B-05 preserved). Max wording (F-02B): "The
  architecture and release plan target CDC-controlled infrastructure and
  bounded offline/no-egress operation."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: NOT_APPLICABLE beyond the
  global withdrawn-novelty rule (sovereign/on-prem deployment patterns are
  established practice; no novelty implied).
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: The architecture and release plan target
  CDC-controlled infrastructure and bounded offline/no-egress operation
  (preregistered release target; not yet measured).
- PROHIBITED: offline operation/sovereign deployment/production readiness/
  no-egress release gate proven; HA/DR, accreditation, hardware
  compatibility implied.

## CDC-CLAIM-12 — Phase-A adversarial record

- INTERNAL_EVIDENCE_CEILING: `MEASURED_ADVERSE_AND_INCOMPLETE`;
  `RECORDED_PRIOR_MEASUREMENT`; denominator: 6 measured classes / 50
  executed mutations / 50 detected / 0 observed misses / 2 classes
  UNMEASURED; §24.5 FAIL(1); overall `FAIL_AND_INCOMPLETE`. Traceability:
  F02B-06 raw-evidence gaps CLOSED by the supplement (bundles, scored and
  adjudication commits, member hashes); environment record for
  Phase-A/EH-3 runs = NOT_RECORDED. Max wording (F-02B): "In the frozen
  Phase-A record, 50/50 mutations across six measured classes were detected
  with zero observed misses; two classes were unmeasured, §24.5 failed, and
  the overall result was FAIL_AND_INCOMPLETE."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: adverse-evidence non-promotion
  is occupied prior/concurrent art (CXI opaque-data slots — SCR-14; SACM
  `isCounter`): **withdrawn as a claimed contribution, cite instead.** The
  Phase-A record itself is internal evidence, not a novelty claim.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: the F-02B max wording verbatim (above), plus:
  adverse-evidence non-promotion as a principle is established art and not
  claimed; the experiment's governance value is that defects were preserved
  as non-measurements rather than repaired or converted.
- PROHIBITED: Phase-A passed; all eight classes measured; 100% recall;
  fail-closed or generalized robustness proven; adverse-evidence
  non-promotion claimed as contribution.

## CDC-CLAIM-13 — currentness: design present, execution blocked

- INTERNAL_EVIDENCE_CEILING: `DESIGN_PRESENT / EXECUTABLE_BLOCKED`;
  `BLOCKED_BEFORE_EXECUTION`; denominator 0 executable cases, 5 classes
  `BLOCKED_CASE_CONSTRUCTION`, reason
  `EXECUTABLE_CURRENTNESS_RELIANCE_SUBSTRATE_ABSENT`; no detection score, no
  containment score, no execution, PASS=FALSE, FAIL=FALSE,
  MEASUREMENT=FALSE. Traceability: F02B-07 package gap CLOSED by the
  supplement (commit 937fe51e, 4 members byte-bound, prereg v0.2 61772f78).
  Max wording (F-02B): "Currentness/reliance semantics are represented in
  the architecture, but the frozen Phase-A substrate could not construct
  executable cases; denominator was zero."
- EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING: runtime authorization
  currentness = established art (CXI policy epochs/trusted snapshots,
  runtime `FUNCTIONAL_EQUIVALENT`); novelty withdrawn. Institutional
  currentness (historical authority invalidation, downstream reliance
  correction) is design-level in our architecture and explicitly out of
  scope in the reviewed neighbor — recorded as boundary, not as
  achievement.
- EXTERNAL_VERIFIED_SYSTEM_CAPABILITY: `NOT_ASSESSED`.
- FINAL_PERMITTED_CLAIM: the F-02B max wording verbatim (above); runtime
  currentness as such is established art and not claimed; institutional
  currentness remains a design requirement with zero executable
  denominator.
- PROHIBITED: currentness passed/failed/measured/executed; detection or
  containment performance stated; runtime currentness claimed as novel.

---

## Closure state

All 13 final permitted claims are at or below both applicable ceilings; no
averaging performed; every measured figure carries its denominator; BLOCKED
and UNMEASURED preserved; disagreements between tracks: none arose at claim
level (the tracks answer different questions and were not merged) — the one
cross-track tension (F-03D's `VC 2.0 partial PASS on S2`) is resolved by the
owner's controlling adjudication (`STRONG_PARTIAL_EQUIVALENT`) and preserved
in F-05 as SCR-16 open work. `SUBMISSION-PERMITTED-CLAIMS` is NOT generated
here (owner stop condition — F-04/F-05 go to owner adjudication first).
