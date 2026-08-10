# 04 — CDC Claims → Evidence → Ceiling Matrix (Part B)

Contributor artifact — standing: `CORE_RESEARCH_AND_ARCHITECTURE_CONTRIBUTOR`. Governing baseline:
TDD-OAM-001 v1.1 bounded by SAR-OAM-001 v1.0. Ceilings: `GATE_SAR_05 = NOT_CLOSED`,
`SEMANTIC_IMPLEMENTATION_GATE = BLOCKED`.

**Discipline:** design-level marked as design; measured carries its denominator; blocked/unmeasured
is never rendered as pass or fail. **Acceptance property (R-CDC-05):** repository, demonstrator,
benchmark, offline package and narrative must make the **same bounded proposition** observable from
different directions — one maturity story, not five.

Columns per claim: `claim` · `evidence_class` · `supporting_artifact` · `measured_denominator` ·
`claim_ceiling` · `known_limitation` · `submission_sections` · `freeze_status`.

---

### CDC-CLAIM-01 — Institutional authority: source authority vs mission authority
- **claim:** authority of external legal/regulatory sources remains **attributable to their recognized issuers / competent authorities**; **CDC retains institutional authority over mission adoption/use, review, reviewer standing, institutional disposition, sign-off, and official record formation**. Machine output never acquires either authority by being produced.
- **evidence_class:** DESIGN + EXTERNALLY_SOURCED_CHALLENGE_BOUNDARY
- **supporting_artifact:** TDD-OAM-001 v1.1; SAR-OAM-001 v1.0; architecture narrative (01); challenge clarification boundary
- **measured_denominator:** N/A (design)
- **claim_ceiling:** architecture preserves the boundary; actual CDC authority configuration requires PoC institutional inputs
- **known_limitation:** no pilot authority configuration / pilot population yet
- **submission_sections:** 1, 6, 10, 13
- **freeze_status:** DESIGN-STABLE (baseline-bound)

### CDC-CLAIM-02 — OIC is the admitted-meaning boundary
- **claim:** OIC owns source anchoring, candidate normative meaning, ambiguity/conflict exposure, the **admission interface/record and representation discipline**, and versioned Open Control projections; the institution admits, OIC records/binds/versions; OIC software does not originate institutional authority; OAM must not silently reinterpret institutional meaning.
- **evidence_class:** DESIGN_BASELINE + OIC artifacts
- **supporting_artifact:** OIC design; R-15 content-anchoring; admission gate (Z-discipline); 01 §Layer 2
- **measured_denominator:** N/A
- **claim_ceiling:** design boundary; OIC→OAM = imported admitted meaning, not model reinterpretation
- **known_limitation:** executable OIC compiler maturity is design/partial, not fully measured
- **submission_sections:** 3, 13
- **freeze_status:** DESIGN-STABLE

### CDC-CLAIM-03 — OAM executes mission logic, does not create meaning
- **claim:** OAM owns scope, population, evidence, control execution, candidate findings, review state, correction/replay, deliverable assembly; it does not decide what the institutional rule means.
- **evidence_class:** DESIGN_BASELINE
- **supporting_artifact:** TDD-OAM-001 v1.1; 01 §Layer 4
- **measured_denominator:** N/A
- **claim_ceiling:** the distinction must survive every diagram and sentence in the submission
- **known_limitation:** design-level separation; runtime not institutionally admitted (gate blocked)
- **submission_sections:** 3, 13
- **freeze_status:** DESIGN-STABLE

### CDC-CLAIM-04 — Evidence-bound candidate
- **claim:** each material candidate binds source, exact anchor, rule/version, expected condition, observed fact, uncertainty/contrary evidence, warrant state, reviewer, disposition, artifact identity/digest.
- **evidence_class:** DESIGN + PARTIAL_ARTIFACT
- **supporting_artifact:** candidate binding schema; OAM evidence model
- **measured_denominator:** N/A (binding schema design-level; end-to-end executable binding not fully measured)
- **claim_ceiling:** candidate audit work, not official finding
- **known_limitation:** full end-to-end executable binding not yet demonstrated/measured
- **submission_sections:** 3, 7, 13
- **freeze_status:** DESIGN + PARTIAL

### CDC-CLAIM-05 — ZTL establishes logical warrant, not institutional authority
- **claim:** ZTL establishes whether a conclusion follows from admitted grounds under the represented logic; it does NOT by itself establish source authority, institutional admission, evidence sufficiency, reviewer authority, official-finding status, or institutional reliance.
- **evidence_class (split by load):** ZTL logical kernel / relevant theorem properties → `MACHINE_CHECKED_FORMAL` (Lean 4, empty axiom lists); Phase-A mutation detection → `MEASURED` (denominator 50/50 across six measured classes); *logical warrant ≠ institutional authority* → `ARCHITECTURAL / THEORETICAL BOUNDARY` (not statistical, and **not** a Lean-proved institutional proposition)
- **supporting_artifact:** ZTL kernel; CLWR (R-06/07/15); Phase-A detection results
- **measured_denominator:** 50/50 across six measured classes (detection only)
- **claim_ceiling:** logical warrant only; the warrant→authority boundary is architectural/theoretical and load-bearing — **do not read Lean formalization as formalizing institutional legitimacy**
- **known_limitation:** Lean formalizes the *logic*, not institutional legitimacy; the authority separation is architectural, enforced procedurally
- **submission_sections:** 3, 13
- **freeze_status:** FORMAL-STABLE + MEASURED(detection)

### CDC-CLAIM-06 — Human authority is standing, not login
- **claim:** identity answers "who"; **role is one input into standing.** Institutional entitlement to perform this consequential transition on this object now depends on actor/identity + role + externally grounded authority_basis + scope + object + action + permitted_consequence + effective_time + currentness + separation_constraints, yielding the bounded standing under which the disposition may occur (canonical model in 02: `ROLE ≠ STANDING`; `ROLE ∈ INPUTS_TO_STANDING`).
- **evidence_class:** DESIGN (OPEN standing model)
- **supporting_artifact:** 02 standing model
- **measured_denominator:** N/A
- **claim_ceiling:** standing model is design-level; executable standing-currentness not operationalized
- **known_limitation:** currentness runtime deferred (see CDC-CLAIM-13)
- **submission_sections:** 6, 10, 13
- **freeze_status:** DESIGN-STABLE

### CDC-CLAIM-07 — Machine candidate cannot silently become official finding
- **claim:** AI may read approved material, execute approved tests, compare evidence, surface candidate issues, recommend next permissible step, assist drafting; AI may NOT declare official findings, finalize official documents, create official records, sanction/refer/accuse externally, or substitute for a required institutional signatory.
- **evidence_class:** DESIGN + OPERATING RULE
- **supporting_artifact:** 01 §Layers 6–7; disposition boundary
- **measured_denominator:** N/A
- **claim_ceiling:** **required / prohibited by architecture** — a design invariant / operating rule, **not** a runtime-enforced capability
- **known_limitation:** where an enforcement path actually exists and is measured, F raises the evidence class; until then, design invariant only
- **submission_sections:** 3, 7, 13
- **freeze_status:** DESIGN-STABLE

### CDC-CLAIM-08 — Human disposition is artifact-bound
- **claim:** a conventional approval record alone is insufficient; the record must stay connected to exact candidate + evidence + rule/version + reviewer + disposition + downstream consequence.
- **evidence_class:** DESIGN + **BASELINE_REFLECTED_CLARIFICATION** (not an independently re-verified quotation)
- **supporting_artifact:** governing baseline; disposition record schema
- **measured_denominator:** N/A
- **claim_ceiling:** baseline-reflected clarification
- **known_limitation:** **PROVENANCE CAVEAT — the original applicant-retained email was not re-read through the connector; treat as baseline-reflected, not a newly independently verified quotation.** (Flag for F to re-verify against source when available.)
- **submission_sections:** 7, 13
- **freeze_status:** DESIGN + PROVENANCE-CAVEAT

### CDC-CLAIM-09 — Correction preserves history
- **claim:** correction preserves predecessor history and creates a successor state. **Current capability claim:** history preserved + successor representation + downstream **eligibility** recalculated where implemented; a new deliverable can be regenerated. **Architectural requirement (not current executable):** reliance/currentness propagation. **Executable reliance claim: NONE.**
- **evidence_class:** DESIGN
- **supporting_artifact:** R-08/R-25; 01 §Layer 8
- **measured_denominator:** N/A
- **claim_ceiling:** correction/replay preserves predecessor history and is *designed* to invalidate/recalculate affected downstream **eligibility**; **institutional reliance/currentness propagation remains design-level until `OAM-EXEC-CURRENTNESS-001`** — do NOT claim rollback-resistant institutional currentness is executable end-to-end
- **known_limitation:** executable currentness ABSENT (CDC-CLAIM-13); avoid `recalculated reliance` in any current-capability statement
- **submission_sections:** 3, 13
- **freeze_status:** DESIGN-STABLE

### CDC-CLAIM-10 — OPEN supplier replacement without legitimacy loss
- **claim:** **OPEN requires** the architecture to permit replacement of model, provider, database, UI, adapter, deployment operator, and ultimately supplier **without requiring** the institution to surrender or reconstruct its admitted control representations, representations of institutionally admitted meaning, evidence, dispositions, mission history, correction lineage, reliance records, or other institution-controlled portable artifacts. **Institutional meaning must be semantically conserved across the transition;** actual provider-replacement performance remains a separate release test.
- **evidence_class:** DESIGN (Open Exit)
- **supporting_artifact:** 03; portability/Open-Exit properties
- **measured_denominator:** N/A
- **claim_ceiling:** OPEN cross-supplier **preservation requirement / portability property** — institution-controlled admitted-meaning representations, evidence, dispositions, and history remain portable across conformant implementations while institutional meaning is semantically conserved; **not a measured guarantee**
- **known_limitation:** actual provider-replacement performance is a separate release test; no executed live supplier-replacement test yet
- **submission_sections:** 8, 11, 13
- **freeze_status:** DESIGN-STABLE

### CDC-CLAIM-11 — Local / sovereign deployment architecture
- **claim:** tools come to CDC; CDC need not become a tenant of a Veraxis-controlled cloud; normal PoC operation is designed around CDC-approved infrastructure and CDC-controlled sources/roles/rules/evidence.
- **evidence_class:** `DESIGN + PREREGISTERED_RELEASE_TARGET` (after a frozen no-egress/offline run, F may change to `MEASURED_RELEASE_GATE` if it actually passes — not called a proof until observed)
- **supporting_artifact:** R-CDC-04 Offline Evaluation Package
- **measured_denominator:** N/A (offline package is a TARGET until frozen/measured)
- **claim_ceiling:** architecture + preregistered offline / no-egress release **target**; **no offline proof is claimed until the frozen release test is executed and observed** — NOT CDC production deployment, certified sovereign environment, exact hardware compatibility, production HA/DR, or operational accreditation
- **known_limitation:** those remain PoC/environment work
- **submission_sections:** 6, 11, 13
- **freeze_status:** DESIGN + TARGET(offline)

### CDC-CLAIM-12 — Phase-A empirical evidence
- **claim:** six measured adversarial classes; 50/50 mutations detected; 0 observed misses among measured classes; two adapter/admission classes UNMEASURED; §24.5 provenance/admission invariant FAIL; therefore `PHASE_A_v0.1 = FAIL_AND_INCOMPLETE`.
- **evidence_class:** MEASURED
- **supporting_artifact:** Phase-A result bundle; EFP (commit 673a8854); owner adjudication
- **measured_denominator:** 6 measured classes, 50/50 detected, 0 misses; 2 adapter/admission classes = UNMEASURED; §24.5 = FAIL
- **claim_ceiling:** measured detection on six classes — **must never be stated as "benchmark passed"**; the strong story is that adverse and incomplete results were preserved
- **known_limitation:** two classes unmeasured; §24.5 admission/provenance defect open
- **submission_sections:** 5, 8, 13
- **freeze_status:** FROZEN (measured)

### CDC-CLAIM-13 — Currentness
- **claim:** the architecture requires currentness/reliance semantics; the existing frozen Phase-A executable substrate does not yet operationalize them.
- **evidence_class:** DESIGN (present) / EXECUTABLE (absent) — BLOCKED
- **supporting_artifact:** currentness preregistration v0.2; construction-blocked package (commit 937fe51e)
- **measured_denominator:** executable denominator = 0; five case classes = BLOCKED_CASE_CONSTRUCTION; no Detection/Containment score; no execution
- **claim_ceiling:** `DESIGN_REPRESENTABILITY = PRESENT`, `EXECUTABLE_REPRESENTABILITY_IN_FROZEN_PHASE_A_SUBSTRATE = ABSENT` — **not a failure, not a pass, not a measurement**
- **known_limitation:** `OAM-EXEC-CURRENTNESS-001` deferred / not authorized
- **submission_sections:** 8, 13
- **freeze_status:** FROZEN (blocked; denominator 0)

---

**Cross-cutting notes for F (evidence-aware reconciliation, when benchmark/release freezes):**
- Re-verify CDC-CLAIM-08 against the original applicant source once the connector is available.
- R-CDC-03 (OAM-Bench CDC S1) has its **own** denominator and evidence classes — do not merge it with
  the Phase-A research experiment (CDC-CLAIM-12); where CDC S1 is not yet frozen/measured, mark
  `TARGET / PREREGISTERED`, not achieved result.
- Every design-level claim (01–11 except the measured/blocked 12–13) must read consistently across all
  five R-CDC objects and all 14 submission sections — one bounded proposition, many viewpoints.
