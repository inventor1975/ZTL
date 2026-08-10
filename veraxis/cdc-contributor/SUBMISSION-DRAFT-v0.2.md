# CDC Submission Draft v0.2 — OIC–ZTL–OAM Institutional Architecture and Evidence Package

Status: DRAFT_FOR_OWNER_REVIEW. Supersedes v0.1 (mechanical reflow into the
owner-controlled 14-section submission architecture + five owner ceiling
corrections; no new claims). Assembled strictly from the owner-approved
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
owner review, strippable at final typesetting. Sections marked
`OWNER_INPUT_REQUIRED` have no content derivable from the permitted-claims
surface and are left for owner-side material; nothing was invented to fill
them.

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

`OWNER_INPUT_REQUIRED` — challenge-fit and customer-outcome statements are
not derivable from the permitted-claims surface. Permitted framing available
for this section: the staged-proposal framing of §1 and the boundary
commitments [PC-01, PC-02, PC-07]; all outcome language must remain within
the Section 13 claim boundaries.

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

Impact statements: `OWNER_INPUT_REQUIRED` (not derivable from the
permitted-claims surface). The measurement record established to date:

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

`OWNER_INPUT_REQUIRED` — no scaling claims are derivable from the
permitted-claims surface; any scaling language must remain design-level and
within the Section 13 boundaries.

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

Further mitigation content: `OWNER_INPUT_REQUIRED`.

## 10. Team, Governance and Delivery Responsibilities

Team and delivery-responsibility content: `OWNER_INPUT_REQUIRED`.
Governance surface derivable from the permitted claims: institutional
authority over adoption, review, reviewer standing, disposition, sign-off
and official record formation remains with the CDC [PC-01]; a separately
recorded, authorized human act stands between machine candidate and
official record [PC-07]; public claims about the system are themselves
governed by the owner-adjudicated claim ceiling (Section 13).

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

`OWNER_INPUT_REQUIRED` — the requirement-coverage mapping binds owner-side
challenge materials to this package; every coverage statement must remain
at or below the Section 13 claim boundaries.

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

`TO_BE_COMPLETED_AT_TYPESETTING` — to include: frozen artifacts 01–05
(freeze commit `973f9eba…`); the F reconciliation record (commit
`4a388e26…`); SUBMISSION-PERMITTED-CLAIMS (commit `2f3ec476…`); the ZTL
corpus at the frozen evidence snapshot (veraxis input pins); prior-art
citations named in Sections 3 and 13 (jurisprudential warrant/authority
formalization; W3C VC 2.0; further items per owner reference list).
