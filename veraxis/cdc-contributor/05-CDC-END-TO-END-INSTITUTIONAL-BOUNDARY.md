# 05 — CDC End-to-End Institutional Boundary (Part D)

Contributor artifact — standing: `CORE_RESEARCH_AND_ARCHITECTURE_CONTRIBUTOR`. Feeds submission
sections: 3, 6, 7, 10, 11, 12, 13. Ceilings: `GATE_SAR_05 = NOT_CLOSED`,
`SEMANTIC_IMPLEMENTATION_GATE = BLOCKED`.

**Controlling operational interpretation:** auditor-support, not autonomous auditor. **Global
invariant across the whole path:** *nowhere does a machine-generated candidate automatically become
an official CDC finding.* Each of the five CDC-shaped outputs (orientation note, provisional report,
final report, findings summary, transmittal letter) remains a **draft** until CDC edits, validates,
signs, circulates, and forms the official record.

## The controlling path

```
authoritative / public institutional source
  → OIC source anchoring
  → candidate normative meaning
  → institutional admission / version
  → Open Control projection
  → OAM mission import
  → evidence intake
  → PMP / dossier reconciliation
  → deterministic control / bounded signal
  → admitted propositions
  → ZTL logical warrant
  → evidence-bound candidate
  → reviewer standing + authority scope
  → explicit disposition
  → eligible statement / five editable deliverable drafts
  → institutional issuance / sign-off [CDC-owned]
  → controlled institutional handoff / receipt where applicable
  → relied-upon state where applicable
  → correction / replay where applicable
```

For the current demonstrator, **institutional issuance / sign-off and relied-upon state are an
architectural / institution-owned boundary, not an executed capability** (Layers 7–8; CDC-CLAIM-09/13).
This executive ordering is the same ontology as 01's top chain (no stage added or lost that changes
authority semantics). The one binding invariant on ordering: **reliance cannot precede whatever
institutional act / receipt the applicable process requires for reliance**; exact CDC official-record
ordering is deferred to CDC's own process and not over-specified here.

A CDC evaluator should be able to trace any single deliverable statement backward along this path to
an authoritative source, and forward from that source without any layer silently gaining authority it
was not given.

## Three mandatory seams

### SEAM-1 — OIC → OAM
- **Question:** did institutional meaning survive import **without OAM silently reinterpreting it**?
- **Permitted:** OAM may reject the import or request recompilation from OIC.
- **Never silently crosses:** a *locally repaired* or *model-reinterpreted* institutional meaning. OAM
  may not fix meaning locally.
- **Failure mode — shadow interpretation:** OAM encounters an ambiguous/conflicting rule and quietly
  resolves it (via model inference, defaulting, or a local patch) instead of bouncing it back to OIC
  for admitted recompilation. Detection: any admitted proposition whose meaning does not resolve to an
  OIC admission record.

### SEAM-2 — ZTL → institutional disposition
- **Question:** did logical warrant remain logical warrant, or was it **silently promoted into
  institutional judgment**?
- **Rule:** `T / F / Z / CONTRADICTION / CANNOT` carry **no** reviewer authority. A perfectly correct
  proof over admitted premises is still not an official CDC finding.
- **Never silently crosses:** a warrant treated as a decision; an `EARNED` verdict rendered as an
  official finding.
- **Failure mode — auto-promotion / authority inheritance:** a CLWR is mechanically inferred, copied, or
  auto-promoted into a disposition/finding **without a separately recorded authorized reviewer act**. A
  reviewer legitimately **agreeing** with the warrant is fine — *same conclusion is permitted; automatic
  authority inheritance is prohibited* (authority comes from reviewer standing, not from the verdict).
  Detection: any eligible statement not traceable to a **separately recorded disposition attributable
  to an actor in valid standing** (SEAM-3) — i.e. a disposition mechanically inherited from the CLWR
  rather than a separate authorized institutional act. (Note: "separate authorized act", **not**
  "independent reviewer" — independence is a distinct institutional standing; a CDC controller in valid
  standing may legitimately agree with the warrant.)

### SEAM-3 — reviewer → deliverable
- **Question:** was the consequential transition based on **authenticated identity**, or on **valid
  institutional standing** for this action / object / context?
- **Rule:** identity is necessary but **insufficient**. Required: standing, scope, authority basis,
  disposition, and connection to the exact candidate / evidence / rule/version.
- **Never silently crosses:** a disposition grounded on login/identity alone; a disposition whose
  standing is expired, out of scope, or not current for this object.
- **Failure mode — login-equals-authority:** an authenticated user's action is treated as an
  institutional act without the **canonical standing stamp defined in 02**. Detection: any disposition
  record lacking that canonical standing stamp, current at the moment of the act. (02 is the single
  semantic source for the standing object; this file does not define a separate tuple.)

## What must be observable at handoff (acceptance)

For each of the five deliverable drafts, the CDC evaluator can confirm:
1. every material statement traces back through SEAM-1/2/3 to an authoritative source;
2. no statement crossed a seam silently (each crossing has its record: admission, warrant, disposition);
3. the deliverable is a **draft** — official status is formed only by CDC action;
4. corrections, if any, created successor states without rewriting history, and (by design)
   invalidate/recalculate downstream **eligibility**; institutional **reliance / currentness propagation
   remains design-level until `OAM-EXEC-CURRENTNESS-001`** (CDC-CLAIM-13).

## Honesty boundary
This is the **design-level** end-to-end boundary bounded by TDD-OAM-001 v1.1 / SAR-OAM-001 v1.0. It
states what the architecture requires and forbids at each seam. Where a seam's enforcement is
procedural/design rather than executed-and-measured, the submission marks it design-level; it does not
present the boundary as a fully executed runtime. `SEMANTIC_IMPLEMENTATION_GATE` remains `BLOCKED`; no
narrative jumps that gate.
