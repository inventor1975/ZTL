# 01 — CDC Institutional Architecture Narrative (Part A)

Contributor artifact — standing: `CORE_RESEARCH_AND_ARCHITECTURE_CONTRIBUTOR` (not independent review).
Governing baseline: TDD-OAM-001 v1.1 (primary) bounded by SAR-OAM-001 v1.0. Operating ceilings:
`GATE_SAR_05 = NOT_CLOSED`, `SEMANTIC_IMPLEMENTATION_GATE = BLOCKED`. No claim of institutional
admission, runtime execution authority, or publication authority follows from this document.
Feeds submission sections: 1, 3, 6, 8, 10, 11, 13.

**Rev 4 (2026-08-09) — final wording normalization; `01 = CONTRIBUTOR_FREEZE_READY`.** Normalizations
(no architecture change, no semantic-model change): source ↔ authoritative *meaning* separated (source
is a basis from which meaning may be represented and admitted, not already-admitted meaning); source
authority (recognized issuer) separated from CDC mission admission/use/disposition authority; distinct
state transition separated from "separate human authorization event" (authority is never inherited from
a predecessor, but not every transition is a human act); Layer 8 split into architecture-requires vs
executable-reference-establishes, `recalculated reliance` removed from current output; Layer 2 OIC output
restated as a recorded representation of *institutionally admitted* meaning (the institution admits; OIC
records/binds/versions/exposes).

**Frame.** The system makes an institutional process *computational* without moving where meaning,
authority, and legitimacy live. Each layer has one job and an explicit authority boundary.

> **The machine never becomes the source of institutional meaning or authority; those remain externally
> grounded in recognized institutions, issuers, and authorized institutional actors. Within the CDC
> mission, CDC retains the authority over admission/use, reviewer standing, disposition, sign-off, and
> official record formation assigned to it.**

```
authoritative source
  → OIC
  → Open Control Profile
  → OAM
  → ZTL logical warrant
  → human institutional disposition
  → eligible statement / deliverable draft
  → institutional issuance / sign-off [institution-owned]
  → relied-upon state where applicable
  → correction / replay
```

*Issuance / reliance = an architectural / institution-owned boundary, not a current demonstrator
capability. This executive chain and the operational path in 05 §controlling-path express the same
ontology — no stage added or lost that changes authority semantics.*

---

### Layer 1 — Authoritative source (externally grounded normative basis)
- **ESTABLISHES:** authoritative source material and the externally grounded normative basis from which institutional meaning may be **represented and admitted**.
- **DOES_NOT_ESTABLISH:** it does not itself create institutional authority, admission, or already-determined meaning — a source document does not admit its own meaning. Between source and admitted meaning there is a representation / interpretation / admission boundary (ambiguity, conflict, candidate meaning, versioning, `Z`/unresolved). Nothing is delegated to the machine.
- **INPUT:** statutes, regulations, decrees, institutional rules, mandates, approved methodologies, other recognized normative instruments.
- **OUTPUT:** authoritative source material — a normative basis *to be* represented and admitted, not yet admitted meaning.
- **AUTHORITY_BOUNDARY:** authority of the normative source remains attributable to its **recognized issuer / competent authority** (which may be external to CDC — e.g. a statute, regulation, ministerial rule, procurement law). Authority to **admit, apply, disposition, issue, or rely** within the CDC mission is separately held and exercised by the institution and its authorized actors. (Where CDC is both issuer and mission authority, the roles coincide; the model does not assume it.)

### Layer 2 — OIC (source anchoring, candidate meaning, admission)
- **ESTABLISHES:** content-anchored references (R-15); a *candidate* representation of stipulated meaning; an admission record; explicit exposure of ambiguity/conflict. Admission enforces the Z-discipline — nothing enters evaluation without an explicit epistemic state; no truth-value without provenance.
- **DOES_NOT_ESTABLISH:** originates no meaning, authority, or warrant. **The institution admits; OIC records, binds, preserves, versions, and exposes the result computationally.** OIC owns the admission interface/record and the representation discipline; the OIC software itself does not originate institutional authority.
- **INPUT:** authoritative source material.
- **OUTPUT:** a recorded representation of **institutionally admitted meaning** + versioned Open Control projections.
- **AUTHORITY_BOUNDARY:** OIC is the admitted-meaning boundary. Downstream layers consume *imported admitted meaning*; they may not silently reinterpret it.

### Layer 3 — Open Control Profile
- **ESTABLISHES:** the declared, deterministic set of controls the mission may exercise.
- **DOES_NOT_ESTABLISH:** no authority beyond what the institution declared; not a policy interpretation.
- **INPUT:** admitted meaning.
- **OUTPUT:** CDC-shaped, versioned control projections.
- **AUTHORITY_BOUNDARY:** controls are bounded by admitted meaning; the profile cannot widen its own authority.

### Layer 4 — OAM (evidence-bound mission execution)
- **ESTABLISHES:** mission scope, population, evidence intake, control execution, **evidence-bound audit candidates**, review state, correction/replay, deliverable assembly. Every material result carries replayable evidence.
- **DOES_NOT_ESTABLISH:** what the institutional rule *means*; creates no institutional finding — candidates, not decisions.
- **INPUT:** imported admitted meaning + control projections + evidence.
- **OUTPUT:** evidence-bound candidates + reviewable mission state.
- **AUTHORITY_BOUNDARY:** OAM executes mission logic; it does not own meaning. It may reject or request recompilation from OIC; it may not repair institutional meaning locally.

### Layer 5 — ZTL (logical warrant)
- **ESTABLISHES:** a contemporaneous logical-warrant record (CLWR) — verdict + grade + **named weak links** — over a fixed marking. Default-deny: unverified is not truth.
- **DOES_NOT_ESTABLISH:** source authority, institutional admission, evidence sufficiency, reviewer authority, official-finding status, or institutional reliance. A CLWR alone effects no reliance-bearing transition (R-10). **Logical warrant ≠ institutional warrant.**
- **INPUT:** admitted propositions.
- **OUTPUT:** a warrant record for each candidate.
- **AUTHORITY_BOUNDARY:** ZTL answers only *does this follow from admitted grounds under the represented logic?* — never *does the institution rely on it?*

### Layer 6 — Human reviewer disposition (in recorded authority scope)
- **ESTABLISHES:** an explicit institutional disposition / judgment by an actor whose **standing and authority scope are established for the exact object**.
- **DOES_NOT_ESTABLISH:** issuance, officiality, or downstream reliance merely by virtue of reviewer action. Hold the **four transitions** distinct: **logical warrant** (the CLWR) → **institutional judgment / disposition** → **issuance / official act** → **reliance**. Institutional warrant is *wider* than the reviewer decision (authority + admissibility + sufficiency + applicable context); the disposition is an authorized judgment **within** those conditions, not their creation from nothing. Nothing on identity alone.
- **INPUT:** evidence-bound candidate + its CLWR.
- **OUTPUT:** an explicit, recorded disposition, tied to the exact candidate/evidence/rule (see 02).
- **AUTHORITY_BOUNDARY:** logical warrant **ends before** this transition; human disposition supplies institutional judgment, but **reliance requires the separate institution-owned issuance / sign-off transition** (Layer 7).

### Layer 7 — Bounded institutional transition / deliverable
- **ESTABLISHES:** **eligibility** — an eligible statement and editable CDC-shaped deliverable drafts (orientation note, provisional report, final report, findings summary, transmittal letter).
- **DOES_NOT_ESTABLISH:** officiality or issuance. No machine-generated candidate auto-becomes an official finding; drafts remain drafts. **Institutional issuance / sign-off is a separate authorized institutional act that the current reference demonstrator does not itself perform.**
- **INPUT:** authorized dispositions.
- **OUTPUT:** eligible statements + deliverable drafts.
- **AUTHORITY_BOUNDARY:** the progression is explicit — **human disposition → eligible statement / draft → institutional issuance / sign-off → relied-upon state.** General rule: *each arrow is a distinct institutional or system state transition with explicit admission conditions; a transition does not inherit authority merely from the validity of its predecessor.* Not every transition is a separate human act — some (e.g. disposition→eligibility, eligibility→draft-assembly) may be deterministic/assisted once conditions are satisfied. But transitions that create **institutional judgment, officiality, issuance, or reliance** require the separately specified institutional authority appropriate to that consequence. Example: a disposition may automatically set `ELIGIBLE_FOR_DRAFT=TRUE`; it may not set `OFFICIALLY_ISSUED=TRUE`, and still less `RELIED_UPON=TRUE`.

> **CDC claim ceiling (Layers 6–8).** The reference system can show *evidence-bound, logically warranted, human-dispositioned material, eligible for drafts.* It does **not** claim that the current CDC demonstrator itself performs official CDC issuance or establishes institutional reliance. *Evaluation establishes the property; issuance creates the reliance.*

### Layer 8 — Correction / replay / currentness / reliance

**What the architecture requires:** corrections create successor records; predecessor history remains
preserved (R-08/R-25); affected downstream **eligibility** must be invalidated/recalculated; a
superseded/revoked issuance must not continue supporting reliance; currentness must distinguish a
historically valid state from the presently authoritative state.

**What the current executable reference establishes:** correction/replay/history preservation only to
the extent actually implemented; downstream **eligibility** may be recalculated where implemented;
**institutional currentness/reliance propagation remains design-level and is not claimed as end-to-end
executable.**

- **INPUT:** a correction/withdrawal event.
- **OUTPUT:** a successor state representation + recalculated downstream **eligibility where implemented**.
- **AUTHORITY_BOUNDARY:** correction changes institutional state only through recorded acts, never by silent overwrite. **Institutional currentness and reliance propagation remain architectural requirements until the corresponding executable substrate is implemented and evaluated** (`OAM-EXEC-CURRENTNESS-001`; executable currentness substrate currently absent — see 03 and CDC-CLAIM-13).

---

**Two boundaries the evaluator should carry away.**
1. **Four distinct transitions, never collapsed:** logical warrant (CLWR) → institutional judgment / disposition → issuance / official act → reliance. A distinct state transition never inherits authority from its predecessor; transitions that create judgment, officiality, issuance, or reliance require their own institutional authority. *Evaluation establishes the property; issuance creates the reliance* (D1/D2).
2. **The operator does not own institutional meaning.** The operator runs implementation machinery; institutional meaning representations, evidence, dispositions, findings, correction and reliance history remain institution-controlled; **institutional authority remains attributable to the competent institution/issuer and is never acquired by the operator through custody of those records.** **OPEN defines a cross-supplier preservation *requirement* (a portability property, not yet a measured guarantee): changing a conformant model, vendor or operator must not require the institution to surrender or reconstruct its representations of institutionally admitted meaning or its legitimacy history; institutional meaning must remain semantically conserved. Actual provider-replacement performance remains a separate release test** (Open Exit — see 03).
