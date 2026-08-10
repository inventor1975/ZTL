# 03 — Advancement Beyond the State of the Art (Part E)

Contributor artifact — standing: `CORE_RESEARCH_AND_ARCHITECTURE_CONTRIBUTOR`. Feeds submission
sections: 1, 3, 8, 11, 13. Operating ceilings apply: `GATE_SAR_05 = NOT_CLOSED`,
`SEMANTIC_IMPLEMENTATION_GATE = BLOCKED`.

**`03_STATUS = CONTRIBUTOR_FREEZE_READY_PENDING_EXTERNAL_SOTA_SUBSTANTIATION`.** The advancement claim
and its honesty boundary are frozen; the comparative table is *architectural positioning* and requires
external state-of-the-art substantiation before any final public prior-art claim.

## The advancement, stated precisely

> **Representations of admitted institutional meaning, authority basis and standing, evidence, and
> human dispositions remain separable, inspectable, and portable as the institutional process becomes
> computational, while institutional authority itself remains externally grounded and non-transferable
> by implication.**

OPEN adds a cross-supplier **preservation requirement** (a portability property, not yet a measured
guarantee):

> **Changing a conformant model, vendor, or operator must not require the institution to surrender or
> reconstruct its representations of institutionally admitted meaning or its legitimacy history.
> Admitted-meaning representations, authority-basis and standing records, evidence, dispositions,
> findings, corrections, and reliance history are the portable institutional records; institutional
> meaning itself must remain semantically conserved, while institutional authority remains externally
> grounded and non-transferable by implication. Actual provider-replacement performance remains a
> separate release test.**

## What each category does not establish by itself (comparative positioning)

> `ARCHITECTURAL_COMPARATIVE_POSITIONING — EXTERNAL SOTA SUBSTANTIATION REQUIRED BEFORE FINAL PUBLIC CLAIM.`

Each category below names a *tool*; particular implementations may realize *parts* of the property set.
The claim is **not** that these cannot do X — it is what each **does not establish by itself**, and what
OPEN requires as a **combined institutional property**:

| Category | By itself it does NOT establish… |
|---|---|
| **RAG / traceable RAG** | the provenance, institutional admission, and semantic conservation of *institutional meaning* across the source→executable transformation; nor portable preservation of authority-basis/standing records, evidence, and dispositions without making institutional authority itself transferable. |
| **Policy-as-code** | that its encoded, interpreted rule preserves the provenance, institutional admission, and semantic conservation of the source→executable transformation. |
| **Workflow approval** | that the approving actor held **valid standing** for this exact object/consequence at the time of disposition. |
| **Human-in-the-loop** | which standing entitles *this* actor to *this* consequence; placement in the pipeline is not authority. |
| **Conventional audit trail** | the *separation* of meaning / authority / evidence / disposition, nor portability of the record across suppliers. |
| **Runtime guardrails** | that representations of institutionally admitted meaning, authority-basis/standing records, evidence, dispositions, and legitimacy history remain institution-controlled and portable across conformant suppliers while institutional meaning is semantically conserved and authority and legitimacy themselves remain externally grounded. |

## Why the claim survives three readers at once

- **Technical:** a separation architecture — content-anchored evidence, a default-deny logical kernel
  (machine-checked), replayable records; each layer's claim is bounded and independently checkable.
- **Governmental / audit:** it answers the questions a public auditor actually asks — *prove no
  machine output became an official finding without an authorized human in recorded standing*, and
  *show what must remain institution-owned across supplier replacement and make that property
  independently testable* (whether a given implementation satisfies it is established by the
  corresponding release test).
- **Academic:** the meaning/authority separation is an explicit **architectural / theoretical
  boundary** — including the distinction that evaluation establishes a property while issuance creates
  reliance (D1/D2); **separately**, the ZTL classification/warrant kernel is machine-checked with empty
  axiom lists. Institutional legitimacy is **not** claimed as Lean-proved — only the logic is
  machine-checked.

## The two additions OPEN makes concrete

1. **Institutional standing is computable but not transferable by implication** (see 02). **Standing
   is a bounded relation, not an actor attribute. Authority is externally grounded through the
   applicable authority basis and becomes actionable only within a valid bounded standing.** This is
   what lets a public institution trust a computational process without ceding separation of powers.
2. **Supplier replacement without legitimacy loss** (Open Exit). "Open" here is not merely "source
   code is published." **OPEN requires** admitted control representations, representations of
   institutionally admitted meaning, evidence, dispositions, mission history, correction lineage, and
   reliance records to remain institution-controlled and portable across conformant supplier changes;
   institutional meaning itself must be **semantically conserved** rather than treated as a
   transferable artifact. Whether a particular implementation satisfies that requirement is
   established by the corresponding release test.

## Honesty boundary (explicit — this is part of the advancement, not a caveat to hide)

The advancement is an **architectural property**, demonstrated in method and *partially* in
implementation. We claim it at the level actually established:

- **Measured today** (ZTL logical warrant, Phase-A): six adversarial classes, **50/50 mutations
  detected, 0 observed misses among measured classes**; **two adapter/admission classes UNMEASURED**;
  the §24.5 provenance/admission invariant **FAILED**; overall **`PHASE_A_v0.1 = FAIL_AND_INCOMPLETE`**.
  This must never be stated as "benchmark passed." The strong story is the opposite: we **preserved
  adverse and incomplete results** instead of converting them into a win.
- **Design-level, not yet executable** (institutional currentness / reliance runtime): the currentness
  preregistration reached the construction boundary — five case classes **BLOCKED_CASE_CONSTRUCTION**,
  executable denominator **0**, no Detection/Containment score, no execution. **Design
  representability = PRESENT; executable representability in the frozen Phase-A substrate = ABSENT.**
  Not a failure, not a pass, not a measurement. `OAM-EXEC-CURRENTNESS-001` remains deferred.

**Claim discipline is itself an institutional feature.** A system whose novelty is that meaning,
authority, evidence, and disposition stay *separable and inspectable* must demonstrate that it does
not inflate its own claims. Preserving negative and incomplete evidence — and marking design-level
capability as design-level — is not a weakness in the submission; it is the property being claimed,
exercised on the submission itself.
