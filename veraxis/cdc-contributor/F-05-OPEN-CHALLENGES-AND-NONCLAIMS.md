# F-05-OPEN-CHALLENGES-AND-NONCLAIMS

From: Vitaly Reznik (`inventor1975`), integration owner for F. Date: 2026-08-10.
Purpose: the honest remainder — every gap, blocked result, open challenge and
explicit nonclaim that survives F. Nothing here is converted into pass, fail,
or achievement. This file is part of the claim-discipline record.

## 1. Capability / evidence gaps (owner-mandated, preserved verbatim)

1. No frozen end-to-end OIC→OAM execution.
2. No full manifest-bound end-to-end candidate-binding execution.
3. No supplier-replacement execution (0 provider-replacement trials).
4. No measured R-CDC-04 offline/no-egress release gate.
5. Standing runtime not operationalized (standing-currentness deferred).
6. Phase-A v0.1 = `FAIL_AND_INCOMPLETE` (6/8 classes measured 50/50 with 0
   observed misses; 2 adapter/admission classes UNMEASURED after two
   owner-side case-construction failures; §24.5 provenance-admission defect
   count 1 — open product remediation item: Admission Integrity Gate).
7. Currentness: denominator 0; 5 × `BLOCKED_CASE_CONSTRUCTION`
   (`EXECUTABLE_CURRENTNESS_RELIANCE_SUBSTRATE_ABSENT`); no detection or
   containment score; neither pass nor fail.
8. External implementation landscape `NOT_SYSTEMATICALLY_ASSESSED`.
9. External independent reproduction `NOT_ASSESSED`.

## 2. Challenge-record registry and dispositions

Internal (F-02B; preserved, not to be closed by new execution):

- `F02B-01` (CLAIM-02): no frozen end-to-end OIC→OAM execution — OPEN /
  future release work.
- `F02B-02` (CLAIM-04): no manifest-bound end-to-end candidate-binding
  result — OPEN / future release work.
- `F02B-03` (CLAIM-05): Phase-A raw/scored/adjudication traceability —
  **CLOSED by F-02B-TRACEABILITY-SUPPLEMENT** (existing artifacts only);
  residual: run environment `NOT_RECORDED` for Phase-A/EH-3.
- `F02B-04` (CLAIM-08): original applicant source not re-read —
  OPEN / `PROVENANCE_CAVEAT`.
- `F02B-05` (CLAIM-11): no frozen R-CDC-04 release-gate result — OPEN /
  future release work.
- `F02B-06` (CLAIM-12): raw-evidence enclosure — **CLOSED by supplement**
  (bundles d5bd9e17/4d8f87bd, scored 40712058, adjudication 9f5a9adf,
  member hashes); residual: environment `NOT_RECORDED`.
- `F02B-07` (CLAIM-13): currentness package traceability — **CLOSED by
  supplement** (937fe51e byte-bound; prereg v0.2 61772f78).

External (F-03D SOTA challenge records; owner-adjudicated):

- `SCR-11`: historical premise withdrawn by its author as unfounded; owner
  ruling `POST_HOC_DEFINITION_CHANGE = FALSE`; the surviving
  carve-out-perception concern is addressed by SCR-17 below.
- `SCR-14` (HIGH): adverse-evidence non-promotion occupied by CXI
  opaque-data slots (and SACM `isCounter`) — **ACTION TAKEN: withdrawn as a
  claimed contribution; cite CXI/SACM** (F-04 CLAIM-12).
- `SCR-15` (HIGH): warrant ≠ institutional power is Hohfeldian prior art
  with modern formalizations — **ACTION TAKEN: cited as prior art, not
  presented as contribution** (F-04 CLAIM-01/05).
- `SCR-16` (HIGH — the live kill risk on S2): VC 2.0 partially passes the
  F-03D form of Test S2. Owner controlling adjudication:
  `VC_2_0 = STRONG_PARTIAL_EQUIVALENT` under the 8-point S2
  operationalization (the reviewed spec does not establish the
  source→candidate-represented-meaning→institutional-admission/refusal
  transition). **OPEN WORK carried forward:** the three candidate deltas —
  (i) admitted content that is not a claim about a subject;
  (ii) conservation of admitted content under transformation;
  (iii) downstream reliance correction on supersession — are retained as
  **challenge probes: secondary discriminators, not exhaustive necessary
  conditions for retaining S2.** Withdrawal condition (owner-controlled):
  **S2 is withdrawn only if a reviewed source documents full satisfaction
  of the controlling eight-point S2 test, or if the S2 operationalization
  itself is invalidated.**
- `SCR-17` (MEDIUM): definition-precedence must be verifiable, not
  asserted — **`SCR-17 = PARTIALLY_CLOSED`**:

  ```
  BYTE_IDENTITY = VERIFIED
  PUBLIC_FREEZE_COORDINATE = VERIFIED
  CURRENT_DEFINITION_CONTENT = VERIFIED
  PRE_SOTA_PUBLIC_DEFINITION_PRECEDENCE = NOT_YET_INDEPENDENTLY_ESTABLISHED
  ```

  What the freeze commit `973f9eba2dfe410efdadad132ce2348d3875e302`
  (2026-08-10, public `inventor1975/ZTL`, `veraxis/cdc-contributor/`, file
  SHA-256s in `00-A-E-FREEZE-MANIFEST.md`) proves: exact bytes, public
  coordinates, current definition content — from its own timestamp onward.
  What it does not prove: that the frozen definitions were independently
  timestamped **before** the start of the external SOTA review.
  **Historical-object search performed (2026-08-10, measurement not
  assumption):** repository history before 2026-08-10 contains no commit
  carrying the A–E definitional content (content search over all branches:
  zero hits; `cdc-contributor/` first exists at `973f9eb`); no Zenodo or
  other immutable publication of A–E exists; local file mtimes and
  party-held transmission receipts are not independent timestamps. Nearest
  existing public precursor: Protocol v0.1, commit
  `61a470b41eccf8e57633d0abee7bbc795329a411` (pushed public 2026-08-09) —
  admission/issuance/reliance/currentness semantics; a conceptual
  precursor, NOT the frozen A–E/S2/T1 definitions. Nothing retrospective
  was created. The precedence line therefore stays honestly
  OPEN/PARTIAL; this does not affect S2/T1 retention — we simply do not
  assert proven public precedence.

## 3. Nonclaims (binding on all public wording)

Not claimed as novel or as contributions (established or heavily
anticipated prior/concurrent art):

- runtime authorization primitives;
- generic semantic preservation;
- standing as a general principle;
- warrant vs authority as a general principle (Hohfeld);
- adverse-evidence non-promotion (CXI, SACM);
- runtime authorization currentness (CXI epochs/snapshots);
- issuance/verification separation (VC 2.0);
- record authenticity/history preservation as generic properties
  (records-management lineage, ISO 15489);
- human-in-the-loop governance (`HITL_ROW = CONTEXTUAL_NON_LOAD_BEARING`).

`NOVELTY_FINDING = NOT_CLAIMED`. The external track asserts only: no full
documented match to the residual core (S2 under the owner operationalization
+ T1) was found in the reviewed published claim/specification corpus. It
never asserts that no working system has the capability.

## 4. Claim-discipline record (epistemic rules fixed for this program)

- `EXTERNAL_PUBLISHED_CLAIM_AND_SPECIFICATION_ANALYSIS` ≠ verified system
  capability: paper reports capability ≠ capability independently verified;
  reported benchmark ≠ independently reproduced benchmark; open-source repo
  exists ≠ property demonstrated.
- Per-source `external_evidence_class` (CONCEPTUAL_PRIOR_ART …
  OBSERVED_OPERATIONAL_DEPLOYMENT) is never promoted above what was
  actually established.
- Internal and external tracks answer different questions ("what did we
  actually build/execute/measure" vs "what remains differentiating in the
  published corpus") and never raise each other's evidence class.
- design = DESIGN; target = TARGET/PREREGISTERED; measured requires a
  denominator; blocked = BLOCKED; unmeasured = UNMEASURED; denominator 0 is
  neither pass nor fail; adverse and negative evidence preserved; Phase-A
  research results never mixed with the CDC S1 benchmark.
- S2/T1 are architectural advancement claims, not executable achievement
  claims; final public wording = intersection of ceilings (F-04), never an
  average.
- Frozen figures cite their snapshot (e.g. Lean 371/21 at the veraxis input
  pin), never a moving repository state.

## 5. Standing open items outside F

- Tier-1 independent reproduction of the ZTL corpus: OPEN (owner side).
- Semantic implementation gate: BLOCKED; GATE-SAR-05: NOT_CLOSED;
  PUBLICATION_AUTHORIZED = FALSE.
- OAM-EXEC-CURRENTNESS-001: deferred and unauthorized.
- Source clearance for the remaining corpus sources (legal work, owner
  side).

`SUBMISSION-PERMITTED-CLAIMS` is not generated until owner adjudication of
F-04/F-05.
