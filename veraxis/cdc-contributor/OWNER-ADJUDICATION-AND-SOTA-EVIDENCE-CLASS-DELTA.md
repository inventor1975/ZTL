# OWNER ADJUDICATION AND SOTA EVIDENCE-CLASS DELTA

Status: CONTROLLING DELTA FOR F-04 RECONCILIATION
Scope: F only. A-E remain frozen and MUST NOT be edited.

## 1. F-02B disposition

F-02B is accepted as the controlling internal evidence reconciliation.

- `F-02B = CLAIM_ALIGNED_RECONCILIATION_COMPLETE_WITH_DISCLOSED_TRACEABILITY_GAPS`
- `tests_executed = 0`
- `historical_measurements_reexecuted = false`
- `claims_invented_or_substituted = 0`
- `A_through_E_modified = false`

Traceability supplement may close provenance gaps, but must not alter claim propositions or evidence classes without exact pre-existing evidence.

## 2. F-03D disposition

F-03D is accepted with owner adjudication.

- `POST_HOC_DEFINITION_CHANGE = FALSE`
- `EXTERNAL_DEFINITIONAL_CARVEOUT_PERCEPTION_RISK = TRUE`
- `FALSIFIABLE_OPERATIONAL_TESTS_REQUIRED = TRUE`

The frozen definitions pre-date the SOTA review. Claude's Pass-3 corrections were corrections to functional-equivalence mapping, not changes to A-E.

## 3. External SOTA epistemic correction

Claude's track is NOT independently verified competing-system capability evidence.

It is primarily:

`EXTERNAL_PUBLISHED_CLAIM_AND_SPECIFICATION_ANALYSIS`

covering papers, standards/specifications, formal models, reported architectures, and author-reported implementations/results.

It does NOT establish, unless separately verified:

- that a reported implementation is a working implementation;
- that a reported benchmark is independently reproducible;
- that a competing system passes S2 or T1 in execution;
- that a published claim equals an observed capability.

Use the following external evidence classes:

1. `CONCEPTUAL_PRIOR_ART`
2. `FORMAL_SPECIFICATION`
3. `REPORTED_ARCHITECTURE`
4. `REPORTED_IMPLEMENTATION`
5. `INSPECTABLE_IMPLEMENTATION`
6. `INDEPENDENTLY_REPRODUCED_CAPABILITY`
7. `OBSERVED_OPERATIONAL_DEPLOYMENT`

Do not promote a source beyond the class actually established.

Therefore normalize external conclusions as:

- not `S2_SURVIVES_SOTA`, but `NO_REVIEWED_PUBLICATION_OR_SPECIFICATION_DOCUMENTS_FULL_S2_TEST_SATISFACTION`;
- not `T1_SURVIVES_SOTA`, but `NO_REVIEWED_PUBLICATION_OR_SPECIFICATION_DOCUMENTS_T1_SATISFACTION_ACROSS_HETEROGENEOUS_IMPLEMENTATION_SUBSTITUTION`;
- `S2_PLUS_T1 = NO_FULL_DOCUMENTED_MATCH_FOUND_IN_REVIEWED_CORPUS`;
- `EXTERNAL_IMPLEMENTATION_STATUS = NOT_SYSTEMATICALLY_ASSESSED`;
- `EXTERNAL_INDEPENDENT_REPRODUCTION_STATUS = NOT_ASSESSED`.

## 4. S2 owner operationalization

### S2 — INSTITUTIONAL ADMISSION OF AUTHORITATIVE MEANING

Given architecture X:

1. Identify an authoritative source S.
2. Identify a proposition P represented from S before admission.
3. P must be inspectable as a candidate while remaining UNADMITTED.
4. A recorded transition T must act on P itself — not merely on an action, credential, access request, schema, or effect.
5. T must be attributable to an actor with authority to admit P for the relevant institutional context.
6. T may ACCEPT or REFUSE P without changing P's propositional content.
7. Acceptance changes P's admissibility for downstream institutional computation; refusal leaves it representable but non-admissible.
8. The admitted P remains linked to S, its representation/version, the admitting authority, and T.

PASS: X establishes all eight properties.

FAIL: the purported admission is issuance/origination of a claim, action authorization, access control, effect admission, schema validation, or execution admission.

INDETERMINATE: reviewed material does not establish what object the authority is admitting.

### VC 2.0 adjudication

`VC_2_0 = STRONG_PARTIAL_EQUIVALENT`, not PASS.

VC materially anticipates issuer assertion, credential issuance, authenticity/currentness verification, and third-party verifier reliance structure, but the reviewed specification does not establish the frozen OIC source -> candidate represented meaning -> institutional admission/refusal transition.

## 5. T1 owner operationalization

### T1 — SEMANTIC CONSERVATION UNDER IMPLEMENTATION SUBSTITUTION

Given admitted meaning M and independently substitutable implementations A and B:

Test corpus must contain:

- semantically equivalent re-encodings of M;
- meaning-altering mutations of M.

PASS requires:

- equivalent re-encodings survive substitution;
- meaning-altering mutations are detected/rejected;
- the determination does not depend on byte identity or schema identity;
- the determination is independent of the substituted component;
- the admitted source/meaning identity remains traceable.

A system that rejects every representation change does not pass.
A system that accepts a meaning-changing representation does not pass.

## 6. External claim-status normalization

The broad comparative surface is narrowed.

Do not claim novelty for:

- runtime authorization primitives;
- generic semantic preservation;
- standing as a general principle;
- warrant vs authority as a general principle;
- adverse-evidence non-promotion;
- runtime authorization currentness;
- issuance/verification separation;
- record authenticity/history preservation as generic properties.

Residual published-claim analysis status:

- `S2_PUBLISHED_CLAIM_PRIOR_ART_STATUS = STRONG_PARTIAL_NEIGHBORS_FOUND; NO_REVIEWED_PUBLICATION_OR_SPECIFICATION_DOCUMENTS_FULL_S2_TEST_SATISFACTION`
- `T1_PUBLISHED_CLAIM_PRIOR_ART_STATUS = SEMANTIC_PRESERVATION_PRIOR_ART_FOUND; NO_REVIEWED_PUBLICATION_OR_SPECIFICATION_DOCUMENTS_T1_TEST_SATISFACTION_ACROSS_HETEROGENEOUS_IMPLEMENTATION_SUBSTITUTION`
- `S2_PLUS_T1 = NO_FULL_DOCUMENTED_MATCH_FOUND_IN_REVIEWED_CORPUS`
- `NOVELTY_FINDING = NOT_CLAIMED`

HITL row is `CONTEXTUAL_NON_LOAD_BEARING` unless primary authoritative literature is separately supplied.

## 7. F-04 reconciliation rule

For every frozen `CDC-CLAIM-01...13`, retain at least these independent fields:

- `INTERNAL_EVIDENCE_CEILING`
- `EXTERNAL_PUBLISHED_CLAIM_PRIOR_ART_CEILING`
- `EXTERNAL_VERIFIED_SYSTEM_CAPABILITY`

Unless separate evidence exists, set:

`EXTERNAL_VERIFIED_SYSTEM_CAPABILITY = NOT_ASSESSED`

Final permitted wording is constrained by the lower applicable ceiling. Do not average or merge epistemic classes.

A published claim about a competitor is not an observed competitor capability.
An internally implemented property is not an advancement claim merely because it exists.

## 8. Stop condition

Do not produce `SUBMISSION-PERMITTED-CLAIMS` until F-04 and F-05 are returned for owner adjudication.

