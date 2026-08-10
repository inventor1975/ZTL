# CDC-EXEC-VERTICAL-SLICE-001 — MERGE-SEAM RESULT 001

Evaluator: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-10. Filled strictly per the frozen
`MERGE-SEAM-RESULT-TEMPLATE-v0.1` (sha256 `a1e8aab6…`) against the frozen
Merge-Seam Checklist v0.1 (`48ea48fc…`) + Addendum 001 (`9032e5de…`).
Frozen instruments unchanged. No remediation was formulated before this
record was frozen.

```
implementation_seen = TRUE
execution_results_seen = FALSE
mission_results_seen = FALSE
```

Combined-head materialization (independent, not from Codex's report):
bundle `CDC-EXEC-VERTICAL-SLICE-001-COMBINED-HEAD-REVIEW.bundle`
(1987699 B, sha256 `59759296dc343d3c9647ca055aa5f00b18d056d9aefe24eefceb047b1d853022`)
verified byte-exact; `git bundle verify` = complete history; cloned into an
isolated repository; object resolved directly:
`%H = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d`,
`%T = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e`
(parent `58209f1f314edfb69e107de47291e370c70ccd82`). All checks below were
made on the checked-out combined state (NON_HEREDITARY_CONFORMANCE: branch
claims not inherited).

---

## Item 1 — candidate ≠ admitted meaning

```text
item = 1
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py:1-8 (module boundary: "consumes an
  already-created evaluation and warrant; does not interpret sources or
  create institutional meaning"); :83-96 (admissions/admission_record_ref
  is a separate required registry binding from candidates/candidate_id)
result = PASS
reason = candidate and admission are distinct bound objects; no combined
  code path originates or reinterprets admitted meaning.
```

## Item 2 — T/F/Z discipline unchanged

```text
item = 2
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = grep census over src/oic/cdc_slice.py, scripts/cdc_slice_*,
  tests/*cdc_slice*: zero T/F/Z re-derivation; warrants consumed as
  digest-bound opaque artifacts (cdc_slice.py:98-134); synthetic corpus
  stand-ins honestly labeled "Not a ZTL kernel output"
  (tests/integration/cdc_slice_corpus.py:217-219); upstream evaluation
  vocabulary (SATISFIED/BREACH/UNRESOLVED) is a separate object class, not
  kernel verdicts.
result = PASS
reason = the combined state neither imports, reimplements, renames nor
  defaults kernel T/F/Z semantics; the kernel discipline is untouched by
  construction.
```

## Item 3 — fallback ≠ ZTL warrant (N-1)

```text
item = 3
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py:98-114 (class collision -> DENY
  WARRANT_ARTIFACT_CLASS_COLLISION; fallback with any ZTL field non-None ->
  DENY FALLBACK_MASQUERADES_AS_ZTL; separate registry categories
  warrants/fallback_warrants; separate digest checks with distinct reason
  codes :132-134); :204-205 (event keeps ZTL_warrant_digest = None under
  fallback; fallback_warrant_digest is its own field)
result = PASS
reason = N-1 is enforced mechanically: a fallback artifact can never be
  represented as, or populate, a ZTL warrant identity.
```

## Item 4 — CANNOT never rewritten as REFUTED

```text
item = 4
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py:47-57 (cannot_condition ->
  epistemic_state = UNRESOLVED_CANNOT preserved even when the operational
  decision is DENY); :145-150 (CANNOT/unknown condition -> ESCALATE with
  UNRESOLVED_CANNOT); grep: the string REFUTED occurs in no slice file
  (only in the pre-existing frozen kernel conformance fixtures, where it
  is legitimate ZTL disposition vocabulary).
result = PASS
reason = no mapping, enum, serializer or record collapses CANNOT (or any
  unresolved state) into a refutation value.
```

## Item 5 — gate decision ≠ epistemic state (N-2)

```text
item = 5
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py:38-45 (GateDecision carries decision
  and epistemic_state as separate fields); :195-196 (the emitted event
  stores reason_code and epistemic_state separately). ESCALATE lexical
  collision checked per WO §6: requested_disposition "ESCALATE" is
  proposal-field vocabulary validated against PERMITTED_DISPOSITIONS
  (:80-81), gate "ESCALATE" is GateDecision.decision; the gate result
  never feeds the disposition field — two dimensions, same spelling,
  never substituted.
result = PASS
reason = operational and epistemic dimensions are represented and stored
  independently throughout the combined state.
```

## Item 6 — reviewer-authority failure carries no truth implication

```text
item = 6
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py:78-79 (scope mismatch -> DENY
  UNAUTHORIZED_REVIEWER_SCOPE before any warrant handling; no candidate or
  warrant truth field is read or written on that path).
result = PASS
reason = authority failure produces an operational refusal only; zero
  epistemic information about the candidate is generated or altered.
```

## Item 7 — no implicit ALLOW

```text
item = 7
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = grep census: the production string "ALLOW" originates at
  exactly one site — src/oic/cdc_slice.py:151, the final return after all
  contract checks; every other path returns explicit DENY/ESCALATE;
  emit_transition_event refuses non-ALLOW (:162-163);
  tests/integration/cdc_slice_interlock.py adds a fail-closed execution
  clearance (missing owner clearance -> refusal, never default-permit; no
  fake reference defined for tests).
result = PASS
reason = ALLOW is reachable only through the explicit full-condition path;
  no default branch, exception path or fall-through yields ALLOW.
```

## Item 8 — no new disposition vocabulary

```text
item = 8
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py:23-25 (PERMITTED_DISPOSITIONS
  frozenset = exactly the six contract dispositions); measured string
  census across all slice files: only the six dispositions plus
  ALLOW/DENY/ESCALATE occur; no alias, no addition.
result = PASS
reason = vocabulary closure holds on the combined state.
```

## Item 9 — correction preserves predecessor

```text
item = 9
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py:214-245 (make_successor is pure:
  reads predecessor, returns a new successor value with supersedes/
  superseded_by/correction fields; no write to the predecessor anywhere in
  the combined state — grep for predecessor mutation: only read access
  :239); production_reliance_semantics = OUT_OF_SCOPE per contract §10.
result = PASS
reason = correction creates a linked successor; the predecessor value is
  never mutated, deleted or de-addressed.
```

## Item 10 — no runtime result can modify the oracle

```text
item = 10
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = src/oic/cdc_slice.py: zero oracle references; scripts hold
  only immutable identity digests explicitly marked
  DECLARED_NOT_RESOLVABLE_ON_THIS_MACHINE
  (scripts/cdc_slice_run_plan.py:54-60) and provenance entries with
  "oracle_is_external_to_runtime": true
  (scripts/cdc_slice_evidence_skeleton.py:120-131);
  scripts/cdc_slice_adjudication_handoff.py "leaves every verdict slot
  empty"; tests/integration/cdc_slice_observation.py:132 raises if an
  observation acquires an adjudication verdict; guard test
  tests/integration/test_cdc_slice_preparation.py:79-86 ("The oracle stays
  external: no favourable result is copied into runtime input").
result = PASS
reason = oracle_as_evidence_reference only (permitted); no import, read,
  parse or parameterization of oracle content by any runtime or test path
  (prohibited class absent).
```

## Item 11 — FO-1/FO-2/FO-3 provenance reachable (per Addendum 001)

```text
item = 11
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = measured at the combined tree: FO-1
  docs/operations/CDC-EXEC-VERTICAL-SLICE-001-FIRST-OBSERVATION.md sha256
  fe6aeee3… EXACT; FO-2 …FO-2-BASELINE-SUITE-FAILURE.md sha256 9c1a3c56…
  EXACT; FO-3 …FIRST-TEST-FAILURE.md sha256 5c4fd185… EXACT; first-bound
  snapshots 617370e5 and 673bb27b both resolve and are ancestors of the
  combined head (git merge-base --is-ancestor = true for both); no
  substitution — designated bytes at designated paths.
result = PASS
reason = exact path + exact bytes + reachable history for all three
  owner-designated objects; no history rewrite, no silent replacement.
```

## Item 12 — FAILURE-PRESERVING AVAILABILITY stays a candidate invariant

```text
item = 12
combined_commit = 6dc88cec0aca048e6117b54bac8bf577ae7bc96d
combined_tree = d19a2f58cf9cbf6de7fde33b6c3aad089660a07e
evidence_refs = repository-wide grep: the phrase occurs exactly once — in
  the vendored owner-attested contract
  docs/contracts/VEIP-CDC-SLICE-EVALUATION-CONTRACT-v0.1-OWNER-ATTESTED.md
  (byte-identical to the attested object, sha256 93fa0cf4… recomputed at
  the combined tree), which itself states "remains a candidate invariant …
  does not prove the invariant generally"; no other artifact, docstring or
  report represents it as proven.
result = PASS
reason = the candidate status is preserved verbatim; no overclaim exists
  in the combined state.
```

---

## Aggregate

```text
PASS_count = 12
FAIL_count = 0
NOT_EVALUABLE_count = 0

MERGE_SEMANTIC_ACCEPTANCE = PASS
reason = all twelve frozen checklist items evaluated on the materialized
  combined head; every item PASS under the frozen aggregate rule
  (12 PASS -> PASS).
```

Per the frozen rule this record is an observation-comparison result only:
it does not authorize the merge into any protected branch, does not create
execution clearance, and does not constitute institutional acceptance.
