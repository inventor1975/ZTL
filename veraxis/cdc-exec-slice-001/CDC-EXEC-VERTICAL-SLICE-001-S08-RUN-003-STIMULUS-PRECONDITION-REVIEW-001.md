# CDC-EXEC-VERTICAL-SLICE-001 — S-08 RUN-003 STIMULUS PRECONDITION REVIEW 001

Reviewer: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-11. The stimulus was inspected, NOT executed. Oracle,
protocol, implementation, stimulus and permissible outcome sets untouched.

Stimulus: `CDC-EXEC-VERTICAL-SLICE-001-S08-RUN-003-STIMULUS-v0.1.json`,
3240 B, sha256
`70fd6f8fd206859858f9fdb38725c751b00af29e015d40e852958111414f7586`
(byte-verified before reading). Controlling implementation: combined head
`6dc88cec…` / tree `d19a2f58…` (already materialized and verified in the
merge-seam evaluation; harness inspected within that already-permitted
scope).

## The one question

**Does this stimulus, as specified, instantiate the frozen S-08
precondition — a component failure during the attempted transition, after
execution has begun and before completed execution?**

**Answer: YES.** Grounds, source-verified at the combined head:

1. **The seam exists as claimed.**
   `tests/integration/cdc_slice_harness.py:22` imports
   `emit_transition_event` as a module global of the harness — a
   late-binding module-attribute boundary substitutable without any change
   to the committed tree (`implementation_change_required = false`
   confirmed).
2. **The window is as claimed.** In `run_procedure`: the gate evaluation
   sits in its own try/except (:82–85); the non-ALLOW early return is at
   :98; the emission call `event = emit_transition_event(...)` follows at
   :110–113 inside try/except; the completed-execution `MissionRunResult`
   is only constructed at :125. A raise at the emission call therefore
   occurs strictly **after the gate returned ALLOW and before completed
   execution** — the POST_GATE_PRE_COMMIT window exactly.
3. **It is an actual component failure, not any excluded class.** The
   stimulus requires a fully conforming proposal (gate reaches ALLOW
   before the component is invoked), which structurally excludes: missing
   warrant/evidence/source; digest mismatch; authority failure; unresolved
   precondition; static validation failure; fixture absence — every one of
   those would have refused BEFORE the emission call and the window would
   never be reached. The failure exists only at component invocation, with
   invocation recorded.

Minor note (non-blocking): the stimulus's own `bytecode_offset: 212`
evidence detail was not independently recomputed (module import requires
package context; not needed — the LOAD_GLOBAL/late-binding claim follows
from the module-level import and function-body reference, and
`co_freevars` emptiness from the absence of any closure).

## Scope ceiling — preserved

The stimulus's `scope_limitation` states exactly the required ceiling:
dependency substitution establishes harness behavior when a **bound
component fails at the existing seam**; it does NOT establish an internal
failure mode of the production `emit_transition_event` ("the committed
implementation exposes no non-validation failure mode reachable without
modifying the tree"). `CLAIMED_FAILURE_CLASS =
BOUND_COMPONENT_FAILURE_AT_EXISTING_HARNESS_SEAM`;
`NOT_CLAIMED = INTERNAL_FAILURE_OF_PRODUCTION_emit_transition_event`.

## Return

```text
S08_STIMULUS_PRECONDITION_REVIEW = COMPLETE

stimulus_sha256 =
70fd6f8fd206859858f9fdb38725c751b00af29e015d40e852958111414f7586

oracle_precondition_instantiated = YES

failure_window = POST_GATE_PRE_COMMIT

implementation_change_required = FALSE

scope_limitation_preserved = TRUE

blocking_issue = NONE
```

No expected operational, epistemic, institutional or adjudication outcome
is encoded here or in the stimulus; RUN-003 observation will be adjudicated
against the unchanged oracle S-08 case only after execution and freezing.
