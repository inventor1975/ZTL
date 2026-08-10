# CDC-EXEC-VERTICAL-SLICE-001 — MERGE-SEAM CHECKLIST v0.1 — ADDENDUM 001: FO BINDINGS

Author: Vitaliy Reznik, semantic/logical-boundary authority.
Date: 2026-08-10. Procedural addendum only.

```
CHECKLIST_v0.1_CHANGED = FALSE
CHECKLIST_ITEM_11_SEMANTICS_CHANGED = FALSE
OWNER_IDENTITIES_BOUND = TRUE

implementation_seen = FALSE
execution_results_seen = FALSE
mission_results_seen = FALSE
```

Base artifact (unchanged):
`CDC-EXEC-VERTICAL-SLICE-001-MERGE-SEAM-CHECKLIST-v0.1.md`,
sha256 `48ea48fc41b6756de9cccf145bb4e89a16cc74ee8e51fabfc1715864bdf41206`.

## Owner-designated first-observation identities (bound verbatim; owner identity bindings — not independently reinterpreted)

### FO-1

```text
record_id = FO-1
path = docs/operations/CDC-EXEC-VERTICAL-SLICE-001-FIRST-OBSERVATION.md
sha256 = fe6aeee35c5aa097812e88128ca1f88bc5f5616171eaefc90a0ca91451ba644b
first_bound_snapshot = 617370e53ee72910408ef3f5d34785f430085ce1
```

### FO-2

```text
record_id = FO-2
path = docs/operations/CDC-EXEC-VERTICAL-SLICE-001-FO-2-BASELINE-SUITE-FAILURE.md
sha256 = 9c1a3c56a03d0608c837a6ed0ec43e1b81d1caa25004b624c4151ff4c9c483f9
first_bound_snapshot = 673bb27b134e43369b4028e9f35af1a0c1a60734
```

### FO-3

```text
record_id = FO-3
path = docs/operations/CDC-EXEC-VERTICAL-SLICE-001-FIRST-TEST-FAILURE.md
sha256 = 5c4fd18587ef75d408a7d818c761ae5cbc2490be9ec0df81abe8f9602e2dc927
first_bound_snapshot = 617370e53ee72910408ef3f5d34785f430085ce1
```

## Effect on checklist item 11 (binding only; semantics unchanged)

At merge time, item 11 requires, for EACH of FO-1, FO-2, FO-3:

1. **exact path reachability** — the designated path resolves in the
   combined state;
2. **exact SHA-256 byte identity** — the file at the designated path
   recomputes to the designated sha256;
3. **no history rewrite** making the record (or its first_bound_snapshot)
   unreachable;
4. **no replacement record silently substituted** for the designated
   object.

A successor record, explanatory record, copy under another path, or any
other artifact does NOT satisfy the requirement if the original designated
object is missing or altered. Item 11 verifies reachability and
byte-integrity only; the meaning of the FO records remains owner-defined.
