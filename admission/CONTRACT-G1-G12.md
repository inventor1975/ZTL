# Admission contract — G1…G12

What the admission boundary promises, what it enforces mechanically, and what it
does not. `independent_review_claim = FALSE`.

The twelve properties are **the external reviewer's**, quoted from
`2026-08-25_the external reviewer-to-Vitaliy_GROUNDING-ADMISSION-ZTL-REVOLUTIONARY-BAR-v0.1.md`.
The right-hand columns are ours and are established by running the code, not by
reading it.

## 0. What this boundary is for

Between "a source supports P" and "P may be taken as a **premise** of formal
inference" there is a decision. Retrieval and guards establish a *support
relation*; they do not confer the right to use P as a premise. Only the gate
does, and only when support, source eligibility, epoch currency and guard
conservation all hold.

The ZTL kernel is **not touched**. A row whose ground came from outside enters
`zfl2` as `verified` only with an admission receipt; without one it is not
rejected loudly but **demoted** to `unverified` — zfl2's own zero-trust default
— and every demotion is reported with its reason.

## 1. The twelve

| # | Property (the external reviewer's words, abridged) | Ours | Where |
|---|---|---|---|
| G1 | No externally sourced proposition becomes an admitted premise without a valid admission object | **ENFORCED** | `admit` accepts only a certificate; there is no string path |
| G2 | A certificate proves a *source-support relation*; it cannot become world truth by type conversion | **ENFORCED** | certificate carries `support_relation`, never `true` |
| G3 | Source support cannot establish that the source is eligible or authoritative | **ENFORCED** | separate `authorize(decision, actor, action, grants)`; `authority` rows are demoted even with a perfect receipt |
| G4 | `NO_SUPPORT_FOUND` / `RETRIEVAL_FAILED` / `AMBIGUOUS` never silently become `SUPPORTED` | **ENFORCED** | each has its own disposition; none maps to ADMIT |
| G5 | Conflicting valid certificates stay represented as conflict until an explicit rule resolves them | **ENFORCED** | `resolve_conflict` refuses majority vote, recency, confidence and model reconciliation; emits `CONFLICT` |
| G6 | A certificate for one epoch cannot silently authorize use in another | **ENFORCED** | epoch mismatch → `EPOCH_MISMATCH` |
| G7 | Changing source bytes, version, locator or proposition bytes changes identity or fails verification | **ENFORCED** | digest over all fields; tampering fails `verify_certificate` |
| G8 | Evidence from `S2` cannot satisfy a claim attributed to `S1` without an explicit cross-source rule | **ENFORCED** | `attributed_to ≠ source_id` → refusal |
| G9 | Invalidating a certificate propagates only through dependent warrants and decisions | **ELSEWHERE** | not this module: descent lives in `tool/warrant_receipt.py` (`verify_descent`, transitive with a cycle guard) |
| G10 | Given the same snapshot, epoch, code version, policy and inputs, the disposition replays | **PARTIAL** | identity is deterministic and every decision is stamped with `tool_version`; **no replay stand exercises it** |
| G11 | The evaluator cannot silently expand its own admissibility rules during evaluation | **NOT ENFORCED** | no mechanism. Searched; found nothing. This is an architectural absence, not a passing test |
| G12 | The system states exactly what a certificate establishes and what it does not | **ENFORCED** | the ceiling is a field of the decision object, not prose |

Nine enforced, one partial, one owned by a neighbouring module, **one absent**.

## 2. The one that is absent, stated plainly

**G11 has no owner.** Nothing prevents the evaluator from widening its own rules
mid-evaluation, and nothing would detect it. We are not reporting this as a
failing test, because there is no test — there is no boundary. Anyone relying on
G11 today is relying on the absence of motive, not on a mechanism.

## 3. The socket — found inert, then wired the same day

`zfl2_gate.py` used to call `admit(...)` **without** the conservation verdict,
which `admit` requires. Consequence, measured on the first run of `test_gate.py`:
the gate admitted **nothing** — a flawless receipt still ended in a demotion
reading "the guards socket is not plugged in". It failed closed and said so,
which is the safe direction, but the receipt path was dead code.

**Wired 2026-08-28 on the curator's word.** `gate_document` now takes an optional
`conservations` map, `{row: guards.conserve_socket verdict}`, and passes it
through. Three properties, each with a stand and a vector:

- `CLEAR` + valid receipt → **admitted**. This is the only road in.
- `BLOCK` → demoted, and the reason names the **guards**, not the receipt.
- `NO_VERDICT` or **no verdict supplied at all** → refused, never a quiet pass.

**The gate carries the verdict, it does not compute it.** Not laziness: the
certificate binds the source by digest, not by text (`evidence_atom_ids` +
`source_digest`), so the gate has no evidence text to judge on. Only the caller
holding the texts can. Inventing a verdict here would be admitting by guess —
the exact thing the boundary exists to stop.

Vector `W06` used to pin the inert behaviour; it was rewritten deliberately when
the socket was wired, which is what it was written to force. `W07` and `W08` now
pin the live path.

## 4. How to check any implementation, including ours

`test_gate.py` and the self-test inside `admission.py` are the vectors. They
assert behaviour, not structure, so a re-implementation in another language can
be held to the same list. The tests are written to fail while a gap is open —
a green run means the gap is closed, never that the test was satisfied.

## 5. Ceiling

Established by running: the ENFORCED rows, the inert bridge, and the disposition
vocabulary.

Not established: that these twelve are sufficient; that our reading of the external reviewer's
wording matches his intent; that anything here holds under concurrency,
adversarial input, or a hostile evaluator. Not searched is not the same as clean.
