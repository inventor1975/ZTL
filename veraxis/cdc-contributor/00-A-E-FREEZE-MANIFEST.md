# 00-A-E-FREEZE-MANIFEST — CDC Contributor Package A–E Freeze Record

From: Vitaly Reznik (`inventor1975`), CDC contributor / integration owner for F.
Date: 2026-08-10.
Authority: owner (Arkadiy) lead-sequence directive of 2026-08-10 opening
F (Evidence-Aware Reconciliation) and closing A–E as a working surface;
mutual contributor-freeze acceptance of 2026-08-10 16:38.

This is an administrative freeze record. It changes no content. It fixes the
exact bytes of the five frozen contributor artifacts, their statuses, the
governing baseline, and the rule under which F operates.

---

## 1. Frozen artifacts (exact bytes)

Canonical copies as accepted at contributor freeze. SHA-256 over exact file
bytes (UTF-8, LF), sizes in bytes.

| # | File | Bytes | SHA-256 |
|---|------|-------|---------|
| 01 | `01-CDC-INSTITUTIONAL-ARCHITECTURE-NARRATIVE.md` | 12424 | `33467da3619b801a8f19ca8a9dd8b7c01b67074f45e6b5a2488df66fbaf776a1` |
| 02 | `02-OPEN-INSTITUTIONAL-STANDING-MODEL.md` | 4737 | `c049f5ab5d40e59be1ddb5b3a22e9ab344a65fb0a377ac32a2fbb85f9465f01e` |
| 03 | `03-ADVANCEMENT-BEYOND-STATE-OF-ART.md` | 7282 | `70bebe3a963ac93f2eded55fcf3df58a94f59fa11aa9f15d8239881583957545` |
| 04 | `04-CDC-CLAIMS-EVIDENCE-CEILING-MATRIX.md` | 14080 | `696354b0394e89d5d6f758172ea9aa283a0ef1cae01a52647f7ba00db5796d8d` |
| 05 | `05-CDC-END-TO-END-INSTITUTIONAL-BOUNDARY.md` | 6358 | `d8071af1bdbab60044ae12677de370e68fa4530e72a197c0e3d8bbea0c04c19d` |

Consistency note: file 02 was last modified 2026-08-09 (the cross-artifact
pass of 2026-08-10 left it untouched by design — it is the canonical standing
model that normalizes 04/05); files 01/03/04/05 carry the 2026-08-10 final
corrections (portable-authority residuals, meaning-conservation distinction,
03 Open Exit canonical blockquote).

## 2. Statuses (frozen)

```
01 = CONTRIBUTOR_FROZEN
02 = CONTRIBUTOR_FROZEN / CANONICAL_STANDING_MODEL
03 = CONTRIBUTOR_FROZEN_PENDING_EXTERNAL_SOTA_SUBSTANTIATION
04 = CONTRIBUTOR_FROZEN
05 = CONTRIBUTOR_FROZEN

A_E_CONCEPTUAL_SCOPE = CLOSED
F = INTENTIONALLY_OPEN

SEMANTIC_IMPLEMENTATION_GATE = BLOCKED
GATE_SAR_05 = NOT_CLOSED
PUBLICATION_AUTHORIZED = FALSE
```

**Controlling claim register: artifact 04 only.** `CDC-CLAIM-01..13` as defined
in `04-CDC-CLAIMS-EVIDENCE-CEILING-MATRIX.md` are the sole authoritative claim
IDs. Any substitute or re-derived claim register (including any generated
before this canonical package was available) is non-authoritative.

Canonical package-wide distinctions locked (not restated, only named):
MEANING = semantically conserved, not transferred; ADMITTED-MEANING
REPRESENTATIONS = portable; AUTHORITY = externally grounded, non-transferable
by implication; STANDING = bounded, non-transitive; LEGITIMACY-HISTORY =
portable; LEGITIMACY = not portable by artifact transfer.

## 3. Governing baseline

- `TDD-OAM-001 v1.1`, bounded by `SAR-OAM-001 v1.0` (owner-supplied governing
  baseline of the CDC contributor packet).
- Release objects `R-CDC-01..05`; claim register `CDC-CLAIM-01..13`;
  14-section submission structure (owner-supplied).
- Timeline: contributor content freeze 2026-08-15; submission 2026-08-21.

## 4. Frozen observed evidence anchors (for F; identities verified against the ZTL repository)

F reconciles against these exact frozen records — no inference from moving
repositories:

| Evidence | Identity |
|---|---|
| Protocol v0.1 (frozen, D1/D2, 26 rules) | commit `61a470b41eccf8e57633d0abee7bbc795329a411` |
| Experiment Freeze Package r5 (37 gates / 91 atoms) | commit `673a8854e68d03f0cc30655b168343cf47887e0f` |
| Phase A v0.1 owner adjudication: `FAIL_AND_INCOMPLETE` | commit `9f5a9adf2bc2ca65af6a55a2e1773c828e51f3a3` |
| Adapter replication v0.1 closure: 2 classes `UNMEASURED` after 2 owner-side construction failures | commit `74cda37c7233c5e6ac1f2b37039b8bb870935538` |
| Currentness/rollback preregistration v0.2 (frozen pre-execution) | commit `61772f78b98f009f93c01a21ded7a64c3d35ff19` |
| Currentness construction return: all 5 cases `BLOCKED_CASE_CONSTRUCTION`, reason `EXECUTABLE_CURRENTNESS_RELIANCE_SUBSTRATE_ABSENT` | commit `937fe51ee75705c7b50c54bff85c87fffaa5acc2` |
| Phase A EH-3 scored bundle (post-disclosure) + full Phase A verdict — the scored-result source, distinct from and referencing EFP `673a8854` | commit `40712058530a407da0710b21b0f62272809c9fe4`, tree `1483097b0a1225be62486a4ccb278a49978497aa`; files: `00-EH3-SCORED-RESULT.json` sha256 `bda0ecb0a122e1ca96679f57f8df0c73de26bd9824a1874f8ac91919efdee164`, `bundle-manifest.json` `2dba3a37fdc07b088ab1440cdba5dcfd8df03813d650a528260194ac35d706f4`, `case-class-binding.json` `af77add42a0c848b1e09cda8dfdfae06df42f0247c5d929ef7481383c2b58c12` (directory unchanged from that commit to current HEAD) |

Exact currentness disposition (frozen, verbatim):
`5 × BLOCKED_CASE_CONSTRUCTION`; `EXECUTABLE_DENOMINATOR = 0`;
`DETECTION_SCORE = NONE`; `CONTAINMENT_SCORE = NONE`; `EXECUTION = NONE`;
`PASS = FALSE`; `FAIL = FALSE`; `MEASUREMENT = FALSE`.

Frozen result summary bound to these anchors (denominators explicit):
Phase-A blinded detection measured on 6 of 8 mutation classes = 50/50
detected, 0 false-clean EARNED, 0 misses; 2 adapter-output classes (20 cases)
UNMEASURED (blocked case construction, never reached the judge); one §24.5
provenance-admission defect (count 1) retained as a product remediation item;
known-seam recall 3/3; EH-4 34/34; currentness/rollback BLOCKED with
denominator 0 (design-present / executable-absent). `FAIL_AND_INCOMPLETE`
and `BLOCKED` are preserved as such and are not converted into pass or fail.

## 5. The F rule

**F may reconcile evidence against A–E; F may not silently amend A–E.**

If F, Codex, or Claude finds a real contradiction with the frozen
architecture, the outcome is a `CHALLENGE / CHANGE-REQUEST CANDIDATE`
addressed to the owner — never a silent edit. A–E reopen only on a concrete
factual inconsistency with frozen evidence, by owner decision.

F answers only: *what does exact frozen observed evidence permit us to assert
relative to the frozen architecture?* Unit of work per claim:
CLAIM → FROZEN ARCHITECTURAL BASIS → OBSERVED EVIDENCE → EVIDENCE CLASS →
DENOMINATOR → RESULT → KNOWN LIMITATION → MAXIMUM PERMITTED PUBLIC WORDING.
Design = DESIGN; target = TARGET/PREREGISTERED; measured requires a
denominator; blocked = BLOCKED; unmeasured = UNMEASURED; denominator 0 is
neither pass nor fail; absent evidence is not replaced by architectural
plausibility; negative evidence is preserved; Phase-A research results are
not mixed with the CDC S1 benchmark; F does not upgrade evidence classes.
The internal/executable track (Codex) and the external/comparative track
(Claude) are held separately; neither raises the other's evidence class.

## 6. Disposition

A–E are no longer a working surface. Next artifacts in sequence:
`F-01-EVIDENCE-AWARE-RECONCILIATION`, `F-02-CODEX-EXECUTABLE-EVIDENCE-LEDGER`
(owner work order), `F-03-CLAUDE-SOTA-SUBSTANTIATION-AND-CHALLENGE` (owner
work order), `F-04-CLAIM-EVIDENCE-CEILING-FINAL`,
`F-05-OPEN-CHALLENGES-AND-NONCLAIMS`, `SUBMISSION-PERMITTED-CLAIMS`.
