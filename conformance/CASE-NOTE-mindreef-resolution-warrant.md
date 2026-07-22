# Case Note — MindReef Resolution Warrant Gate: First Cross-Language Consumer of ZTL Reference Semantics

*Internal record. 2026-07-22.*

## Summary

MindReef (a discussion platform) is the first live consumer of a ZTL warrant
rule across a language boundary. A single warrant rule —
`MR-WARRANT-RESOLUTION-001` — is defined once as reference semantics in the ZTL
repository (Python), re-implemented natively in MindReef (PHP), and the two are
held together by one shared set of fixtures rather than by a runtime
dependency. This is the first observable case where ZTL-like warrant semantics
stopped being purely formal work and changed the behaviour of a running
product.

## The rule

`MR-WARRANT-RESOLUTION-001`, v1.0.0 (rule_hash `27d1d4d9…`):

> A topic may transition to `resolved` only if every idea in the presented
> topic state has a KNOWN, DECIDED status (`approved` or `rejected`). Any idea
> whose status is `pending`, or unknown / missing / null / malformed, blocks
> the transition, which is downgraded to `discussing`. **Fail closed:** an
> unrecognised status is treated as unresolved ground, never waved through. A
> non-`resolved` proposed status passes through unchanged.

This is a minimal but clean form of **runtime admissibility**: the AI may
*propose* a resolution, but the system does not permit that proposal to become a
consequential institutional state transition while presented unresolved ground
remains. It makes operational two distinctions:

- *Text synthesis is not an earned resolution.*
- *The absence of a **processed** objection cannot be converted into the absence
  of an objection.*

`resolved` is not an interface description; it is a consequential institutional
state. Model confidence is therefore insufficient for the transition — the
transition must satisfy the warrant condition.

## The hierarchy (semantics owned once, replicated, proven)

1. **Lean / ZTL** — fixes the formal grounds where they apply.
2. **`conformance/resolution_warrant.py`** — the reference evaluator of this
   specific warrant rule (the definition of correctness).
3. **MindReef PHP** — implements the rule natively (`Topic::admissibleResolution`).
4. **Shared fixtures** (`conformance/MR-WARRANT-RESOLUTION-001.json`) prove the
   PHP implementation replicates the reference semantics.
5. **MindReef owns the institutional mapping** — which logical result blocks
   which product transition — not the ZTL side.

The reference is never a runtime dependency of the consumer; PHP does not call a
Python process. The reference is only the definition of correctness. This is the
architecturally correct form, on one condition, which is met: **PHP is not a
second independent source of semantics** — it is a checked replica.

## PHP mapping

- `Topic::admissibleResolution(string $proposed, array $ideaStatuses): string` —
  the rule as a **pure function**, so it is tested against the same shared
  fixtures as the reference. Fail closed via `in_array($status, ['approved',
  'rejected'], true)`.
- `Topic::gateResolution(string $proposed): string` — applies the pure rule to
  this topic's presented idea statuses.
- Call sites: `App\Console\Commands\AnalyzeTopic` gates every write of
  `resolution_status` (the child-aggregation path and the AI-verdict path), and
  re-evaluates on re-analysis, so a new pending idea after a resolution proposal
  invalidates it.

## Test evidence

13 shared fixtures, positive and adversarial, covering every required case:
`0 / 1 / N pending → block`, `all-decided → proceed`, `pending→addressed →
recompute proceeds`, `new pending after proposal → invalidate`, and — the case
that most needed guarding — `unknown / null / empty status → fail closed`.

- Reference (Python): `conformance/resolution_warrant.py` — 13/13 pass.
- Consumer (PHP): `tests/Feature/ResolutionWarrantConformanceTest` — 13/13 pass
  against the byte-identical fixtures (22 assertions incl. rule id/version).

Both implementations produce the fixtures' expected outputs on identical inputs;
they therefore agree.

## Incident prevented

Before the gate, MindReef's AI could mark a topic `resolved` (via its `RESOLVED`
verdict on a leaf, which did not inspect idea statuses) while ideas remained
`pending`. The gate downgrades such a proposal to `discussing` and names the
work left. Verified live on production: re-analysing a topic runs the gate as
expected.

## Claim ceiling

The rule proves **only** the absence of a *presented* `pending` (or
unrecognised) idea status. It does **not** prove:

- the quality of the AI's synthesis;
- the absence of unrecorded dissent;
- the correctness of the idea statuses themselves;
- the authority of any particular actor to close the topic;
- the sufficiency of the resolution for external reliance.

Correct claim: *MindReef blocks a topic's transition to `resolved` while any
idea in the presented topic state has a `pending` (or unrecognised) status.*
Not: *MindReef guarantees a resolved topic is actually fully resolved.*

## Drift safeguards (in place)

- **Versioned rule id**: `MR-WARRANT-RESOLUTION-001`.
- **Semantic version + hash**: v1.0.0. `rule_hash`
  (`27d1d4d9795da569186b3d6dc098982a684d2305a6017699af44f98e91af34a8`) is
  anchored in the spec JSON (the `rule_hash` field) AND recomputed in the
  reference (`resolution_warrant.rule_hash()`), which asserts the two are equal
  at check time. The PHP consumer pins the id, version, AND hash
  (`Topic::RESOLUTION_RULE_HASH`), and its test asserts the shared fixtures'
  `rule_hash` equals that pin.
- **One shared fixture set** for both languages (the JSON, synced verbatim;
  sha256 `99a487bc8fa1e779d8f9063ed9acc39c5aa5d8603ef93c1f98bc8a6e9b7d50f3`).
- **Dual conformance test**: the Python reference and the PHP consumer each run
  the same fixtures in their own CI; both matching the shared expected outputs
  is the cross-language agreement check.

## Consumer provenance (evidence pin)

MindReef is not git-tracked and its source is private, so the immutable
consumer pin is a content hash of the rule-bearing file, not a commit SHA. The
private PHP source is not published; the pins below make the conformance claim
independently checkable against the public reference without it.

```yaml
consumer:
  implementation: "MindReef PHP (App\\Models\\Topic::admissibleResolution)"
  repository_visibility: "private"
  version_control: "not git-tracked; edits applied directly to production"
  consumer_commit: null
  consumer_file: "app/Models/Topic.php"
  consumer_file_sha256: "446bac0641b35d5bea1ede254345a2d1e9a4b3defdd0ca601119cde0c7bf658b"
  rule_id: "MR-WARRANT-RESOLUTION-001"
  rule_version: "1.0.0"
  rule_hash: "27d1d4d9795da569186b3d6dc098982a684d2305a6017699af44f98e91af34a8"
  fixture_blob_sha256: "99a487bc8fa1e779d8f9063ed9acc39c5aa5d8603ef93c1f98bc8a6e9b7d50f3"
  test_command: "php artisan test --filter=ResolutionWarrantConformanceTest"
  test_result: "13/13 (17 assertions)"
  test_output_sha256: "723451620015d22e8b48a60c4d196d06015298ab0efe047692e4531132553c35"
  production_release_id: "direct-deploy, worker restart 2026-07-22T17:25:34Z"
  deployed_at: "2026-07-22T17:25:34Z"
  production_observation: "author triggered topic re-analysis via the UI; the gate applied as expected (2026-07-22; no personal data referenced)"
```

The `fixture_blob_sha256` above equals the sha256 of the public reference
fixtures (`conformance/MR-WARRANT-RESOLUTION-001.json`): the consumer is proven,
byte-for-byte, against the same fixtures anyone can inspect. What remains
private is only the PHP source and the raw run, pinned by the hashes above.

## Non-normative note

The `ztltool.py → ztljudge.py` rename is a non-normative tooling update. The
utility is not among the frozen 28 Lean declarations; the theorem surface is
unchanged; the upstream tag and hashes remain valid.

## Strategic significance

This confirms the Veraxis architectural hypothesis: interoperable semantics can
be made precise enough that an independent consumer implements them locally and
proves conformance **without handing the owner of the reference engine control
over the consumer's production runtime.** Warrant semantics crossed a language
boundary and changed real product behaviour — and did so as a checked replica,
not a runtime dependency.
