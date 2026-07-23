# ZTL Connector — Drop-in Guide

How a consumer protocol or application plugs into ZTL trust-signatures. Four
steps, nothing more (SPEC §6). MindReef-ZTL is the worked example — it is
connector **instance #1**.

## The idea in one line

You express a decision as a **claim over atoms**, hand it to the connector, and
get back a **signed, re-computable verdict**. Anyone can re-check that verdict
offline with the open reference — they never call your servers, and they never
call ours. That is what keeps the trust protocol-independent (no monopoly).

## Step 1 — Pin the rule

Give your warrant rule an id, a semantic version, and a content hash, and pin
all three:

```
rule = { "id": "MR-WARRANT-RESOLUTION-001", "version": "1.0.0", "hash": "<sha256>" }
```

The hash is computed once over the rule's canonical descriptor and pinned in the
fixtures, the reference, and your consumer. Changing semantics = new version +
new hash; old verdicts stay valid under their pinned version.

## Step 2 — Build the warrant-form

Map your domain data to atoms. Each atom is a decided verdict or the mark:

```json
{
  "claim": "cleared & ~flagged",
  "rule":  { "id": "...", "version": "1.0.0", "hash": "..." },
  "atoms": [
    { "name": "cleared", "value": "T", "provenance": "audit-2024-A", "admissible": "yes" },
    { "name": "flagged", "value": "F", "provenance": "audit-2024-A", "admissible": "yes" }
  ]
}
```

Rules that matter:
- `value` is `"T"` / `"F"` (decided) or `"Z"` (the mark: unverified/unknown).
- **Fail-closed is on your side too**: map anything you are unsure about to `Z`,
  or set `admissible: "no"` — the connector will treat it as unverified ground
  and never wave it through. Do not invent a `T`/`F` you cannot stand behind.
- `provenance` is for the record only; the judge never reads it. Put your source
  id / method there.
- An atom named in the claim but omitted from the list is treated as `Z`
  (default-deny).

## Step 3 — Judge, and get the artifact

Reference (Python):

```python
from connector.verdict import judge_warrant
from connector.signer import Signer

signer = Signer("ed25519")          # or a PQC/hybrid scheme when its backend is installed
artifact = judge_warrant(warrant_form, signer)
```

The artifact carries the `verdict` (`T`/`F`/`Z`), the warranty `grade`
(`hereditary` / `sound` / `until-verification`), the `disposition`
(`EARNED` / `REFUTED` / `ON CREDIT` / `OPEN`), the weak-link `unverified` list,
the `input_digest`, the pinned `rule`, and the `signature`.

**Read the disposition, not just the verdict:**
- `EARNED` — grounded; safe to act on.
- `REFUTED` — grounded false.
- `ON CREDIT` — true only while an unverified link holds; it can die. Do **not**
  treat it as settled.
- `OPEN` — not established; the `unverified` list names exactly what to check
  next.

## Step 4 — Map the verdict to your product, and prove conformance

The connector gives you the **logical** verdict. **You** own the institutional
mapping — which disposition permits which product transition. Example (MindReef):
a topic may go `resolved` only when the resolution claim is `EARNED`; anything
else stays `discussing`.

If you re-implement the rule natively (e.g. in PHP, so you do not call a Python
process in production), prove your implementation matches the reference:

1. take the **shared fixtures** (`connector/fixtures/…json`) verbatim;
2. run them through your native implementation;
3. assert every expected verdict record matches, and that your pinned
   `rule.hash` equals the fixtures' `rule_hash`.

Both sides producing the fixtures' expected outputs on byte-identical inputs
**is** the cross-language agreement. Your production source can stay private; the
public record exposes the reference, the fixtures, the hashes, and the claim
boundary — enough for a party with access to audit you, without you handing over
your runtime.

## The claim ceiling — do not overstate

A verdict proves the logical disposition **given the submitted atoms**. It does
NOT prove the atoms are true, complete, or authoritative, nor that the
resolution is sufficient for anyone to rely on. The connector certifies
warrant-status and provenance, **not facts of the world** (SPEC §7). State your
consumer's claim at that ceiling and no higher.

## Verifying someone else's verdict (offline)

```python
from connector.verdict import verify_artifact
report = verify_artifact(artifact, warrant_form)   # re-computes + checks digest + signature
assert report["ok"]
```

No server is contacted. Open reference + artifact + warrant-form is all it takes.
That is the anti-monopoly guarantee in code: the trust lives in the
re-computation, not in any protocol that carried it.
