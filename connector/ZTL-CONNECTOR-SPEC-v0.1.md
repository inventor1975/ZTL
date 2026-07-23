# ZTL Connector — Specification v0.1 (word-first, for review)

*Status: DRAFT for curator read. No code until this is accepted. 2026-07-23.*

## 0. What the connector is — and is not

The **ZTL Connector** is the standard socket a consumer protocol or application
plugs into to obtain a **ZTL trust-signature**: submit a claim in warrant-form,
get back a signed, independently re-computable verdict.

**In scope (this is the deliverable):**
- the warrant-form input contract,
- the judge (the one ZTL kernel),
- the verdict artifact (the portable trust-signature),
- independent verification,
- the conformance harness that proves a consumer's local implementation matches
  the reference semantics.

**Out of scope (the *protocol / federation* layer that sits ABOVE the connector —
Veraxis's job or a later stage):** the multi-judge tree, BFT consensus, the
ledger database, delegation-with-ceiling, the domain adapter (e.g. tax
rules → atoms), and any client requirements. The connector is self-sufficient
underneath all of that.

**Derived from two real instances, not speculation:**
- **MindReef-ZTL** (live): rule_id/version/hash + reference evaluator + shared
  fixtures + native re-implementation → this is connector **instance #1**.
- **Veraxis** (reference protocol): the warrant-form → signed re-computable
  verdict shape.
Two concrete consumers justify the abstraction; recognition-discipline holds.

## 1. Input — the warrant-form

A single JSON object:

```
claim  : string   — a ZTL formula over named atoms (e.g. "cleared & ~flagged")
rule   : { id: string, version: semver, hash: sha256-hex }
atoms  : [ { name       : string,
             value      : "T" | "F" | "Z",   # Z = the mark: unverified / unknown ground (default-deny)
             provenance : string,            # audit-only; NEVER judged
             admissible : "yes" | "no" } ]    # "no" ⇒ coerced to Z (fail-closed)
```

**Atom model — true to the kernel.** In the ZTL kernel an atom's marking is
*one* value from `{T, F, Z}`. `Z` **is** the mark — it means the ground is
unverified/unknown, and it is default-deny (an atom absent from `atoms` is `Z`,
never on credit). There is no separate "mark" field; `Z` carries that role.

**Fail-closed (the MindReef lesson, non-negotiable).** Before judging, the
connector coerces to `Z` any atom whose `value ∉ {T, F}` (unknown / missing /
malformed) **or** whose `admissible == "no"`. Unrecognised ground is never waved
through — it is treated as unverified.

**`provenance` is audit-only.** It records where the value came from (source id,
method). The judge never reads it. It travels for the record, not the verdict —
this is the honest boundary (see §7).

## 2. The judge — the one kernel

`ztljudge.judge(claim, marking) → verdict record`. Pure, deterministic, imports
nothing upward. Real signature (from code): `marking` is `{atom_name: value}`
with values in `{T, F, Z}`; unspecified atoms default to `Z`.

Output record fields:

```
verdict      : "T" | "F"                              — the truth-check result
grade        : "hereditary" | "sound" | "until-verification"   — the warranty ladder (zverify)
disposition  : "EARNED" | "REFUTED" | "ON CREDIT" | "OPEN"
why          : string                                 — plain-language reason
unverified   : [atom names still on Z]                — the weak link(s)
```

Disposition rule (exactly as the kernel computes it):
- `grade == hereditary` & `verdict T` → **EARNED** (grounded; marks irrelevant).
- `grade == hereditary` & `verdict F` → **REFUTED** (false regardless of marks).
- `grade != hereditary` & `verdict T` → **ON CREDIT** (true only while an
  unverified link holds; if it flips, the claim can die).
- otherwise → **OPEN** (not established; a mark actually matters — verify it).

The warranty ladder is `hereditary ⟹ sound ⟹ until-verification`; the judge
keys off *hereditary vs not*. `EARNED`/`REFUTED` are the only terminal
dispositions.

## 3. Output — the verdict artifact (the portable trust-signature)

```
input_digest   : sha256 of the RFC-8785-canonicalized {claim, rule, atoms}
rule           : { id, version, hash }
kernel_version : string      — which reference judge produced this
verdict, grade, disposition, why, unverified   — from §2
signature      : { scheme: "ed25519+ml-dsa", value: ... }   — crypto-agile
```

**Re-computability is the source of trust — not the signature.** Given the
warrant-form input plus the open reference at the pinned `rule.version`, anyone
re-runs the judge and MUST get the same `verdict`/`grade`/`disposition`. The
**signature attests only WHO ran it** (non-repudiation of the signer); it is not
where the truth lives. This is what makes the trust *protocol-independent*
(§5).

**Signature scheme.** Crypto-agile; default **hybrid Ed25519 + ML-DSA
(Dilithium, FIPS 204)**. `input_digest` and the artifact are hashed with
**SHA-384**. The scheme name travels in the artifact so a verifier knows what to
check.

## 4. Verification + the conformance harness

**Verify one artifact (anyone, offline):**
1. re-canonicalize the warrant-form, recompute `input_digest` — must match;
2. re-run the reference judge at `rule.version` on the input — verdict must match;
3. check the `signature` against the signer's public key.
No protocol server is contacted; open reference + artifact suffice.

**Prove a consumer's native implementation conforms (the MindReef pattern,
generalized):**
- one **shared fixture set** (JSON): input warrant-forms + expected verdict
  records, covering positive, adversarial, and fail-closed (unknown / null /
  empty / inadmissible) cases;
- the **reference evaluator** (Python) runs the fixtures → must match;
- the **consumer's native** implementation runs the *byte-identical* fixtures →
  must match;
- `rule.hash` is pinned in the fixtures, the reference, and the consumer, and
  asserted equal at check time.
Both sides matching the shared expected outputs *is* the cross-language /
cross-protocol agreement check.

## 5. Invariants — anti-monopoly, in code

1. The connector defines **semantics + artifact + verification**, NOT transport,
   packaging, or governance. Those live in the protocol ABOVE (Veraxis, or
   another) and are pluggable.
2. A verdict is verifiable **without any protocol's servers** (open reference +
   artifact only). Trust lives in the re-computable verdict and the open
   reference — **not in Veraxis**.
3. The signature scheme is **swappable** (crypto-agility).
4. Therefore any protocol *implements* the connector; **none owns it.** No place
   for a monopoly to settle — this is "against the law" answered in code.

## 6. Drop-in — how a consumer adopts (MindReef-ZTL, generalized)

1. Pin `rule.id` / `version` / `hash`.
2. Implement the rule natively as a **pure function** (or call the reference).
3. Run the shared fixtures in your own CI.
4. Map the **logical verdict → your product's transition** — the consumer owns
   this institutional mapping; the connector does not.

"Drops easily into MindReef or something else" = these four steps and nothing
more.

## 7. Claim ceiling — the honest boundary

The connector judges by the **submitted** atom markings, not by the truth of the
atoms. It certifies **warrant-status and provenance, not facts of the world**
(the oracle boundary). A verdict proves the logical disposition *given* the
inputs; it does not prove the inputs are true, complete, or authoritative. This
ceiling is stated in the artifact's meaning and must not be overstated in any
consumer's claims.

## 7a. Input bounds (DoS guard)

The connector takes untrusted warrant-forms, so the wire is bounded (this is
separate from §7, which is about the *world*). Two costs make bounds mandatory,
both measured: the warranty grade is **O(3^(distinct atoms))** (it scans every
completion of the Z-marked atoms — 14 atoms hung for >8s), and the claim parser
is recursive (~1000-deep nesting raised `RecursionError`). `warrant.validate`
therefore enforces, and rejects with a clean `WarrantError` (never hang/crash):

- `MAX_CLAIM_LEN` 1024 chars, `MAX_ATOMS` 64, `MAX_NAME_LEN` 128,
  `MAX_PROVENANCE_LEN` 4096;
- `MAX_DISTINCT_ATOMS` 12 in the claim (3^12 ≈ 5.3e5, sub-second) — the real cap;
- deep nesting is caught (`RecursionError → WarrantError`).

No code/SQL/shell injection surface exists: the parser is hand-written recursive
descent (no `eval`/`exec`), and there is no query or shell layer. Bad atom
*values* are fail-closed to Z (§1), not errors. The harness exercises all three
abuse classes as regression guards.

## 8. Locked decisions (the four forks, curator-accepted 2026-07-23)

1. **Mark dialect:** public warrant-form uses `value: "T"|"F"|"Z"` (Z = the
   mark). Internally mapped to `zverify`'s `'M'` at one tested point
   (`_grade_marking`), closing the historic grade bug.
2. **JSON canonicalization:** **RFC 8785 (JCS)** for `input_digest` — a
   standard, cross-language; not reinvented.
3. **`input_digest` scope:** canonicalized **{claim, rule, atoms}** in full — the
   verdict binds to both the exact input and the rule version.
4. **Signature role:** voucher / non-repudiation of the signer, **not** the
   source of truth (truth = re-computation). Stated in §3.

## 9. Artifacts to build (after this spec is accepted)

- this SPEC (done, in review);
- reference judge — `ztljudge` exists; tidy its interface to §2;
- warrant-form JSON schema (§1);
- verdict-artifact schema (§3) + signer/verifier (PQC-hybrid, §3);
- conformance harness + starter fixtures (§4);
- **MindReef-ZTL re-expressed as connector instance #1** (live proof it
  generalizes);
- drop-in guide (§6).

## 10. Legs of the voyage (checkpoint after each; nothing outward without word)

1. Close the four forks — **done** (§8, accepted).
2. This SPEC → **curator read.**  ← *we are here*
3. Schemas (warrant-form, verdict-artifact) + canonicalization.
4. Tidy `ztljudge` to the §2 interface + canonical mark dialect.
5. Signer / verifier (PQC-hybrid).
6. Harness + starter fixtures; reference green.
7. MindReef-ZTL as instance #1 — re-express the existing gate onto the connector.
8. Drop-in guide.
