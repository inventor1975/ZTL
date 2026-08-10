Final pass. Fetching CXI and closing the two literature gaps.

# F-03D — FINAL SOTA DELTA AND FALSIFIABILITY CHALLENGE

## 1. SCR-11 — procedural correction accepted

```
POST_HOC_DEFINITION_CHANGE                    = FALSE
EXTERNAL_DEFINITIONAL_CARVEOUT_PERCEPTION_RISK = REAL
FALSIFIABLE_OPERATIONAL_TESTS_REQUIRED         = TRUE

```

**Correction accepted, with one disclosure.** I never read frozen A–E; I worked from the ten-point boundary summary supplied at the start of Pass 1. My inference that definitions had been tightened was drawn from the *sequence of my own corrections*, not from evidence about the artifacts. That inference was unsound — a tightening of my reading is indistinguishable, from where I sat, from a tightening of the definitions, and I asserted the latter without grounds. **SCR-11's historical premise is withdrawn as unfounded.**

Note the asymmetry that remains: I am accepting `POST_HOC_DEFINITION_CHANGE = FALSE` on the owner's representation, not on inspection. An external reviewer will not accept it on that basis either. It is verifiable — the frozen A–E commit timestamps precede the first SOTA pass — and **that verification should be produced, not asserted**, since the carve-out perception risk survives regardless.

---

## 2. CXI — arXiv:2607.06000 (7 July 2026), full text reviewed

**Verdict: NOT a meaning-admission neighbor. The shared word** **`admission`** **does not create equivalence.**

CXI's operative object is **a structured side-effect action at a mediated sink**. Three authorities — field authority, exact-effect authorization, invocation authority — must bind to the same canonical action manifest.

The paper draws the boundary itself, and draws it against meaning:

> "CXI does not judge whether the effect is desirable; it enforces that the admitted effect matches the exact effect trusted validator code authorized."

> Non-goals: "Task quality, validator completeness, provider internals, external exactly-once delivery, and complete transformer-level noninterference are separate obligations."

| test finding status                              |                                                                                                                                                                                                                                                                                                                                          |                                                     |
| ------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------- |
| institutional admission of authoritative meaning | admits effects, not meaning; semantic task quality is an explicit non-goal                                                                                                                                                                                                                                                               | `NOT_ESTABLISHED`                                   |
| action admission vs meaning admission            | **the distinction is the paper's own** — it enforces that policy decisions execute, not that they are correct                                                                                                                                                                                                                            | `NOT_ESTABLISHED` for meaning                       |
| semantic conservation                            | structural only: field→destination, effect→manifest, invocation→capability                                                                                                                                                                                                                                                               | `NOT_ESTABLISHED` (syntactic `PARTIAL`)             |
| warrant vs institutional judgment                | gate enforces; validators/humans decide field classification and acceptance criteria. Separation exists but is **enforcement-vs-policy**, not epistemic-conclusion-then-authorized-judgment                                                                                                                                              | `PARTIAL_EQUIVALENT`                                |
| issuance vs reliance                             | capability naming (sink, operation, budget, sequence state, idempotency token, expiry, snapshot, policy version); no institutional issuance act, no reliance state                                                                                                                                                                       | `NOT_ESTABLISHED`                                   |
| institutional currentness                        | policy epochs and trusted snapshots reject stale state; "does not address historical authority invalidation or downstream reliance correction beyond the immediate gate"                                                                                                                                                                 | `NOT_ESTABLISHED` (runtime `FUNCTIONAL_EQUIVALENT`) |
| cross-supplier preservation                      | **explicitly out of scope** — substituting providers "changes the trusted boundary assumptions"                                                                                                                                                                                                                                          | `NOT_ESTABLISHED`                                   |
| authority transferability                        | authority is manifest-bound and non-transferable by construction                                                                                                                                                                                                                                                                         | `FUNCTIONAL_EQUIVALENT` — conceded                  |
| **adverse evidence / provenance**                | **materially strong**: "Opaque data may only go into declared non-authority slots… If it later enters another agent, tool, bot, memory, or workflow that can create side effects, that boundary treats it as W again." Evidence is preserved for human review **without granting it executive authority**, and reentry resets provenance | `FUNCTIONAL_EQUIVALENT`                             |
| standing                                         | "no concept of standing, delegation chains, or reliance relationships beyond the immediate manifest"                                                                                                                                                                                                                                     | `NOT_ESTABLISHED`                                   |

**Material delta.** CXI's opaque-data-slot mechanism is the **strongest reviewed instance of evidence being carried without being promoted to authority** — functionally equivalent to the frozen "adverse/incomplete evidence remains visible rather than being promoted," and cleaner than SACM's `isCounter` because non-promotion is enforced structurally with provenance reset on reentry. **SCR-14 issued.**

---

## 3. Two literature gaps closed

### Hohfeld / institutional power — `PARTIAL_EQUIVALENT`, and it reaches further back than any system reviewed

Hohfeld (1913) separates **first-order** relations (right/duty, privilege/no-right) from **second-order** relations (power/liability, immunity/disability). A power is "the legal authority to change jural relations" — categorically distinct from a claim right, and not derivable from it.

This is the classical form of *logical warrant ≠ institutional authority*: establishing that a state of affairs obtains (first-order) does not confer the power to alter jural relations (second-order). Markovich's formalization and Lindahl's work make it computationally tractable. Critically, one reviewed source distinguishes the Sergot counts-as reading as "a Searlean conception of power rather than the Hohfeldian one" — so **two independent classical formalisms** occupy this ground.

**Effect: T5 (****`warrant ≠ consequential institutional judgment`****) is narrowed further, from** **`PARTIAL_EQUIVALENT`** **against SAB routing to** **`PARTIAL_EQUIVALENT`** **against a century-old formal jurisprudence with modern logical formalization.** The claim must not be stated as though the distinction is new.

### HITL institutional governance — `PARTIAL_EQUIVALENT`

Established: "human governance means the system cannot complete any high-risk action without human control"; the regulatory standard is "the delegation chain: every agent action must be attributable to a human authorizer who defined the scope of what the agent is permitted to do, with that authorization preserved in a tamper-evident audit record."

That is a functional equivalent of scoped, attributable, recorded authorization. **What the literature reports as unsolved** is precisely the frozen concern: "what decision options are provided to the human participants, what data is made available… whether the time… is sufficient, and what level of oversight, accountability and liability are attached to human-made decisions." The field names the gap; no reviewed source closes it.

**Effect: the human-judgment conjunct is narrowed but not occupied.**

---

## 4. Falsifiability — objective third-party tests

**Both tests are formulable.** Neither requires Veraxis terminology.

### S2 — INSTITUTIONAL\_ADMISSION\_OF\_AUTHORITATIVE\_MEANING

> **Test S2.** Given architecture *X*, exhibit a candidate proposition *p* whose **truth conditions are unchanged** but whose **institutional admissibility differs** between two states of *X*.
>
> - **PASS** (S2 established by *X*, claim killed): *X* contains a transition *T* such that (i) before *T*, *p* is representable and evaluable but not relied upon; (ii) *T* is performed by an identified authority under a recorded basis; (iii) after *T*, *p* is authoritative **for consumers other than the actor that produced it**; (iv) *T* can be refused while *p* remains true, and refusal is recorded with a reason.
> - **FAIL** (S2 not established): every admission in *X* is an admission of an action, an effect, an access decision, or a schema conformance — i.e. *p*'s admissibility is a function of its form or of a permitted operation, not of an authority's act over its content.
> - **INDETERMINATE**: *X* has a human approval step whose object cannot be determined from the reviewed material to be content rather than action.

Applied to the corpus: SAB/SEB **FAIL** (admission object is an action proposal). CXI **FAILS explicitly** — semantic task quality is a non-goal. OAP **FAILS**. VC 2.0 is the closest **INDETERMINATE→PASS candidate**: an issuer's act makes a *claim* authoritative for a third-party verifier, the claim's truth conditions are independent of the act, and issuance can be refused. **VC is a genuine partial PASS on S2** and must be treated as the live kill risk, not the runtime systems.

### T1 — CONSERVATION\_OF\_ADMITTED\_MEANING\_ACROSS\_HETEROGENEOUS\_IMPLEMENTATION\_SUBSTITUTION

> **Test T1.** Substitute a conformant implementation of any one component of *X* — different vendor, language, or runtime — while holding the admitted content fixed.
>
> - **PASS** (T1 established, claim killed): *X* provides a **check that fails** if the substituted implementation alters what was admitted, where the check is (i) computed over admitted content rather than over transport bytes, (ii) independent of the substituted component, and (iii) capable of distinguishing an equivalence-preserving re-encoding from a meaning-altering one.
> - **FAIL**: *X*'s only preservation guarantee is byte-identity, digest-identity, schema conformance, or syntactic match — all of which are broken by a legitimate re-encoding and satisfied by some meaning-altering transformations.
> - **INDETERMINATE**: *X* proves preservation for one fixed pipeline and is silent on substitution.

Applied: SEB **FAILS** — syntactic match, "cannot verify if the certificate's contract itself is semantically safe." CXI **FAILS** — structural binding, substitution explicitly out of scope. Catala is **INDETERMINATE** — mechanized preservation, one fixed pipeline. ISO 15489 is **INDETERMINATE** — authenticity across custody transfer is doctrinal, not a computable check.

**Falsifiability finding: both tests return PASS/FAIL/INDETERMINATE on third-party architectures without Veraxis vocabulary, and both return FAIL or INDETERMINATE on every reviewed system except VC 2.0 on S2.** The carve-out is therefore **not unfalsifiable** — which is the substantive answer to SCR-11's surviving concern.

---

# `RESIDUAL_CLAIM_NARROWED`

**Not** **`SURVIVES`****,** as Pass 3 concluded. Two findings this pass move it:

1. **VC 2.0 is a partial PASS on Test S2.** An issuer's official act renders a claim authoritative for a third party, independent of the claim's truth conditions, refusable, and revocable. That is meaning-admission in functional substance, for credential-shaped content. It is not general — VC admits *claims about subjects*, with no conservation guarantee across transformation and no downstream reliance correction — but S2 can no longer be reported as unoccupied. **This is the correction to Pass 3, and it is the reason the status changes.**
2. **CXI occupies the adverse-evidence conjunct** more cleanly than anything previously reviewed, and **Hohfeld occupies the warrant/authority distinction** more fundamentally than any system.

**What remains after narrowing.** T1 is unoccupied: no reviewed system provides a substitution-surviving check computed over admitted content rather than over bytes or schemas. S2 is *partially* occupied by VC for credential-shaped claims only. The conjunction of S2 with T1 — admitted meaning that survives heterogeneous implementation substitution as *meaning* — is unoccupied in the reviewed corpus.

**Not** **`KILLED`****:** no reviewed system passes both tests, and VC's S2 pass is domain-bounded. **Not** **`INDETERMINATE`****:** the tests are operational and were applied.

---

## New SOTA\_CHALLENGE\_RECORDs

**SCR-14 — against the adverse-evidence conjunct. Severity: HIGH.** CXI opaque data slots carry evidence without authority and reset provenance classification on reentry into any side-effect-capable boundary. *Required action: withdraw adverse-evidence non-promotion as a claimed contribution; cite CXI and SACM.*

**SCR-15 — against** **`warrant ≠ institutional judgment`****. Severity: HIGH.** Hohfeld's power/liability second-order relations, with modern formalizations, establish this distinction as foundational jurisprudence. *Required action: cite as prior art; do not present as a contribution.*

**SCR-16 — against S2, the primary residual claim. Severity: HIGH — this is the live kill risk.** W3C VC 2.0 partially passes Test S2. *Required action: state precisely what meaning-admission does that credential issuance does not — candidate deltas are (i) admitted content that is not a claim about a subject, (ii) conservation of admitted content under transformation, (iii) downstream reliance correction on supersession. If none survives scrutiny, S2 must be withdrawn and only T1 retained.*

**SCR-17 — procedural. Severity: MEDIUM.** `POST_HOC_DEFINITION_CHANGE = FALSE` is accepted on representation, not inspection. *Required action: publish the frozen A–E commit coordinate and timestamp alongside Test S2 and Test T1, so a third party can verify definition-precedence and apply the tests without trusting either party.*

---

**Recommended maximum public wording (final).**

> Two operational tests are stated in advance and applied to the reviewed corpus. On Test T1 — conservation of admitted content across heterogeneous implementation substitution, checked over content rather than bytes or schemas — no reviewed system passes. On Test S2 — institutional admission of content as authoritative for third parties, distinct from authorizing an action — W3C Verifiable Credentials partially passes for credential-shaped claims; every reviewed runtime system fails, several by explicit non-goal. Runtime authorization currentness, certificate-bound execution authority, transaction-scoped credentials, separation of duty, record authenticity over time, evidence carried without authority, and the distinction between logical warrant and institutional power are established prior or concurrent art and are not claimed.

Frozen 03 untouched. Standing state unchanged: `READY_FOR_DIAGNOSTIC_EXECUTION_PENDING_INDEPENDENT_REVIEW_AND_OWNER_PERSISTENCE`.

Sources:

- [Context-to-Execution Integrity for LLM Agents (arXiv:2607.06000)](https://arxiv.org/html/2607.06000)
- [Understanding Hohfeld and Formalizing Legal Rights — Markovich](https://link.springer.com/content/pdf/10.1007/s11225-019-09870-5.pdf)
- [Hohfeld Relations and Spielraum for Action — Lindahl](https://dialnet.unirioja.es/descarga/articulo/8850523.pdf)
- [Hohfeld's Jural Relations](https://www.thomasalspaugh.org/pub/fnd/hohfeld.html)
- [Humans in the Loop: Challenges of Human Participation in Automated Decision-Making](https://www.frontiersin.org/research-topics/29074/humans-in-the-loop-exploring-the-challenges-of-human-participation-in-automated-decision-making-systems)
- [Human in the Loop: AI Compliance](https://www.kiteworks.com/regulatory-compliance/human-in-the-loop-ai-compliance/)
- [W3C Verifiable Credentials Data Model 2.0](https://www.w3.org/TR/vc-data-model-2.0/)
- [Sovereign Execution Broker (arXiv:2606.20520)](https://arxiv.org/html/2606.20520v2)
- [Sovereign Assurance Boundary (arXiv:2606.11632)](https://arxiv.org/html/2606.11632)