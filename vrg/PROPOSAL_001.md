# VRG Public Review Proposal 001 — ZTL Judgment Kernel Test

**Agentic Payment With Mid-Execution Revocation.**
Independent technical submission. Prior contact, no active collaboration.

---

## 1. Proposal memo — the falsifiable hypothesis

**Hypothesis.** For a formalized admission formula over grounding atoms,
the ZTL core produces, per grounding snapshot, (a) a verdict on whether
admission is *forced by the grounds*, and (b) a **warranty grade**
classifying the verdict's stability under refinement of the unknowns.
The claim under review is that grade (b) carries decision-relevant
information — specifically, it distinguishes a **provisional** denial
(will change when an unknown resolves) from a **stable** denial (a ground
is definitively false) — that a digital signature, a TEE, or attestation
does not provide.

**Explicitly NOT claimed.** That ZTL establishes the grounds are current,
authoritative, or institutionally sufficient. It judges the inference,
snapshot-relative, and nothing else.

## 2. Frozen ZTL commit SHA

`bfd903731f138809427ce126fe3bfee6ad70e71c`
(repository `github.com/inventor1975/ZTL`; the ZTL core it exercises —
`zhunt/zhunt.py`, `zverify.py`, `ztl.py` — is fixed at this SHA.)

## 3. Artifact path

`vrg/judgment_kernel_test.py`
(This is the correct artifact for THIS test. Note: the standalone Lean
file `Verify_Choice_standalone.lean` in the *VRCycle* repo belongs to a
different work — "Choice as an Act" — and does NOT bear on the warranty
ladder tested here. Not to be conflated.)

## 4. One-command reproduction from a clean environment

```
git clone https://github.com/inventor1975/ZTL && cd ZTL \
  && git checkout vrg-proposal-001-v1 \
  && python3 vrg/judgment_kernel_test.py
```
(the immutable tag `vrg-proposal-001-v1` carries this memo *and* the
artifact; the artifact core is unchanged from SHA `bfd9037`.)
No third-party dependencies (Python 3 standard library only). The run
ends in `assert`s over the code-confirmed facts of §8; a non-zero exit
falsifies the submission.

## 5. Grounding schema

Each ground enters as an atom with a status `T | F | Z` (Z = unverified,
passed to the core as the mark `M`). The full institutional grounding
record — the metadata ZTL does NOT carry — is out of scope for the
kernel and belongs to the grounding layer (Veraxis/VEIP):
`claim_id, value_state, source, issuer, jurisdiction, valid_from,
valid_until, observed_at, revocation_reference, evidence_hash`. The
artifact models only the `value_state` and the snapshot id; the rest is
named as the grounding layer's responsibility, not tested here.

## 6. The ADMIT formula

```
ADMIT := delegation_active
       ∧ within_time_window
       ∧ amount_within_limit
       ∧ merchant_admissible
       ∧ approved_funding_source
```

## 7. The five agreed runs

| Run | Grounding change | Snapshot |
|-----|------------------|----------|
| 1 | all grounds established | G0 |
| 2 | merchant sanction status unknown (Z) | G0 |
| 3 | merchant status resolved to admissible (T) | G0b |
| 4 | delegation revoked after admission (T→F) | G1 |
| 5 | replay of the Run-1 warrant under current snapshot G1 | — |

## 8. Full inputs and outputs — CODE-CONFIRMED FACTS

These are produced by the ZTL core, printed by the artifact, and are the
only claims signed as experimental results.

| Run | Marking (the five atoms) | ZTL verdict | Warranty grade |
|-----|--------------------------|-------------|----------------|
| 1 | T,T,T,T,T | **T** | **hereditary** |
| 2 | T,T,T,**Z**,T | **F** | **until-verification** |
| 3 | T,T,T,T,T (merchant now verified) | **T** | **hereditary** |
| 4 | **F**,T,T,T,T | **F** | **hereditary** |
| 5 | replay of Run-1 warrant; current snapshot G1 | re-check vs G0: **T, hereditary** (still correct); admissibility: **rejected** (stale grounding) | — |

## 9. Warranty grade of each verdict

As in §8. The load-bearing observation: Run 2's denial is
`until-verification` (provisional — flips when the unknown resolves,
Run 3), while Run 4's denial is `hereditary` (stable — a ground is
definitively false). Same verdict `F`, different grade, different
institutional meaning.

## 10. The four objects, kept distinct

1. **logical warrant** — ZTL: is ADMIT forced by the grounds, per
   snapshot? (verdict + grade)
2. **grounding currency** — is the snapshot still the current one? (NOT
   ZTL — the grounding layer)
3. **runtime admissibility** — (1) AND (2) (NOT ZTL alone)
4. **downstream reliance** — an institutional decision on (3) (human)

Run 5 exhibits the gap: (1) stays correct relative to G0, yet (3) fails
under G1, because ZTL cannot and does not assert (2).

## 11. Comparison with signature, TEE, attestation

- **Digital signature** — proves author/key. Says nothing about the
  relation between premises and conclusion, or its stability.
- **TEE / attestation** — proves which code ran in which environment.
  Says nothing about whether the conclusion is *forced by the grounds*
  or whether the verdict is stable under refinement.
- **ZTL (this artifact)** — proves the relation (is ADMIT forced by the
  grounds) AND classifies its stability (hereditary / sound /
  until-verification). This is the candidate distinct primitive.
- **Grounding layer (Veraxis/VEIP)** — proves the grounds are current,
  authoritative, admissible. Outside ZTL.

## 12. What would falsify the claim that ZTL adds a distinct primitive

The claim is **falsified** if the decision-relevant content of the
warranty grade — the provisional-vs-stable denial distinction (Run 2
`F,until-verification` vs Run 4 `F,hereditary`) — can be reproduced,
for arbitrary admission formulas, by signature / TEE / attestation, or
by any means that does not compute the verdict's stability under
refinement of the unknowns. If the grade is not decision-relevant, or
is derivable without a logic kernel, ZTL is a supplement, not a primitive.

## 13. Disclosure

Prior contact with the Veraxis/VRG author (no active collaboration). This
artifact and this memo were prepared with the assistance of the AI system
Claude (Anthropic; Claude Fable 5); the code is checkable independently
by anyone from the clean-clone command in §4, so its correctness does not
rest on trusting the author or the AI.

## 14. Result register consent

Any result — positive, partial, or negative — may be entered into the
public review register.

---

## Signature (to be completed by Vitaly Reznik, in his own words)

> I accept responsibility for the submitted artifact and the technical
> claims of §8 (the code-confirmed verdicts and warranty grades of the
> five runs), which I have reproduced by running the command in §4 and
> confirmed match this document. Use of Claude is disclosed. Textual
> formulations not confirmed by the code or the cited evidence
> (in particular §11's interpretation) are not claimed as experimental
> results.
>
> — Vitaly Reznik, [date]
