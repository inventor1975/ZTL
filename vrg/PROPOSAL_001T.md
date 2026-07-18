# VRG Proposal 001-T (DRAFT — NOT SENT) — The Temporal Addendum

**Status: prepared in advance, held until Proposal 001 receives its
boundary review. Not sent; the curator decides if and when.**

Extends Proposal 001 (the ZTL Judgment Kernel Test). Everything below is
reproducible from the public repository; nothing here modifies 001.

---

## 1. What changed since 001

The warranty ladder that 001 exercised statically now has a measured and
partially machine-checked **temporal semantics** (expedition E24 + Lean
`ZTime.lean`, empty axiom list): logical time whose only clock is the
arrival of ground — one tick = one verification resolving an unknown.

The mapping onto VRG's own vocabulary is direct:

| VRG term (001 / Veraxis) | Temporal-layer object |
|---|---|
| grounding record | the **chronicle**: verdict + warranty grade per tick |
| snapshot-relative warrant (the R5 lesson) | warrant = (verdict, grade, snapshot, tick) — staleness is now a formal event, not an incident |
| runtime admissibility | verdict at the current tick (grade: until-verification) |
| logical warrant | sound — agrees with every completion of the unknowns |
| **downstream reliance** | **hereditary** — machine-checked license: NO verification path can revoke it (Lean: `hereditary_absorbing`, empty axiom list) |
| verification economics (ICAC-adjacent) | `settled_at` / `checks_saved`: the tick after which every remaining check buys nothing |

Demonstration: `usage/car.py` — three ZFL documents with a verification
timeline; the core answers "which checks can be skipped, and when can
one stop paying" (measured: 3 checks saved on a first-tick failure; 2
checks saved by verifying the selector — *which world am I in* — first).

## 2. The falsifiable claim of this addendum

For an admission formula over grounding atoms with a declared timeline
of verifications, the core produces a **chronicle** whose grade
trajectory carries decision-relevant information beyond 001's static
grades: specifically (a) the earliest tick at which the verdict becomes
revocation-proof under further verification (`settled_at`), and (b) the
count of declared checks that buy no information after that tick
(`checks_saved`). Falsifier: exhibit a chronicle where a check
performed after `settled_at` changes the verdict — by
`hereditary_absorbing` (machine-checked) this is impossible, so the
falsifier would have to break the Lean theorem's premises, which would
itself be reportable.

## 3. The honest boundary — and the co-design surface

E24 time is **monotone**: ground only arrives. Institutional time is
not: documents expire, registries are re-pledged, snapshots G0 → G1
take ground back — the exact R5 phenomenon. Probe E25 (`zexpire.py`)
measures what the anti-tick `expire` (ground → unknown) does:

1. **Hereditary is a warranty against future verification, not against
   the loss of ground.** Witness: a fully verified admission
   (T/hereditary) falls to F/until-verification on one expiry.
2. **Unrestricted expiry trivializes all warranties** (small theorem +
   census): if anything may expire at any time, the only verdicts with
   a shelf life are frames — assertions that read none of their
   grounds. Measured: 2,906 formulas, contentful survivors: 0.
3. **Scoped expiry prices the shortcut.** With a declared expiry scope
   (which atoms carry a clock), the "saved" checks are revealed as a
   loan against the expirable ground; paying for them before the clock
   runs out is expiry-insurance, and the core prices it (measured:
   the settled verdict survives the warranty's death iff the insurance
   was paid).

The consequence is the co-design proposal: **which atoms are expirable,
and on what clock, is not logic — it is institutional semantics**
(snapshot policy, document validity windows, consequence-absorption
capacity). The core supplies the machine: grades relative to a declared
expiry scope. The scope declaration is the institution's seat at the
table. This is the specific, bounded piece where Veraxis semantics
would drive the next operator of the core, rather than review a
finished one.

## 4. Explicitly NOT claimed

- Not claimed: that the temporal layer establishes currency or
  authority of grounds (unchanged from 001).
- Not claimed: a theory of non-monotone institutional time. E25 is a
  probe: one witness, one census, one priced scenario. The general
  expiry discipline (clocks, scopes, re-verification policy) is
  precisely the open co-design surface.
- Not claimed: novelty of three-valued temporal logic as such (LTL3
  exists). The claimed novelty is narrower: warranty grades as
  temporal quantifiers over the verification tree, with the absorption
  law machine-checked on the empty axiom list, and the grade
  trajectory (settling, demotion, expiry-insurance) as the
  decision-relevant object.

## 5. Reproduction

```
git clone https://github.com/inventor1975/ZTL && cd ZTL
python3 run_all.py            # 36 stands + Lean, ALL GREEN expected
python3 usage/car.py          # the chronicle demo
python3 zexpire.py            # the expiry probe
lean lean/ZTime.lean          # 7 objects, empty axiom list, ~0.6 s
```
