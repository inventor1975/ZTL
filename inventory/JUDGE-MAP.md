# The judge, part by part — which part is a theorem (2026-11-27)

The curator: «Мы всегда делали ZTL судью так, что каждая его деталь — теорема… пройдёмся, проверим, так как мы
дорабатывали ZTL и могло что-то измениться». This map replaces, for the JUDGE, the tiers of `THEOREM_INVENTORY.md`
(last edited 2026-09-24, before the pure branch, zcertify's later tranches, zdiagnose and the zfl layer of 2026-11-24).

The judge's closure: the 38 Python modules imported from `ztljudge`, `zfl`, `znumjudge`, `zbackward`, `zdiagnose`,
`zcertify`. Searched for a twin: module names AND concept words in all `lean/*.lean` (233 files) and VR-ZTL's
`ZTL/*.agda` (85 files), plus every module's own references. "Not found" below means not found there.

## Tiers

| tier | meaning |
|---|---|
| **A** | a Lean theorem (empty axiom list) AND a bridge in `run_all` where the KERNEL computes the answer on a battery and the Python answer must equal it |
| **B** | the RULE is a Lean theorem; the Python applies it; the tie is a Python stand (measured), not the kernel |
| **C** | measured only (a stand), no theorem |

## The map

| part | Python | Lean | bridge / stand | tier |
|---|---|---|---|---|
| connectives, Z, tables | `ztl.py` | `ZTL.lean`, `ZGrade.lean` | `bridge.py` (141 answers) | A |
| forced outcome, dispositions | `ztljudge._forced` | `ZForced.lean`, `Receipt.lean`, `LabelExact*.lean` | `bridge.py`, `test_zjudge2lean.py` | A |
| stable grounding, lfp, phase n | `fixedpoint.py`, `zread.py` | `ZGround.lean`, `ZRead.lean` | `bridge.py` | A |
| passport: stipulation theorem | `zpassport.py` | **`ZStipulate.lean` (27.11)** | **`zpassport_lean_bridge.py`** — 141 models, 129 systems | A |
| passport: kinds by model count | `zpassport.passports` | (definitional: 0 / 1 / ≥2 models) | `zpassport_lean_bridge.py` | A (def.) |
| per-occurrence inputs in cycles | `zfl.cyclic_stable` | **`ZInputSubst.lean` (27.11)** `lfp_subst_mono` | **`zinputsubst_lean_bridge.py`** — 150 systems | A |
| defined rows written out | `zfl.inline_definitions` | `ZAlgebra.evalF_subst` (since 07) | **`zfl_inline_lean_bridge.py`** — 159 chains | A |
| what to check: minimal sets | `zbackward.backward` (enum + tree) | **`ZBackward.lean` (27.11)** | **`zbackward_lean_bridge.py`** — 555 cases × 2 routes | A |
| check this next | `ztljudge.next_check` | `ZBackward.lean` (size-1 sets) | `zbackward_lean_bridge.py` — 66 cases | A |
| diagnoses = minimal hitting sets | `zdiagnose.diagnose` | **`ZDiagnose.lean` (27.11)** | **`zdiagnose_lean_bridge.py`** — 150 + 5 | A |
| solver narrowing, linear hull | `znumsolve._hull` | **`ZHull.lean` (27.11)** (le/ge sound+exact, eq sound) | **`zhull_lean_bridge.py`** — 300 | A |
| solver: one unknown, quadratic | `znumsolve._parabola_pieces`, `_quadratic` | **`ZQuad.lean` (27.11)**: t² ≤ d inside, d ≤ t² outside, t² = d on a root; the piece −s ≤ 2qx+p ≤ s under ℚ's order laws (named); the sign of p + q√d (+ `ZParabola`: d < 0) | **`zquad_bridge.py`** — 400 (Python stand: the code's pieces = the theorem's intervals; the clamp holds) | B |
| linear system, affine RHS | `znumsolve._superpose` | `ZSuperpose.lean` | `zsystem_lean_bridge.py` (kernel refuses a wrong one) | A |
| numeric floor: narrowing heredity | `znum.py` | `ZNum.lean`, `ZNumCoherent.lean` | `test_certify.py` | B |
| certificates: bisection, monotone leaf, cases, implicit | `zcertify.py` | `ZCertify.lean`, `ZCases.lean`, `ZImplicit.lean` | `test_certify.py`, `zimplicit_lean_bridge.py`, `zbound_lean_bridge.py` | A/B |
| derivative certificates | `zaffinecert`, `zatancert`, `zexpcert`, `zmonocert`, `ztaylorcert`, `ztrigcert` | `ZAffine2`, `ZAtanCert`, `ZExp`, `ZMonoStep`, `ZJetRead`, `ZTrig10` | their `test_*` stands | B |
| integrals, functions | `zintegral.py`, `zfunc.py` | `ZIntegral*`, `ZTaylor*`, `ZTransfer`, `ZTrig*` | `test_zintegral.py`, `test_zfunc.py` | B |
| implicit roots, systems | `zimplicit.py`, `zsystem.py` | `ZImplicit`, `ZRootPar`, `ZKraw*` | `zimplicit_lean_bridge.py`, `zsystem_lean_bridge.py` | A |
| grade, refinements, reach | `zverify.py`, `zreach.py` | `NoGift`, `ZReach`, `ContextClosure` | `zverify.py`, `test_zreach.py` | B |
| logical time | `ztime.py` | `ZTime.lean` | `ztime.py` | B |
| degrees (Fréchet) | `zfrechet.py` | `ZDegrees.lean` | `zfrechet*.py` | B |
| degrees, exact LP | `zdegree.py` | `ZLP.lean` (weak duality: a dual certificate bounds the optimum) — zdegree checks its primal and dual certificates in Python | `zdegree.py` | B |
| receipt record | `warrant_receipt.py` | `Receipt.lean` | `test_warrant_receipt.py` | B |
| strict bound = gap | `zgap.py` | `ZNum.lean` (cited) | `test_*` | B |
| solver: elimination over equalities (x, x² as columns), refutation 0 = c ≠ 0 | `znumsolve._solve_monomial_system` | **`ZElim.lean` (27.11)** `row_comb_zero`, `refutation_sound`: every derived row is a consequence | `test_quadratic.py` (the plot) | B |
| solver: a disjunction of equalities of one unknown | `znumsolve._disjunction_pieces` | **`ZElim.union_sound`** + the alternatives' own rules (`ZQuad`, `_exact_eq`) | `test_*` | B |
| solver: `name == E`, E exact (a Fraction or p + q√d) | `znumsolve._exact_eq`, `znum.QSqrt` | **`ZQuad.qsqrt_sign_pos`** (the sign of p + q√d, opposite signs) | its stand | B |
| solver: degree ≥ 3, Sturm root isolation | `znumsolve._upoly_roots` → `znum._real_roots` | Sturm's theorem not proved; per INSTANCE: every gap between the brackets is root-free by a `ZNone.chk` certificate (overlapping bisection, Horner interval leaves), `chk_sound` (zero axioms) | **`zsturm_lean_bridge.py`** — 60 polynomials, 89 gap theorems by `decide +kernel`; a forged leaf refused; RATIONAL roots: 15 polynomials, the identity p = Π(x − r)^m·q by `identX` + q's gaps, 50 theorems, closed by **`ZRootFactor.root_factor`** | A (per instance) |
| solver: rank-many (Cramer + Sturm on the parameter) | `znumsolve._solve_rank_many` | per-instance: `zbound_lean_bridge.py` (Bareiss) | stands | B |
| exact logarithms | `zlogexact.py` | **`ZExpAdd`…`ZExpAdd5` + `ZLnMul` (27.11)**: exp(x + y) = exp x · exp y on VR's reals (the law `ZExpLaw` had left open as 'the hardest'), hence ln(xy) = ln x + ln y, ln 1 = 0. Hermite–Lindemann is NOT used by any verdict (`sign()` reads proved brackets otherwise) | **`zlogexact_lean_bridge.py`** — 309 factorisations (kernel product), 200 quotient splits | A |
| power series (Bessel, Kelvin), at a point | `zseries.point` | **`ZAltSeries.lean` (27.11)**: an alternating series with non-growing terms — every later partial sum and the limit lie between S_k and S_{k+1} (`alt_bracket`, `limit_in_bracket`); terms do not grow once ρ_k ≤ 1 and ρ non-increasing (`ratio_decreasing`) | **`zseries_bridge.py`** — 144 points × 12 functions (premises at k, 300 later sums inside) | B |
| power series over an INTERVAL (Taylor with the D2 bound) | `zseries._taylor2`, `_abs_series_bound` | **`ZPowTaylor.lean` (27.11)**: Taylor for a monomial (`taylor_mono`, no calculus), for every partial sum (`taylor_sum`), the halving tail (`tail_halving`); the monotone branch: **`ZMonoTaylor.lean`** `mono_up`(`_right`) — a derivative floor m > 0 and the Taylor bound give f(a) ≤ f(x) ≤ f(b), no mean value theorem. The clamp \|J_n\| ≤ 1 REMOVED (27.11, curator): not proved, so not used | **`zseries_interval_bridge.py`** — 48 intervals × 6 functions | B |
| Leibniz rule for limits | `zleibcert.py` | `ZLeibniz.lean` (`leibniz_low/high`; zleibcert checks its premises) | via `test_zintegral.py` | B |
| modal layer (completions, □/◇) | `zmodal.py` (used by `zverify`) | `ZGround.evalS` — the same three-way reading | **`zmodal_lean_bridge.py`** — 400 | A |
| naive sets | `znaive.py` | the grounding is `ZGround.lfp` (and the passport, `ZStipulate`); the translation spec → system is checked by its independent oracle (`znaive.oracle_check`) | **`znaive_lean_bridge.py`** — 120 universes, 698 cells, Python lfp = kernel lfp; `test_znaive_hinnion.py` | A (grounding) + oracle (translation) |
| affine forms | `zaffine.py` | `ZAffine.lean` (cited by zintegral) | `test_affine.py` | B? |
| the formula parser (text → formula) | `ztljudge.formalize` | a translation: checked by round trip, not proved | **`zparse_roundtrip.py`** — 3000 × 3 printers, 9 refusals, precedence + LEFT-associative → | round trip |
| the ZFL document layer itself (validation, rows, routing to the judges) | `zfl.run`, `zfl.validate` | orchestration, not a rule: every instrument it routes to is tied above; its behaviour is pinned by `test_zfl.py` and the judge's sweep fingerprint (`conformance/judge_table.py`, 184k verdicts) | stands | conformance |
| the book's tables | `zbook.py` | `EpochBoundary.lean` (part) | `zbook.py` | C |
| the Python refusal layer | `zpy.py` | — | `test_zpy.py` | C (not logic) |

## What changed today (2026-11-27)

Seven Lean modules, all on the empty axiom list, each tied to its Python by a kernel bridge in `run_all`:
`ZBackward`, `ZDiagnose`, `ZStipulate`, `ZInputSubst`, `ZHull` (+ `next_check` and `zfl.inline_definitions` tied to
existing theorems). Four of the parts were MEASURED-only before (zbackward, zdiagnose, the stipulation theorem,
cyclic_stable's first return), one was untied (inline vs `evalF_subst`), one untested as a rule (`_hull`).

## Where the work is

Nothing on the judge's path is measured-only any more. Named premise left (a theorem of analysis, not of ZTL):
1. `_solve_rank_many`: per instance only (Bareiss certificates in `zbound_lean_bridge.py`), no general theorem.
(The former premise |J_n(x)| ≤ 1 of `zseries` is gone: the clamp was removed on 27.11 — the reading is the proved
enclosure alone; run_all ALL GREEN after it.)

## Agda (VR-ZTL, 2026-11-27, the curator: «после всего леан ещё и в Агда»)

Carried the same day, `--safe --without-K --exact-split`, `tools/guard.sh` green, rows in `Crosswalk.tsv`:

| Lean | Agda | note |
|---|---|---|
| `ZBackward` | `ZTL/ZBackward.agda` | whole |
| `ZDiagnose` | `ZTL/ZDiagnose.agda` | whole |
| `ZStipulate` | `ZTL/ZStipulate.agda` | whole |
| `ZInputSubst` | `ZTL/ZInputSubst.agda` | whole |
| `ZHull` (+ `ZLP.OMul`, `ZSuperpose`'s ends) | `ZTL/ZHull.agda` | whole |
| `ZElim` | `VR/Numbers/ZElim.agda` | whole (under VR/: the layer rule — ZTL/ may not import VR) |
| `ZQuad` | `VR/Numbers/ZQuad.agda` | whole; cancellation-free encoding (4q·f + p² = t² + 4qc) |
| `ZRootFactor` | `VR/Numbers/ZRootFactor.agda` | whole; CF laws as module parameters |
| `ZAltSeries` | `VR/Numbers/ZAltSeries.agda` | over any OCR; `limit_in_bracket` not yet (Agda has no `rle` on VR's reals) |
| `ZPowTaylor` | `VR/Numbers/ZPowTaylor.agda` | whole, over any OCR (mul-nonneg, sq-nonneg as laws) |
| `ZMonoTaylor` | `VR/Numbers/ZMonoTaylor.agda` | whole, over any OCR; the Archimedean step a hypothesis |
| `ZExpAdd`…`ZExpAdd5`, `ZLnMul` | — | wait for `ZExp`, `ZRealExp`, `ZLn`, `ZExpLaw` in Agda (not ported before today) |

The judge's older machinery and the numeric floor (~100 modules) remain Lean-only, as before today.
