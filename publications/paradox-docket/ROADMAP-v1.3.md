# Paradox Docket v1.3 — the cases and their status

The working draft is `paradox-docket-EN-v1.3-draft.md`. The curator's decision (2026-10-28): v1.3 is published once,
when every case below has its machine-checked account. One case = a Lean file (or theorems in an existing one) on
the empty axiom list, the stand (if any) kept as the measurement, and the paper's paragraph rewritten from the
theorems. Status: LEAN = theorems exist (named), STAND = only an executable stand, TODO = neither.

| Case | Status | Where |
|---|---|---|
| Liar, barber, Grelling, Russell's cell (one equation) | LEAN | `Facts.lean` liar_period2; `ZTime.lean` liar_not_completable |
| Jourdain / crocodile (period 4) | LEAN | `Facts.lean` carousel_no_fp, carousel_period4, crocodile_deal_void |
| Odd 3-cycle / even 2-cycle (the parity law) | LEAN for n = 2, 3 | `Facts.lean` odd3_no_model, even2_has_model — the general parity law: TODO |
| Curry | LEAN | `Facts.lean` curry_homeless |
| Truth-teller, Russell's twin, sameness | check | `Agrippa.lean` (truth-teller as a chosen stop) — verify it covers the docket row |
| Strong liar, revenge, Henkin (INTRINSIC) | check | `ZTL.lean` mentions revenge — verify; Henkin: TODO |
| Yablo (truncated) | LEAN | `Facts.lean` yablo3_unique; `ZYablo.lean` |
| Theseus title contest | STAND | `dilemmas/theseus.py` |
| Agrippa | LEAN | `Agrippa.lean`, `AgrippaNet.lean`, `AgrippaZ.lean` |
| Contingent liar (§4.7) | check | `Surprise.lean` liar_when_exam_today is an instance; general form: TODO |
| Surprise exam | LEAN (2026-10-28) | `Surprise.lean`, 11 theorems |
| Sorites | STAND | `dilemmas/solved/sorites/` |
| Lottery | STAND | `dilemmas/lottery.py` |
| Berry | STAND | `dilemmas/berry.py` |
| Moore | STAND | `dilemmas/moore.py` |
| Omnipotence stone (§5.1) | STAND | `dilemmas/omnipotence.py` |

Each case also gets a literature check (a Sonnet fork) before its paragraph is rewritten: what is known, what the
theorems add, the first objection to answer.
