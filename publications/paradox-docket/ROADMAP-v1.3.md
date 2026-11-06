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
| §5.2 mathematical docket (2026-11-06): | | |
| Bertrand's chord | STAND | `dilemmas/bertrand.py` |
| Sleeping Beauty | STAND | `dilemmas/sleeping_beauty.py` |
| 1 + 2 + 3 + … = −1/12 | LEAN | `lean/ZZeta.lean`, `lean/ZZetaBridge.lean` |
| Grandi's series, Riemann's rearrangement | STAND | `dilemmas/series.py` |
| 0⁰ | STAND | `dilemmas/zero_power_zero.py` |
| Galileo's squares, Hilbert's hotel | STAND | `dilemmas/galileo.py` |
| Monty Hall | STAND | `dilemmas/monty_hall.py` |
| Simpson's paradox | STAND | `dilemmas/simpson.py` |
| 0.999… = 1 | STAND | `dilemmas/point_nine.py` |
| Skolem | STAND | `dilemmas/skolem.py` |
| Perron's "largest natural" | STAND | `dilemmas/perron.py` |
| Two envelopes, St. Petersburg | STAND | `dilemmas/expectations.py` |
| Zeno's Achilles, Gabriel's horn | STAND | `dilemmas/zeno.py` |
| Banach–Tarski | STAND | `dilemmas/banach_tarski.py` |
| Cantor's set of all sets | LEAN | `VR/SetsNaive/Cantor.lean` (VRCycle) |
| Burali-Forti | STAND | `dilemmas/burali_forti.py` |
| A theory's consistency polynomial (ground) | LEAN (finite face) | `lean/ZDiophantine.lean`, `dilemmas/diophantine.py` |
| Lottery: degrees and a declared threshold (§5) | STAND | `dilemmas/lottery.py` §5 (2026-11-05) |

Each case also gets a literature check (a Sonnet fork) before its paragraph is rewritten: what is known, what the
theorems add, the first objection to answer.

## Reader findings on unchanged text (Sonnet, 2026-10-31, during v1.2.1) — to settle in v1.3
- Lottery: "dies on the LAST stamp" is measured on five tickets but stated for the thousand; "closure over CREDIT" generalised from one example.
- Berry: "ends in E when every number has been named" — say how a march that never repeats ends (finite book).
- "§§21-23" does not match the paper's section numbering; "the eighth, acquitting verdict" is never defined.
- §7 "holds this paper's entire collection" — the no-loop cases (sorites, surprise, lottery, Moore, Berry) are not in the studio list; qualify.
- Moore: the 1-of-27 past-tense count and the Wittgenstein–Shoemaker–Heal attribution want a reference line.
