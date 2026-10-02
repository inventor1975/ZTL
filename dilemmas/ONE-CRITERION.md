# One criterion, six quantum puzzles

*ZTL's stamp Z_PERMANENT — "no act can witness it" — read against six known quantum puzzles, 2 October 2026.*

## The claim, and its limit

In each of the six cases below, a classical line of reasoning runs into trouble. In cases 1–4 experiment refutes
it; in cases 5–6 the trouble is a theoretical dispute, not an experimental refutation. Each time the reasoning
leans on one step: it treats as a fact something that no act can witness. ZTL (Zero-Trust Logic) marks such an atom Z_PERMANENT and
never grants a conclusion that rests on it. So one rule flags the same kind of step in all six. Whether that step is THE culprit is exactly what each
debate is about; ZTL gives one consistent answer, not a neutral proof.

This is not new physics. ZTL produces no amplitudes: the quantum numbers (1/12, 2√2, the Born weights) are
computed from amplitudes in each stand, not by ZTL. The physics input — who can witness what — is a premise
taken from the physics, not derived. And the rule itself is a position: a realist (Everett, Bohm, Wallace,
Carroll) rejects "a fact is what some act can witness". ZTL does not win that debate. It shows that the six debates share one fork, and makes the choice explicit; the verdicts are machine-checked.

## The six cases

| # | Puzzle | The classical step that fails | The atom no act witnesses | ZTL verdict | Checked in the stand |
|---|---|---|---|---|---|
| 1 | Indistinguishable particles (counting) | "these are two different objects" | which bearer is which | the number of acts is earned, the number of objects is not; earned distinctions give the Bose–Einstein count | ZQuasi.lean (Lean, no axioms); indistinguishable.py: C(n+k−1, n) vs kⁿ |
| 2 | Hong–Ou–Mandel | add the probabilities of the two routes | which photon took which route | with a tag the routes are events (ceiling open); without, frozen | indistinguishable.py (I2), from amplitudes: P(coincidence) 1/2 with a tag, 0 without |
| 3 | Bell / CHSH | all four readings have values | the readings not made | "all four have values" frozen; the measured pair earned | bell.py: CHSH 2.000 for the literal figure-eight (Bell's theorem: no model where a part carries its own value exceeds 2); about 2.83 by Monte Carlo, 2√2 exactly, when the waves add |
| 4 | Frauchiger–Renner | chain the agents' conclusions | records erased by the Wigners' measurements | the chain is refuted only on the erased links; what was observed stays earned | wigner_friends.py, from amplitudes: P = 1/12, each statement's exception 0 |
| 5 | AMPS firewall | one observer holds both entanglements | the joint witness | frozen if no act checks both (Harlow–Hayden), redeemable if one can (Oppenheim–Unruh) | firewall.py: the debate reduced to one question |
| 6 | Many worlds | count branches; "the other branches are real" | the number of branches; another branch | branch counting refused; "the other branch exists" and its denial both frozen | many_worlds.py: counting gives 1/(k+1), Born stays 1/3 |

Stands live in `ZTL/dilemmas/`: indistinguishable.py (cases 1 and 2), bell.py, wigner_friends.py, firewall.py,
many_worlds.py; case 1 is also proved in `ZTL/lean/ZQuasi.lean`.
Each one asserts every number it prints; run with `python3 dilemmas/<name>.py`.

## How sure

- For cases 4–6 a prediction of the verdict was written down and timestamped before the stand was run (notes
  in the author's private repository). All three held. Case 5's verdict is conditional (it depends on whether one
  act can check both entanglements), so "held" there means the reduction held, not that the dispute was decided.
  Cases 1–3 were measured, but no prediction was recorded first.
- None of these tests is blind. The author of the stands knew the literature. So each result confirms a known
  resolution; none discovers one.
- What ZTL adds is the bookkeeping. It shows which premise each conclusion rides on and whether some act could
  still settle it. That no act ever can is the physics premise ZTL carries; ZTL does not show it.

## Where it stands among known views

- Case 1: Krause's quasi-set theory and the "quasets" of Dalla Chiara and Toraldo di Francia take the
  cardinal as given; Holik (2011) argues that particle number itself can be undefined. ZTL's narrower point
  is that the count of acts is earned while the count of objects is not, and this follows without a
  primitive quasi-cardinal (Krause's qc).
- Case 2 is Feynman's rule, and the quantum eraser.
- Case 3 is Peres (1978): "unperformed experiments have no results".
- Case 4 is close to Brukner (2018), Bong et al. (2020) and Di Biagio & Rovelli (2021), who hold that facts
  are stable only while their record holds.
- Case 5 is the line from Susskind's complementarity through Harlow–Hayden.
- Case 6 agrees with Wallace in refusing naive branch counting and with Vaidman on self-location. Wallace,
  a realist, affirms the other branches that ZTL leaves frozen.

ZTL sides with the operational reading in cases 1–4 and 6, for one stated reason; in case 5 it does not decide.

---
Vitaly Reznik. Prepared with Logik (Claude Opus 5.5, an AI assistant); the stands, measurements and this note
were produced in a working session with the author, who directed the line of inquiry.
