# One criterion, six quantum puzzles (v2)

*ZTL's stamp Z_PERMANENT — "no act can witness it" — read against six known quantum puzzles, 2 October 2026.*

## The claim, and its limit

In each of the six cases below, a classical line of reasoning runs into trouble. In cases 1–3 experiment refutes
it. In case 4 it is refuted by the outcome quantum mechanics predicts for a thought experiment that has not been run
with agents. In cases 5–6 the trouble is a theoretical dispute, not an experimental refutation. In each case the reasoning
leans on one step that treats as a fact something no act can witness. ZTL (Zero-Trust Logic) marks such an atom
Z_PERMANENT and never grants a conclusion that rests on it. So one rule flags the same kind of step in all six.

Read that claim narrowly.

- **What the table shows.** The column "the atom no act witnesses" is filled in from the physics, by an author
  who knew each standard resolution. Any refuted step could be relabelled this way after the fact. So the table
  shows that the rule can be applied consistently across six cases. It does not show that the rule found
  anything.
- **No negative control.** The six cases were chosen because they have operational resolutions. No case was
  tested where the rule could have picked the wrong step; Kochen–Specker contextuality and the PBR theorem are
  candidates. That test is still missing.
- **Not new physics.** ZTL produces no amplitudes. The quantum numbers (1/12, 2√2, the Born weights) are computed
  from amplitudes in each stand. Who can witness what is a premise taken from the physics, not derived.
- **The rule is a position.** A realist (Everett, Bohm, Wallace, Carroll) rejects "a fact is what some act can
  witness". ZTL does not win that debate. Under the rule, the six puzzles get one consistent answer. Without the
  rule, realists resolve them by different moves: nonlocality for Bell, many outcomes for Frauchiger–Renner,
  symmetrization for counting. So the six share one fork only for someone who takes the operational branch.

## Words

- **EARNED / REFUTED:** a claim is true / false on every future the facts can reach.
- **OPEN:** neither earned nor refuted yet.
- **Redeemable:** some act could still settle an atom.
- **Z_PERMANENT:** no act can ever settle it.
- **Frozen ceiling:** no reachable future ever earns the claim.
- **On credit:** the kernel's verdict is T, but it rests on an unverified atom, so the claim is not EARNED.
- **"Never grants":** a conclusion resting on a Z_PERMANENT atom is not EARNED. It may still be REFUTED by what was
  observed, as in case 4.

## The six cases

| # | Puzzle | The classical step that runs into trouble | The atom no act witnesses | ZTL verdict | What the stand checks |
|---|---|---|---|---|---|
| 1 | Indistinguishable particles (counting) | "these are two different objects" | which bearer is which | two clicks are earned, "one object" and "two objects" are each open, and "one or two" is not earned | lean/ZQuasi.lean (no axioms); indistinguishable.py: the earned distinctions number C(n+k−1, n), where n counts clicks |
| 2 | Hong–Ou–Mandel | add the probabilities of the two routes | which photon took which route | with a tag the routes are events (ceiling open); without one, frozen | indistinguishable.py (I2): the verdicts, and from amplitudes P(coincidence) 1/2 with a tag, 0 without |
| 3 | Bell / CHSH | all four readings have values; local causality and free settings stated through the hidden state | the readings not made; the hidden state | "all four have values" frozen; parameter independence, outcome independence and free settings each frozen; Bell's conclusion "not all three" only on credit, its ceiling frozen; the violation and no signalling earned | bell.py: the verdicts (B3, B4); CHSH 2.000 for the literal figure-eight (no local model exceeds 2, by Bell's theorem); about 2.83 by Monte Carlo (2√2 exactly) when the waves add |
| 4 | Frauchiger–Renner | chain the agents' conclusions | records erased by the Wigners' measurements | the chain is REFUTED by the predicted outcome (a thought experiment); its weak links are exactly the erased records (Z_PERMANENT); what was observed stays EARNED | wigner_friends.py: the verdicts; from amplitudes P = 1/12 and each statement's exception probability 0 |
| 5 | AMPS firewall | one observer holds both entanglements | the joint witness | frozen if no act checks both (Harlow–Hayden), redeemable if one can (Oppenheim–Unruh); undecided | firewall.py: the stamps under each repertoire; no number |
| 6 | Many worlds | count branches; "the other branches are real" | the number of branches; another branch | branch counting refused; "the other branch exists" and its denial both frozen | many_worlds.py: the verdicts; for a\|up⟩+b\|down⟩ with \|a\|² = 1/3, splitting the down-branch into k environment records makes branch counting give 1/(k+1) while Born stays 1/3 |

The stands are in `ZTL/dilemmas/`. Run each from the ZTL root with `python3 dilemmas/<name>.py`. Each asserts
the ZTL verdicts it prints, not only the quantum numbers. The same author wrote the stands and their expected
values, so the stands guard against regressions; they do not prove the verdicts correct.

## Caveats, case by case

- **Case 1.** Indistinguishability alone does not give Bose–Einstein statistics. Fermions give C(k, n), and
  classical identical particles with Gibbs's 1/N! give kⁿ/n!. Equal weighting of states is a further premise.
  What ZTL adds is narrower: the count of acts is earned while the count of objects is not, and this needs no
  primitive quasi-cardinal (Krause's qc). Counting acts still uses number.
- **Case 3.** Bell's theorem can be derived from local causality without assuming that unmade readings have
  values (Bell 1976; Maudlin). Bohmians keep definite values and drop locality. So "all four readings have values"
  is one reading of the failing step, not the only one. The B4 stand therefore also runs the other premises
  (Jarrett's parameter and outcome independence, and free settings). Each speaks of the hidden state, which no act
  witnesses, so each is frozen; and so is Bell's conclusion that one of them must fail. ZTL keeps only the
  observed pair, a violation with no signalling. It does not say which premise fails, nor grant that one does as a
  fact about nature. So case 3 is not one step: several premises are frozen, and ZTL picks none of them.
  Two causes are at work, and they are different. The dilemma's frozen ceiling comes from the physics premise
  that no act witnesses the hidden state. Separately, the theorem itself, written over these atoms, is also only
  on credit, because a propositional kernel cannot see the mathematics inside the atoms. That second one is a
  limit of the encoding, not a finding about Bell. "Earned" for the violation and for no signalling means that the
  stand marks them as measured. In a real experiment both are statistical inferences, with loophole assumptions.
- **Case 6.** Branch counting is a step that Everettians themselves reject. Wallace, a realist, affirms the other
  branches that ZTL leaves frozen.

## How sure

- **Predictions.** For cases 4–6 the verdict was predicted, written down and timestamped before the stand ran.
  The notes are in the author's private repository, not public. All three held. Case 5's verdict is conditional,
  so for case 5 "held" means only that the debate reduced to one question. Cases 1–3 were measured, but nothing
  was predicted first, except case 3's second stand (B4), whose verdicts were predicted and timestamped before
  it ran, and held.
- **Not blind.** The author knew the literature. Each result confirms a known resolution; none discovers one.
- **What ZTL adds.** It does the bookkeeping: which premise each conclusion rides on, and whether some act could
  still settle it. That no act ever can is a physics premise that ZTL carries, not something it shows.

## Where it stands among known views

- **Case 1.** Krause's quasi-set theory, and the quasets of Dalla Chiara and Toraldo di Francia, take the
  cardinal as given. Holik (2011) argues that particle number can be undefined.
- **Case 2.** This is Feynman's rule, and the quantum eraser.
- **Case 3.** This is Peres (1978): "unperformed experiments have no results"; for the other premises,
  Jarrett (1984) and Shimony's "peaceful coexistence" of non-local correlation with no signalling.
- **Case 4.** Brukner (2018) and Bong et al. (2020) prove no-go results against observer-independent facts. Di
  Biagio & Rovelli (2021) hold that facts are stable only while their record holds. ZTL's reading is nearest to
  theirs.
- **Case 5.** This is the line from Susskind's complementarity to Harlow–Hayden.
- **Case 6.** ZTL agrees with Wallace in refusing naive branch counting, and with Vaidman on self-location.

ZTL takes the operational reading in cases 1–4 and 6, for the one stated reason. In case 5 it does not decide.

---
Vitaly Reznik. Prepared with Logik (Claude Opus 5.5, an AI assistant). The stands, the measurements and this
note were produced in a working session with the author, who directed the line of inquiry. v2 answers a
critical review of v1 by a fresh model reader: 17 findings, all addressed.
