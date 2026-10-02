# One criterion, six quantum puzzles, read operationally (v3)

*ZTL's stamp Z_PERMANENT — "no act can witness it" — read against six known quantum puzzles, 2 October 2026.
The unification below holds only for someone who takes the operational reading; see "The rule is a position".*

## The claim, and its limit

In each of the six cases below, a classical line of reasoning runs into trouble. In cases 1–3 experiment refutes
it. In case 4, if quantum mechanics applies to agents, it is refuted by the outcome quantum mechanics predicts for a
thought experiment that has not been run with agents. In cases 5–6 the trouble is a theoretical dispute, not an experimental refutation. In cases 1–4 and 6
the reasoning leans on at least one step that treats as a fact something no act can witness; in case 3 there are
several such steps. ZTL (Zero-Trust Logic) marks such an atom Z_PERMANENT and never grants a conclusion that rests
on it. So in those five cases one rule flags the same kind of step. In case 5 the rule does not decide: whether the
atom is witnessable depends on a physical premise that is itself disputed.

Read that claim narrowly.

- **What the table shows.** The column "the atom no act witnesses" is filled in from the physics, by an author
  who knew each standard resolution. Any refuted step could be relabelled this way after the fact. So the
  consistency of the table is partly guaranteed by how it was built: it shows that the rule can be applied to
  these cases without contradiction, and that in case 5 it cannot be applied without a further premise. It does
  not show that the rule found anything.
- **No negative control.** Five of the six cases were chosen because they have operational resolutions; case 5
  was chosen as a known open dispute. No case was
  tested where the rule could have picked the wrong step; Kochen–Specker contextuality and the PBR theorem are
  candidates. That test is still missing.
- **Not new physics.** ZTL produces no amplitudes. Where a stand has a quantum number (1/12, 2√2, the Born
  weights, the HOM coincidence), it is computed from amplitudes. Case 1's numbers are combinatorial counts, and
  case 5's stand has no number. Who can witness what is a premise taken from the physics, not derived.
- **The rule is a position.** A realist (Everett, Bohm, Wallace, Carroll) rejects "a fact is what some act can
  witness". ZTL does not win that debate. Under the rule, five of the puzzles get one consistent answer and the
  sixth (case 5) is reduced to one question. Realists resolve them by different moves, and not all realists by
  the same ones: Bohmians accept nonlocality for Bell; Everettians accept many outcomes for Frauchiger–Renner,
  while Bohmians answer it differently. So the cases share one fork only for someone who takes the operational
  branch.

## Words

- **EARNED / REFUTED:** a claim is true / false on every future that the acts still available can produce.
- **OPEN:** neither earned nor refuted now. With a frozen ceiling it stays so for good (case 1).
- **Redeemable:** some act could still settle an atom.
- **Z_PERMANENT:** no act available from now on can settle it. The atom may have been witnessed earlier and its
  record erased since (case 4, read with a single definite outcome for the friend); the stamp is about the
  future, not the past.
- **Frozen ceiling:** no reachable future ever earns the claim. A claim with a Z_PERMANENT atom it needs has one.
- **Ceiling open:** some reachable future earns the claim.
- **On credit:** the kernel's verdict is T, but it rests on an unverified atom, so the claim is not EARNED.
- **"Never grants":** a conclusion resting on a Z_PERMANENT atom is not EARNED. The kernel's raw verdict may be T
  ("on credit", case 3), but the grade is not EARNED. Such a conclusion may still be REFUTED by what is recorded,
  as in case 4's modelled run.

## The six cases

| # | Puzzle | The classical step that runs into trouble | The atom no act witnesses | ZTL verdict | What the stand checks |
|---|---|---|---|---|---|
| 1 | Indistinguishable particles (counting) | "these are two different objects" | which bearer is which | two clicks are earned, "one object" and "two objects" are each open, and "one or two" is not earned (it presupposes a definite number of objects, which is the claim not earned) | lean/ZQuasi.lean (no axioms); indistinguishable.py: n particles in k cells; the earned distinctions number C(n+k−1, n), the Bose–Einstein count of states (not its statistics: see the caveat) |
| 2 | Hong–Ou–Mandel | add the probabilities of the two routes | which photon took which route | with a tag the routes are events (ceiling open); without one, frozen | indistinguishable.py (I2): the verdicts, and from amplitudes P(coincidence) 1/2 with a tag, 0 without |
| 3 | Bell / CHSH | all four readings have values; local causality and free settings stated through the hidden state | the readings not made; the hidden state | "all four have values" frozen; parameter independence, outcome independence and free settings each frozen; Bell's conclusion "not all three" only on credit, its ceiling frozen; the violation and no signalling earned | bell.py: the verdicts (B3, B4); CHSH 2.000 for the literal figure-eight (the author's ring picture taken literally: one shared phase, the two lobes running opposite ways — a local model) (no local model exceeds 2, by Bell's theorem); about 2.83 by Monte Carlo (2√2 exactly) when the waves add |
| 4 | Frauchiger–Renner | chain the agents' conclusions | records erased by the Wigners' measurements | granting quantum mechanics for agents (Q), the chain is REFUTED by the outcome it predicts for this thought experiment; on ZTL's reading its weak links are the erased records (Z_PERMANENT); in the modelled run, what the Wigners record stays EARNED | wigner_friends.py: the verdicts; from amplitudes P = 1/12 and each statement's exception probability 0 |
| 5 | AMPS firewall | one observer holds both entanglements | the joint witness | frozen if no act checks both in time (Harlow–Hayden argue the decoding is computationally infeasible before evaporation; treating that as "no act" is a premise), redeemable if one can (Oppenheim–Unruh); undecided | firewall.py: the stamps under each repertoire; no number |
| 6 | Many worlds | count branches; "the other branches are real" | the number of branches; another branch | branch counting refused; "the other branch exists" and its denial both frozen | many_worlds.py: the verdicts; for a\|up⟩+b\|down⟩ with \|a\|² = 1/3, splitting the down-branch into k environment records makes branch counting give the up-outcome weight 1/(k+1), while Born gives it 1/3 |

The stands are in `ZTL/dilemmas/`. Run each from the ZTL root with `python3 dilemmas/<name>.py`. Each asserts
the ZTL verdicts it prints, not only the quantum numbers. The same author wrote the stands and their expected
values, so the stands guard against regressions; they do not prove the verdicts correct.

## Caveats, case by case

- **Case 1.** Indistinguishability alone does not give Bose–Einstein statistics. Fermions give C(k, n), and
  classical identical particles with Gibbs's 1/N! give kⁿ/n!. Equal weighting of states is a further premise.
  What ZTL adds is narrower: the count of acts is earned while the count of objects is not, and this needs no
  primitive quasi-cardinal (Krause's qc). Counting acts still uses number.
- **Case 2.** The tag reading (an alternative is an event only if some act could tell it apart) is one common
  reading of the quantum eraser; the delayed-choice versions have competing readings. ZTL matches only the two ends, tag or no tag; a partial tag is outside a binary
  stamp.
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
  limit of the encoding, not a finding about Bell. The violation and no signalling are EARNED only inside the
  stand, where they are marked as recorded facts. In a real experiment both are statistical inferences, with
  loophole assumptions; the stand does not model those.
- **Case 4.** The Frauchiger–Renner literature is split on which assumption fails: quantum mechanics for agents
  (Q), combining conclusions (C), or single outcomes (S). "The weak links are the erased records" is ZTL's
  reading, a narrow form of C, not a consensus.
- **Case 5.** Undecided. Whether one observer can check both entanglements is a physical premise the literature
  has not settled, and ZTL takes it from the physics.
- **Case 6.** Branch counting is a step that Everettians themselves reject. Wallace, a realist, affirms the other
  branches that ZTL leaves frozen. So ZTL agrees with him on one step (no naive branch counting) for a different
  reason, and disagrees on the branches.

## How sure

- **Predictions.** For cases 4–6 the verdict was predicted, written down and timestamped before the stand ran.
  The notes are in the author's private repository, not public, so readers cannot check them. Cases 4 and 6
  were predictions that could have failed, and they held. Case 5's prediction was conditional by design ("the
  debate reduces to one question"), so it was a weak test. Cases 1–3 were computed by the stands, but nothing
  was predicted first, except case 3's second stand (B4), whose verdicts were predicted and timestamped before
  it ran, and held.
- **Not blind.** The author knew the literature. Each result confirms a known resolution; none discovers one.
- **What ZTL adds.** It does the bookkeeping: which premise each conclusion rides on, and whether some act could
  still settle it. That no act ever can is a physics premise that ZTL carries, not something it shows.

## Where it stands among known views

- **Case 1.** Krause's quasi-set theory postulates a quasi-cardinal as a primitive; the quasets of Dalla Chiara
  and Toraldo di Francia are often presented as lacking a well-defined cardinal. Holik (2011) argues that particle number can be undefined.
- **Case 2.** This is Feynman's rule, and the quantum eraser.
- **Case 3.** This is Peres (1978): "unperformed experiments have no results"; for the other premises,
  Jarrett (1984) and Shimony's "peaceful coexistence" of non-local correlation with no signalling.
- **Case 4.** Brukner (2018) and Bong et al. (2020) prove no-go results against conjunctions of assumptions that
  include observer-independent facts (for Bong et al., local friendliness: locality, no superdeterminism and
  absoluteness of observed events). Di
  Biagio & Rovelli (2021) hold that facts are stable only while their record holds. ZTL's reading is nearest to
  theirs.
- **Case 5.** This is the line from Susskind's complementarity to Harlow–Hayden.
- **Case 6.** ZTL agrees with Wallace in refusing naive branch counting, and with Vaidman on self-location.

ZTL takes the operational reading in cases 1–4 and 6, because it adopts the rule above: a position, not a
result. In case 5 it does not decide.

---
Vitaly Reznik. Prepared with Logik (Claude Opus 5.5, an AI assistant). The stands, the measurements and this
note were produced in a working session with the author, who directed the line of inquiry. v2 answered a
critical review of v1 by a fresh model reader (17 findings). v3 adds case 3's second stand (B4) and answers a
second fresh review (20 findings). A third review (22 findings) led to further fixes of fact and logic; its remaining
objections (the weight of the author's own tests, what counts as unification) are recorded with the review, not
claimed resolved.
