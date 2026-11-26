import ZMajority

/-!
# Pigeonhole — the quantum pigeonhole paradox through the ZTL lens. Zero axioms.

The paradox is from Aharonov, Colombo, Popescu, Sabadini, Struppa and Tollaksen, PNAS 113, 532 (2016). This file was
written 2026-11-26 at the curator's request: «исследуем какой-то парадокс из физики и напишем теорему по результатам».
It is the twin of VR-ZTL's `ZTL/Pigeonhole.agda`. The judge's run on the same four documents is in VR-ZTL's
`research/pigeonhole/`.

THE SETUP. Three particles and two boxes, 0 and 1. Each particle is pre-selected in |0⟩+|1⟩ and post-selected in
|0⟩+i|1⟩. Everything is exact and unnormalised, in Gaussian integers: ⟨post|0⟩ = 1 and ⟨post|1⟩ = −i. By the ABL rule,
an intermediate projective measurement with projectors Πₖ gives outcome k with weight |⟨post|Πₖ|pre⟩|².

THE PARADOX. Ask any ONE pair "same box?". The answer "same" has weight 0, so the pair is certainly in different
boxes, and this holds for every pair. Yet no record of three particles in two boxes has all three pairs different.

PROVED HERE:
1. Physics.
   * Post-selection is possible: the amplitude is −2−2i, of weight 8.
   * Each pair asked alone has "same" = 0.
   * "All three differ" has amplitude 0 (pigeonhole).
   * Two pairs asked TOGETHER give four outcomes of weight 2 each, so P(23 differs | 12 differs) = 1/2.
2. The rule. Hardy.lean reads "an atom about the other, non-commuting question is Z". There, "unasked" and "unasked
   and non-commuting" coincide. Here all pair questions COMMUTE, so the two readings part.
   * R-asked (every unasked atom is Z): "12 differs" is EARNED, and "all three differ" is OPEN.
   * R-commuting (an unasked but commuting atom keeps its certain-when-asked-alone value): "all three differ" is
     EARNED, a claim that every box record refutes.
   So the grounding criterion is being ASKED, not commutation. Hardy's verdicts stand under either reading.
3. The judge's disposition of the pigeonhole itself: REFUTED IF STABLE, not REFUTED (`pigeonhole_stable`,
   `pigeonhole_not_refuted`). It fails only if each particle is in one box at every place it is mentioned.

NOT CLAIMED: new physics. That ABL must not be applied counterfactually is known (Sharp & Shanks 1993; Kastner 1999,
on the three-box paradox).
-/

namespace Pigeonhole

open V ZTopology

/-! ## Gaussian integers -/

structure G where
  re : Int
  im : Int

def G.add (a b : G) : G := ⟨a.re + b.re, a.im + b.im⟩
def G.mul (a b : G) : G := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- |z|². -/
def weight (a : G) : Int := a.re * a.re + a.im * a.im

def g0 : G := ⟨0, 0⟩

/-! ## The physics -/

/-- ⟨post|box⟩ for one particle (false = box 0, true = box 1). -/
def cpost : Bool → G
  | false => ⟨1, 0⟩
  | true => ⟨0, -1⟩

/-- Written out in full, so that no `BEq` instance enters. -/
def differ : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

def same : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

def term (P : Bool → Bool → Bool → Bool) (x y z : Bool) : G :=
  match P x y z with
  | true => ((cpost x).mul (cpost y)).mul (cpost z)
  | false => g0

/-- ⟨post|Π_P|pre⟩ for the projector onto the box records satisfying `P`. -/
def amp (P : Bool → Bool → Bool → Bool) : G :=
  (((((((term P false false false).add (term P false false true)).add (term P false true false)).add
    (term P false true true)).add (term P true false false)).add (term P true false true)).add
    (term P true true false)).add (term P true true true)

/-- Post-selection is possible: ⟨post|pre⟩ = −2 − 2i, of weight 8. -/
theorem post_possible : amp (fun _ _ _ => true) = ⟨-2, -2⟩ ∧ weight (amp (fun _ _ _ => true)) = 8 := ⟨rfl, rfl⟩

/-- Each pair asked ALONE: "same box" has amplitude 0, and "different" carries the whole weight. -/
theorem pair12_alone : amp (fun x y _ => same x y) = g0 ∧ weight (amp (fun x y _ => differ x y)) = 8 := ⟨rfl, rfl⟩
theorem pair23_alone : amp (fun _ y z => same y z) = g0 ∧ weight (amp (fun _ y z => differ y z)) = 8 := ⟨rfl, rfl⟩
theorem pair13_alone : amp (fun x _ z => same x z) = g0 ∧ weight (amp (fun x _ z => differ x z)) = 8 := ⟨rfl, rfl⟩

/-- The pigeonhole holds in every record. -/
theorem pigeonhole : ∀ x y z : Bool, (differ x y && differ y z && differ x z) = false := by decide

/-- …so "all three pairs differ", asked of all three, has amplitude 0: it never happens. -/
theorem all_differ_never : amp (fun x y z => differ x y && differ y z && differ x z) = g0 := rfl

/-- Asked TOGETHER (pairs 12 and 23, which commute): four joint outcomes, of weight 2 each. -/
theorem joint_12_23 :
    weight (amp (fun x y z => differ x y && differ y z)) = 2 ∧
    weight (amp (fun x y z => differ x y && same y z)) = 2 ∧
    weight (amp (fun x y z => same x y && differ y z)) = 2 ∧
    weight (amp (fun x y z => same x y && same y z)) = 2 := ⟨rfl, rfl, rfl, rfl⟩

/-! ## The ZTL reading -/

/-- Atoms: 0 = "pair 12 differs", 1 = "pair 23 differs", 2 = "pair 13 differs". -/
def allDiffer : Fm := .conj (.conj (.atom 0) (.atom 1)) (.atom 2)

def ofB : Bool → V
  | true => T
  | false => F

/-- The record's own marking: every atom read off the boxes. -/
def record3 (x y z : Bool) : Nat → V :=
  ZMajority.mark (ofB (differ x y)) (ofB (differ y z)) (ofB (differ x z))

/-- Every box record refutes "all three differ". -/
theorem every_record_refutes : ∀ x y z : Bool, evalF (record3 x y z) allDiffer = F := by decide

/-- The run that asks pair 12 and gets the only possible answer, "different". R-asked: the unasked atoms are Z.
R-commuting: they keep their certain-when-asked-alone value, T. -/
def runAsked : Nat → V := ZMajority.mark T Z Z
def runCommuting : Nat → V := ZMajority.mark T T T

/-- R-asked: "pair 12 differs" is earned… -/
theorem asked_pair_earned : earned (.atom 0) runAsked := forced_sub_earned rfl

theorem ref_TFF : refines runAsked (ZMajority.mark T F F)
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem ref_TTT : refines runAsked (ZMajority.mark T T T)
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- …and "all three differ" is OPEN: one refinement makes it false, another makes it true. -/
theorem asked_all_open : ¬ earned allDiffer runAsked ∧ ¬ refuted allDiffer runAsked :=
  ⟨fun h => absurd (h _ ref_TFF) (by decide), fun h => absurd (h _ ref_TTT) (by decide)⟩

/-- R-commuting: in the same run "all three differ" is EARNED, the claim that every record refutes. -/
theorem commuting_earns_the_impossible :
    earned allDiffer runCommuting ∧ ∀ x y z : Bool, evalF (record3 x y z) allDiffer = F :=
  ⟨forced_sub_earned rfl, every_record_refutes⟩

/-! ## The pigeonhole itself, as the judge reads it

Measured with zfl.run (2026-11-26). The three pair atoms are DEFINED from three unverified boxes, and the claim
"d12 & d23 & d13" comes back REFUTED IF STABLE, not REFUTED. -/

/-- Atoms 0, 1, 2 = the box of particle 1, 2, 3 (unverified). -/
def boxesDiffer : Fm := .conj (.conj (.xor (.atom 0) (.atom 1)) (.xor (.atom 1) (.atom 2))) (.xor (.atom 0) (.atom 2))

def unverifiedBoxes : Nat → V := fun _ => Z

theorem three : ∀ x y z : Bool, ((x != y && y != z) && x != z) = false := by decide

/-- REFUTED IF STABLE: false in every cleaning, i.e. with each particle in ONE box at all the places it is mentioned. -/
theorem pigeonhole_stable : stableF unverifiedBoxes boxesDiffer := fun c _ => three (c 0) (c 1) (c 2)

/-- …and NOT refuted: read occurrence by occurrence, it can come out true. -/
theorem pigeonhole_not_refuted : ¬ refutedR unverifiedBoxes boxesDiffer :=
  fun h => absurd (show (rd unverifiedBoxes boxesDiffer).1 = false from h) (by decide)

/-- **THE THEOREM.** Every pair question commutes with every other, each is certain when asked alone, and the
conjunction is impossible in every record. Granting an unasked COMMUTING atom its certain value earns that impossible
conjunction. Reading every unasked atom as Z leaves it OPEN and earns exactly the asked pair. So the grounding criterion
is "asked", not "non-commuting". The pigeonhole itself is REFUTED IF STABLE, not REFUTED. -/
theorem pigeonhole_verdict :
    weight (amp (fun _ _ _ => true)) = 8 ∧
    amp (fun x y _ => same x y) = g0 ∧ amp (fun _ y z => same y z) = g0 ∧ amp (fun x _ z => same x z) = g0 ∧
    amp (fun x y z => differ x y && differ y z && differ x z) = g0 ∧
    weight (amp (fun x y z => differ x y && differ y z)) = weight (amp (fun x y z => differ x y && same y z)) ∧
    earned (.atom 0) runAsked ∧ ¬ earned allDiffer runAsked ∧ ¬ refuted allDiffer runAsked ∧
    earned allDiffer runCommuting ∧ (∀ x y z : Bool, evalF (record3 x y z) allDiffer = F) ∧
    stableF unverifiedBoxes boxesDiffer ∧ ¬ refutedR unverifiedBoxes boxesDiffer :=
  ⟨post_possible.2, pair12_alone.1, pair23_alone.1, pair13_alone.1, all_differ_never, rfl,
   asked_pair_earned, asked_all_open.1, asked_all_open.2,
   commuting_earns_the_impossible.1, commuting_earns_the_impossible.2,
   pigeonhole_stable, pigeonhole_not_refuted⟩

end Pigeonhole

#print axioms Pigeonhole.post_possible
#print axioms Pigeonhole.pair12_alone
#print axioms Pigeonhole.pair23_alone
#print axioms Pigeonhole.pair13_alone
#print axioms Pigeonhole.pigeonhole
#print axioms Pigeonhole.all_differ_never
#print axioms Pigeonhole.joint_12_23
#print axioms Pigeonhole.every_record_refutes
#print axioms Pigeonhole.asked_pair_earned
#print axioms Pigeonhole.ref_TFF
#print axioms Pigeonhole.ref_TTT
#print axioms Pigeonhole.asked_all_open
#print axioms Pigeonhole.commuting_earns_the_impossible
#print axioms Pigeonhole.three
#print axioms Pigeonhole.pigeonhole_stable
#print axioms Pigeonhole.pigeonhole_not_refuted
#print axioms Pigeonhole.pigeonhole_verdict
