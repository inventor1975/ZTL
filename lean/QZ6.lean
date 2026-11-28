import ZTL
import ZRead
import QZ3
import QZ4
/-!
# QZ, theorem 6 — inside a context the count of a formula IS a classical count. Written with AI, 2026-11-27.

    sh research/qz/build.sh

THE GAP IT CLOSES. The kernel's degree calculus (ZTL zdegree: the Boole–Fréchet range) is defined over "every joint
distribution" of the atoms. That its range holds for quantum probabilities inside one context was a measurement
(0 misses in 23320 cases, research/qz/degree_probe.py; 9538 misses across contexts with tilted questions). What a proof needs is
one thing: that inside a context a joint distribution of the atoms EXISTS which gives every formula its true
probability. Then the true probability is one of the values the kernel's range runs over, by the range's definition.

THE COUNT. Probabilities are carried as natural numbers, as in the kernel's own ZDegrees.lean ("how many of N"; the
statements are scale-free). A count `c` on the lattice is asked for:
    monotone                  x ≤ y ⇒ c x ≤ c y
    never more than the whole u, u' ≤ y and u ≤ ¬u'  ⇒  c u + c u' ≤ c y     (two exclusive parts of y)
    additive along a split    s ≤ (s ∧ a) ∨ (s ∧ ¬a)  ⇒  c s = c (s ∧ a) + c (s ∧ ¬a)
The Born probability of a state, times N, has these three properties (standard, not proved here).

THE CELLS. Splitting the state `s` along the listed atoms, one after another, cuts it into cells; in each cell every
listed atom is settled, so the formula is classically true or false there. `massT` adds the counts of the cells where
it is true: the count of the formula's truth set under the joint distribution "weight of a world = count of its cell".

THEOREM (`count_is_classical`). If the state splits along the dirty atoms of the formula, then
        c (s ∧ ⟦φ⟧) = massT.
The same theorem applied to a single atom gives the marginals, so the cell weights are a joint distribution of the
atoms that reproduces the count of EVERY formula over them: the true probability lies in the kernel's range.

ACROSS CONTEXTS no such joint exists (`no_joint_across`): on the qubit of QZ5 (c ⊤ = 2, c a = 2, c b = 1,
c (a ∧ b) = 0) no table of four weights has those marginals and that mass. This is Boole's condition failing.

Boundary (Logik2's condition, 2026-11-27). "The true probability lies between the two ends the kernel's linear program
returns" needs one more thing than this theorem: the cell weights must be a FEASIBLE POINT OF THAT VERY PROGRAM - the
same events, and marginals inside the intervals the document wrote for the atoms (so the degrees in the rows must
contain the atoms' true probabilities). Granted that, it holds by the definition of the ends, which the kernel
certifies call by call (primal and dual). That step is by definition of the ends, not re-proved here. Known mathematics: a probability on a Boolean algebra is a classical probability (the cells
are its atoms); Pitowsky 1994 for the failure across contexts (not read). What is ours: the statement for the kernel's
formulas and readings, with the splitting condition, checked by machine.
-/

namespace QZ6
open V QZ3 QZ4

variable {α : Type} (L : NLat α)

/-- a count on the lattice ("how many of N") -/
structure Count where
  c : α → Nat
  mono : ∀ {x y}, L.le x y → c x ≤ c y
  super : ∀ {u u' y}, L.le u y → L.le u' y → L.le u (L.neg u') → c u + c u' ≤ c y
  split : ∀ s a, L.le s (L.join (L.meet s a) (L.meet s (L.neg a))) → c s = c (L.meet s a) + c (L.meet s (L.neg a))

variable (K : Count L) (val : Nat → α) (φ : Fm)

/-- the count of the cells of `s` (cut along the list) in which the formula is classically true -/
def massT : List Nat → α → (Nat → V) → Nat
  | [], s, v => cond (clEval (cl v) φ) (K.c s) 0
  | k :: zs, s, v => massT zs (L.meet s (val k)) (set v k T) + massT zs (L.meet s (L.neg (val k))) (set v k F)

/-- …and of the cells in which it is classically false -/
def massF : List Nat → α → (Nat → V) → Nat
  | [], s, v => cond (clEval (cl v) φ) 0 (K.c s)
  | k :: zs, s, v => massF zs (L.meet s (val k)) (set v k T) + massF zs (L.meet s (L.neg (val k))) (set v k F)

theorem neg_of_true : ∀ b : Bool, b = true → (!b) = false := by decide

/-- cancelling on the right, by hand (the library lemma carries `propext`) -/
theorem cancel : ∀ (k a b : Nat), a + k ≤ b + k → a ≤ b
  | 0, _, _, h => h
  | k + 1, a, b, h => cancel k a b (Nat.le_of_succ_le_succ h)

/-- the three facts carried through the cells -/
theorem cells (refl : ∀ a : α, L.le a a) :
    ∀ (zs : List Nat) (s : α) (v : Nat → V), AgreesOn L s v val φ → DirtyIn v zs φ → Splits L s (zs.map val) →
      massT L K val φ zs s v ≤ K.c (L.meet s (qe L val φ)) ∧
      massF L K val φ zs s v ≤ K.c (L.meet s (L.neg (qe L val φ))) ∧
      massT L K val φ zs s v + massF L K val φ zs s v = K.c s
  | [], s, v, ag, hz, _ => by
    have cln := clean_of_nil v φ hz
    have d := definite v φ cln
    show cond (clEval (cl v) φ) (K.c s) 0 ≤ _ ∧ cond (clEval (cl v) φ) 0 (K.c s) ≤ _ ∧
         cond (clEval (cl v) φ) (K.c s) 0 + cond (clEval (cl v) φ) 0 (K.c s) = K.c s
    cases hb : clEval (cl v) φ with
    | true =>
      have e : earnedR v φ := d.2.trans (neg_of_true _ hb)
      have le1 := earned_sound_on L s v val φ ag e
      exact ⟨K.mono (L.le_meet (refl s) le1), Nat.zero_le _, Nat.add_zero _⟩
    | false =>
      have r : refutedR v φ := d.1.trans hb
      have le1 := refuted_sound_on L s v val φ ag r
      exact ⟨Nat.zero_le _, K.mono (L.le_meet (refl s) le1), Nat.zero_add _⟩
  | k :: zs, s, v, ag, hz, sp => by
    obtain ⟨cover, sp1, sp2⟩ := sp
    have h1 := cells refl zs _ (set v k T) (on_setT L s v val k φ ag)
      (dirty_set v k zs T (fun e => V.noConfusion e) φ hz) sp1
    have h2 := cells refl zs _ (set v k F) (on_setF L s v val k φ ag)
      (dirty_set v k zs F (fun e => V.noConfusion e) φ hz) sp2
    -- two exclusive parts of `s ∧ y`, for any y: the part under val k and the part under its negation
    have two : ∀ y : α, K.c (L.meet (L.meet s (val k)) y) + K.c (L.meet (L.meet s (L.neg (val k))) y)
        ≤ K.c (L.meet s y) := fun y =>
      K.super
        (L.le_meet (L.le_trans (L.meet_le_l _ _) (L.meet_le_l _ _)) (L.meet_le_r _ _))
        (L.le_meet (L.le_trans (L.meet_le_l _ _) (L.meet_le_l _ _)) (L.meet_le_r _ _))
        (L.le_trans (L.le_trans (L.meet_le_l _ _) (L.meet_le_r _ _))
          (L.le_trans (L.le_nn _) (L.anti (L.le_trans (L.meet_le_l _ _) (L.meet_le_r _ _)))))
    refine ⟨Nat.le_trans (Nat.add_le_add h1.1 h2.1) (two _), Nat.le_trans (Nat.add_le_add h1.2.1 h2.2.1) (two _), ?_⟩
    show massT L K val φ zs _ _ + massT L K val φ zs _ _ + (massF L K val φ zs _ _ + massF L K val φ zs _ _) = K.c s
    rw [Nat.add_add_add_comm, h1.2.2, h2.2.2]
    exact (K.split s (val k) cover).symm

/-- **QZ 6.** Where the state splits along the dirty atoms of the formula, the count of the formula is the classical
count over the cells: a joint distribution of the atoms exists and gives the formula its true probability. -/
theorem count_is_classical (refl : ∀ a : α, L.le a a) (zs : List Nat) (s : α) (v : Nat → V)
    (ag : AgreesOn L s v val φ) (hz : DirtyIn v zs φ) (sp : Splits L s (zs.map val)) :
    K.c (L.meet s (qe L val φ)) = massT L K val φ zs s v := by
  obtain ⟨hT, hF, tot⟩ := cells L K val φ refl zs s v ag hz sp
  -- the formula's part and its negation's part are two exclusive parts of the state
  have both : K.c (L.meet s (qe L val φ)) + K.c (L.meet s (L.neg (qe L val φ))) ≤ K.c s :=
    K.super (L.meet_le_l _ _) (L.meet_le_l _ _)
      (L.le_trans (L.meet_le_r _ _) (L.le_trans (L.le_nn _) (L.anti (L.meet_le_r _ _))))
  have up : K.c (L.meet s (qe L val φ)) + massF L K val φ zs s v ≤ massT L K val φ zs s v + massF L K val φ zs s v :=
    tot ▸ Nat.le_trans (Nat.add_le_add_left hF _) both
  exact Nat.le_antisymm (cancel _ _ _ up) hT

/-! ### the qubit of QZ5, counted out of two -/

def twice : Q → Nat
  | .bot => 0 | .top => 2 | .a => 2 | .a' => 0 | .b => 1 | .b' => 1

theorem twice_mono : ∀ x y : Q, qle x y → twice x ≤ twice y := by decide
theorem twice_super : ∀ u u' y : Q, qle u y → qle u' y → qle u (qneg u') → twice u + twice u' ≤ twice y := by decide
theorem twice_split : ∀ s x : Q, qle s (qjoin (qmeet s x) (qmeet s (qneg x))) →
    twice s = twice (qmeet s x) + twice (qmeet s (qneg x)) := by decide

/-- the class is not empty: MO2 with "a sure, b one half", counted out of two -/
def qubitCount : Count mo2 where
  c := twice
  mono := fun {x y} h => twice_mono x y h
  super := fun {u u' y} h1 h2 h3 => twice_super u u' y h1 h2 h3
  split := fun s x h => twice_split s x h

/-- **Across contexts no joint exists.** No table of four weights (a and b; a, not b; not a, b; neither) has the
marginals of that qubit (a: 2 of 2, b: 1 of 2) and its count of a ∧ b (which is 0). -/
theorem no_joint_across (tt tf ft ff : Nat) (_ha : tt + tf = twice .a) (hb : tt + ft = twice .b)
    (hna : ft + ff = twice .a') (hab : tt = twice (qmeet .a .b)) : False := by
  have ft0 : ft = 0 := (Nat.eq_zero_of_add_eq_zero hna).1
  have h1 : tt = 1 := by rw [ft0] at hb; exact hb
  have h0 : tt = 0 := hab
  rw [h0] at h1; exact Nat.noConfusion h1

end QZ6

#print axioms QZ6.cells
#print axioms QZ6.count_is_classical
#print axioms QZ6.qubitCount
#print axioms QZ6.no_joint_across
