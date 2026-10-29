import ZDirty
import ZComplete
/-! # ZSpeaks — every disposition of the judge is a ZTL formula over the atoms of φ. Zero axioms.

Paper v7 §5.3 (2026-10-29). Two steps, glued here into one theorem:
(1) for a fixed φ, each disposition at v is decided by a finite search over the refinements of the dirty
    atoms of φ (`allR`), so it is a yes/no function of the values of the atoms of φ;
(2) every such function is a ZTL formula (`Cpl.ztl_expressively_complete`, the J-DNF).
The six dispositions: EARNED, EARNED IF STABLE, ON CREDIT, OPEN, REFUTED IF STABLE, REFUTED.
Strong Kleene cannot state even "p is established" (`ZDirty.kleene_cannot_say_established`).
Expressible is not cheap: the J-DNF has 3^|atoms| leaves; this is about the language, not the cost.
-/

namespace V
namespace Speak
open Cpl

theorem and3 : ∀ a b c : Bool, (a && b && c) = true → a = true ∧ b = true ∧ c = true := by decide
theorem and3_intro : ∀ a b c : Bool, a = true → b = true → c = true → (a && b && c) = true := by decide
theorem bool_eq_of_iff : ∀ a b : Bool, (a = true ↔ b = true) → a = b
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, h => nomatch h.mp rfl
  | false, true, h => nomatch h.mpr rfl
theorem toV_iff : ∀ b : Bool, toV b = T ↔ b = true
  | true => Iff.intro (fun _ => rfl) (fun _ => rfl)
  | false => Iff.intro (fun h => nomatch h) (fun h => nomatch h)
theorem decide_iff (p : Prop) [Decidable p] : decide p = true ↔ p := ⟨of_decide_eq_true, decide_eq_true⟩
theorem and_not_iff : ∀ a b : Bool, (a && !b) = true ↔ (a = true ∧ ¬ b = true) := by decide
theorem not_and_not_iff : ∀ a b : Bool, (!a && !b) = true ↔ (¬ a = true ∧ ¬ b = true) := by decide

/-! ## (1) The finite search over refinements -/

/-- does φ take the value t at every refinement of v? Branch on each dirty atom of xs. -/
def allR (t : V) (φ : Fm) : List Nat → (Nat → V) → Bool
  | [], v => decide (evalF v φ = t)
  | x :: xs, v =>
      if v x = Z then allR t φ xs (upd v x T) && allR t φ xs (upd v x F) && allR t φ xs (upd v x Z)
      else allR t φ xs v

theorem allR_sound (t : V) (φ : Fm) : ∀ (xs : List Nat) (v w : Nat → V), refines v w →
    (∀ n, occurs n φ = true → memB n xs = false → w n = v n) → allR t φ xs v = true → evalF w φ = t
  | [], v, w, _, hoff, h => by
      rw [evalF_congr w v φ (fun n hn => hoff n hn rfl)]
      exact of_decide_eq_true h
  | x :: xs, v, w, hr, hoff, h => by
      have offx : ∀ n, memB n (x :: xs) = false → ¬ n = x ∧ memB n xs = false := by
        intro n hn
        have hn' : (decide (n = x) || memB n xs) = false := hn
        cases hd : decide (n = x) with
        | true => rw [hd] at hn'; exact nomatch hn'
        | false => rw [hd] at hn'; exact ⟨of_decide_eq_false hd, hn'⟩
      match decEq (v x) Z with
      | isTrue hz =>
          have h' : (allR t φ xs (upd v x T) && allR t φ xs (upd v x F) && allR t φ xs (upd v x Z)) = true := by
            have e : allR t φ (x :: xs) v =
                (allR t φ xs (upd v x T) && allR t φ xs (upd v x F) && allR t φ xs (upd v x Z)) := if_pos hz
            rw [← e]; exact h
          have key : ∀ c : V, w x = c → allR t φ xs (upd v x c) = true → evalF w φ = t := by
            intro c hc hall
            apply allR_sound t φ xs (upd v x c) w
            · intro n hn
              match Nat.decEq n x with
              | isTrue e =>
                  rw [e, hc]; exact (upd_at v x c).symm
              | isFalse e =>
                  have hu : upd v x c n = v n := if_neg e
                  rw [hu] at hn ⊢; exact hr n hn
            · intro n hocc hm
              match Nat.decEq n x with
              | isTrue e => rw [e, hc]; exact (upd_at v x c).symm
              | isFalse e =>
                  have hu : upd v x c n = v n := if_neg e
                  rw [hu]
                  exact hoff n hocc (by
                    show (decide (n = x) || memB n xs) = false
                    rw [decide_eq_false e, hm]; rfl)
            · exact hall
          obtain ⟨hT, hF, hZ⟩ := and3 _ _ _ h'
          cases hw : w x with
          | T => exact key T hw hT
          | F => exact key F hw hF
          | Z => exact key Z hw hZ
      | isFalse hz =>
          have e : allR t φ (x :: xs) v = allR t φ xs v := if_neg hz
          rw [e] at h
          apply allR_sound t φ xs v w hr _ h
          intro n hocc hm
          match Nat.decEq n x with
          | isTrue en => rw [en]; exact hr x hz
          | isFalse en =>
              exact hoff n hocc (by
                show (decide (n = x) || memB n xs) = false
                rw [decide_eq_false en, hm]; rfl)

theorem allR_complete (t : V) (φ : Fm) : ∀ (xs : List Nat) (v : Nat → V),
    (∀ w, refines v w → evalF w φ = t) → allR t φ xs v = true
  | [], v, h => decide_eq_true (h v (refines_refl v))
  | x :: xs, v, h => by
      match decEq (v x) Z with
      | isTrue hz =>
          have e : allR t φ (x :: xs) v =
              (allR t φ xs (upd v x T) && allR t φ xs (upd v x F) && allR t φ xs (upd v x Z)) := if_pos hz
          rw [e]
          have br : ∀ c : V, allR t φ xs (upd v x c) = true := by
            intro c
            apply allR_complete t φ xs (upd v x c)
            intro w hr
            apply h w
            intro n hn
            match Nat.decEq n x with
            | isTrue en => rw [en] at hn; exact absurd hz hn
            | isFalse en =>
                have hu : upd v x c n = v n := if_neg en
                have := hr n (by rw [hu]; exact hn)
                rw [this, hu]
          exact and3_intro _ _ _ (br T) (br F) (br Z)
      | isFalse hz =>
          have e : allR t φ (x :: xs) v = allR t φ xs v := if_neg hz
          rw [e]; exact allR_complete t φ xs v h

/-- the search over the atoms of φ decides "t at every refinement" -/
theorem allR_iff (t : V) (φ : Fm) (v : Nat → V) :
    allR t φ (atomsL φ) v = true ↔ ∀ w, refines v w → evalF w φ = t :=
  ⟨fun h w hr => allR_sound t φ (atomsL φ) v w hr (fun n hocc hm => by
      rw [occurs_memB n φ hocc] at hm; exact nomatch hm) h,
   allR_complete t φ (atomsL φ) v⟩

/-- "t at every refinement" depends only on the atoms of φ -/
theorem every_refinement_congr (t : V) (φ : Fm) (v w : Nat → V) (h : ∀ n, occurs n φ = true → v n = w n)
    (hv : ∀ w', refines v w' → evalF w' φ = t) : ∀ w', refines w w' → evalF w' φ = t := by
  intro w' hr
  let v' : Nat → V := fun n => if occurs n φ = true then w' n else v n
  have hrv : refines v v' := by
    intro n hn
    show (if occurs n φ = true then w' n else v n) = v n
    match decEq (occurs n φ) true with
    | isTrue ho =>
        rw [if_pos ho, h n ho]
        exact hr n (by rw [← h n ho]; exact hn)
    | isFalse ho => rw [if_neg ho]
  rw [← hv v' hrv]
  exact evalF_congr w' v' φ (fun n ho => by
    show w' n = (if occurs n φ = true then w' n else v n)
    rw [if_pos ho])

theorem allR_congr (t : V) (φ : Fm) (v w : Nat → V) (h : ∀ n, occurs n φ = true → v n = w n) :
    allR t φ (atomsL φ) v = allR t φ (atomsL φ) w :=
  bool_eq_of_iff _ _ ⟨
    fun hv => (allR_iff t φ w).mpr (every_refinement_congr t φ v w h ((allR_iff t φ v).mp hv)),
    fun hw => (allR_iff t φ v).mpr (every_refinement_congr t φ w v (fun n ho => (h n ho).symm)
      ((allR_iff t φ w).mp hw))⟩

/-- strong Kleene depends only on the atoms of φ -/
theorem kev_congr (v w : Nat → V) : ∀ φ : Fm, (∀ n, occurs n φ = true → v n = w n) → kev v φ = kev w φ := by
  have l : ∀ (φ ψ : Fm) (n : Nat), occurs n φ = true → (occurs n φ || occurs n ψ) = true := by
    intro φ ψ n h; rw [h]; rfl
  have r : ∀ (φ ψ : Fm) (n : Nat), occurs n ψ = true → (occurs n φ || occurs n ψ) = true := by
    intro φ ψ n h; rw [h]; cases occurs n φ <;> rfl
  intro φ
  induction φ with
  | atom n => intro h; exact h n (by show decide (n = n) = true; exact decide_eq_true rfl)
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih => intro h; show k1 _ (kev v φ) = k1 _ (kev w φ); rw [ih h]
  | conj φ ψ ihφ ihψ =>
      intro h; show k2 _ (kev v φ) (kev v ψ) = k2 _ (kev w φ) (kev w ψ)
      rw [ihφ (fun n hn => h n (l φ ψ n hn)), ihψ (fun n hn => h n (r φ ψ n hn))]
  | disj φ ψ ihφ ihψ =>
      intro h; show k2 _ (kev v φ) (kev v ψ) = k2 _ (kev w φ) (kev w ψ)
      rw [ihφ (fun n hn => h n (l φ ψ n hn)), ihψ (fun n hn => h n (r φ ψ n hn))]
  | imp φ ψ ihφ ihψ =>
      intro h; show k2 _ (kev v φ) (kev v ψ) = k2 _ (kev w φ) (kev w ψ)
      rw [ihφ (fun n hn => h n (l φ ψ n hn)), ihψ (fun n hn => h n (r φ ψ n hn))]
  | xor φ ψ ihφ ihψ =>
      intro h; show k2 _ (kev v φ) (kev v ψ) = k2 _ (kev w φ) (kev w ψ)
      rw [ihφ (fun n hn => h n (l φ ψ n hn)), ihψ (fun n hn => h n (r φ ψ n hn))]
  | xnor φ ψ ihφ ihψ =>
      intro h; show k2 _ (kev v φ) (kev v ψ) = k2 _ (kev w φ) (kev w ψ)
      rw [ihφ (fun n hn => h n (l φ ψ n hn)), ihψ (fun n hn => h n (r φ ψ n hn))]

/-! ## The six dispositions (paper §5.1) -/

def EarnedIfStable (v : Nat → V) (φ : Fm) : Prop := Earned v φ ∧ kev v φ ≠ T
def RefutedIfStable (v : Nat → V) (φ : Fm) : Prop := Refuted v φ ∧ kev v φ ≠ F
/-- T now, but some refinement does not keep it T -/
def OnCredit (v : Nat → V) (φ : Fm) : Prop := evalF v φ = T ∧ ¬ Earned v φ
/-- not T now, and not refuted -/
def Open (v : Nat → V) (φ : Fm) : Prop := evalF v φ ≠ T ∧ ¬ Refuted v φ

/-! ## (2) The glue: a decided disposition is a ZTL formula over the atoms of φ -/

theorem speak (φ : Fm) (P : (Nat → V) → Prop) (g : (Nat → V) → Bool) (hg : ∀ v, g v = true ↔ P v)
    (hdep : ∀ v w, (∀ n, occurs n φ = true → v n = w n) → g v = g w) :
    ∃ ψ : Fm, (∀ n, occurs n ψ = true → occurs n φ = true) ∧ ∀ v, evalF v ψ = T ↔ P v := by
  have hD : Dep (atomsL φ) g := fun v w ha =>
    hdep v w (fun n ho => agree_mem n (atomsL φ) v w ha (occurs_memB n φ ho))
  refine ⟨dnf (atomsL φ) g, fun n hn => atomsL_occurs n φ (dnf_atoms n _ g hn), fun v => ?_⟩
  rw [dnf_spec (atomsL φ) g hD v]
  exact (toV_iff (g v)).trans (hg v)

/-- Each disposition is the T-value of a ZTL formula whose atoms are atoms of φ. -/
abbrev Says (φ : Fm) (P : (Nat → V) → Prop) : Prop :=
  ∃ ψ : Fm, (∀ n, occurs n ψ = true → occurs n φ = true) ∧ ∀ v, evalF v ψ = T ↔ P v

/-- **The judge speaks ZTL** (paper §5.3). For every formula φ, each of the six dispositions of φ is the
T-value of a ZTL formula over the atoms of φ. -/
theorem judge_speaks_ztl (φ : Fm) :
    Says φ (fun v => StrictEarned v φ) ∧ Says φ (fun v => EarnedIfStable v φ) ∧
    Says φ (fun v => OnCredit v φ) ∧ Says φ (fun v => Open v φ) ∧
    Says φ (fun v => RefutedIfStable v φ) ∧ Says φ (fun v => StrictRefuted v φ) := by
  have eB := fun v => allR_iff T φ v
  have rB := fun v => allR_iff F φ v
  have eC := fun v w h => allR_congr T φ v w h
  have rC := fun v w h => allR_congr F φ v w h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact speak φ _ (fun v => decide (kev v φ = T))
      (fun v => (decide_iff _).trans (strict_earned_iff_kleene v φ).symm)
      (fun v w h => by dsimp only; rw [kev_congr v w φ h])
  · exact speak φ _ (fun v => allR T φ (atomsL φ) v && !decide (kev v φ = T))
      (fun v => (and_not_iff _ _).trans ⟨fun ⟨a, b⟩ => ⟨(eB v).mp a, fun k => b (decide_eq_true k)⟩,
        fun ⟨a, b⟩ => ⟨(eB v).mpr a, fun k => b (of_decide_eq_true k)⟩⟩)
      (fun v w h => by dsimp only; rw [eC v w h, kev_congr v w φ h])
  · exact speak φ _ (fun v => decide (evalF v φ = T) && !allR T φ (atomsL φ) v)
      (fun v => (and_not_iff _ _).trans ⟨fun ⟨a, b⟩ => ⟨of_decide_eq_true a, fun k => b ((eB v).mpr k)⟩,
        fun ⟨a, b⟩ => ⟨decide_eq_true a, fun k => b ((eB v).mp k)⟩⟩)
      (fun v w h => by dsimp only; rw [eC v w h, evalF_congr v w φ h])
  · exact speak φ _ (fun v => !decide (evalF v φ = T) && !allR F φ (atomsL φ) v)
      (fun v => (not_and_not_iff _ _).trans ⟨fun ⟨a, b⟩ => ⟨fun k => a (decide_eq_true k), fun k => b ((rB v).mpr k)⟩,
        fun ⟨a, b⟩ => ⟨fun k => a (of_decide_eq_true k), fun k => b ((rB v).mp k)⟩⟩)
      (fun v w h => by dsimp only; rw [rC v w h, evalF_congr v w φ h])
  · exact speak φ _ (fun v => allR F φ (atomsL φ) v && !decide (kev v φ = F))
      (fun v => (and_not_iff _ _).trans ⟨fun ⟨a, b⟩ => ⟨(rB v).mp a, fun k => b (decide_eq_true k)⟩,
        fun ⟨a, b⟩ => ⟨(rB v).mpr a, fun k => b (of_decide_eq_true k)⟩⟩)
      (fun v w h => by dsimp only; rw [rC v w h, kev_congr v w φ h])
  · exact speak φ _ (fun v => decide (kev v φ = F))
      (fun v => (decide_iff _).trans (strict_refuted_iff_kleene v φ).symm)
      (fun v w h => by dsimp only; rw [kev_congr v w φ h])

/-- The six dispositions cover every case, and earned and refuted exclude each other (the other pairs are
disjoint by their definitions: Kleene T or not, earned or not, T now or not). -/
theorem dispositions_partition (v : Nat → V) (φ : Fm) :
    (StrictEarned v φ ∨ EarnedIfStable v φ ∨ OnCredit v φ ∨ Open v φ ∨ RefutedIfStable v φ ∨ StrictRefuted v φ) ∧
    ¬ (Earned v φ ∧ Refuted v φ) := by
  have eB := allR_iff T φ v
  have rB := allR_iff F φ v
  refine ⟨?_, fun ⟨e, r⟩ => absurd ((e v (refines_refl v)).symm.trans (r v (refines_refl v))) (by decide)⟩
  cases he : allR T φ (atomsL φ) v with
  | true =>
      have e := eB.mp he
      match decEq (kev v φ) T with
      | isTrue k => exact Or.inl ⟨e, k⟩
      | isFalse k => exact Or.inr (Or.inl ⟨e, k⟩)
  | false =>
      have ne : ¬ Earned v φ := fun e => by rw [eB.mpr e] at he; exact nomatch he
      match decEq (evalF v φ) T with
      | isTrue t => exact Or.inr (Or.inr (Or.inl ⟨t, ne⟩))
      | isFalse t =>
          cases hr : allR F φ (atomsL φ) v with
          | false =>
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, fun r => by rw [rB.mpr r] at hr; exact nomatch hr⟩)))
          | true =>
              have r := rB.mp hr
              match decEq (kev v φ) F with
              | isTrue k => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, k⟩))))
              | isFalse k => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k⟩))))

end Speak
end V

#print axioms V.Speak.allR_iff
#print axioms V.Speak.kev_congr
#print axioms V.Speak.speak
#print axioms V.Speak.judge_speaks_ztl
#print axioms V.Speak.dispositions_partition
