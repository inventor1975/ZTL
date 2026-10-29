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

/-! ## (1') The search over completions (IF STABLE, 2026-10-29 evening)

A completion of v fills every dirty atom with T or F (`total`, `refines`); `Enum` (ZDirty) is "T in every
completion". `allC` decides it for the atoms of φ: it branches on each dirty atom with T and F only. -/

/-- v with its remaining dirty atoms filled with T (used only where none of φ's atoms is dirty any more) -/
def fill (v : Nat → V) : Nat → V := fun n => if v n = Z then T else v n

theorem fill_total (v : Nat → V) : total (fill v) := by
  intro n
  show (if v n = Z then T else v n) ≠ Z
  match decEq (v n) Z with
  | isTrue h => rw [if_pos h]; exact fun e => nomatch e
  | isFalse h => rw [if_neg h]; exact h

theorem fill_refines (v : Nat → V) : refines v (fill v) := by
  intro n hn; show (if v n = Z then T else v n) = v n; exact if_neg hn

/-- φ takes the value t in every completion of v, completing the atoms xs -/
def allC (t : V) (φ : Fm) : List Nat → (Nat → V) → Bool
  | [], v => decide (evalF (fill v) φ = t)
  | x :: xs, v =>
      if v x = Z then allC t φ xs (upd v x T) && allC t φ xs (upd v x F)
      else allC t φ xs v

theorem not_decide_iff (p : Prop) [Decidable p] : (!decide p) = true ↔ ¬ p := by
  constructor
  · intro h k
    rw [decide_eq_true k] at h
    exact nomatch h
  · intro h
    rw [decide_eq_false h]
    rfl

theorem and2 : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by decide
theorem and2_intro : ∀ a b : Bool, a = true → b = true → (a && b) = true := by decide

theorem allC_sound (t : V) (φ : Fm) : ∀ (xs : List Nat) (v w : Nat → V), refines v w → total w →
    (∀ n, occurs n φ = true → memB n xs = false → w n = v n) → allC t φ xs v = true → evalF w φ = t
  | [], v, w, _, ht, hoff, h => by
      rw [evalF_congr w (fill v) φ (fun n hn => by
        have e := hoff n hn rfl
        show w n = (if v n = Z then T else v n)
        match decEq (v n) Z with
        | isTrue hz => exact absurd (e.trans hz) (ht n)
        | isFalse hz => rw [if_neg hz]; exact e)]
      exact of_decide_eq_true h
  | x :: xs, v, w, hr, ht, hoff, h => by
      match decEq (v x) Z with
      | isTrue hz =>
          have e : allC t φ (x :: xs) v = (allC t φ xs (upd v x T) && allC t φ xs (upd v x F)) := if_pos hz
          rw [e] at h
          have key : ∀ c : V, w x = c → allC t φ xs (upd v x c) = true → evalF w φ = t := by
            intro c hc hall
            apply allC_sound t φ xs (upd v x c) w _ ht _ hall
            · intro n hn
              match Nat.decEq n x with
              | isTrue en => rw [en, hc]; exact (upd_at v x c).symm
              | isFalse en =>
                  have hu : upd v x c n = v n := if_neg en
                  rw [hu] at hn ⊢; exact hr n hn
            · intro n hocc hm
              match Nat.decEq n x with
              | isTrue en => rw [en, hc]; exact (upd_at v x c).symm
              | isFalse en =>
                  have hu : upd v x c n = v n := if_neg en
                  rw [hu]
                  exact hoff n hocc (by
                    show (decide (n = x) || memB n xs) = false
                    rw [decide_eq_false en, hm]; rfl)
          obtain ⟨hT, hF⟩ := and2 _ _ h
          cases hw : w x with
          | T => exact key T hw hT
          | F => exact key F hw hF
          | Z => exact absurd hw (ht x)
      | isFalse hz =>
          have e : allC t φ (x :: xs) v = allC t φ xs v := if_neg hz
          rw [e] at h
          apply allC_sound t φ xs v w hr ht _ h
          intro n hocc hm
          match Nat.decEq n x with
          | isTrue en => rw [en]; exact hr x hz
          | isFalse en =>
              exact hoff n hocc (by
                show (decide (n = x) || memB n xs) = false
                rw [decide_eq_false en, hm]; rfl)

theorem allC_complete (t : V) (φ : Fm) : ∀ (xs : List Nat) (v : Nat → V),
    (∀ w, refines v w → total w → evalF w φ = t) → allC t φ xs v = true
  | [], v, h => decide_eq_true (h (fill v) (fill_refines v) (fill_total v))
  | x :: xs, v, h => by
      match decEq (v x) Z with
      | isTrue hz =>
          have e : allC t φ (x :: xs) v = (allC t φ xs (upd v x T) && allC t φ xs (upd v x F)) := if_pos hz
          rw [e]
          have br : ∀ c : V, allC t φ xs (upd v x c) = true := by
            intro c
            apply allC_complete t φ xs (upd v x c)
            intro w hr ht
            apply h w _ ht
            intro n hn
            match Nat.decEq n x with
            | isTrue en => rw [en] at hn; exact absurd hz hn
            | isFalse en =>
                have hu : upd v x c n = v n := if_neg en
                have := hr n (by rw [hu]; exact hn)
                rw [this, hu]
          exact and2_intro _ _ (br T) (br F)
      | isFalse hz =>
          have e : allC t φ (x :: xs) v = allC t φ xs v := if_neg hz
          rw [e]; exact allC_complete t φ xs v h

/-- the search over the atoms of φ decides "t in every completion" -/
theorem allC_iff (t : V) (φ : Fm) (v : Nat → V) :
    allC t φ (atomsL φ) v = true ↔ ∀ w, refines v w → total w → evalF w φ = t :=
  ⟨fun h w hr ht => allC_sound t φ (atomsL φ) v w hr ht (fun n hocc hm => by
      rw [occurs_memB n φ hocc] at hm; exact nomatch hm) h,
   allC_complete t φ (atomsL φ) v⟩

theorem every_completion_congr (t : V) (φ : Fm) (v w : Nat → V) (h : ∀ n, occurs n φ = true → v n = w n)
    (hv : ∀ w', refines v w' → total w' → evalF w' φ = t) : ∀ w', refines w w' → total w' → evalF w' φ = t := by
  intro w' hr ht
  let v' : Nat → V := fun n => if occurs n φ = true then w' n else fill v n
  have hrv : refines v v' := by
    intro n hn
    show (if occurs n φ = true then w' n else fill v n) = v n
    match decEq (occurs n φ) true with
    | isTrue ho =>
        rw [if_pos ho, h n ho]
        exact hr n (by rw [← h n ho]; exact hn)
    | isFalse ho => rw [if_neg ho]; exact fill_refines v n hn
  have htv : total v' := by
    intro n
    show (if occurs n φ = true then w' n else fill v n) ≠ Z
    match decEq (occurs n φ) true with
    | isTrue ho => rw [if_pos ho]; exact ht n
    | isFalse ho => rw [if_neg ho]; exact fill_total v n
  rw [← hv v' hrv htv]
  exact evalF_congr w' v' φ (fun n ho => by
    show w' n = (if occurs n φ = true then w' n else fill v n)
    rw [if_pos ho])

theorem allC_congr (t : V) (φ : Fm) (v w : Nat → V) (h : ∀ n, occurs n φ = true → v n = w n) :
    allC t φ (atomsL φ) v = allC t φ (atomsL φ) w :=
  bool_eq_of_iff _ _ ⟨
    fun hv => (allC_iff t φ w).mpr (every_completion_congr t φ v w h ((allC_iff t φ v).mp hv)),
    fun hw => (allC_iff t φ v).mpr (every_completion_congr t φ w v (fun n ho => (h n ho).symm)
      ((allC_iff t φ w).mp hw))⟩

/-! ## The six dispositions (the judge since 2026-10-29 evening)

EARNED: strong Kleene T. REFUTED: strong Kleene F. Otherwise EARNED IF STABLE: T in every completion (each dirty
atom read the same at all its occurrences); REFUTED IF STABLE: F in every completion; ON CREDIT: T now, and the
completions disagree; OPEN: not T now, and the completions disagree. -/

def StableF (v : Nat → V) (φ : Fm) : Prop := ∀ w, refines v w → total w → evalF w φ = F
def EarnedIfStable (v : Nat → V) (φ : Fm) : Prop := kev v φ ≠ T ∧ Enum v φ
def RefutedIfStable (v : Nat → V) (φ : Fm) : Prop := kev v φ ≠ F ∧ StableF v φ
def OnCredit (v : Nat → V) (φ : Fm) : Prop := evalF v φ = T ∧ kev v φ ≠ T ∧ ¬ Enum v φ ∧ ¬ StableF v φ
def Open (v : Nat → V) (φ : Fm) : Prop := evalF v φ ≠ T ∧ kev v φ ≠ F ∧ ¬ Enum v φ ∧ ¬ StableF v φ

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

/-- **The judge speaks ZTL.** For every formula φ, each of the six dispositions of φ is the T-value of a ZTL
formula over the atoms of φ. -/
theorem judge_speaks_ztl (φ : Fm) :
    Says φ (fun v => StrictEarned v φ) ∧ Says φ (fun v => EarnedIfStable v φ) ∧
    Says φ (fun v => OnCredit v φ) ∧ Says φ (fun v => Open v φ) ∧
    Says φ (fun v => RefutedIfStable v φ) ∧ Says φ (fun v => StrictRefuted v φ) := by
  have eB := fun v => allC_iff T φ v
  have rB := fun v => allC_iff F φ v
  have eC := fun v w h => allC_congr T φ v w h
  have rC := fun v w h => allC_congr F φ v w h
  have nn := @not_decide_iff
  have nb : ∀ b : Bool, (!b) = true ↔ ¬ b = true := by decide
  have a2 : ∀ a b : Bool, (a && b) = true ↔ (a = true ∧ b = true) := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact speak φ _ (fun v => decide (kev v φ = T))
      (fun v => (decide_iff _).trans (strict_earned_iff_kleene v φ).symm)
      (fun v w h => by dsimp only; rw [kev_congr v w φ h])
  · exact speak φ _ (fun v => !decide (kev v φ = T) && allC T φ (atomsL φ) v)
      (fun v => (a2 _ _).trans ⟨fun ⟨a, b⟩ => ⟨(nn _).mp a, (eB v).mp b⟩,
        fun ⟨a, b⟩ => ⟨(nn _).mpr a, (eB v).mpr b⟩⟩)
      (fun v w h => by dsimp only; rw [eC v w h, kev_congr v w φ h])
  · exact speak φ _ (fun v => decide (evalF v φ = T) && !decide (kev v φ = T) &&
        !allC T φ (atomsL φ) v && !allC F φ (atomsL φ) v)
      (fun v => by
        refine ⟨fun h => ?_, fun ⟨a, b, c, d⟩ => ?_⟩
        · obtain ⟨h, d⟩ := (a2 _ _).mp h; obtain ⟨h, c⟩ := (a2 _ _).mp h; obtain ⟨a, b⟩ := (a2 _ _).mp h
          exact ⟨of_decide_eq_true a, (nn _).mp b, fun k => (nb _).mp c ((eB v).mpr k),
            fun k => (nb _).mp d ((rB v).mpr k)⟩
        · exact (a2 _ _).mpr ⟨(a2 _ _).mpr ⟨(a2 _ _).mpr ⟨decide_eq_true a, (nn _).mpr b⟩,
            (nb _).mpr (fun k => c ((eB v).mp k))⟩, (nb _).mpr (fun k => d ((rB v).mp k))⟩)
      (fun v w h => by dsimp only; rw [eC v w h, rC v w h, kev_congr v w φ h, evalF_congr v w φ h])
  · exact speak φ _ (fun v => !decide (evalF v φ = T) && !decide (kev v φ = F) &&
        !allC T φ (atomsL φ) v && !allC F φ (atomsL φ) v)
      (fun v => by
        refine ⟨fun h => ?_, fun ⟨a, b, c, d⟩ => ?_⟩
        · obtain ⟨h, d⟩ := (a2 _ _).mp h; obtain ⟨h, c⟩ := (a2 _ _).mp h; obtain ⟨a, b⟩ := (a2 _ _).mp h
          exact ⟨(nn _).mp a, (nn _).mp b, fun k => (nb _).mp c ((eB v).mpr k),
            fun k => (nb _).mp d ((rB v).mpr k)⟩
        · exact (a2 _ _).mpr ⟨(a2 _ _).mpr ⟨(a2 _ _).mpr ⟨(nn _).mpr a, (nn _).mpr b⟩,
            (nb _).mpr (fun k => c ((eB v).mp k))⟩, (nb _).mpr (fun k => d ((rB v).mp k))⟩)
      (fun v w h => by dsimp only; rw [eC v w h, rC v w h, kev_congr v w φ h, evalF_congr v w φ h])
  · exact speak φ _ (fun v => !decide (kev v φ = F) && allC F φ (atomsL φ) v)
      (fun v => (a2 _ _).trans ⟨fun ⟨a, b⟩ => ⟨(nn _).mp a, (rB v).mp b⟩,
        fun ⟨a, b⟩ => ⟨(nn _).mpr a, (rB v).mpr b⟩⟩)
      (fun v w h => by dsimp only; rw [rC v w h, kev_congr v w φ h])
  · exact speak φ _ (fun v => decide (kev v φ = F))
      (fun v => (decide_iff _).trans (strict_refuted_iff_kleene v φ).symm)
      (fun v w h => by dsimp only; rw [kev_congr v w φ h])

/-- The six dispositions cover every case. -/
theorem dispositions_partition (v : Nat → V) (φ : Fm) :
    StrictEarned v φ ∨ EarnedIfStable v φ ∨ OnCredit v φ ∨ Open v φ ∨ RefutedIfStable v φ ∨
      StrictRefuted v φ := by
  have eB := allC_iff T φ v
  have rB := allC_iff F φ v
  match decEq (kev v φ) T with
  | isTrue k => exact Or.inl ((strict_earned_iff_kleene v φ).mpr k)
  | isFalse kT =>
  match decEq (kev v φ) F with
  | isTrue k => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((strict_refuted_iff_kleene v φ).mpr k)))))
  | isFalse kF =>
  cases he : allC T φ (atomsL φ) v with
  | true => exact Or.inr (Or.inl ⟨kT, eB.mp he⟩)
  | false =>
  have ne : ¬ Enum v φ := fun e => by rw [eB.mpr e] at he; exact nomatch he
  cases hr : allC F φ (atomsL φ) v with
  | true => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨kF, rB.mp hr⟩))))
  | false =>
  have nr : ¬ StableF v φ := fun e => by rw [rB.mpr e] at hr; exact nomatch hr
  match decEq (evalF v φ) T with
  | isTrue t => exact Or.inr (Or.inr (Or.inl ⟨t, kT, ne, nr⟩))
  | isFalse t => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, kF, ne, nr⟩)))

/-! ## Two statements the first cloud review asked for (2026-10-29) -/

/-- ¬(p ∧ ¬p) on a dirty p: strong Kleene does not say T, the judge says EARNED IF STABLE, and every completion
(every classical substitution of p) grants it. -/
theorem lnc_if_stable :
    kev (fun _ => Z) (.neg (.conj (.atom 0) (.neg (.atom 0)))) ≠ T ∧
    EarnedIfStable (fun _ => Z) (.neg (.conj (.atom 0) (.neg (.atom 0)))) :=
  ⟨by decide, by decide, (allC_iff T _ _).mp (by decide)⟩

/-- **Dominance, in one statement.** Let w be any classical substitution of the dirty atoms of v (a completion).
Wherever w answers right — it grants φ exactly when the dirty reading earns φ (strong Kleene T) — the judge's
grant (EARNED or EARNED IF STABLE, i.e. T in every completion) is right too. -/
theorem grant_right_where_substitution_right (v w : Nat → V) (φ : Fm) (hr : refines v w) (ht : total w)
    (hw : evalF w φ = T ↔ kev v φ = T) : Enum v φ ↔ kev v φ = T :=
  ⟨fun h => hw.mp (h w hr ht), fun k => enum_of_earned v φ (earned_of_kleene v φ k)⟩

/-- The judge's grant is EARNED or EARNED IF STABLE, and that is exactly "T in every completion". -/
theorem grant_iff_enum (v : Nat → V) (φ : Fm) : (StrictEarned v φ ∨ EarnedIfStable v φ) ↔ Enum v φ :=
  ⟨fun h => h.elim (fun e => enum_of_earned v φ e.1) (fun e => e.2),
   fun h => match decEq (kev v φ) T with
     | isTrue k => Or.inl ((strict_earned_iff_kleene v φ).mpr k)
     | isFalse k => Or.inr ⟨k, h⟩⟩

end Speak
end V

#print axioms V.Speak.allR_iff
#print axioms V.Speak.allC_iff
#print axioms V.Speak.kev_congr
#print axioms V.Speak.speak
#print axioms V.Speak.judge_speaks_ztl
#print axioms V.Speak.dispositions_partition
#print axioms V.Speak.lnc_if_stable
#print axioms V.Speak.grant_right_where_substitution_right
#print axioms V.Speak.grant_iff_enum
