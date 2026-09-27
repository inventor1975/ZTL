import LabelExact
import NoGift

/-!
# The warranty grade without the walk, proved. Zero axioms. (2026-09-27)

`zverify._only(φ, fixed, free, v)` (2026-09-27, PR #2) answers "is φ equal to v under
every choice of the free atoms?" without enumerating the choices. It replaced a walk over
3ⁿ refinements whose running time depended on the hash seed (0.19–12.9 s on one claim,
now 0.047 s on every seed), and it was checked on 1,000,000 claims against that walk.
This module is why it is right for every claim.

An atom's allowed values are a predicate `ch n` (a fixed atom: one value; a free mark:
T, F or Z; a free unknown: T or F). A valuation is admissible (`Adm`) when every atom
takes an allowed value. `Reach` is the compositional pass (`zverify._reach`): an atom
reaches its allowed values, a node reaches its connective applied to what its children
reach.

    reach_sound      every admissible valuation's value is reached
    reach_complete   if no atom with a choice occurs twice, every reached value is the
                     value of some admissible valuation
    only_exact       hence, under that linearity, "all admissible valuations give v"
                     is exactly "everything reached is v" — `_reach` answers exactly
    split            fixing one atom to each of its values in turn loses nothing — the
                     Shannon step `_values` uses on a repeated atom; a pinned atom is
                     fixed, so repeated splitting ends in the linear case

What is argued, not checked: `_fold` (a node whose value no longer depends on its free
side is replaced by that value) is an evaluation step, not a change of meaning; and the
recursion of `_values` — split on a repeated free atom until none is left, then `_reach`
— is `split` applied until `only_exact` applies. Both are measured: the million-claim
equivalence and `test_judge_perf.py`.
-/

namespace V

/-- Every atom takes one of its allowed values. -/
def Adm (ch : Nat → V → Prop) (w : Nat → V) : Prop := ∀ n, ch n (w n)

/-- An atom whose allowed values are all equal — fixed, not free. -/
def Fixed (ch : Nat → V → Prop) (n : Nat) : Prop := ∀ x y, ch n x → ch n y → x = y

/-- The compositional pass `zverify._reach`. -/
inductive Reach (ch : Nat → V → Prop) : Fm → V → Prop
  | atom (n : Nat) (x : V) : ch n x → Reach ch (.atom n) x
  | top : Reach ch .top T
  | bot : Reach ch .bot F
  | neg (φ : Fm) (x : V) : Reach ch φ x → Reach ch (.neg φ) (znot x)
  | conj (φ ψ : Fm) (x y : V) : Reach ch φ x → Reach ch ψ y → Reach ch (.conj φ ψ) (zand x y)
  | disj (φ ψ : Fm) (x y : V) : Reach ch φ x → Reach ch ψ y → Reach ch (.disj φ ψ) (zor x y)
  | imp (φ ψ : Fm) (x y : V) : Reach ch φ x → Reach ch ψ y → Reach ch (.imp φ ψ) (zimp x y)
  | xor (φ ψ : Fm) (x y : V) : Reach ch φ x → Reach ch ψ y → Reach ch (.xor φ ψ) (zxor x y)
  | xnor (φ ψ : Fm) (x y : V) : Reach ch φ x → Reach ch ψ y → Reach ch (.xnor φ ψ) (zxnor x y)

/-- SOUND: every admissible valuation's value is reached. -/
theorem reach_sound (ch : Nat → V → Prop) (w : Nat → V) (hw : Adm ch w) :
    ∀ φ : Fm, Reach ch φ (evalF w φ) := by
  intro φ
  induction φ with
  | atom n => exact Reach.atom n (w n) (hw n)
  | top => exact Reach.top
  | bot => exact Reach.bot
  | neg φ ih => exact Reach.neg φ _ ih
  | conj φ ψ ihφ ihψ => exact Reach.conj φ ψ _ _ ihφ ihψ
  | disj φ ψ ihφ ihψ => exact Reach.disj φ ψ _ _ ihφ ihψ
  | imp φ ψ ihφ ihψ => exact Reach.imp φ ψ _ _ ihφ ihψ
  | xor φ ψ ihφ ihψ => exact Reach.xor φ ψ _ _ ihφ ihψ
  | xnor φ ψ ihφ ihψ => exact Reach.xnor φ ψ _ _ ihφ ihψ

/-- Two admissible valuations, one per branch, merged into one that keeps both values —
possible exactly because no atom with a choice sits in both branches. -/
theorem merge_both (ch : Nat → V → Prop) (φ ψ : Fm) (wφ wψ : Nat → V)
    (hφ : Adm ch wφ) (hψ : Adm ch wψ)
    (hlin : ∀ n, 2 ≤ occCount n φ + occCount n ψ → Fixed ch n) :
    Adm ch (merge φ wφ wψ) ∧ evalF (merge φ wφ wψ) φ = evalF wφ φ
      ∧ evalF (merge φ wφ wψ) ψ = evalF wψ ψ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    show ch n (if occurs n φ = true then wφ n else wψ n)
    cases occurs n φ with
    | true => exact hφ n
    | false => exact hψ n
  · exact evalF_congr _ _ φ (fun n hn => merge_left φ wφ wψ n hn)
  · apply evalF_congr
    intro n hn
    show (if occurs n φ = true then wφ n else wψ n) = wψ n
    cases hp : occurs n φ with
    | false => rfl
    | true =>
        have h1 : 1 ≤ occCount n φ := Nat.pos_of_ne_zero (occCount_pos_of_occurs n φ hp)
        have h2 : 1 ≤ occCount n ψ := Nat.pos_of_ne_zero (occCount_pos_of_occurs n ψ hn)
        exact hlin n (Nat.add_le_add h1 h2) _ _ (hφ n) (hψ n)

/-- A valuation that puts `x` at `n` and agrees with `w0` elsewhere. -/
def setAt (w0 : Nat → V) (n : Nat) (x : V) : Nat → V := fun m => if m = n then x else w0 m

/-- COMPLETE when no atom with a choice occurs twice: every reached value is attained. -/
theorem reach_complete (ch : Nat → V → Prop) (w0 : Nat → V) (h0 : Adm ch w0) :
    ∀ φ x, Reach ch φ x → (∀ n, 2 ≤ occCount n φ → Fixed ch n) →
      ∃ w, Adm ch w ∧ evalF w φ = x := by
  intro φ x hr
  induction hr with
  | atom n x hx =>
      intro _
      refine ⟨setAt w0 n x, ?_, ?_⟩
      · intro m
        show ch m (if m = n then x else w0 m)
        cases Nat.decEq m n with
        | isTrue e => rw [if_pos e]; rw [e]; exact hx
        | isFalse e => rw [if_neg e]; exact h0 m
      · show (if n = n then x else w0 n) = x
        rw [if_pos rfl]
  | top => intro _; exact ⟨w0, h0, rfl⟩
  | bot => intro _; exact ⟨w0, h0, rfl⟩
  | neg φ x _ ih =>
      intro hlin
      match ih hlin with
      | ⟨w, hw, he⟩ => exact ⟨w, hw, by show znot (evalF w φ) = znot x; rw [he]⟩
  | conj φ ψ x y _ _ ihφ ihψ =>
      intro hlin
      match ihφ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_right _ _))),
            ihψ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_left _ _))) with
      | ⟨wφ, hwφ, eφ⟩, ⟨wψ, hwψ, eψ⟩ =>
          match merge_both ch φ ψ wφ wψ hwφ hwψ hlin with
          | ⟨ha, e1, e2⟩ =>
              exact ⟨_, ha, by show zand (evalF _ φ) (evalF _ ψ) = zand x y; rw [e1, e2, eφ, eψ]⟩
  | disj φ ψ x y _ _ ihφ ihψ =>
      intro hlin
      match ihφ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_right _ _))),
            ihψ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_left _ _))) with
      | ⟨wφ, hwφ, eφ⟩, ⟨wψ, hwψ, eψ⟩ =>
          match merge_both ch φ ψ wφ wψ hwφ hwψ hlin with
          | ⟨ha, e1, e2⟩ =>
              exact ⟨_, ha, by show zor (evalF _ φ) (evalF _ ψ) = zor x y; rw [e1, e2, eφ, eψ]⟩
  | imp φ ψ x y _ _ ihφ ihψ =>
      intro hlin
      match ihφ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_right _ _))),
            ihψ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_left _ _))) with
      | ⟨wφ, hwφ, eφ⟩, ⟨wψ, hwψ, eψ⟩ =>
          match merge_both ch φ ψ wφ wψ hwφ hwψ hlin with
          | ⟨ha, e1, e2⟩ =>
              exact ⟨_, ha, by show zimp (evalF _ φ) (evalF _ ψ) = zimp x y; rw [e1, e2, eφ, eψ]⟩
  | xor φ ψ x y _ _ ihφ ihψ =>
      intro hlin
      match ihφ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_right _ _))),
            ihψ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_left _ _))) with
      | ⟨wφ, hwφ, eφ⟩, ⟨wψ, hwψ, eψ⟩ =>
          match merge_both ch φ ψ wφ wψ hwφ hwψ hlin with
          | ⟨ha, e1, e2⟩ =>
              exact ⟨_, ha, by show zxor (evalF _ φ) (evalF _ ψ) = zxor x y; rw [e1, e2, eφ, eψ]⟩
  | xnor φ ψ x y _ _ ihφ ihψ =>
      intro hlin
      match ihφ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_right _ _))),
            ihψ (fun n h => hlin n (Nat.le_trans h (Nat.le_add_left _ _))) with
      | ⟨wφ, hwφ, eφ⟩, ⟨wψ, hwψ, eψ⟩ =>
          match merge_both ch φ ψ wφ wψ hwφ hwψ hlin with
          | ⟨ha, e1, e2⟩ =>
              exact ⟨_, ha, by show zxnor (evalF _ φ) (evalF _ ψ) = zxnor x y; rw [e1, e2, eφ, eψ]⟩

/-- EXACT: under linearity, "every admissible valuation gives v" is exactly "everything
reached is v" — what `_only` returns when no free atom repeats. -/
theorem only_exact (ch : Nat → V → Prop) (w0 : Nat → V) (h0 : Adm ch w0) (φ : Fm) (v : V)
    (hlin : ∀ n, 2 ≤ occCount n φ → Fixed ch n) :
    (∀ w, Adm ch w → evalF w φ = v) ↔ (∀ x, Reach ch φ x → x = v) := by
  constructor
  · intro hall x hr
    match reach_complete ch w0 h0 φ x hr hlin with
    | ⟨w, hw, e⟩ => rw [← e]; exact hall w hw
  · intro hre w hw
    exact hre _ (reach_sound ch w hw φ)

/-- Atom `a` pinned to the value `c`; every other atom keeps its choices. -/
def pin (ch : Nat → V → Prop) (a : Nat) (c : V) : Nat → V → Prop :=
  fun n x => if n = a then x = c else ch n x

theorem pin_fixed (ch : Nat → V → Prop) (a : Nat) (c : V) : Fixed (pin ch a c) a := by
  intro x y hx hy
  have ex : x = c := by
    have h : (if a = a then x = c else ch a x) := hx
    rw [if_pos rfl] at h; exact h
  have ey : y = c := by
    have h : (if a = a then y = c else ch a y) := hy
    rw [if_pos rfl] at h; exact h
  rw [ex, ey]

/-- SPLIT: fixing atom `a` to each of its allowed values in turn loses nothing. -/
theorem split (ch : Nat → V → Prop) (a : Nat) (φ : Fm) (v : V) :
    (∀ w, Adm ch w → evalF w φ = v) ↔
      (∀ c, ch a c → ∀ w, Adm (pin ch a c) w → evalF w φ = v) := by
  constructor
  · intro hall c hc w hw
    apply hall w
    intro n
    have h : (if n = a then w n = c else ch n (w n)) := hw n
    cases Nat.decEq n a with
    | isTrue e => rw [if_pos e] at h; rw [e] at h ⊢; rw [h]; exact hc
    | isFalse e => rw [if_neg e] at h; exact h
  · intro hsp w hw
    apply hsp (w a) (hw a) w
    intro n
    show (if n = a then w n = w a else ch n (w n))
    cases Nat.decEq n a with
    | isTrue e => rw [if_pos e, e]
    | isFalse e => rw [if_neg e]; exact hw n

end V
