/-
  ZAxiomsRead.lean — Lean's three axioms read inside ZTL: each fails on a dirty input, each holds on clean ones.
  Zero axioms.

  WHY (2026-11-06, the curator: "Мы философски следуем безаксиомности… можем использовать их, если нет грязного
  параметра. Как они есть — это опасно. Но если выведем теоремы-аналоги, нам будет полезно"). The corpus proves
  everything on the empty axiom list. Each of Lean's three axioms says "this need not be checked":
    propext        equivalent propositions are equal — "what is equivalent need not be told apart";
    Quot.sound     related elements have equal classes; funext follows — "what agrees on every observation is the same";
    Classical.choice  a witness may be picked without being produced; excluded middle follows — "A or not A is decided".
  Read with ZTL's values, each "need not be checked" fails exactly on a DIRTY input (Z), and holds on CLEAN ones (T, F).
  So the analogues below are tools with their condition written in: usable where no dirty parameter is involved.

  NOT CLAIMED: that the axioms are false in Lean. They are consistent there and true in the usual set-theoretic model.
  What is shown is that their ZTL readings break on unchecked data — the reason the corpus keeps them out by default,
  and a proof on the empty list stays valid whoever adds them later.

  PROVED, all by finite cases over ZTL's three values:
  1. propext:   `propext_fails_dirty` — p and p∧p are interderivable yet not interchangeable (¬(p∧p) is T, ¬p is not,
                at p = Z; ZAlgebra.not_selfextensional is the same fact); `propext_needs_clean` — without "clean", "T exactly
                together" is not equality (F and Z); `propext_clean` — on clean values it is, so interchangeable in
                every context.
  2. Quot.sound / funext:  `funext_obs_fails` — x and x∧x agree on T and on F, and differ at Z; `funext_obs_lift1`,
                `funext_obs_lift2` — for ONE connective, agreeing on the clean inputs is agreeing everywhere (its value
                at Z is fixed by its clean values). The boundary is per connective, not per formula — as for degrees
                (ZDegrees.compound_is_node_by_node).
  3. Excluded middle (choice's consequence): `lem_fails_dirty` — A ∨ ¬A is not T at A = Z; `lem_clean` — it is T on
                every clean A.
-/
import ZTL

namespace ZAxiomsRead

open V

/-! ### 1. propext -/

/-- Interderivable (each T exactly when the other is) — yet a context tells them apart at Z. -/
theorem propext_fails_dirty :
    (∀ a : V, a = T ↔ zand a a = T) ∧ znot (zand Z Z) = T ∧ znot Z ≠ T :=
  ⟨by decide, rfl, by decide⟩

/-- The boundary: without "clean", "T exactly together" is not equality — F and Z are both "not T", and differ. -/
theorem propext_needs_clean : ¬ ∀ a b : V, (a = T ↔ b = T) → a = b := by decide

/-- On clean values, "T exactly together" is equality — and equal values are interchangeable in every context. -/
theorem propext_clean (a b : V) (ha : a ≠ Z) (hb : b ≠ Z) (h : a = T ↔ b = T) (f : V → V) : f a = f b := by
  have : a = b := by
    cases a <;> cases b
    · rfl
    · exact absurd (h.mp rfl) (by decide)
    · exact absurd rfl hb
    · exact absurd (h.mpr rfl) (by decide)
    · rfl
    · exact absurd rfl hb
    · exact absurd rfl ha
    · exact absurd rfl ha
    · exact absurd rfl ha
  rw [this]

/-! ### 2. Quot.sound / funext by observation -/

/-- Two formulas that agree on every clean input, and are not the same function. -/
theorem funext_obs_fails :
    (∀ x : V, x ≠ Z → zand x x = x) ∧ zand Z Z ≠ Z := by
  refine ⟨?_, by decide⟩
  intro x hx
  cases x
  · rfl
  · rfl
  · exact absurd rfl hx

/-- A one-argument connective as its truth table, and a two-argument one. -/
def tab1 (p q : Bool) : Bool → Bool
  | true => p
  | false => q

def tab2 (p q r t : Bool) : Bool → Bool → Bool
  | true, true => p
  | true, false => q
  | false, true => r
  | false, false => t

theorem lift1_tab (g : Bool → Bool) (x : V) : lift1 g x = lift1 (tab1 (g true) (g false)) x := by
  cases x <;> rfl

theorem lift2_tab (g : Bool → Bool → Bool) (x y : V) :
    lift2 g x y = lift2 (tab2 (g true true) (g true false) (g false true) (g false false)) x y := by
  cases x <;> cases y <;> rfl

/-- On tables: agreeing at T and at F is agreeing everywhere (finite cases). -/
theorem tab1_obs (p q p' q' : Bool) (hT : lift1 (tab1 p q) T = lift1 (tab1 p' q') T)
    (hF : lift1 (tab1 p q) F = lift1 (tab1 p' q') F) : ∀ x : V, lift1 (tab1 p q) x = lift1 (tab1 p' q') x := by
  revert hT hF
  cases p <;> cases q <;> cases p' <;> cases q' <;> decide

/-- One lifted connective is fixed by its clean values: agreeing on T and F is agreeing on Z too. -/
theorem funext_obs_lift1 (g h : Bool → Bool) (hT : lift1 g T = lift1 h T) (hF : lift1 g F = lift1 h F) :
    ∀ x : V, lift1 g x = lift1 h x := by
  intro x
  rw [lift1_tab g x, lift1_tab h x]
  rw [lift1_tab g T, lift1_tab h T] at hT
  rw [lift1_tab g F, lift1_tab h F] at hF
  exact tab1_obs _ _ _ _ hT hF x

/-- The same for one two-argument connective: equal classical tables give equal ZTL tables, Z cells included. -/
theorem funext_obs_lift2 (g h : Bool → Bool → Bool)
    (hc : ∀ a b : Bool, g a b = h a b) : ∀ x y : V, lift2 g x y = lift2 h x y := by
  intro x y
  rw [lift2_tab g x y, lift2_tab h x y, hc true true, hc true false, hc false true, hc false false]

/-! ### 3. Excluded middle -/

theorem lem_fails_dirty : zor Z (znot Z) ≠ T := by decide

theorem lem_clean (a : V) (ha : a ≠ Z) : zor a (znot a) = T := by
  cases a
  · rfl
  · rfl
  · exact absurd rfl ha

end ZAxiomsRead

#print axioms ZAxiomsRead.propext_fails_dirty
#print axioms ZAxiomsRead.propext_needs_clean
#print axioms ZAxiomsRead.propext_clean
#print axioms ZAxiomsRead.funext_obs_fails
#print axioms ZAxiomsRead.funext_obs_lift1
#print axioms ZAxiomsRead.funext_obs_lift2
#print axioms ZAxiomsRead.lem_fails_dirty
#print axioms ZAxiomsRead.lem_clean
