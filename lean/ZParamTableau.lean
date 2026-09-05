/-
  ZParamTableau.lean — E44: THE QUANTIFIER STEPS, ON BRANCHES.

  The last named piece of §27's port that can be settled without the
  classical tier: the two quantifier rules whose soundness does not need it,
  stated where a tableau actually works — on a branch.

  WHAT A STEP HAS TO PROVE. A tableau is sound when every step PRESERVES
  SATISFIABILITY: if the branch had a model before the step, some branch has
  one after. Closure then gives unsatisfiability by contraposition. Here are
  the two steps, each with that property proved.

    γ on T:∀   — instantiate with ANY parameter already in play. The model
                 does not change at all; the universal already delivered
                 every element, and `holds_inst` turns that into a verdict
                 about the instance.

    δ on T:∃   — instantiate with a FRESH parameter. The model DOES change:
                 the fresh parameter is pointed at the witness. That this
                 disturbs nothing else on the branch is exactly `holds_fresh`,
                 and it is where that lemma earns its place.

  AND THE THIRD STEP IS HERE TOO, WITH ITS COST IN PLAIN SIGHT. γ on F:∃
  needs a VALUE for the instance, and over an arbitrary domain the existence
  of a value for a quantified formula is itself a classical fact — deciding
  whether every element gives T is the survey this logic declines to call an
  act. So it is stated with an explicit totality hypothesis about the model
  rather than proved outright. The hypothesis is visible in the statement;
  it is not smuggled into a definition where every other theorem would pay
  for it.

  This is the same split measured this morning in `ZParamSound`, now
  reappearing one level up: the calculus is choice-free exactly where the
  logic itself is.

  STILL NOT HERE: closure, the fuel-bounded search, and the soundness
  theorem for a whole tableau. Those need the propositional steps ported to
  the quantified language as well, and that is the next piece of work.
-/
import ZParamSyntax
import TableauCert

namespace ZParamTableau

open V
open ZParamSyntax

variable {α : Type}

/-- A signed formula on a branch. -/
abbrev QNode := Sign × QFm

/-- A branch is a list of them. -/
abbrev Branch := List QNode

/-- One node is satisfied when the formula takes a value the sign admits. -/
def satNode (I : Nat → α → V) (ρ : Nat → α) (d : α) (nd : QNode) : Prop :=
  ∃ v, Holds I ρ d [] nd.2 v ∧ nd.1 v = true

def satBranch (I : Nat → α → V) (ρ : Nat → α) (d : α) (b : Branch) : Prop :=
  ∀ nd, nd ∈ b → satNode I ρ d nd

/-- A parameter is fresh for a branch when it occurs in none of its
formulas. -/
def freshFor (c : Nat) (b : Branch) : Prop :=
  ∀ nd, nd ∈ b → occurs c nd.2 = false

/-! ### γ on T:∀ — the model does not move -/

theorem gamma_all_step (I : Nat → α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ : QFm) (c : Nat)
    (hb : satBranch I ρ d b) (hmem : (SignT, QFm.all φ) ∈ b) :
    satBranch I ρ d ((SignT, inst c 0 φ) :: b) := by
  intro nd hnd
  cases hnd with
  | head =>
      have ⟨v, hv, hs⟩ := hb _ hmem
      have hvT : v = T := by
        have := (vT v).mp hs
        exact this
      have hall : ∀ a, Holds I ρ d (a :: []) φ T := by
        have : ((v = T) ↔ ∀ a, Holds I ρ d (a :: []) φ T) ∧ (v = T ∨ v = F) := hv
        exact this.1.mp hvT
      refine ⟨T, ?_, rfl⟩
      show Holds I ρ d [] (inst c 0 φ) T
      exact (holds_inst I ρ d c φ [] T 0).mpr (hall (ρ c))
  | tail _ ht => exact hb nd ht

/-! ### δ on T:∃ — the model moves, and freshness says it is safe -/

theorem delta_ex_step (I : Nat → α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ : QFm) (c : Nat)
    (hb : satBranch I ρ d b) (hmem : (SignT, QFm.ex φ) ∈ b)
    (hfresh : freshFor c ((SignT, QFm.ex φ) :: b)) :
    ∃ a : α, satBranch I (upd ρ c a) d ((SignT, inst c 0 φ) :: b) := by
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvT : v = T := (vT v).mp hs
  have hex : ∃ a, Holds I ρ d (a :: []) φ T := by
    have : ((v = T) ↔ ∃ a, Holds I ρ d (a :: []) φ T) ∧ (v = T ∨ v = F) := hv
    exact this.1.mp hvT
  match hex with
  | ⟨a, ha⟩ =>
      refine ⟨a, ?_⟩
      intro nd hnd
      cases hnd with
      | head =>
          refine ⟨T, ?_, rfl⟩
          show Holds I (upd ρ c a) d [] (inst c 0 φ) T
          have hc : upd ρ c a c = a := by
            show (match Nat.beq c c with | true => a | false => ρ c) = a
            rw [natBeq_refl c]
          refine (holds_inst I (upd ρ c a) d c φ [] T 0).mpr ?_
          rw [hc]
          -- c does not occur in φ, since it does not occur in ∃xφ
          have hφ : occurs c φ = false := hfresh _ (List.Mem.head b)
          exact (holds_fresh I ρ c a d φ (a :: []) T hφ).mpr ha
      | tail _ ht =>
          have ⟨w, hw, hsw⟩ := hb nd ht
          have hnf : occurs c nd.2 = false := hfresh nd (List.Mem.tail _ ht)
          exact ⟨w, (holds_fresh I ρ c a d nd.2 [] w hnf).mpr hw, hsw⟩

/-! ### γ on F:∃ — and the cost is in the statement -/

/-- Every formula takes a value under this model. Over an arbitrary domain
this is a CLASSICAL assumption — deciding whether every element gives T is
the survey §6 refuses to call an act — so it is a hypothesis, visible, and
not a clause in the definition of `Holds`. -/
def Total (I : Nat → α → V) (ρ : Nat → α) (d : α) : Prop :=
  ∀ (φ : QFm) (η : List α), ∃ v, Holds I ρ d η φ v

theorem gamma_ex_step (I : Nat → α → V) (ρ : Nat → α) (d : α)
    (htot : Total I ρ d) (b : Branch) (φ : QFm) (c : Nat)
    (hb : satBranch I ρ d b) (hmem : (SignF, QFm.ex φ) ∈ b) :
    satBranch I ρ d ((SignN, inst c 0 φ) :: b) := by
  intro nd hnd
  cases hnd with
  | head =>
      have ⟨v, hv, hs⟩ := hb _ hmem
      have hvF : v = F := (vF v).mp hs
      have hno : ¬ ∃ a, Holds I ρ d (a :: []) φ T := by
        intro hx
        have : ((v = T) ↔ ∃ a, Holds I ρ d (a :: []) φ T) ∧ (v = T ∨ v = F) := hv
        have : v = T := this.1.mpr hx
        rw [hvF] at this
        exact V.noConfusion this
      match htot (inst c 0 φ) [] with
      | ⟨u, hu⟩ =>
          refine ⟨u, hu, ?_⟩
          have hnT : u ≠ T := by
            intro huT
            rw [huT] at hu
            exact hno ⟨ρ c, (holds_inst I ρ d c φ [] T 0).mp hu⟩
          exact (vN u).mpr ((vN_neq u).mpr hnT)
  | tail _ ht => exact hb nd ht

end ZParamTableau

#print axioms ZParamTableau.gamma_all_step
#print axioms ZParamTableau.delta_ex_step
#print axioms ZParamTableau.gamma_ex_step
