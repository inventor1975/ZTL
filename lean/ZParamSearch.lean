/-
  ZParamSearch.lean — E47: WHAT THE SEARCH STANDS ON, AND WHAT BLOCKS IT.

  Everything before this proves that individual rules behave: each step
  preserves satisfiability (`ZParamTableau`, `ZParamProp`) and closure denies
  it (`ZParamClosure`). What remains for an end-to-end theorem is the
  PROCEDURE that applies the steps — and this file is honest about being its
  foundation rather than the procedure.

  WHAT IS PROVED HERE. Satisfaction of a branch is a statement about
  MEMBERSHIP, not about order, so a search may move nodes around freely.
  Rotation — taking the head to the back, which is how a fair search avoids
  starving a node — cannot change whether the branch is satisfied. It is the
  kind of step that looks too obvious to check and is exactly where an
  order-dependent bug would live, so it is proved.

  AND HERE IS THE OBSTACLE THAT STOPPED THE PROCEDURE, recorded because it is
  a design fact and not a difficulty of effort.

  A search must DECIDE whether a branch is closed. Closure means two nodes
  about the same formula whose signs cannot both be met. But in this
  development a sign is a FUNCTION `V → Bool`, and two functions cannot be
  compared; nor can `Closed`, an existential over such functions, be decided.
  So the procedure cannot be written over the branches used so far. It needs
  a layer this file does not build: nodes tagged by a small inductive rather
  than by a function, a translation from tags to signs, and decidable
  equality on formulas.

  That is a sub-project — tagged nodes, a decidable closure test, the
  fuel-bounded recursion, and a soundness proof threading eleven lemmas
  through some ten cases. It is not started here, and a half-built search
  would be worth less than none: it would look like the port is finished.

  WHY FUEL WILL BE NEEDED WHEN IT IS BUILT. §6 records that FO-ZTL is
  undecidable and that on some invalid sequents the tableau spawns witnesses
  forever. A terminating search would be incomplete by construction or
  wrong; fuel makes the failure honest, since running out claims nothing.
-/
import ZParamProp
import ZParamClosure

namespace ZParamSearch

open V
open ZParamSyntax
open ZParamTableau
open ZParamProp
open ZParamClosure

variable {α : Type}

/-! ### Satisfaction cares about membership, not order -/

theorem sat_of_mem_sub (I : Nat → α → V) (ρ : Nat → α) (d : α)
    (b c : Branch) (h : ∀ nd, nd ∈ c → nd ∈ b) (hb : satBranch I ρ d b) :
    satBranch I ρ d c := fun nd hnd => hb nd (h nd hnd)

/-- `List.mem_append` from core carries propext (measured), so the induction
is written out. -/
theorem mem_rotate (x : QNode) : ∀ (r : Branch) (nd : QNode),
    nd ∈ r ++ [x] → nd ∈ x :: r
  | [],     nd, h => by
      cases h with
      | head       => exact List.Mem.head []
      | tail _ hn  => nomatch hn
  | a :: r, nd, h => by
      cases h with
      | head      => exact List.Mem.tail x (List.Mem.head r)
      | tail _ ht =>
          cases mem_rotate x r nd ht with
          | head      => exact List.Mem.head (a :: r)
          | tail _ hr => exact List.Mem.tail x (List.Mem.tail a hr)

/-- **ROTATION CANNOT CHANGE SATISFACTION.** Proved, not assumed: this is
where an order-dependent bug would live. -/
theorem sat_rotate (I : Nat → α → V) (ρ : Nat → α) (d : α)
    (x : QNode) (r : Branch) (h : satBranch I ρ d (x :: r)) :
    satBranch I ρ d (r ++ [x]) :=
  sat_of_mem_sub I ρ d (x :: r) (r ++ [x]) (mem_rotate x r) h

end ZParamSearch

#print axioms ZParamSearch.sat_of_mem_sub
#print axioms ZParamSearch.mem_rotate
#print axioms ZParamSearch.sat_rotate
