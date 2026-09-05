/-
  ZParamSyntax.lean — E43: THE GROUND THE δ RULE STANDS ON.

  §27's first roadmap item is a Lean port of the parameter tableaux of §6.
  This file is its foundation and nothing more: the syntax with parameters,
  the satisfaction relation, and the ONE lemma the δ rule cannot do without.

  WHY FRESHNESS IS THE LOAD-BEARING LEMMA. The δ rule interprets a FRESH
  parameter as a witness. That is legitimate only if fixing the meaning of a
  parameter that occurs nowhere in the branch disturbs nothing already there.
  Written out, that is exactly:

      occurs c φ = false  →  (φ holds under ρ  ↔  φ holds under ρ with c
                              reassigned to anything at all)

  Every soundness argument for a fresh-witness rule is that lemma plus
  bookkeeping. It is proved here for the whole language, quantifiers
  included.

  SCOPE, DECIDED IN WORDS BEFORE ANY CODE AND STATED HERE. The fragment is
  MONADIC — one-place predicates, quantifiers over one variable at a time,
  bound variables by de Bruijn index and parameters by name. It covers
  UI/EG, both fallen quantifier bridges, quantified LEM and the drinker. It
  does NOT cover the quantifier swap ∃x∀yR, which needs a two-place
  predicate. A full first-order syntax is a larger object and is not
  promised here.

  SATISFACTION IS A RELATION, NOT A COMPUTATION, and that is forced rather
  than chosen. ZTL's greedy `∀` is "T if every instance is strictly T, else
  F"; over an arbitrary domain that `else` is a decision about an
  undecidable proposition. Measured today in `ZParamSound`: the fourth
  quantifier rule needs `¬∀ → ∃¬` and lands at the classical tier. Writing
  the semantics as a relation keeps that cost where it belongs — in the one
  rule that incurs it — instead of importing it into the definition and
  paying it everywhere.

  WHAT IS NOT HERE. The tableau itself: branches, the rule steps, closure,
  and the soundness theorem. Those are the next piece of work and are not
  begun; this file deliberately stops at the ground they stand on.
-/
import ZTL

namespace ZParamSyntax

open V

/-! ### Syntax -/

inductive Trm where
  | bvar : Nat → Trm
  | par  : Nat → Trm

inductive QFm where
  | atom : Nat → Trm → QFm
  | neg  : QFm → QFm
  | conj : QFm → QFm → QFm
  | disj : QFm → QFm → QFm
  | imp  : QFm → QFm → QFm
  | all  : QFm → QFm
  | ex   : QFm → QFm

/-- Does the parameter `c` occur? Own recursion, `Nat.beq`, no wildcards —
the three traps measured today. -/
def occursT (c : Nat) : Trm → Bool
  | Trm.bvar _ => false
  | Trm.par p  => Nat.beq p c

def occurs (c : Nat) : QFm → Bool
  | QFm.atom _ t => occursT c t
  | QFm.neg φ    => occurs c φ
  | QFm.conj φ ψ => occurs c φ || occurs c ψ
  | QFm.disj φ ψ => occurs c φ || occurs c ψ
  | QFm.imp φ ψ  => occurs c φ || occurs c ψ
  | QFm.all φ    => occurs c φ
  | QFm.ex φ     => occurs c φ

/-! ### Semantics -/

variable {α : Type}

/-- The value of a term: a parameter through the assignment, a bound
variable through the de Bruijn stack. Off the end of the stack the value is
the default `d` — the stack is never consulted off its end in a closed
formula, and giving it a total reading avoids an option type. -/
def trmVal (ρ : Nat → α) (η : List α) (d : α) : Trm → α
  | Trm.par p  => ρ p
  | Trm.bvar k => go η k
where
  go : List α → Nat → α
    | [],      _     => d
    | a :: _,  0     => a
    | _ :: r,  k + 1 => go r k

/-- Reassign one parameter. -/
def upd (ρ : Nat → α) (c : Nat) (a : α) : Nat → α :=
  fun n => match Nat.beq n c with
           | true  => a
           | false => ρ n

/-- Satisfaction, as a relation. The quantifier clauses are the greedy
readings of §6 written as conditions the value must meet, not as something
computed — see the header. -/
def Holds (I : Nat → α → V) (ρ : Nat → α) (d : α) :
    List α → QFm → V → Prop
  | η, QFm.atom P t, v => I P (trmVal ρ η d t) = v
  | η, QFm.neg φ,    v => ∃ u, Holds I ρ d η φ u ∧ znot u = v
  | η, QFm.conj φ ψ, v => ∃ u w, Holds I ρ d η φ u ∧ Holds I ρ d η ψ w ∧ zand u w = v
  | η, QFm.disj φ ψ, v => ∃ u w, Holds I ρ d η φ u ∧ Holds I ρ d η ψ w ∧ zor u w = v
  | η, QFm.imp φ ψ,  v => ∃ u w, Holds I ρ d η φ u ∧ Holds I ρ d η ψ w ∧ zimp u w = v
  | η, QFm.all φ,    v => ((v = T) ↔ ∀ a, Holds I ρ d (a :: η) φ T) ∧ (v = T ∨ v = F)
  | η, QFm.ex φ,     v => ((v = T) ↔ ∃ a, Holds I ρ d (a :: η) φ T) ∧ (v = T ∨ v = F)

/-! ### The freshness lemma -/

theorem natBeq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0     => rfl
  | n + 1 => natBeq_refl n

theorem upd_at_other (ρ : Nat → α) (c : Nat) (a : α) (p : Nat)
    (h : Nat.beq p c = false) : upd ρ c a p = ρ p := by
  show (match Nat.beq p c with | true => a | false => ρ p) = ρ p
  rw [h]

theorem or_false_left : ∀ {a b : Bool}, (a || b) = false → a = false
  | false, _, _ => rfl
  | true,  _, h => Bool.noConfusion h

theorem or_false_right : ∀ {a b : Bool}, (a || b) = false → b = false
  | false, _, h => h
  | true,  _, h => Bool.noConfusion h

theorem trmVal_fresh (ρ : Nat → α) (c : Nat) (a : α) (η : List α) (d : α) :
    ∀ t : Trm, occursT c t = false → trmVal (upd ρ c a) η d t = trmVal ρ η d t
  | Trm.bvar _, _ => rfl
  | Trm.par p,  h => by
      show upd ρ c a p = ρ p
      exact upd_at_other ρ c a p h

/-- **FIXING A FRESH PARAMETER DISTURBS NOTHING.** If `c` occurs nowhere in
`φ`, then reassigning it — to any element of any domain — leaves every
verdict of `φ` exactly as it was. This is what licenses the δ rule to name a
witness, and it is proved for the whole language, quantifiers included. -/
theorem holds_fresh (I : Nat → α → V) (ρ : Nat → α) (c : Nat) (a : α) (d : α) :
    ∀ (φ : QFm) (η : List α) (v : V), occurs c φ = false →
      (Holds I (upd ρ c a) d η φ v ↔ Holds I ρ d η φ v)
  | QFm.atom P t, η, v, h => by
      show I P (trmVal (upd ρ c a) η d t) = v ↔ I P (trmVal ρ η d t) = v
      rw [trmVal_fresh ρ c a η d t h]
  | QFm.neg φ, η, v, h => by
      constructor
      · intro ⟨u, hu, he⟩
        exact ⟨u, (holds_fresh I ρ c a d φ η u h).mp hu, he⟩
      · intro ⟨u, hu, he⟩
        exact ⟨u, (holds_fresh I ρ c a d φ η u h).mpr hu, he⟩
  | QFm.conj φ ψ, η, v, h => by
      have hb : (occurs c φ || occurs c ψ) = false := h
      have h1 : occurs c φ = false := or_false_left hb
      have h2 : occurs c ψ = false := or_false_right hb
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_fresh I ρ c a d φ η u h1).mp hu,
                     (holds_fresh I ρ c a d ψ η w h2).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_fresh I ρ c a d φ η u h1).mpr hu,
                     (holds_fresh I ρ c a d ψ η w h2).mpr hw, he⟩
  | QFm.disj φ ψ, η, v, h => by
      have hb : (occurs c φ || occurs c ψ) = false := h
      have h1 : occurs c φ = false := or_false_left hb
      have h2 : occurs c ψ = false := or_false_right hb
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_fresh I ρ c a d φ η u h1).mp hu,
                     (holds_fresh I ρ c a d ψ η w h2).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_fresh I ρ c a d φ η u h1).mpr hu,
                     (holds_fresh I ρ c a d ψ η w h2).mpr hw, he⟩
  | QFm.imp φ ψ, η, v, h => by
      have hb : (occurs c φ || occurs c ψ) = false := h
      have h1 : occurs c φ = false := or_false_left hb
      have h2 : occurs c ψ = false := or_false_right hb
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_fresh I ρ c a d φ η u h1).mp hu,
                     (holds_fresh I ρ c a d ψ η w h2).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_fresh I ρ c a d φ η u h1).mpr hu,
                     (holds_fresh I ρ c a d ψ η w h2).mpr hw, he⟩
  | QFm.all φ, η, v, h => by
      constructor
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv => fun b => (holds_fresh I ρ c a d φ (b :: η) T h).mp
                                      (hiff.mp hv b),
                fun hall => hiff.mpr (fun b =>
                  (holds_fresh I ρ c a d φ (b :: η) T h).mpr (hall b))⟩, hcl⟩
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv => fun b => (holds_fresh I ρ c a d φ (b :: η) T h).mpr
                                      (hiff.mp hv b),
                fun hall => hiff.mpr (fun b =>
                  (holds_fresh I ρ c a d φ (b :: η) T h).mp (hall b))⟩, hcl⟩
  | QFm.ex φ, η, v, h => by
      constructor
      · intro ⟨hiff, hcl⟩
        refine ⟨⟨fun hv => ?_, fun hex => ?_⟩, hcl⟩
        · match hiff.mp hv with
          | ⟨b, hb⟩ => exact ⟨b, (holds_fresh I ρ c a d φ (b :: η) T h).mp hb⟩
        · match hex with
          | ⟨b, hb⟩ =>
              exact hiff.mpr ⟨b, (holds_fresh I ρ c a d φ (b :: η) T h).mpr hb⟩
      · intro ⟨hiff, hcl⟩
        refine ⟨⟨fun hv => ?_, fun hex => ?_⟩, hcl⟩
        · match hiff.mp hv with
          | ⟨b, hb⟩ => exact ⟨b, (holds_fresh I ρ c a d φ (b :: η) T h).mpr hb⟩
        · match hex with
          | ⟨b, hb⟩ =>
              exact hiff.mpr ⟨b, (holds_fresh I ρ c a d φ (b :: η) T h).mp hb⟩

end ZParamSyntax

#print axioms ZParamSyntax.trmVal_fresh
#print axioms ZParamSyntax.holds_fresh
