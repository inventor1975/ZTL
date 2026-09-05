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
  | atom : Nat → List Trm → QFm
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

/-- Over the argument list — own recursion, no `List.any`. -/
def occursL (c : Nat) : List Trm → Bool
  | []     => false
  | t :: r => occursT c t || occursL c r

def occurs (c : Nat) : QFm → Bool
  | QFm.atom _ ts => occursL c ts
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
def stackVal (d : α) : List α → Nat → α
  | [],      _     => d
  | a :: _,  0     => a
  | _ :: r,  k + 1 => stackVal d r k

def trmVal (ρ : Nat → α) (η : List α) (d : α) : Trm → α
  | Trm.par p  => ρ p
  | Trm.bvar k => stackVal d η k

/-- The values of an argument list — own map. -/
def trmVals (ρ : Nat → α) (η : List α) (d : α) : List Trm → List α
  | []     => []
  | t :: r => trmVal ρ η d t :: trmVals ρ η d r

/-- Reassign one parameter. -/
def upd (ρ : Nat → α) (c : Nat) (a : α) : Nat → α :=
  fun n => match Nat.beq n c with
           | true  => a
           | false => ρ n

/-- Satisfaction, as a relation. The quantifier clauses are the greedy
readings of §6 written as conditions the value must meet, not as something
computed — see the header. -/
def Holds (I : Nat → List α → V) (ρ : Nat → α) (d : α) :
    List α → QFm → V → Prop
  | η, QFm.atom P ts, v => I P (trmVals ρ η d ts) = v
  | η, QFm.neg φ,    v => ∃ u, Holds I ρ d η φ u ∧ znot u = v
  | η, QFm.conj φ ψ, v => ∃ u w, Holds I ρ d η φ u ∧ Holds I ρ d η ψ w ∧ zand u w = v
  | η, QFm.disj φ ψ, v => ∃ u w, Holds I ρ d η φ u ∧ Holds I ρ d η ψ w ∧ zor u w = v
  | η, QFm.imp φ ψ,  v => ∃ u w, Holds I ρ d η φ u ∧ Holds I ρ d η ψ w ∧ zimp u w = v
  | η, QFm.all φ,    v => ((v = T) ↔ ∀ a, Holds I ρ d (a :: η) φ T) ∧ (v = T ∨ v = F)
  | η, QFm.ex φ,     v => ((v = T) ↔ ∃ a, Holds I ρ d (a :: η) φ T) ∧ (v = T ∨ v = F)


/-! ### Instantiation, and the second load-bearing lemma

    The γ rule replaces `∀xφ` by `φ(c)` for a parameter already in play; the
    δ rule does the same with a fresh one. Both need the SAME fact: putting a
    parameter into a formula is the same as putting its value into the stack.

    THE DE BRUIJN DETAIL THAT DECIDES THE STATEMENT. `inst` replaces the
    variable at depth `k` and leaves every other index alone — it does not
    shift. So the semantic counterpart REPLACES position `k` of the stack; it
    does not insert. Written with an insertion the two sides would disagree at
    every index above `k`, and the error would have surfaced only in the
    tableau, three files later. -/

/-- Replace the variable at depth `k` by the parameter `c`. -/
def instT (c : Nat) (k : Nat) : Trm → Trm
  | Trm.bvar j => match Nat.beq j k with
                  | true  => Trm.par c
                  | false => Trm.bvar j
  | Trm.par p  => Trm.par p

def instL (c : Nat) (k : Nat) : List Trm → List Trm
  | []     => []
  | t :: r => instT c k t :: instL c k r

def inst (c : Nat) : Nat → QFm → QFm
  | k, QFm.atom P ts => QFm.atom P (instL c k ts)
  | k, QFm.neg φ    => QFm.neg (inst c k φ)
  | k, QFm.conj φ ψ => QFm.conj (inst c k φ) (inst c k ψ)
  | k, QFm.disj φ ψ => QFm.disj (inst c k φ) (inst c k ψ)
  | k, QFm.imp φ ψ  => QFm.imp (inst c k φ) (inst c k ψ)
  | k, QFm.all φ    => QFm.all (inst c (k + 1) φ)
  | k, QFm.ex φ     => QFm.ex (inst c (k + 1) φ)

/-- Put `x` at position `k` of the stack, padding with the default. REPLACES
rather than inserts — see the note above. -/
def setAt (d : α) : List α → Nat → α → List α
  | [],      0,     x => [x]
  | _ :: r,  0,     x => x :: r
  | [],      k + 1, x => d :: setAt d [] k x
  | a :: r,  k + 1, x => a :: setAt d r k x

theorem stackVal_setAt_same (d x : α) :
    ∀ (η : List α) (k : Nat), stackVal d (setAt d η k x) k = x
  | [],     0     => rfl
  | _ :: _, 0     => rfl
  | [],     k + 1 => stackVal_setAt_same d x [] k
  | _ :: r, k + 1 => stackVal_setAt_same d x r k

theorem stackVal_setAt_other (d x : α) :
    ∀ (η : List α) (k j : Nat), Nat.beq j k = false →
      stackVal d (setAt d η k x) j = stackVal d η j
  | [],     0,     0,     h => Bool.noConfusion h
  | [],     0,     _ + 1, _ => rfl
  | _ :: _, 0,     0,     h => Bool.noConfusion h
  | _ :: _, 0,     _ + 1, _ => rfl
  | [],     _ + 1, 0,     _ => rfl
  | _ :: _, _ + 1, 0,     _ => rfl
  | [],     k + 1, j + 1, h => stackVal_setAt_other d x [] k j h
  | _ :: r, k + 1, j + 1, h => stackVal_setAt_other d x r k j h

theorem trmVal_inst (ρ : Nat → α) (d : α) (c : Nat) :
    ∀ (t : Trm) (η : List α) (k : Nat),
      trmVal ρ η d (instT c k t) = trmVal ρ (setAt d η k (ρ c)) d t
  | Trm.par _,  _, _ => rfl
  | Trm.bvar j, η, k => by
      show trmVal ρ η d (match Nat.beq j k with
                         | true => Trm.par c | false => Trm.bvar j)
         = stackVal d (setAt d η k (ρ c)) j
      cases hj : Nat.beq j k with
      | true =>
          have : j = k := Nat.eq_of_beq_eq_true hj
          rw [this]
          exact (stackVal_setAt_same d (ρ c) η k).symm
      | false =>
          exact (stackVal_setAt_other d (ρ c) η k j hj).symm

theorem trmVals_inst (ρ : Nat → α) (d : α) (c : Nat) (η : List α) (k : Nat) :
    ∀ ts : List Trm, trmVals ρ η d (instL c k ts) = trmVals ρ (setAt d η k (ρ c)) d ts
  | []     => rfl
  | t :: r => by
      show trmVal ρ η d (instT c k t) :: trmVals ρ η d (instL c k r)
         = trmVal ρ (setAt d η k (ρ c)) d t :: trmVals ρ (setAt d η k (ρ c)) d r
      rw [trmVal_inst ρ d c t η k, trmVals_inst ρ d c η k r]

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

theorem trmVals_fresh (ρ : Nat → α) (c : Nat) (a : α) (η : List α) (d : α) :
    ∀ ts : List Trm, occursL c ts = false → trmVals (upd ρ c a) η d ts = trmVals ρ η d ts
  | [], _ => rfl
  | t :: r, h => by
      have hb : (occursT c t || occursL c r) = false := h
      show trmVal (upd ρ c a) η d t :: trmVals (upd ρ c a) η d r
         = trmVal ρ η d t :: trmVals ρ η d r
      rw [trmVal_fresh ρ c a η d t (or_false_left hb), trmVals_fresh ρ c a η d r (or_false_right hb)]

/-- **FIXING A FRESH PARAMETER DISTURBS NOTHING.** If `c` occurs nowhere in
`φ`, then reassigning it — to any element of any domain — leaves every
verdict of `φ` exactly as it was. This is what licenses the δ rule to name a
witness, and it is proved for the whole language, quantifiers included. -/
theorem holds_fresh (I : Nat → List α → V) (ρ : Nat → α) (c : Nat) (a : α) (d : α) :
    ∀ (φ : QFm) (η : List α) (v : V), occurs c φ = false →
      (Holds I (upd ρ c a) d η φ v ↔ Holds I ρ d η φ v)
  | QFm.atom P ts, η, v, h => by
      show I P (trmVals (upd ρ c a) η d ts) = v ↔ I P (trmVals ρ η d ts) = v
      rw [trmVals_fresh ρ c a η d ts h]
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

/-- **PUTTING A PARAMETER IN IS PUTTING ITS VALUE ON THE STACK.** The second
lemma both quantifier rules stand on: γ instantiates with a parameter already
in play, δ with a fresh one, and each is licensed by this. -/
theorem holds_inst (I : Nat → List α → V) (ρ : Nat → α) (d : α) (c : Nat) :
    ∀ (φ : QFm) (η : List α) (v : V) (k : Nat),
      Holds I ρ d η (inst c k φ) v ↔ Holds I ρ d (setAt d η k (ρ c)) φ v
  | QFm.atom P ts, η, v, k => by
      show I P (trmVals ρ η d (instL c k ts)) = v
         ↔ I P (trmVals ρ (setAt d η k (ρ c)) d ts) = v
      rw [trmVals_inst ρ d c η k ts]
  | QFm.neg φ, η, v, k => by
      constructor
      · intro ⟨u, hu, he⟩
        exact ⟨u, (holds_inst I ρ d c φ η u k).mp hu, he⟩
      · intro ⟨u, hu, he⟩
        exact ⟨u, (holds_inst I ρ d c φ η u k).mpr hu, he⟩
  | QFm.conj φ ψ, η, v, k => by
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_inst I ρ d c φ η u k).mp hu,
                     (holds_inst I ρ d c ψ η w k).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_inst I ρ d c φ η u k).mpr hu,
                     (holds_inst I ρ d c ψ η w k).mpr hw, he⟩
  | QFm.disj φ ψ, η, v, k => by
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_inst I ρ d c φ η u k).mp hu,
                     (holds_inst I ρ d c ψ η w k).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_inst I ρ d c φ η u k).mpr hu,
                     (holds_inst I ρ d c ψ η w k).mpr hw, he⟩
  | QFm.imp φ ψ, η, v, k => by
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_inst I ρ d c φ η u k).mp hu,
                     (holds_inst I ρ d c ψ η w k).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_inst I ρ d c φ η u k).mpr hu,
                     (holds_inst I ρ d c ψ η w k).mpr hw, he⟩
  | QFm.all φ, η, v, k => by
      constructor
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv b => (holds_inst I ρ d c φ (b :: η) T (k + 1)).mp (hiff.mp hv b),
                fun hall => hiff.mpr (fun b =>
                  (holds_inst I ρ d c φ (b :: η) T (k + 1)).mpr (hall b))⟩, hcl⟩
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv b => (holds_inst I ρ d c φ (b :: η) T (k + 1)).mpr (hiff.mp hv b),
                fun hall => hiff.mpr (fun b =>
                  (holds_inst I ρ d c φ (b :: η) T (k + 1)).mp (hall b))⟩, hcl⟩
  | QFm.ex φ, η, v, k => by
      constructor
      · intro ⟨hiff, hcl⟩
        refine ⟨⟨fun hv => ?_, fun hex => ?_⟩, hcl⟩
        · match hiff.mp hv with
          | ⟨b, hb⟩ =>
              exact ⟨b, (holds_inst I ρ d c φ (b :: η) T (k + 1)).mp hb⟩
        · match hex with
          | ⟨b, hb⟩ =>
              exact hiff.mpr ⟨b, (holds_inst I ρ d c φ (b :: η) T (k + 1)).mpr hb⟩
      · intro ⟨hiff, hcl⟩
        refine ⟨⟨fun hv => ?_, fun hex => ?_⟩, hcl⟩
        · match hiff.mp hv with
          | ⟨b, hb⟩ =>
              exact ⟨b, (holds_inst I ρ d c φ (b :: η) T (k + 1)).mpr hb⟩
        · match hex with
          | ⟨b, hb⟩ =>
              exact hiff.mpr ⟨b, (holds_inst I ρ d c φ (b :: η) T (k + 1)).mp hb⟩

end ZParamSyntax

#print axioms ZParamSyntax.trmVal_fresh
#print axioms ZParamSyntax.holds_fresh
#print axioms ZParamSyntax.stackVal_setAt_same
#print axioms ZParamSyntax.stackVal_setAt_other
#print axioms ZParamSyntax.trmVal_inst
#print axioms ZParamSyntax.holds_inst
#print axioms ZParamSyntax.trmVals_fresh
#print axioms ZParamSyntax.trmVals_inst
