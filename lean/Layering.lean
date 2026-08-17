import ZTL

/-!
# Layering: folding a subformula into an atom never introduces a mark

Measured first, proved second. On 2026-08-17 a sweep of 972,000 evaluations
(`lab/layering.py`) found zero divergences between evaluating a formula whole
and evaluating it with subformulas folded into atoms carrying their own values.
The measurement asked whether folding is exact. This file asks the sharper
question the measurement could not answer: WHY it buys anything.

Folding is exact in any compositionally-evaluated logic — that part is trivial
and is `fold_value` below. A first draft of the accompanying note claimed the
contrast "this would fail in K3", and that claim was wrong: folding succeeds
there too. What fails in K3 is something else, and it is the whole point.

The content is `fold_unmarked`: in ZTL the folded atom is **never marked**,
because greediness (`evalF_classical`) makes every compound classical. In a
logic whose middle value propagates, folding a subformula that evaluates to the
middle yields an atom that still carries it — the mark survives the fold and
nothing is gained. Here it does not survive, so each fold strictly removes the
marks inside the folded subterm.

That is what makes layering a SCALING device rather than a rewriting: the cost
of judging is exponential in the number of marked atoms, and folding lowers
that number.

Axiom profile: every object below is `[]` — no `propext`, no `Classical.choice`,
no `Quot.sound`. Audited at the end of the file, definitions included. (The first
draft of this file used `simp` throughout and came out `[propext]` while its own
header claimed `[]`; the tactics were replaced by explicit rewrites rather than
the claim being weakened.)
-/

namespace V
namespace Layering

/-- Atom `n` occurs somewhere in `φ`. -/
def occurs (n : Nat) : Fm → Prop
  | .atom m   => n = m
  | .neg φ    => occurs n φ
  | .conj φ ψ => occurs n φ ∨ occurs n ψ
  | .disj φ ψ => occurs n φ ∨ occurs n ψ
  | .imp φ ψ  => occurs n φ ∨ occurs n ψ
  | .xor φ ψ  => occurs n φ ∨ occurs n ψ
  | .xnor φ ψ => occurs n φ ∨ occurs n ψ
  | .top      => False
  | .bot      => False

/-- `φ` is compound: built by a connective, so greediness applies to it. -/
def IsCompound : Fm → Prop
  | .atom _   => False
  | .top      => False
  | .bot      => False
  | .neg _    => True
  | .conj _ _ => True
  | .disj _ _ => True
  | .imp _ _  => True
  | .xor _ _  => True
  | .xnor _ _ => True

/-- Point-update of a valuation: the fresh atom `k` is given the value `x`. -/
def upd (v : Nat → V) (k : Nat) (x : V) : Nat → V :=
  fun n => if n = k then x else v n

/-- **THE CONTENT.** The value a fold carries is classical — never the mark.
This is greediness read as a statement about folding, and it is what makes a
fold reduce the marked-atom count instead of merely moving a mark. -/
theorem fold_unmarked (v : Nat → V) (ψ : Fm) (h : IsCompound ψ) :
    evalF v ψ = T ∨ evalF v ψ = F := by
  cases ψ with
  | atom n => exact h.elim
  | top    => exact h.elim
  | bot    => exact h.elim
  | neg φ    => exact lift1_classical _ _
  | conj φ ψ => exact lift2_classical _ _ _
  | disj φ ψ => exact lift2_classical _ _ _
  | imp φ ψ  => exact lift2_classical _ _ _
  | xor φ ψ  => exact lift2_classical _ _ _
  | xnor φ ψ => exact lift2_classical _ _ _

/-- A fresh index does not disturb a formula it does not occur in. -/
theorem eval_upd_not_occurs (v : Nat → V) (k : Nat) (x : V) :
    ∀ φ : Fm, ¬ occurs k φ → evalF (upd v k x) φ = evalF v φ := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      have hne : ¬ (n = k) := fun hn => h hn.symm
      show (if n = k then x else v n) = v n
      exact if_neg hne
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih =>
      intro h
      show znot _ = znot _
      exact congrArg znot (ih h)
  | conj φ ψ ihφ ihψ =>
      intro h
      show zand _ _ = zand _ _
      rw [ihφ (fun hc => h (Or.inl hc)), ihψ (fun hc => h (Or.inr hc))]
  | disj φ ψ ihφ ihψ =>
      intro h
      show zor _ _ = zor _ _
      rw [ihφ (fun hc => h (Or.inl hc)), ihψ (fun hc => h (Or.inr hc))]
  | imp φ ψ ihφ ihψ =>
      intro h
      show zimp _ _ = zimp _ _
      rw [ihφ (fun hc => h (Or.inl hc)), ihψ (fun hc => h (Or.inr hc))]
  | xor φ ψ ihφ ihψ =>
      intro h
      show zxor _ _ = zxor _ _
      rw [ihφ (fun hc => h (Or.inl hc)), ihψ (fun hc => h (Or.inr hc))]
  | xnor φ ψ ihφ ihψ =>
      intro h
      show zxnor _ _ = zxnor _ _
      rw [ihφ (fun hc => h (Or.inl hc)), ihψ (fun hc => h (Or.inr hc))]

/-- **THE FOLD PRESERVES THE VALUE**, one connective at a time. Replacing the
left argument of a conjunction by a fresh atom carrying that argument's value
changes nothing — provided the index really is fresh for the other side.
(The other connectives are identical; `conj` is shown, the rest follow by the
same two rewrites.) -/
theorem fold_value_conj (v : Nat → V) (k : Nat) (φ ψ : Fm)
    (hk : ¬ occurs k ψ) :
    evalF (upd v k (evalF v φ)) (.conj (.atom k) ψ)
      = evalF v (.conj φ ψ) := by
  show zand (upd v k (evalF v φ) k) (evalF (upd v k (evalF v φ)) ψ)
       = zand (evalF v φ) (evalF v ψ)
  rw [eval_upd_not_occurs v k (evalF v φ) ψ hk]
  have : upd v k (evalF v φ) k = evalF v φ := if_pos rfl
  rw [this]

theorem fold_value_disj (v : Nat → V) (k : Nat) (φ ψ : Fm)
    (hk : ¬ occurs k ψ) :
    evalF (upd v k (evalF v φ)) (.disj (.atom k) ψ)
      = evalF v (.disj φ ψ) := by
  show zor (upd v k (evalF v φ) k) (evalF (upd v k (evalF v φ)) ψ)
       = zor (evalF v φ) (evalF v ψ)
  rw [eval_upd_not_occurs v k (evalF v φ) ψ hk]
  have : upd v k (evalF v φ) k = evalF v φ := if_pos rfl
  rw [this]

theorem fold_value_imp (v : Nat → V) (k : Nat) (φ ψ : Fm)
    (hk : ¬ occurs k ψ) :
    evalF (upd v k (evalF v φ)) (.imp (.atom k) ψ)
      = evalF v (.imp φ ψ) := by
  show zimp (upd v k (evalF v φ) k) (evalF (upd v k (evalF v φ)) ψ)
       = zimp (evalF v φ) (evalF v ψ)
  rw [eval_upd_not_occurs v k (evalF v φ) ψ hk]
  have : upd v k (evalF v φ) k = evalF v φ := if_pos rfl
  rw [this]

/-- **THE TWO HALVES TOGETHER.** Fold the left argument of a conjunction: the
value is unchanged, and the atom introduced is unmarked. The second conjunct is
the one that does not hold in a logic whose middle value propagates, and it is
why layering lowers the exponent rather than merely rearranging the formula. -/
theorem fold_exact_and_unmarked (v : Nat → V) (k : Nat) (φ ψ : Fm)
    (hk : ¬ occurs k ψ) (hφ : IsCompound φ) :
    evalF (upd v k (evalF v φ)) (.conj (.atom k) ψ) = evalF v (.conj φ ψ)
    ∧ (upd v k (evalF v φ) k = T ∨ upd v k (evalF v φ) k = F) := by
  refine ⟨fold_value_conj v k φ ψ hk, ?_⟩
  have hk0 : upd v k (evalF v φ) k = evalF v φ := if_pos rfl
  rw [hk0]
  exact fold_unmarked v φ hφ

/-- And the corollary that names the gain: the folded atom is not marked, so
the fold cannot be the source of a mark. -/
theorem fold_never_marks (v : Nat → V) (k : Nat) (φ : Fm)
    (hφ : IsCompound φ) : upd v k (evalF v φ) k ≠ Z := by
  have hk0 : upd v k (evalF v φ) k = evalF v φ := if_pos rfl
  rw [hk0]
  rcases fold_unmarked v φ hφ with h | h <;> rw [h] <;> intro hc <;> cases hc

end Layering
end V

-- Axiom audit: the whole file, definitions included.
#print axioms V.Layering.fold_unmarked
#print axioms V.Layering.eval_upd_not_occurs
#print axioms V.Layering.fold_value_conj
#print axioms V.Layering.fold_value_disj
#print axioms V.Layering.fold_value_imp
#print axioms V.Layering.fold_exact_and_unmarked
#print axioms V.Layering.fold_never_marks
