import ZRead
import ZGround
/-! # ZForced — the forced outcome of a formula, as a phase, with its connective rules DERIVED. Zero axioms.

Pure branch (curator 2026-11-22, option 2: "the definition by readings, the fast count as a proved theorem").
`rd v φ` (ZRead) is which classical values the readings of the occurrences reach. Its outcome as a phase
(`Ph`, ZGround): `t` — every reading true (EARNED), `f` — every reading false (REFUTED), `n` — not forced.
The rules below that compute the outcome connective by connective are NOT postulated tables: each is a theorem
about `rd` (`fo_neg`, `fo_conj`, …). `n` is the phase, never the mark Z. -/

namespace V

/-- the outcome of a pair of reached readings -/
def phOf : Bool × Bool → Ph
  | (true, false)  => .t
  | (false, true)  => .f
  | (true, true)   => .n
  | (false, false) => .n

/-- the forced outcome of φ under v -/
def fo (v : Nat → V) (φ : Fm) : Ph := phOf (rd v φ)

/-- some reading always exists -/
theorem rd_nonempty (v : Nat → V) : ∀ φ : Fm, ((rd v φ).1 || (rd v φ).2) = true
  | .atom n    => by show (((subs (v n)).contains true) || ((subs (v n)).contains false)) = true; cases v n <;> rfl
  | .top       => rfl
  | .bot       => rfl
  | .neg φ     => by
      have h := rd_nonempty v φ
      show ((rd v φ).2 || (rd v φ).1) = true
      revert h; cases (rd v φ).1 <;> cases (rd v φ).2 <;> decide
  | .conj φ ψ  => ne_comb _ (rd_nonempty v φ) (rd_nonempty v ψ)
  | .disj φ ψ  => ne_comb _ (rd_nonempty v φ) (rd_nonempty v ψ)
  | .imp φ ψ   => ne_comb _ (rd_nonempty v φ) (rd_nonempty v ψ)
  | .xor φ ψ   => ne_comb _ (rd_nonempty v φ) (rd_nonempty v ψ)
  | .xnor φ ψ  => ne_comb _ (rd_nonempty v φ) (rd_nonempty v ψ)
where
  ne_comb (g : Bool → Bool → Bool) {p q : Bool × Bool} (hp : (p.1 || p.2) = true) (hq : (q.1 || q.2) = true) :
      ((comb g p q).1 || (comb g p q).2) = true := by
    obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
    revert hp hq
    dsimp only [comb, ok, List.any]
    generalize g true true = w1
    generalize g true false = w2
    generalize g false true = w3
    generalize g false false = w4
    cases a <;> cases b <;> cases c <;> cases d <;> cases w1 <;> cases w2 <;> cases w3 <;> cases w4 <;> decide

/-! ## The derived rules: the outcome of a compound from the outcomes of its parts -/

def phNot : Ph → Ph
  | .t => .f | .f => .t | .n => .n

def phAnd : Ph → Ph → Ph
  | .t, .t => .t | .t, .f => .f | .t, .n => .n
  | .f, .t => .f | .f, .f => .f | .f, .n => .f
  | .n, .t => .n | .n, .f => .f | .n, .n => .n

def phOr : Ph → Ph → Ph
  | .t, .t => .t | .t, .f => .t | .t, .n => .t
  | .f, .t => .t | .f, .f => .f | .f, .n => .n
  | .n, .t => .t | .n, .f => .n | .n, .n => .n

def phImp : Ph → Ph → Ph
  | .t, .t => .t | .t, .f => .f | .t, .n => .n
  | .f, .t => .t | .f, .f => .t | .f, .n => .t
  | .n, .t => .t | .n, .f => .n | .n, .n => .n

def phXor : Ph → Ph → Ph
  | .t, .t => .f | .t, .f => .t | .t, .n => .n
  | .f, .t => .t | .f, .f => .f | .f, .n => .n
  | .n, .t => .n | .n, .f => .n | .n, .n => .n

def phXnor : Ph → Ph → Ph
  | .t, .t => .t | .t, .f => .f | .t, .n => .n
  | .f, .t => .f | .f, .f => .t | .f, .n => .n
  | .n, .t => .n | .n, .f => .n | .n, .n => .n

/-- one derived rule, checked on every pair of reachable reading-pairs -/
theorem rule2 (g : Bool → Bool → Bool) (r : Ph → Ph → Ph)
    (h : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
      phOf (comb g (a, b) (c, d)) = r (phOf (a, b)) (phOf (c, d)))
    (p q : Bool × Bool) (hp : (p.1 || p.2) = true) (hq : (q.1 || q.2) = true) :
    phOf (comb g p q) = r (phOf p) (phOf q) := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q; exact h a b c d hp hq

theorem fo_neg (v : Nat → V) (φ : Fm) : fo v (.neg φ) = phNot (fo v φ) := by
  have h := rd_nonempty v φ
  show phOf ((rd v φ).2, (rd v φ).1) = phNot (phOf (rd v φ))
  revert h; generalize rd v φ = p; obtain ⟨a, b⟩ := p; cases a <;> cases b <;> decide

theorem fo_conj (v : Nat → V) (φ ψ : Fm) : fo v (.conj φ ψ) = phAnd (fo v φ) (fo v ψ) :=
  rule2 _ _ (by intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide) _ _ (rd_nonempty v φ) (rd_nonempty v ψ)
theorem fo_disj (v : Nat → V) (φ ψ : Fm) : fo v (.disj φ ψ) = phOr (fo v φ) (fo v ψ) :=
  rule2 _ _ (by intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide) _ _ (rd_nonempty v φ) (rd_nonempty v ψ)
theorem fo_imp (v : Nat → V) (φ ψ : Fm) : fo v (.imp φ ψ) = phImp (fo v φ) (fo v ψ) :=
  rule2 _ _ (by intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide) _ _ (rd_nonempty v φ) (rd_nonempty v ψ)
theorem fo_xor (v : Nat → V) (φ ψ : Fm) : fo v (.xor φ ψ) = phXor (fo v φ) (fo v ψ) :=
  rule2 _ _ (by intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide) _ _ (rd_nonempty v φ) (rd_nonempty v ψ)
theorem fo_xnor (v : Nat → V) (φ ψ : Fm) : fo v (.xnor φ ψ) = phXnor (fo v φ) (fo v ψ) :=
  rule2 _ _ (by intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide) _ _ (rd_nonempty v φ) (rd_nonempty v ψ)

/-- the outcome of an atom -/
def phAtom : V → Ph
  | T => .t | F => .f | Z => .n

theorem fo_atom (v : Nat → V) (n : Nat) : fo v (.atom n) = phAtom (v n) := by
  show phOf ((subs (v n)).contains true, (subs (v n)).contains false) = phAtom (v n)
  cases v n <;> rfl

theorem fo_top (v : Nat → V) : fo v .top = .t := rfl
theorem fo_bot (v : Nat → V) : fo v .bot = .f := rfl

/-- EARNED is the outcome t; REFUTED is the outcome f. -/
theorem earnedR_iff_t (v : Nat → V) (φ : Fm) : earnedR v φ ↔ fo v φ = .t := by
  have h := rd_nonempty v φ
  unfold earnedR fo
  revert h; generalize rd v φ = p; obtain ⟨a, b⟩ := p; cases a <;> cases b <;> decide
theorem refutedR_iff_f (v : Nat → V) (φ : Fm) : refutedR v φ ↔ fo v φ = .f := by
  have h := rd_nonempty v φ
  unfold refutedR fo
  revert h; generalize rd v φ = p; obtain ⟨a, b⟩ := p; cases a <;> cases b <;> decide

/-! ## The fast count, connective by connective — and the theorem that it IS the forced reading -/

/-- the forced outcome computed in one pass (each rule is `fo_neg`, `fo_conj`, … above) -/
def foC (v : Nat → V) : Fm → Ph
  | .atom n    => phAtom (v n)
  | .top       => .t
  | .bot       => .f
  | .neg φ     => phNot (foC v φ)
  | .conj φ ψ  => phAnd (foC v φ) (foC v ψ)
  | .disj φ ψ  => phOr (foC v φ) (foC v ψ)
  | .imp φ ψ   => phImp (foC v φ) (foC v ψ)
  | .xor φ ψ   => phXor (foC v φ) (foC v ψ)
  | .xnor φ ψ  => phXnor (foC v φ) (foC v ψ)

/-- **the one-pass count is exactly the forced reading** (option 2: definition by readings, speed by theorem) -/
theorem foC_eq_fo (v : Nat → V) : ∀ φ : Fm, foC v φ = fo v φ
  | .atom n    => (fo_atom v n).symm
  | .top       => rfl
  | .bot       => rfl
  | .neg φ     => by show phNot (foC v φ) = _; rw [foC_eq_fo v φ, fo_neg]
  | .conj φ ψ  => by show phAnd (foC v φ) (foC v ψ) = _; rw [foC_eq_fo v φ, foC_eq_fo v ψ, fo_conj]
  | .disj φ ψ  => by show phOr (foC v φ) (foC v ψ) = _; rw [foC_eq_fo v φ, foC_eq_fo v ψ, fo_disj]
  | .imp φ ψ   => by show phImp (foC v φ) (foC v ψ) = _; rw [foC_eq_fo v φ, foC_eq_fo v ψ, fo_imp]
  | .xor φ ψ   => by show phXor (foC v φ) (foC v ψ) = _; rw [foC_eq_fo v φ, foC_eq_fo v ψ, fo_xor]
  | .xnor φ ψ  => by show phXnor (foC v φ) (foC v ψ) = _; rw [foC_eq_fo v φ, foC_eq_fo v ψ, fo_xnor]

/-- the verdict a decided outcome stands for (n is never read: it is only used under "decided") -/
def phVal : Ph → V
  | .t => T | .f => F | .n => F

/-! ## More data never revokes a forced outcome -/

theorem leqb_to_refinesR : ∀ a b : V, leqb a b = true → a ≠ Z → b = a := by decide

/-- forced T stays forced T under refinement (the information order, pointwise) -/
theorem foC_t_mono {v w : Nat → V} (h : ∀ n, leqb (v n) (w n) = true) {φ : Fm}
    (hv : foC v φ = .t) : foC w φ = .t := by
  have r : refinesR v w := fun n hn => leqb_to_refinesR (v n) (w n) (h n) hn
  rw [foC_eq_fo] at hv ⊢
  exact (earnedR_iff_t w φ).mp (earnedR_open r ((earnedR_iff_t v φ).mpr hv))

/-- forced F stays forced F under refinement -/
theorem foC_f_mono {v w : Nat → V} (h : ∀ n, leqb (v n) (w n) = true) {φ : Fm}
    (hv : foC v φ = .f) : foC w φ = .f := by
  have r : refinesR v w := fun n hn => leqb_to_refinesR (v n) (w n) (h n) hn
  rw [foC_eq_fo] at hv ⊢
  exact (refutedR_iff_f w φ).mp (refutedR_open r ((refutedR_iff_f v φ).mpr hv))

/-- a decided outcome stays the same under refinement -/
theorem foC_def_mono {v w : Nat → V} (h : ∀ n, leqb (v n) (w n) = true) {φ : Fm} {x : Ph}
    (hx : x ≠ .n) (hv : foC v φ = x) : foC w φ = x := by
  cases x with
  | t => exact foC_t_mono h hv
  | f => exact foC_f_mono h hv
  | n => exact absurd rfl hx

end V

#print axioms V.rd_nonempty
#print axioms V.fo_neg
#print axioms V.fo_conj
#print axioms V.fo_disj
#print axioms V.fo_imp
#print axioms V.fo_xor
#print axioms V.fo_xnor
#print axioms V.fo_atom
#print axioms V.earnedR_iff_t
#print axioms V.refutedR_iff_f
#print axioms V.foC_eq_fo
#print axioms V.foC_t_mono
#print axioms V.foC_f_mono
#print axioms V.foC_def_mono
