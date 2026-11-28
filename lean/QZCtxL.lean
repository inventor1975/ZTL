import QZ3
import QZ4
import QZCtx

/-!
# QZCtxL — the lattice side of QZCtx: the Kochen–Specker formula is TRUE in the lattice. Zero axioms.

(2026-11-28, Logik2; word-first T2(a), T2(d) in QZ/THEOREMS-WORDFIRST.md. Written with AI.)

  `ctx_true_in_lattice`  in any lattice of QZ3 (`NLat`) with NON-CONTRADICTION (x ∧ ¬x ≤ ⊥ — QZ3 does not assume it;
                         the lattice of subspaces has it), if every basis's rays join to ⊤ and are pairwise
                         orthogonal (a ≤ ¬b), the formula `QZCtx.ctx B` is ⊤: true in every state. With QZCtx:
                         the same formula that the kernel refutes IF STABLE (exactly for KS-uncolourable families)
                         is true in the lattice.
  `splits_pair`          QZ4's `Splits` of the full space along x then y contains "x is compatible with y"
                         (x ≤ (x ∧ y) ∨ (x ∧ ¬y)). That compatibility fails for non-commuting projections is QZ9
                         (split_comm: splitting ⇒ commuting); here only the unfolding — so a KS family, whose rays of
                         different bases do not commute, makes the QZ judge withdraw the stable verdict.
Hypotheses, named, not hidden: completeness and orthogonality of each basis are given (no subspace lattice is built
here; calib/ks18_lattice.py measures them for the 18 rays).
-/

namespace QZCtxL
open V QZ3 QZ4 QZCtx

variable {α : Type} (L : NLat α)

/-- every ray of the list is orthogonal to the ray of `a` -/
def OrthTo (val : Nat → α) (a : Nat) : List Nat → Prop
  | [] => True
  | b :: bs => L.le (val a) (L.neg (val b)) ∧ OrthTo val a bs

/-- the rays of the list are pairwise orthogonal -/
def Orth (val : Nat → α) : List Nat → Prop
  | [] => True
  | a :: as => OrthTo L val a as ∧ Orth val as

/-- every basis complete (its rays join to ⊤) and orthogonal -/
def Good (val : Nat → α) : List (List Nat) → Prop
  | [] => True
  | b :: bs => (L.le L.top (qe L val (bigOr b)) ∧ Orth L val b) ∧ Good val bs

/-- two orthogonal rays: ¬(a ∧ b) is ⊤ -/
theorem excl_pair_top (nc : ∀ x, L.le (L.meet (L.neg x) x) L.bot) (val : Nat → α) (a b : Nat) (h : L.le (val a) (L.neg (val b))) :
    L.le L.top (L.neg (L.meet (val a) (val b))) :=
  L.le_trans (L.le_neg_bot L.top)
    (L.anti (L.le_trans (L.le_meet (L.le_trans (L.meet_le_l _ _) h) (L.meet_le_r _ _)) (nc (val b))))

theorem allNot_top (nc : ∀ x, L.le (L.meet (L.neg x) x) L.bot) (val : Nat → α) (a : Nat) : ∀ bs, OrthTo L val a bs → L.le L.top (qe L val (allNot a bs))
  | [], _ => L.le_top L.top
  | b :: bs, ⟨h, hs⟩ => L.le_meet (excl_pair_top L nc val a b h) (allNot_top nc val a bs hs)

theorem excl_top (nc : ∀ x, L.le (L.meet (L.neg x) x) L.bot) (val : Nat → α) : ∀ b, Orth L val b → L.le L.top (qe L val (excl b))
  | [], _ => L.le_top L.top
  | a :: as, ⟨h, hs⟩ => L.le_meet (allNot_top L nc val a as h) (excl_top nc val as hs)

/-- THE KOCHEN–SPECKER FORMULA IS TRUE IN THE LATTICE: ⊤, in every state -/
theorem ctx_true_in_lattice (nc : ∀ x, L.le (L.meet (L.neg x) x) L.bot) (val : Nat → α) : ∀ B, Good L val B → L.le L.top (qe L val (ctx B))
  | [], _ => L.le_top L.top
  | b :: bs, ⟨⟨hc, ho⟩, hs⟩ => L.le_meet (L.le_meet hc (excl_top L nc val b ho)) (ctx_true_in_lattice nc val bs hs)

/-- `Splits` of ⊤ along x then y contains: x (= ⊤ ∧ x) is compatible with y -/
theorem splits_pair (s x y : α) (rest : List α) (h : Splits L s (x :: y :: rest)) :
    L.le (L.meet s x) (L.join (L.meet (L.meet s x) y) (L.meet (L.meet s x) (L.neg y))) :=
  h.2.1.1

end QZCtxL

#print axioms QZCtxL.excl_pair_top
#print axioms QZCtxL.ctx_true_in_lattice
#print axioms QZCtxL.splits_pair
