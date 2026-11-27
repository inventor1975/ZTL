import VR.Meta.CSRNorm

/-!
# ZElim — what `znumsolve` derives is a consequence: eliminated rows and disjunctions. Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема». Two narrowings of `znumsolve` rest on one
fact each:

  `_solve_monomial_system` (x and x² as separate columns) eliminates over the EQUALITIES: every row it derives is a
  linear combination of the given rows, so `row_comb_zero` — at a point where every given row is 0, every combination
  is 0 — makes each derived row (and the refutation 0 = c ≠ 0) a CONSEQUENCE, whatever the columns are (monomials
  included: a column is any value).

  `_disjunction_pieces` (`x == 2 | x == 3`): the unknown lies in the union of the alternatives' pieces — `union_sound`:
  if each alternative's pieces contain its solutions, the union contains the disjunction's.

Over VR's commutative semiring (`CSR`, up to its equivalence `r`): every instance qualifies, ℚ among them.
-/

namespace ZElim
open VR.CSR

variable {α : Type} (S : CSR α)

/-- Σ λᵢ·vᵢ over a list of (multiplier, row value). -/
def comb : List (α × α) → α
  | [] => S.zero
  | (l, v) :: rest => S.add (S.mul l v) (comb rest)

/-- Every row 0 at the point ⇒ every linear combination 0 there. -/
theorem row_comb_zero : ∀ (rows : List (α × α)), (∀ lv, List.Mem lv rows → S.r lv.2 S.zero) → S.r (comb S rows) S.zero
  | [], _ => S.refl _
  | (l, v) :: rest, h => by
      have hv : S.r v S.zero := h (l, v) (List.Mem.head _)
      have ih := row_comb_zero rest (fun lv hm => h lv (List.Mem.tail _ hm))
      show S.r (S.add (S.mul l v) (comb S rest)) S.zero
      exact S.trans (S.add_congr (S.trans (S.mul_congr (S.refl l) hv) (CSR.mul_zero S l)) ih) (S.zero_add _)

/-- A refutation by elimination is sound: if a combination of the rows is a NONZERO constant, the rows have no common
zero — at no point are all of them 0. -/
theorem refutation_sound (rows : List (α × α)) (c : α) (hc : S.r (comb S rows) c) (hnz : ¬ S.r c S.zero) :
    ¬ (∀ lv, List.Mem lv rows → S.r lv.2 S.zero) :=
  fun h => hnz (S.trans (S.symm hc) (row_comb_zero S rows h))

/-- The union of pieces contains the solutions of a disjunction. `mem x P` is "x lies in one of the pieces P". -/
theorem union_sound {β : Type} (mem : β → List (β × β) → Prop)
    (mem_append_l : ∀ x P Q, mem x P → mem x (P ++ Q)) (mem_append_r : ∀ x P Q, mem x Q → mem x (P ++ Q))
    (A B : β → Prop) (PA PB : List (β × β)) (hA : ∀ x, A x → mem x PA) (hB : ∀ x, B x → mem x PB) :
    ∀ x, (A x ∨ B x) → mem x (PA ++ PB)
  | x, Or.inl h => mem_append_l x PA PB (hA x h)
  | x, Or.inr h => mem_append_r x PA PB (hB x h)

end ZElim

#print axioms ZElim.row_comb_zero
#print axioms ZElim.refutation_sound
#print axioms ZElim.union_sound
