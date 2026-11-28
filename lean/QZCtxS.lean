import QZ4
import QZ7
import QZ9

/-!
# QZCtxS — the last link of T2: a splitting state commutes with every question it splits along. Zero axioms.

(2026-11-28, Logik2; twin of Q/CtxSplit.agda; word-first T2(d) in QZ/THEOREMS-WORDFIRST.md. Written with AI.)

  `splits_comm_all`  if s splits along the list (QZ4 `Splits`), the projection of s commutes with every question of
                     the list, at every depth: the head by QZ9 `split_comm`; the rest because s is the sum of its two
                     cells (QZ7 `split_sum`) and a sum of commuting projections commutes
  `first_commutes`   the full space splitting along x, then the rest: x commutes with every later question. So one
                     later ray that does not commute with the first makes `Splits` fail and the QZ judge withdraws
                     the stable verdict — which, with QZCtx / QZCtxL, closes T2 for Kochen–Specker families
-/

namespace QZCtxS
open QZ3 QZ4 QZ7 QZ9

variable {A : Type} {R : Alg A} {α : Type} {L : NLat α}

/-- every member of the list satisfies P -/
def AllL {X : Type} (P : X → Prop) : List X → Prop
  | [] => True
  | x :: xs => P x ∧ AllL P xs

theorem cm_add {a b z : A} (ha : Comm R a z) (hb : Comm R b z) : Comm R (R.add a b) z :=
  R.trans (R.add_mul a b z) (R.trans (R.add_congr ha hb) (R.symm (R.mul_add z a b)))

/-- A SPLITTING STATE COMMUTES WITH EVERY QUESTION IT SPLITS ALONG -/
theorem splits_comm_all (E : Rep R L) : ∀ (s : α) (xs : List α), Splits L s xs → AllL (fun z => Comm R (E.e s) (E.e z)) xs
  | _, [], _ => True.intro
  | s, x :: rest, ⟨h0, h1, h2⟩ =>
    ⟨split_comm E s x h0, go (h0 := h0) rest (splits_comm_all E (L.meet s x) rest h1) (splits_comm_all E (L.meet s (L.neg x)) rest h2)⟩
where
  go {s x : α} {h0 : L.le s (L.join (L.meet s x) (L.meet s (L.neg x)))} : ∀ zs : List α,
      AllL (fun z => Comm R (E.e (L.meet s x)) (E.e z)) zs → AllL (fun z => Comm R (E.e (L.meet s (L.neg x))) (E.e z)) zs →
      AllL (fun z => Comm R (E.e s) (E.e z)) zs
    | [], _, _ => True.intro
    | z :: zs, ⟨c1, cs1⟩, ⟨c2, cs2⟩ =>
      ⟨comm_congr R (R.symm (split_sum E s x h0)) (R.refl _) (cm_add c1 c2), go (h0 := h0) zs cs1 cs2⟩

theorem top_meet (E : Rep R L) (x : α) : R.eqv (E.e (L.meet L.top x)) (E.e x) :=
  le_antisymm R (E.le_to (L.meet_le_r L.top x)) (E.le_to (L.le_meet (L.le_top x) (E.le_of ⟨E.isP x, E.isP x⟩)))

/-- THE JUDGE'S CHECK: the full space splitting along x then the rest ⇒ x commutes with every later question -/
theorem first_commutes (E : Rep R L) (x : α) (rest : List α) (h : Splits L L.top (x :: rest)) :
    AllL (fun z => Comm R (E.e x) (E.e z)) rest :=
  conv rest (splits_comm_all E (L.meet L.top x) rest h.2.1)
where
  conv : ∀ zs : List α, AllL (fun z => Comm R (E.e (L.meet L.top x)) (E.e z)) zs → AllL (fun z => Comm R (E.e x) (E.e z)) zs
    | [], _ => True.intro
    | z :: zs, ⟨c, cs⟩ => ⟨comm_congr R (top_meet E x) (R.refl _) c, conv zs cs⟩

/-- the contrapositive the judge uses, with the two projections named by matrices the caller writes -/
theorem no_split_of' (E : Rep R L) (x y : α) (X Y : A) (ex : E.e x = X) (ey : E.e y = Y) (nc : ¬ Comm R X Y) :
    ¬ Splits L L.top [x, y] := fun h => by
  cases ex; cases ey
  exact nc (first_commutes E x [y] h).1

end QZCtxS

#print axioms QZCtxS.splits_comm_all
#print axioms QZCtxS.first_commutes
#print axioms QZCtxS.no_split_of'
