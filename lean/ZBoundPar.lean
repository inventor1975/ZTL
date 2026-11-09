import ZBound
import ZRootPar
/-!
# ZBoundPar — a requirement on an IMPLICIT quantity: the zimplicit judge's root and ZBound's bound, one theorem.

The curator's course (2026-11-08, "связка судьи zimplicit с системами → вердикты как теоремы"), and ztl-stand's
`--prove` (2026-11-09: 8 requirements on implicit roots — a fan's operating point, a pump's — stood untranslated).

`ZRootPar` proves, for every parameter vector `p` strictly inside its box (`InnerIn`), a UNIQUE root `x ∈ [qa, qb]`
of the law `FP e qa ps p x = evR (envP qa ps p x) e = 0`. `ZBound` proves a bound of an expression over a box, on
the same `evR`. The box `boxPS qa qb ps` — the root's bracket at variable 0, each parameter's interval at its own
index — holds the point `envP qa ps p x` (`inbox_envP`). So a bound over that box holds at THE root: the
requirement on the implicit quantity, for every parameter vector. Zero axioms.

Said, not hidden: the bound is proved over the whole bracket × the parameters' box, so the root's dependence on the
parameters is not used — a requirement with a margin is provable, one met exactly is not.
-/

namespace ZBoundPar

open VR VR.Numbers ZNumBin ZField ZPoly ZIv ZXE ZRealCF ZRootDiv ZBound ZRootPVR ZRootPar

/-- The root's bracket at variable 0, each parameter's interval at its own index. -/
def boxPS (a b : D) (ps : PS) : Box := fun i => cond (Nat.beq i 0) (some (a, b)) (lookI i ps)

/-- **The root's point lies in the box**: parameters on their intervals, the root in its bracket. -/
theorem inbox_envP {a lo hi : D} {ps : PS} {p : Nat → RExpr} {x : RExpr} (hp : ParIn p ps)
    (hx1 : rle (dv rOH lo) x) (hx2 : rle x (dv rOH hi)) : InBox rCF (boxPS lo hi ps) (envP a ps p x) := by
  intro i I hI
  cases h0 : Nat.beq i 0 with
  | true =>
    have hI' : some (lo, hi) = some I := by
      have : cond (Nat.beq i 0) (some (lo, hi)) (lookI i ps) = some I := hI
      rw [h0] at this; exact this
    cases hI'
    have e : envP a ps p x i = x := by
      show cond (Nat.beq i 0) x (envOf a ps p i) = x
      rw [h0]; rfl
    rw [e]; exact ⟨hx1, hx2⟩
  | false =>
    have hI' : lookI i ps = some I := by
      have : cond (Nat.beq i 0) (some (lo, hi)) (lookI i ps) = some I := hI
      rw [h0] at this; exact this
    have hP := isP_of_lookI hI'
    have e : envP a ps p x i = p i := by
      show cond (Nat.beq i 0) x (cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (p i) rzero)) = p i
      rw [h0, hP]; rfl
    rw [e]; exact lookI_mem hp hI'

/-- **The bound at the root**: a bound over `boxPS qa qb ps` holds at every root in the bracket, for every
parameter vector strictly inside its box. -/
theorem bound_at_root {lo : Bool} {e : XE} {c : D} {vs : List Nat} {T : VT} {a b : D} {ps : PS} {μ : Nat}
    (h : chkV lo e c vs T (boxPS a b ps) = true) (hpos : posOK (boxPS a b ps) e = true)
    {p : Nat → RExpr} (hin : InnerIn μ p ps) {x : RExpr} (hx1 : rle (dv rOH a) x) (hx2 : rle x (dv rOH b)) :
    Holds rCF lo c (evR (envP a ps p x) e) :=
  bound_vrM h hpos _ (inbox_envP (parIn_inner (p := p) hin) hx1 hx2)

/-! ## The root's own side: a requirement `q ≥ c` (or `q ≤ c`) from the law's SIGN

A bound over the bracket cannot prove `q ≥ c` when the bracket reaches below `c` (zimplicit widens it past the
root's range for its certificate: ztl-stand tasks/t19, `Q ≥ 1/400`). The law's sign does: strictly signed on
`[qa, c]` (a ZBound bound away from 0), it has no root there — the root is `≥ c`. -/

section Sep
variable {α : Type} {S : CF α}
theorem le_of_pos_sub {a b : α} (h : S.pos (S.add b (S.neg a))) : S.le a b := by
  have h0 := S.pos_nonneg h
  cr_linarith S.toOCR [h0]
theorem neg_le_zero_of {d : α} (h : S.le S.zero d) : S.le (S.neg d) S.zero := by cr_linarith S.toOCR [h]
end Sep

/-- A bound's side that excludes 0: `d > 0` for a lower bound, `d < 0` for an upper one. -/
def SepD (lo : Bool) (d : D) : Prop := cond lo (rCF.pos (dv rOH d)) (rCF.pos (rCF.neg (dv rOH d)))

theorem holds_ne {lo : Bool} {d : D} {v : RExpr} (hd : SepD lo d) (h : Holds rCF lo d v) (hz : rCF.r v rCF.zero) :
    False := by
  cases lo with
  | true =>
    have hd' : rCF.pos (dv rOH d) := hd
    have h' : rCF.le (dv rOH d) v := h
    exact rCF.pos_not_le hd' (rCF.le_respects (rCF.refl _) hz h')
  | false =>
    have hd' : rCF.pos (rCF.neg (dv rOH d)) := hd
    have h' : rCF.le v (dv rOH d) := h
    have h0 : rCF.le rCF.zero (dv rOH d) := rCF.le_respects hz (rCF.refl _) h'
    exact rCF.pos_not_le hd' (neg_le_zero_of h0)

/-- **The root is `≥ c`**: the law strictly signed on `[a, c]` (for every parameter vector). -/
theorem root_ge {lo : Bool} {e : XE} {d : D} {vs : List Nat} {T : VT} {a c : D} {ps : PS} {μ : Nat}
    (h : chkV lo e d vs T (boxPS a c ps) = true) (hpos : posOK (boxPS a c ps) e = true) (hd : SepD lo d)
    {p : Nat → RExpr} (hin : InnerIn μ p ps) {x : RExpr} (hxa : rle (dv rOH a) x)
    (hroot : rEq (FP e a ps p x) rzero) : rle (dv rOH c) x :=
  rCF.le_of_not_pos (fun hp => holds_ne hd
    (bound_vrM h hpos _ (inbox_envP (parIn_inner (p := p) hin) hxa (le_of_pos_sub hp))) hroot)

/-- **The root is `≤ c`**: the law strictly signed on `[c, b]`. -/
theorem root_le {lo : Bool} {e : XE} {d : D} {vs : List Nat} {T : VT} {a b c : D} {ps : PS} {μ : Nat}
    (h : chkV lo e d vs T (boxPS c b ps) = true) (hpos : posOK (boxPS c b ps) e = true) (hd : SepD lo d)
    {p : Nat → RExpr} (hin : InnerIn μ p ps) {x : RExpr} (hxb : rle x (dv rOH b))
    (hroot : rEq (FP e a ps p x) rzero) : rle x (dv rOH c) :=
  rCF.le_of_not_pos (fun hp => holds_ne hd
    (bound_vrM h hpos _ (inbox_envP (a := a) (parIn_inner (p := p) hin) (le_of_pos_sub hp) hxb)) hroot)

end ZBoundPar

#print axioms ZBoundPar.boxPS
#print axioms ZBoundPar.inbox_envP
#print axioms ZBoundPar.bound_at_root
#print axioms ZBoundPar.le_of_pos_sub
#print axioms ZBoundPar.neg_le_zero_of
#print axioms ZBoundPar.SepD
#print axioms ZBoundPar.holds_ne
#print axioms ZBoundPar.root_ge
#print axioms ZBoundPar.root_le
