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
theorem inbox_envP {a b : D} {ps : PS} {p : Nat → RExpr} {x : RExpr} (hp : ParIn p ps)
    (hx1 : rle (dv rOH a) x) (hx2 : rle x (dv rOH b)) : InBox rCF (boxPS a b ps) (envP a ps p x) := by
  intro i I hI
  cases h0 : Nat.beq i 0 with
  | true =>
    have hI' : some (a, b) = some I := by
      have : cond (Nat.beq i 0) (some (a, b)) (lookI i ps) = some I := hI
      rw [h0] at this; exact this
    cases hI'
    have e : envP a ps p x i = x := by
      show cond (Nat.beq i 0) x (envOf a ps p i) = x
      rw [h0]; rfl
    rw [e]; exact ⟨hx1, hx2⟩
  | false =>
    have hI' : lookI i ps = some I := by
      have : cond (Nat.beq i 0) (some (a, b)) (lookI i ps) = some I := hI
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

end ZBoundPar

#print axioms ZBoundPar.boxPS
#print axioms ZBoundPar.inbox_envP
#print axioms ZBoundPar.bound_at_root
