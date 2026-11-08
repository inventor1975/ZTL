import ZBound
/-!
# ZBoundDivider — the stand's divider requirement as a THEOREM on VR's continuum. Zero axioms.

ztl-stand `examples/divider-1pct-req-1pct.json`: `Vin − Vout = I·R1`, `Vout = I·R2`, `Vin = 5 V`, R1 and R2 from the
E24 series at ±1 %, the requirement `Vout ∈ [2.475, 2.525]` ("2.5 V ±1 %"). For the stand's design R1 = R2 = 1 kΩ the
requirement is met EXACTLY at the corners (5·1010/2000 = 2.525) — no margin, so no interval reading proves it; the
monotone leaf does (`ZBound.chkV`: the slope's sign takes the point to the corner, where the cleared form is exact).

The theorem, for EVERY real R1, R2 in [990, 1010]:  `2475 ≤ 1000·Vout ≤ 2525`, `Vout = 5·R2/(R1 + R2)`
(`1000·Vout` = `5000·R2/(R1 + R2)`; the bound is read as `c·(R1 + R2) − 5000·R2 ≥ 0`, `R1 + R2 > 0` — `ZBound.le_of_quot`).

Said, not hidden: `Vout = Vin·R2/(R1 + R2)` is the laws' elimination (the stand's exact solver), not proved here; the
theorem is about that expression.
-/

namespace ZBoundDivider

open VR VR.Numbers ZNumBin ZField ZPoly ZIv ZXE ZRealCF ZRootDiv ZBound

def n (k : Nat) : D := ⟨⟨k, 0⟩, 0⟩

/-- The box: R1 = var 0, R2 = var 1, each in [990, 1010]. -/
def B : Box := fun i => cond (Nat.beq i 0) (some (n 990, n 1010)) (cond (Nat.beq i 1) (some (n 990, n 1010)) none)

def num : XE := .mul (.cst (n 5000)) (.var 1)
def den : XE := .add (.var 0) (.var 1)
/-- `1000·Vout`. -/
def vout : XE := .div num den

/-- The cleared forms: `2525·(R1 + R2) − 5000·R2 ≥ 0` and `5000·R2 − 2475·(R1 + R2) ≥ 0`. -/
def upC : XE := .sub (.mul (.cst (n 2525)) den) num
def loC : XE := .sub num (.mul (.cst (n 2475)) den)

theorem up_holds : ∀ x : Nat → RExpr, InBox rCF B x → rCF.le (dv rOH (n 0)) (evR x upC) :=
  bound_vrM (lo := true) (vs := [0, 1]) (T := .mono) (by decide +kernel) (by decide +kernel)

theorem lo_holds : ∀ x : Nat → RExpr, InBox rCF B x → rCF.le (dv rOH (n 0)) (evR x loC) :=
  bound_vrM (lo := true) (vs := [0, 1]) (T := .mono) (by decide +kernel) (by decide +kernel)

/-- **THE DIVIDER MEETS ITS REQUIREMENT**: for every real R1, R2 in [990, 1010], `2475 ≤ 1000·Vout ≤ 2525`. -/
theorem divider (x : Nat → RExpr) (hx : InBox rCF B x) :
    rCF.le (dv rOH (n 2475)) (evR x vout) ∧ rCF.le (evR x vout) (dv rOH (n 2525)) := by
  obtain ⟨hpos, hv⟩ := div_value hx (a := num) (b := den) (by decide +kernel)
  have z : rCF.r (dv rOH (n 0)) rCF.zero := zv_isZ rOH (c := n 0) rfl
  have u := rCF.le_respects z (rCF.refl _) (up_holds x hx)
  have l := rCF.le_respects z (rCF.refl _) (lo_holds x hx)
  exact ⟨ge_of_quot hpos hv l, le_of_quot hpos hv u⟩

/-! ## The other side: a requirement the design does NOT meet is refused by the kernel -/

/-- `1000·Vout ≤ 2524` fails at R1 = 990, R2 = 1010 (2525): no tree passes; the monotone leaf reads the corner -1. -/
example : chkV true (.sub (.mul (.cst (n 2524)) den) num) (n 0) [0, 1] .mono B = false := by decide +kernel

/-! ## Not monotone: `x·e⁻ˣ ≤ 3/8` on [0, 3] (its maximum `1/e ≈ 0.3679` at x = 1), a tree of cuts -/

def B1 : Box := fun i => cond (Nat.beq i 0) (some (n 0, n 3)) none
def xe : XE := .mul (.var 0) (.exp (.sub (.cst (n 0)) (.var 0)))

/-- The tree, found by `ZBound.findV` and pasted: 22 leaves, mostly monotone. -/
def T1 : VT := (.cut 0 (⟨⟨3, 0⟩, 1⟩ : D) (.cut 0 (⟨⟨3, 0⟩, 2⟩ : D) (.cut 0 (⟨⟨3, 0⟩, 3⟩ : D) .mono (.cut 0 (⟨⟨9, 0⟩, 4⟩ : D) .mono .mono)) (.cut 0 (⟨⟨9, 0⟩, 3⟩ : D) (.cut 0 (⟨⟨15, 0⟩, 4⟩ : D) (.cut 0 (⟨⟨27, 0⟩, 5⟩ : D) .mono (.cut 0 (⟨⟨57, 0⟩, 6⟩ : D) .mono .mono)) (.cut 0 (⟨⟨33, 0⟩, 5⟩ : D) (.cut 0 (⟨⟨63, 0⟩, 6⟩ : D) (.cut 0 (⟨⟨123, 0⟩, 7⟩ : D) .mono (.cut 0 (⟨⟨249, 0⟩, 8⟩ : D) .mono .mono)) (.cut 0 (⟨⟨129, 0⟩, 7⟩ : D) (.cut 0 (⟨⟨255, 0⟩, 8⟩ : D) .leaf .leaf) (.cut 0 (⟨⟨261, 0⟩, 8⟩ : D) .leaf .mono))) (.cut 0 (⟨⟨69, 0⟩, 6⟩ : D) (.cut 0 (⟨⟨135, 0⟩, 7⟩ : D) .mono .mono) .mono))) (.cut 0 (⟨⟨21, 0⟩, 4⟩ : D) (.cut 0 (⟨⟨39, 0⟩, 5⟩ : D) .mono .mono) .mono))) (.cut 0 (⟨⟨9, 0⟩, 2⟩ : D) (.cut 0 (⟨⟨15, 0⟩, 3⟩ : D) .mono .mono) .mono))

/-- **x·e⁻ˣ ≤ 3/8 FOR EVERY REAL x IN [0, 3]**, VR's `exp`. -/
theorem xexp_bound : ∀ x : Nat → RExpr, InBox rCF B1 x → rCF.le (evR x xe) (dv rOH ⟨⟨3, 0⟩, 3⟩) :=
  bound_vrM (lo := false) (vs := [0]) (T := T1) (by decide +kernel) (by decide +kernel)

/-- The other side: `x·e⁻ˣ ≤ 367/1024 ≈ 0.3584` (below 1/e) — the same tree is refused. -/
example : chkV false xe ⟨⟨367, 0⟩, 10⟩ [0] T1 B1 = false := by decide +kernel

end ZBoundDivider

#print axioms ZBoundDivider.up_holds
#print axioms ZBoundDivider.lo_holds
#print axioms ZBoundDivider.divider
#print axioms ZBoundDivider.xexp_bound
