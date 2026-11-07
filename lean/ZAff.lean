import ZIv
/-!
# ZAff — the AFFINE reading of a polynomial expression over a box, computed by the kernel. Zero axioms.

A tail of the Lean-checked `check_none` (curator, 2026-11-07: "не забудь" — the affine reading). A form is
`c + Σ sᵢ·(xᵢ − mᵢ) ± e`, `mᵢ` the midpoint of variable `i`'s interval in the box (computed from the box, not
stored — so equal variables MERGE and `x − x` cancels, which the interval reading cannot do). `+`, `−` are exact
on the linear part; `×` keeps `c₁c₂ + c₁L₂ + c₂L₁` and bounds the rest by `|c₁|e₂ + |c₂|e₁ + (R₁ + e₁)(R₂ + e₂)`,
`Rᵢ = Σ |s|·rᵢ` (`ZIv.mul_lower`/`mul_upper` on `[−A, A] × [−B, B]`). The interval of a form is
`[c − R − e, c + R + e]`. Soundness (`af_sound`) in every `CF`. Rounding is a separate step that moves the
rounding error into `e`.

Part 1: forms and their meaning; midpoint and radius; the variable, the constant, the sum.
-/

namespace ZAff
open VR.CSR ZNumBin ZField ZPoly ZIv

structure AF where
  c : D
  L : List (Nat × D)
  e : D

variable {α : Type} (S : CF α)

/-- `(lo + hi)/2` and `(hi − lo)/2`, exact. -/
def mid (I : Iv) : D := let d := dadd I.1 I.2; ⟨d.m, d.e + 1⟩
def rad (I : Iv) : D := let d := dadd I.2 (dneg I.1); ⟨d.m, d.e + 1⟩

def midv (B : Box) (p : Nat → α) (i : Nat) : α :=
  match B i with
  | some I => S.add (p i) (S.neg (dv S.toOH (mid I)))
  | none => S.zero

/-- The linear part at a point: `Σ sᵢ·(pᵢ − mᵢ)`. -/
def linv (B : Box) (p : Nat → α) : List (Nat × D) → α
  | [] => S.zero
  | (i, s) :: L => S.add (S.mul (dv S.toOH s) (midv S B p i)) (linv B p L)

/-- `v` is within `e` of the form at `p`. -/
def Enc (B : Box) (p : Nat → α) (v : α) (F : AF) : Prop :=
  S.le (S.neg (dv S.toOH F.e)) (S.add v (S.neg (S.add (dv S.toOH F.c) (linv S B p F.L)))) ∧
  S.le (S.add v (S.neg (S.add (dv S.toOH F.c) (linv S B p F.L)))) (dv S.toOH F.e)

theorem dv_succ (m : BZ) (e : Nat) : S.r (dv S.toOH ⟨m, e + 1⟩) (S.mul S.half (dv S.toOH ⟨m, e⟩)) := by
  show S.r (S.mul (zv S.toOH m) (S.mul S.half (hp S.toOH e))) (S.mul S.half (S.mul (zv S.toOH m) (hp S.toOH e)))
  cr_ring S.toCR

/-- A point of the box is within the radius of the midpoint. -/
theorem near_mid {B : Box} {p : Nat → α} (hp : InBox S B p) {i : Nat} {I : Iv} (hI : B i = some I) :
    S.le (S.neg (dv S.toOH (rad I))) (S.add (p i) (S.neg (dv S.toOH (mid I)))) ∧
    S.le (S.add (p i) (S.neg (dv S.toOH (mid I)))) (dv S.toOH (rad I)) := by
  have m := hp i I hI
  have hm := S.trans (dv_succ S (dadd I.1 I.2).m (dadd I.1 I.2).e) (S.mul_congr (S.refl _) (dv_add S.toOH I.1 I.2))
  have hr := S.trans (dv_succ S (dadd I.2 (dneg I.1)).m (dadd I.2 (dneg I.1)).e)
    (S.mul_congr (S.refl _) (S.trans (dv_add S.toOH I.2 (dneg I.1)) (S.add_congr (S.refl _) (dv_neg S.toOH I.1))))
  have hs := S.half_spec
  have em : S.r (dv S.toOH (mid I)) (S.mul S.half (S.add (dv S.toOH I.1) (dv S.toOH I.2))) := hm
  have er : S.r (dv S.toOH (rad I)) (S.mul S.half (S.add (dv S.toOH I.2) (S.neg (dv S.toOH I.1)))) := hr
  have m1 := m.1
  have m2 := m.2
  have p2 : S.r (S.add (S.mul S.half (p i)) (S.mul S.half (p i))) (p i) :=
    S.trans (by cr_ring S.toCR : S.r (S.add (S.mul S.half (p i)) (S.mul S.half (p i))) (S.mul (S.add S.half S.half) (p i)))
      (S.trans (S.mul_congr hs (S.refl _)) (S.one_mul _))
  have p2a := S.le_respects (S.refl _) p2 (S.le_refl (S.add (S.mul S.half (p i)) (S.mul S.half (p i))))
  have p2b := S.le_respects p2 (S.refl _) (S.le_refl (S.add (S.mul S.half (p i)) (S.mul S.half (p i))))
  constructor
  · refine S.le_respects (S.neg_congr (S.symm er)) (S.add_congr (S.refl _) (S.neg_congr (S.symm em))) ?_
    have q := le_mul_right S.toOH m1 (half_nonneg S.toOH)
    cr_linarith S.toOCR [q, p2a, p2b]
  · refine S.le_respects (S.add_congr (S.refl _) (S.neg_congr (S.symm em))) (S.symm er) ?_
    have q := le_mul_right S.toOH m2 (half_nonneg S.toOH)
    cr_linarith S.toOCR [q, p2a, p2b]

/-! ## The linear part: merge, scale, bound -/

def insertL (t : Nat × D) : List (Nat × D) → List (Nat × D)
  | [] => [t]
  | u :: L => cond (Nat.beq t.1 u.1) ((u.1, dadd t.2 u.2) :: L)
      (cond (Nat.blt t.1 u.1) (t :: u :: L) (u :: insertL t L))

def addL : List (Nat × D) → List (Nat × D) → List (Nat × D)
  | [], M => M
  | t :: L, M => insertL t (addL L M)

def scaleL (c : D) : List (Nat × D) → List (Nat × D)
  | [] => []
  | (i, s) :: L => (i, dmul c s) :: scaleL c L

def negL : List (Nat × D) → List (Nat × D)
  | [] => []
  | (i, s) :: L => (i, dneg s) :: negL L

theorem insertL_sound (B : Box) (p : Nat → α) (t : Nat × D) :
    ∀ L, S.r (linv S B p (insertL t L)) (S.add (S.mul (dv S.toOH t.2) (midv S B p t.1)) (linv S B p L))
  | [] => S.refl _
  | u :: L => by
      cases he : Nat.beq t.1 u.1 with
      | true =>
          rw [insertL, he]
          have e := Nat.eq_of_beq_eq_true he
          show S.r (S.add (S.mul (dv S.toOH (dadd t.2 u.2)) (midv S B p u.1)) (linv S B p L)) _
          rw [e]
          refine S.trans (S.add_congr (S.mul_congr (dv_add S.toOH t.2 u.2) (S.refl _)) (S.refl _)) ?_
          show S.r _ (S.add (S.mul (dv S.toOH t.2) (midv S B p u.1)) (S.add (S.mul (dv S.toOH u.2) (midv S B p u.1)) (linv S B p L)))
          cr_ring S.toCR
      | false =>
          rw [insertL, he]
          cases hl : Nat.blt t.1 u.1 with
          | true => exact S.refl _
          | false =>
              show S.r (S.add (S.mul (dv S.toOH u.2) (midv S B p u.1)) (linv S B p (insertL t L))) _
              refine S.trans (S.add_congr (S.refl _) (insertL_sound B p t L)) ?_
              show S.r _ (S.add (S.mul (dv S.toOH t.2) (midv S B p t.1)) (S.add (S.mul (dv S.toOH u.2) (midv S B p u.1)) (linv S B p L)))
              cr_ring S.toCR

theorem addL_sound (B : Box) (p : Nat → α) :
    ∀ L M, S.r (linv S B p (addL L M)) (S.add (linv S B p L) (linv S B p M))
  | [], M => S.symm (S.zero_add _)
  | t :: L, M => by
      show S.r (linv S B p (insertL t (addL L M))) (S.add (S.add (S.mul (dv S.toOH t.2) (midv S B p t.1)) (linv S B p L)) (linv S B p M))
      refine S.trans (insertL_sound S B p t _) (S.trans (S.add_congr (S.refl _) (addL_sound B p L M)) ?_)
      cr_ring S.toCR

theorem scaleL_sound (B : Box) (p : Nat → α) (c : D) :
    ∀ L, S.r (linv S B p (scaleL c L)) (S.mul (dv S.toOH c) (linv S B p L))
  | [] => S.symm (S.mul_zero _)
  | (i, s) :: L => by
      show S.r (S.add (S.mul (dv S.toOH (dmul c s)) (midv S B p i)) (linv S B p (scaleL c L)))
        (S.mul (dv S.toOH c) (S.add (S.mul (dv S.toOH s) (midv S B p i)) (linv S B p L)))
      refine S.trans (S.add_congr (S.mul_congr (dv_mul S.toOH c s) (S.refl _)) (scaleL_sound B p c L)) ?_
      cr_ring S.toCR

theorem negL_sound (B : Box) (p : Nat → α) :
    ∀ L, S.r (linv S B p (negL L)) (S.neg (linv S B p L))
  | [] => S.symm S.neg_zero
  | (i, s) :: L => by
      show S.r (S.add (S.mul (dv S.toOH (dneg s)) (midv S B p i)) (linv S B p (negL L)))
        (S.neg (S.add (S.mul (dv S.toOH s) (midv S B p i)) (linv S B p L)))
      refine S.trans (S.add_congr (S.mul_congr (dv_neg S.toOH s) (S.refl _)) (negL_sound B p L)) ?_
      cr_ring S.toCR

/-! ## Signs and absolute values of dyadics, decided by the kernel -/

def isNeg (d : D) : Bool := Nat.blt d.m.p d.m.n
def dabs (d : D) : D := cond (isNeg d) (dneg d) d

theorem dv_nonneg_of {d : D} (h : isNeg d = false) : S.le S.zero (dv S.toOH d) := by
  have hle : d.m.n ≤ d.m.p := by
    cases hb : Nat.ble (d.m.p + 1) d.m.n with
    | true => unfold isNeg at h; exact absurd (h.symm.trans hb) (by decide)
    | false =>
        cases Nat.lt_or_ge d.m.p d.m.n with
        | inl hl => exact absurd (Nat.ble_eq_true_of_le hl) (by rw [hb]; decide)
        | inr hg => exact hg
  have l := nI_le S.toOH hle
  have z : S.le S.zero (zv S.toOH d.m) := by unfold zv; cr_linarith S.toOCR [l]
  exact S.mul_nonneg z (hp_nonneg S.toOH d.e)

theorem dv_nonpos_of {d : D} (h : isNeg d = true) : S.le (dv S.toOH d) S.zero := by
  have l := nI_le_of_ble S.toOH (a := d.m.p + 1) (b := d.m.n) h
  have a := nI_add S.toOH d.m.p 1
  have one : S.r (nI S.toOH 1) S.one := by show S.r (S.add S.one S.zero) S.one; cr_ring S.toCR
  have l' := S.le_respects (S.trans a (S.add_congr (S.refl _) one)) (S.refl _) l
  have h0 := S.zero_le_one
  have z' : S.le (zv S.toOH d.m) S.zero := by unfold zv; cr_linarith S.toOCR [l', h0]
  have q := le_mul_right S.toOH z' (hp_nonneg S.toOH d.e)
  exact S.le_respects (S.refl _) (S.zero_mul _) q

/-- `|d|` bounds `d` both ways, and is non-negative. -/
theorem dabs_sound (d : D) : S.le S.zero (dv S.toOH (dabs d)) ∧
    S.le (S.neg (dv S.toOH (dabs d))) (dv S.toOH d) ∧ S.le (dv S.toOH d) (dv S.toOH (dabs d)) := by
  unfold dabs
  cases h : isNeg d with
  | true =>
      have n := dv_nonpos_of S h
      have e := dv_neg S.toOH d
      refine ⟨S.le_respects (S.refl _) (S.symm e) (by cr_linarith S.toOCR [n]),
        S.le_respects (S.neg_congr (S.symm e)) (S.refl _) (by cr_linarith S.toOCR [n]),
        S.le_respects (S.refl _) (S.symm e) (by cr_linarith S.toOCR [n])⟩
  | false =>
      have n := dv_nonneg_of S h
      show S.le S.zero (dv S.toOH d) ∧ S.le (S.neg (dv S.toOH d)) (dv S.toOH d) ∧ S.le (dv S.toOH d) (dv S.toOH d)
      exact ⟨n, by cr_linarith S.toOCR [n], S.le_refl _⟩

/-! ## Bounds -/

/-- `|a| ≤ A`, `|x| ≤ R` (as two inequalities each): `|a·x| ≤ A·R` — the corners of `[−A, A] × [−R, R]`. -/
theorem abs_mul_bound {a x A R : α} (ha1 : S.le (S.neg A) a) (ha2 : S.le a A) (hx1 : S.le (S.neg R) x)
    (hx2 : S.le x R) : S.le (S.neg (S.mul A R)) (S.mul a x) ∧ S.le (S.mul a x) (S.mul A R) := by
  have hA : S.le S.zero A := by cr_linarith S.toOCR [ha1, ha2]
  have hR : S.le S.zero R := by cr_linarith S.toOCR [hx1, hx2]
  have p0 := S.mul_nonneg hA hR
  constructor
  · exact mul_lower S ha1 ha2 hx1 hx2 (by cr_linarith S.toOCR [p0]) (by cr_linarith S.toOCR [p0])
      (by cr_linarith S.toOCR [p0]) (by cr_linarith S.toOCR [p0])
  · exact mul_upper S ha1 ha2 hx1 hx2 (by cr_linarith S.toOCR [p0]) (by cr_linarith S.toOCR [p0])
      (by cr_linarith S.toOCR [p0]) (by cr_linarith S.toOCR [p0])

def zeroD : D := ⟨⟨0, 0⟩, 0⟩
def oneD : D := ⟨⟨1, 0⟩, 0⟩

theorem dv_zeroD : S.r (dv S.toOH zeroD) S.zero := by
  show S.r (S.mul (S.add S.zero (S.neg S.zero)) S.one) S.zero; cr_ring S.toCR
theorem dv_oneD : S.r (dv S.toOH oneD) S.one := by
  show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) S.one; cr_ring S.toCR

/-- `Σ |sᵢ|·rᵢ` over the box (none if a variable has no interval). -/
def radL (B : Box) : List (Nat × D) → Option D
  | [] => some zeroD
  | (i, s) :: L => match B i with
      | none => none
      | some I => match radL B L with
          | none => none
          | some R => some (dadd (dmul (dabs s) (rad I)) R)

theorem midv_some {B : Box} {p : Nat → α} {i : Nat} {I : Iv} (h : B i = some I) :
    midv S B p i = S.add (p i) (S.neg (dv S.toOH (mid I))) := by unfold midv; rw [h]

theorem lin_bound {B : Box} {p : Nat → α} (hp : InBox S B p) :
    ∀ (L : List (Nat × D)) (R : D), radL B L = some R →
      S.le (S.neg (dv S.toOH R)) (linv S B p L) ∧ S.le (linv S B p L) (dv S.toOH R)
  | [], R, h => by
      cases h
      have z := dv_zeroD S
      exact ⟨S.le_respects (S.trans S.neg_zero (S.symm z) |> S.symm |> fun e => S.symm (S.trans (S.neg_congr z) S.neg_zero)) (S.refl _) (S.le_refl _),
        S.le_respects (S.refl _) (S.symm z) (S.le_refl _)⟩
  | (i, s) :: L, R, h => by
      unfold radL at h
      cases hB : B i with
      | none => rw [hB] at h; cases h
      | some I =>
          rw [hB] at h
          cases hR : radL B L with
          | none => rw [hR] at h; cases h
          | some R' =>
              rw [hR] at h
              cases h
              have ih := lin_bound hp L R' hR
              have nm := near_mid S hp hB
              have ab := dabs_sound S s
              have t := abs_mul_bound S ab.2.1 ab.2.2 nm.1 nm.2
              have e1 := S.trans (dv_add S.toOH (dmul (dabs s) (rad I)) R') (S.add_congr (dv_mul S.toOH _ _) (S.refl _))
              show S.le (S.neg (dv S.toOH (dadd (dmul (dabs s) (rad I)) R'))) (S.add (S.mul (dv S.toOH s) (midv S B p i)) (linv S B p L)) ∧
                S.le (S.add (S.mul (dv S.toOH s) (midv S B p i)) (linv S B p L)) (dv S.toOH (dadd (dmul (dabs s) (rad I)) R'))
              rw [midv_some S hB]
              constructor
              · refine S.le_respects (S.neg_congr (S.symm e1)) (S.refl _) ?_
                cr_linarith S.toOCR [t.1, ih.1]
              · refine S.le_respects (S.refl _) (S.symm e1) ?_
                cr_linarith S.toOCR [t.2, ih.2]

/-! ## Forms: the operations -/

def afVar (B : Box) (i : Nat) : Option AF :=
  match B i with
  | some I => some ⟨mid I, [(i, oneD)], zeroD⟩
  | none => none

def afCst (c : D) : AF := ⟨c, [], zeroD⟩
def afAdd (F G : AF) : AF := ⟨dadd F.c G.c, addL F.L G.L, dadd F.e G.e⟩
def afSub (F G : AF) : AF := ⟨dadd F.c (dneg G.c), addL F.L (negL G.L), dadd F.e G.e⟩

def afMul (B : Box) (F G : AF) : Option AF :=
  match radL B F.L with
  | none => none
  | some R1 => match radL B G.L with
      | none => none
      | some R2 => some ⟨dmul F.c G.c, addL (scaleL F.c G.L) (scaleL G.c F.L),
          dadd (dadd (dmul (dabs F.c) G.e) (dmul (dabs G.c) F.e)) (dmul (dadd R1 F.e) (dadd R2 G.e))⟩

/-- Rounding of the constant and the error (the shift goes into the error). -/
def afRnd (F : AF) : AF :=
  let c' := rdn F.c
  ⟨c', F.L, rup (dadd F.e (dabs (dadd F.c (dneg c'))))⟩

/-- The interval of a form: `[c − R − e, c + R + e]`, rounded outward. -/
def afIv (B : Box) (F : AF) : Option Iv :=
  match radL B F.L with
  | none => none
  | some R => some (rdn (dadd F.c (dneg (dadd R F.e))), rup (dadd F.c (dadd R F.e)))

def bind2 (f : AF → AF → Option AF) : Option AF → Option AF → Option AF
  | none, _ => none
  | some _, none => none
  | some a, some b => f a b

def afPow (B : Box) (F : AF) : Nat → Option AF
  | 0 => some (afCst oneD)
  | n + 1 => match afPow B F n with
      | none => none
      | some G => (afMul B F G).map afRnd

/-- The kernel's affine reading of an expression over a box. -/
def afE (B : Box) : PE → Option AF
  | .var i => afVar B i
  | .cst c => some (afCst c)
  | .add p q => bind2 (fun a b => some (afAdd a b)) (afE B p) (afE B q)
  | .sub p q => bind2 (fun a b => some (afSub a b)) (afE B p) (afE B q)
  | .mul p q => (bind2 (afMul B) (afE B p) (afE B q)).map afRnd
  | .pow p n => match afE B p with
      | none => none
      | some F => afPow B F n

/-! ## Soundness of the operations -/

theorem enc_var {B : Box} {p : Nat → α} {i : Nat} {I : Iv} (h : B i = some I) :
    Enc S B p (p i) ⟨mid I, [(i, oneD)], zeroD⟩ := by
  have z := dv_zeroD S
  have o := dv_oneD S
  have hl : S.r (linv S B p [(i, oneD)]) (S.add (S.mul (dv S.toOH oneD) (S.add (p i) (S.neg (dv S.toOH (mid I))))) S.zero) := by
    show S.r (S.add (S.mul (dv S.toOH oneD) (midv S B p i)) S.zero) _
    rw [midv_some S h]; exact S.refl _
  have e : S.r (S.add (p i) (S.neg (S.add (dv S.toOH (mid I)) (linv S B p [(i, oneD)])))) S.zero := by
    refine S.trans (S.add_congr (S.refl _) (S.neg_congr (S.add_congr (S.refl _) (S.trans hl
      (S.add_congr (S.mul_congr o (S.refl _)) (S.refl _)))))) ?_
    cr_ring S.toCR
  exact ⟨S.le_respects (S.symm (S.trans (S.neg_congr z) S.neg_zero)) (S.symm e) (S.le_refl _),
    S.le_respects (S.symm e) (S.symm z) (S.le_refl _)⟩

theorem enc_cst (B : Box) (p : Nat → α) (c : D) : Enc S B p (dv S.toOH c) (afCst c) := by
  have z := dv_zeroD S
  have e : S.r (S.add (dv S.toOH c) (S.neg (S.add (dv S.toOH c) S.zero))) S.zero := by cr_ring S.toCR
  exact ⟨S.le_respects (S.symm (S.trans (S.neg_congr z) S.neg_zero)) (S.symm e) (S.le_refl _),
    S.le_respects (S.symm e) (S.symm z) (S.le_refl _)⟩

theorem enc_add {B : Box} {p : Nat → α} {v w : α} {F G : AF} (hv : Enc S B p v F) (hw : Enc S B p w G) :
    Enc S B p (S.add v w) (afAdd F G) := by
  have l := addL_sound S B p F.L G.L
  have c := dv_add S.toOH F.c G.c
  have e := dv_add S.toOH F.e G.e
  unfold Enc at *
  show S.le (S.neg (dv S.toOH (dadd F.e G.e))) (S.add (S.add v w) (S.neg (S.add (dv S.toOH (dadd F.c G.c)) (linv S B p (addL F.L G.L))))) ∧
    S.le (S.add (S.add v w) (S.neg (S.add (dv S.toOH (dadd F.c G.c)) (linv S B p (addL F.L G.L))))) (dv S.toOH (dadd F.e G.e))
  have k : S.r (S.add (S.add v w) (S.neg (S.add (dv S.toOH (dadd F.c G.c)) (linv S B p (addL F.L G.L)))))
      (S.add (S.add v (S.neg (S.add (dv S.toOH F.c) (linv S B p F.L)))) (S.add w (S.neg (S.add (dv S.toOH G.c) (linv S B p G.L))))) := by
    refine S.trans (S.add_congr (S.refl _) (S.neg_congr (S.add_congr c l))) ?_
    cr_ring S.toCR
  exact ⟨S.le_respects (S.neg_congr (S.symm e)) (S.symm k) (by cr_linarith S.toOCR [hv.1, hw.1]),
    S.le_respects (S.symm k) (S.symm e) (by cr_linarith S.toOCR [hv.2, hw.2])⟩

theorem enc_sub {B : Box} {p : Nat → α} {v w : α} {F G : AF} (hv : Enc S B p v F) (hw : Enc S B p w G) :
    Enc S B p (S.add v (S.neg w)) (afSub F G) := by
  have l := S.trans (addL_sound S B p F.L (negL G.L)) (S.add_congr (S.refl _) (negL_sound S B p G.L))
  have c := S.trans (dv_add S.toOH F.c (dneg G.c)) (S.add_congr (S.refl _) (dv_neg S.toOH G.c))
  have e := dv_add S.toOH F.e G.e
  unfold Enc at *
  show S.le (S.neg (dv S.toOH (dadd F.e G.e))) (S.add (S.add v (S.neg w)) (S.neg (S.add (dv S.toOH (dadd F.c (dneg G.c))) (linv S B p (addL F.L (negL G.L)))))) ∧
    S.le (S.add (S.add v (S.neg w)) (S.neg (S.add (dv S.toOH (dadd F.c (dneg G.c))) (linv S B p (addL F.L (negL G.L)))))) (dv S.toOH (dadd F.e G.e))
  have k : S.r (S.add (S.add v (S.neg w)) (S.neg (S.add (dv S.toOH (dadd F.c (dneg G.c))) (linv S B p (addL F.L (negL G.L))))))
      (S.add (S.add v (S.neg (S.add (dv S.toOH F.c) (linv S B p F.L)))) (S.neg (S.add w (S.neg (S.add (dv S.toOH G.c) (linv S B p G.L)))))) := by
    refine S.trans (S.add_congr (S.refl _) (S.neg_congr (S.add_congr c l))) ?_
    cr_ring S.toCR
  exact ⟨S.le_respects (S.neg_congr (S.symm e)) (S.symm k) (by cr_linarith S.toOCR [hv.1, hw.2]),
    S.le_respects (S.symm k) (S.symm e) (by cr_linarith S.toOCR [hv.2, hw.1])⟩

theorem enc_mul {B : Box} {p : Nat → α} (hp : InBox S B p) {v w : α} {F G H : AF}
    (hv : Enc S B p v F) (hw : Enc S B p w G) (h : afMul B F G = some H) : Enc S B p (S.mul v w) H := by
  unfold afMul at h
  cases h1 : radL B F.L with
  | none => rw [h1] at h; cases h
  | some R1 =>
      rw [h1] at h
      cases h2 : radL B G.L with
      | none => rw [h2] at h; cases h
      | some R2 =>
          rw [h2] at h
          cases h
          have b1 := lin_bound S hp F.L R1 h1
          have b2 := lin_bound S hp G.L R2 h2
          have a1 := dabs_sound S F.c
          have a2 := dabs_sound S G.c
          unfold Enc at hv hw
          -- the three remainders
          have t1 := abs_mul_bound S a1.2.1 a1.2.2 hw.1 hw.2
          have t2 := abs_mul_bound S a2.2.1 a2.2.2 hv.1 hv.2
          have x1a : S.le (S.neg (S.add (dv S.toOH R1) (dv S.toOH F.e))) (S.add v (S.neg (dv S.toOH F.c))) := by
            cr_linarith S.toOCR [b1.1, hv.1]
          have x1b : S.le (S.add v (S.neg (dv S.toOH F.c))) (S.add (dv S.toOH R1) (dv S.toOH F.e)) := by
            cr_linarith S.toOCR [b1.2, hv.2]
          have x2a : S.le (S.neg (S.add (dv S.toOH R2) (dv S.toOH G.e))) (S.add w (S.neg (dv S.toOH G.c))) := by
            cr_linarith S.toOCR [b2.1, hw.1]
          have x2b : S.le (S.add w (S.neg (dv S.toOH G.c))) (S.add (dv S.toOH R2) (dv S.toOH G.e)) := by
            cr_linarith S.toOCR [b2.2, hw.2]
          have t3 := abs_mul_bound S x1a x1b x2a x2b
          -- the new constant, linear part and error, read
          have ec := dv_mul S.toOH F.c G.c
          have el := S.trans (addL_sound S B p (scaleL F.c G.L) (scaleL G.c F.L))
            (S.add_congr (scaleL_sound S B p F.c G.L) (scaleL_sound S B p G.c F.L))
          have ee : S.r (dv S.toOH (dadd (dadd (dmul (dabs F.c) G.e) (dmul (dabs G.c) F.e)) (dmul (dadd R1 F.e) (dadd R2 G.e))))
              (S.add (S.add (S.mul (dv S.toOH (dabs F.c)) (dv S.toOH G.e)) (S.mul (dv S.toOH (dabs G.c)) (dv S.toOH F.e)))
                (S.mul (S.add (dv S.toOH R1) (dv S.toOH F.e)) (S.add (dv S.toOH R2) (dv S.toOH G.e)))) :=
            S.trans (dv_add S.toOH _ _) (S.add_congr (S.trans (dv_add S.toOH _ _) (S.add_congr (dv_mul S.toOH _ _) (dv_mul S.toOH _ _)))
              (S.trans (dv_mul S.toOH _ _) (S.mul_congr (dv_add S.toOH _ _) (dv_add S.toOH _ _))))
          show S.le (S.neg (dv S.toOH _)) (S.add (S.mul v w) (S.neg (S.add (dv S.toOH (dmul F.c G.c)) (linv S B p (addL (scaleL F.c G.L) (scaleL G.c F.L)))))) ∧
            S.le (S.add (S.mul v w) (S.neg (S.add (dv S.toOH (dmul F.c G.c)) (linv S B p (addL (scaleL F.c G.L) (scaleL G.c F.L)))))) (dv S.toOH _)
          have k : S.r (S.add (S.mul v w) (S.neg (S.add (dv S.toOH (dmul F.c G.c)) (linv S B p (addL (scaleL F.c G.L) (scaleL G.c F.L))))))
              (S.add (S.mul v w) (S.neg (S.add (S.mul (dv S.toOH F.c) (dv S.toOH G.c))
                (S.add (S.mul (dv S.toOH F.c) (linv S B p G.L)) (S.mul (dv S.toOH G.c) (linv S B p F.L)))))) :=
            S.add_congr (S.refl _) (S.neg_congr (S.add_congr ec el))
          constructor
          · refine S.le_respects (S.neg_congr (S.symm ee)) (S.symm k) ?_
            cr_linarith S.toOCR [t1.1, t2.1, t3.1]
          · refine S.le_respects (S.symm k) (S.symm ee) ?_
            cr_linarith S.toOCR [t1.2, t2.2, t3.2]

theorem enc_rnd {B : Box} {p : Nat → α} {v : α} {F : AF} (hv : Enc S B p v F) : Enc S B p v (afRnd F) := by
  unfold Enc at *
  have a := dabs_sound S (dadd F.c (dneg (rdn F.c)))
  have d := S.trans (dv_add S.toOH F.c (dneg (rdn F.c))) (S.add_congr (S.refl _) (dv_neg S.toOH (rdn F.c)))
  have u := le_rup S.toOH (dadd F.e (dabs (dadd F.c (dneg (rdn F.c)))))
  have ue := dv_add S.toOH F.e (dabs (dadd F.c (dneg (rdn F.c))))
  have u' := S.le_respects ue (S.refl _) u
  have a1 := S.le_respects (S.neg_congr (S.refl _)) d a.2.1
  have a2 := S.le_respects d (S.refl _) a.2.2
  show S.le (S.neg (dv S.toOH (rup (dadd F.e (dabs (dadd F.c (dneg (rdn F.c)))))))) (S.add v (S.neg (S.add (dv S.toOH (rdn F.c)) (linv S B p F.L)))) ∧
    S.le (S.add v (S.neg (S.add (dv S.toOH (rdn F.c)) (linv S B p F.L)))) (dv S.toOH (rup (dadd F.e (dabs (dadd F.c (dneg (rdn F.c)))))))
  constructor
  · cr_linarith S.toOCR [hv.1, a1, a2, u']
  · cr_linarith S.toOCR [hv.2, a1, a2, u']

theorem afIv_sound {B : Box} {p : Nat → α} (hp : InBox S B p) {v : α} {F : AF} {K : Iv}
    (hv : Enc S B p v F) (h : afIv B F = some K) : Mem S v K := by
  unfold afIv at h
  cases hR : radL B F.L with
  | none => rw [hR] at h; cases h
  | some R =>
      rw [hR] at h
      cases h
      have b := lin_bound S hp F.L R hR
      unfold Enc at hv
      have l := rdn_le S.toOH (dadd F.c (dneg (dadd R F.e)))
      have u := le_rup S.toOH (dadd F.c (dadd R F.e))
      have el := S.trans (dv_add S.toOH F.c (dneg (dadd R F.e)))
        (S.add_congr (S.refl _) (S.trans (dv_neg S.toOH _) (S.neg_congr (dv_add S.toOH R F.e))))
      have eu := S.trans (dv_add S.toOH F.c (dadd R F.e)) (S.add_congr (S.refl _) (dv_add S.toOH R F.e))
      have l' := S.le_respects (S.refl _) el l
      have u' := S.le_respects eu (S.refl _) u
      exact ⟨by cr_linarith S.toOCR [l', b.1, hv.1], by cr_linarith S.toOCR [u', b.2, hv.2]⟩

theorem bind2_some {f : AF → AF → Option AF} {a b : Option AF} {H : AF} (h : bind2 f a b = some H) :
    ∃ x y, a = some x ∧ b = some y ∧ f x y = some H := by
  cases a with
  | none => cases h
  | some x =>
      cases b with
      | none => cases h
      | some y => exact ⟨x, y, rfl, rfl, h⟩

theorem map_some {o : Option AF} {H : AF} (h : o.map afRnd = some H) : ∃ x, o = some x ∧ afRnd x = H := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, Option.some.inj h⟩

theorem afPow_sound {B : Box} {p : Nat → α} (hp : InBox S B p) {v : α} {F : AF} (hv : Enc S B p v F) :
    ∀ n H, afPow B F n = some H → Enc S B p (powS S.toOH v n) H
  | 0, H, h => by
      cases h
      have e := dv_oneD S
      have c := enc_cst S B p oneD
      unfold Enc at c ⊢
      exact ⟨S.le_respects (S.refl _) (S.add_congr e (S.refl _)) c.1, S.le_respects (S.add_congr e (S.refl _)) (S.refl _) c.2⟩
  | n + 1, H, h => by
      unfold afPow at h
      cases hn : afPow B F n with
      | none => rw [hn] at h; cases h
      | some G =>
          rw [hn] at h
          obtain ⟨M, hM, hr⟩ := map_some h
          cases hr
          exact enc_rnd S (enc_mul S hp hv (afPow_sound hp hv n G hn) hM)

/-- **THE AFFINE READING ENCLOSES THE VALUE**, at every point of the box, in every `CF`. -/
theorem afE_sound {B : Box} {p : Nat → α} (hp : InBox S B p) :
    ∀ (e : PE) (F : AF), afE B e = some F → Enc S B p (eval S.toOH p e) F
  | .var i, F, h => by
      unfold afE afVar at h
      cases hB : B i with
      | none => rw [hB] at h; cases h
      | some I => rw [hB] at h; cases h; exact enc_var S hB
  | .cst c, F, h => by cases h; exact enc_cst S B p c
  | .add a b, F, h => by
      obtain ⟨x, y, ex, ey, hk⟩ := bind2_some h
      cases hk; exact enc_add S (afE_sound hp a x ex) (afE_sound hp b y ey)
  | .sub a b, F, h => by
      obtain ⟨x, y, ex, ey, hk⟩ := bind2_some h
      cases hk; exact enc_sub S (afE_sound hp a x ex) (afE_sound hp b y ey)
  | .mul a b, F, h => by
      obtain ⟨M, hM, hr⟩ := map_some h
      obtain ⟨x, y, ex, ey, hk⟩ := bind2_some hM
      cases hr
      exact enc_rnd S (enc_mul S hp (afE_sound hp a x ex) (afE_sound hp b y ey) hk)
  | .pow a n, F, h => by
      unfold afE at h
      cases ha : afE B a with
      | none => rw [ha] at h; cases h
      | some G => rw [ha] at h; exact afPow_sound S hp (afE_sound hp a G ha) n F h

/-- The affine reading as an interval. -/
def afIvE (B : Box) (e : PE) : Option Iv :=
  match afE B e with
  | none => none
  | some F => afIv B F

theorem afIvE_sound {B : Box} {p : Nat → α} (hp : InBox S B p) (e : PE) (K : Iv) (h : afIvE B e = some K) :
    Mem S (eval S.toOH p e) K := by
  unfold afIvE at h
  cases hF : afE B e with
  | none => rw [hF] at h; cases h
  | some F => rw [hF] at h; exact afIv_sound S hp (afE_sound S hp e F hF) h

end ZAff
