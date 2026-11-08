import ZPoly
/-!
# ZKron — a polynomial identity decided by ONE exact integer evaluation (Kronecker). Zero axioms.

The symbolic normal form of `ZPoly.ident` is exact but, in the kernel, expensive: MEASURED 2026-11-08 on a KS-23
chart identity `E(φ) = r⁸·G` — 59 s and a 14.5 GB peak. Here the same question is decided by evaluating the
expression at one integer point, in the kernel's big-number arithmetic: 1 s, flat memory, same identity.

THE TEST (`kron`). All constants integers (`e = 0`), variables below `n`. Points `B₀, B₁, …, B_{n−1}`: `Bᵢ` is
one more than the ABSOLUTE evaluation `|e|` (every constant by its absolute value, `−` read as `+`) at
`(B₀, …, B_{i−1}, 1, …, 1)`. The test: `e(B₀, …, B_{n−1}) = 0` as an integer.

WHY IT IS SOUND (`kron_sound`): `e` is a polynomial in its last variable `x_{n−1}` with coefficients `q_j` in the
others (`cl` — used only in the proof, never computed). At the point, `e = Σ_j q_j(B_<)·B_{n−1}^j`, and every
`|q_j(B_<)| ≤ |e|(B_<, 1) < B_{n−1}`. An integer combination `Σ c_j·Bʲ = 0` with every `|c_j| < B` has every
`c_j = 0` (`digits`): `c₀ = −B·(rest)`, and `rest ≠ 0` would make `|c₀| ≥ B`. So every `q_j` vanishes at
`B_<`, and by induction on `n` (the same bounds hold for the `q_j`) every `q_j` vanishes EVERYWHERE — in every
ordered ring `OH` — and so does `e`.
-/

namespace ZKron
open VR.CSR ZNumBin ZPoly

/-! ## The test (computed) -/

/-- Constants are integers and variables are below `n`. -/
def gd (n : Nat) : PE → Bool
  | .var i => Nat.blt i n
  | .cst c => Nat.beq c.e 0
  | .add p q => gd n p && gd n q
  | .sub p q => gd n p && gd n q
  | .mul p q => gd n p && gd n q
  | .pow p _ => gd n p

/-- The absolute evaluation: constants by their absolute value, `−` as `+`. -/
def evA (y : Nat → Nat) : PE → Nat
  | .var i => y i
  | .cst c => c.m.p + c.m.n
  | .add p q => evA y p + evA y q
  | .sub p q => evA y p + evA y q
  | .mul p q => evA y p * evA y q
  | .pow p k => evA y p ^ k

def zpw (z : BZ) : Nat → BZ
  | 0 => ⟨1, 0⟩
  | k + 1 => znorm (zmul z (zpw z k))

/-- The integer evaluation (signed binary, normalised after each step). -/
def evZ (x : Nat → BZ) : PE → BZ
  | .var i => x i
  | .cst c => c.m
  | .add p q => znorm (zadd (evZ x p) (evZ x q))
  | .sub p q => znorm (zadd (evZ x p) (zneg (evZ x q)))
  | .mul p q => znorm (zmul (evZ x p) (evZ x q))
  | .pow p k => zpw (evZ x p) k

/-- The points: after `i` steps, `B₀ … B_{i−1}` set, the rest `1`. -/
def pt (e : PE) : Nat → Nat → Nat
  | 0 => fun _ => 1
  | i + 1 => fun j => cond (Nat.beq j i) (evA (pt e i) e + 1) (pt e i j)

def kron (n : Nat) (e : PE) : Bool :=
  gd n e && (let z := evZ (fun j => zofNat (pt e n j)) e; Nat.beq z.p z.n)

/-! ## Coefficients in one variable (proof only) -/

def czero : PE := .cst ⟨⟨0, 0⟩, 0⟩
def cone : PE := .cst ⟨⟨1, 0⟩, 0⟩
def pneg (a : PE) : PE := .sub czero a

def lzip : List PE → List PE → List PE
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => .add a b :: lzip p q

def lneg : List PE → List PE
  | [] => []
  | a :: p => pneg a :: lneg p

def lsc (a : PE) : List PE → List PE
  | [] => []
  | b :: q => .mul a b :: lsc a q

def conv : List PE → List PE → List PE
  | [], _ => []
  | a :: p, q => lzip (lsc a q) (czero :: conv p q)

def lpow (l : List PE) : Nat → List PE
  | 0 => [cone]
  | k + 1 => conv l (lpow l k)

/-- The coefficients of `e` as a polynomial in `x_v`, lowest first. -/
def cl (v : Nat) : PE → List PE
  | .var i => cond (Nat.beq i v) [czero, cone] [.var i]
  | .cst c => [.cst c]
  | .add p q => lzip (cl v p) (cl v q)
  | .sub p q => lzip (cl v p) (lneg (cl v q))
  | .mul p q => conv (cl v p) (cl v q)
  | .pow p k => lpow (cl v p) k

variable {α : Type} (S : OH α)

/-- `Σ_j eval(l_j)·xʲ`, by Horner. -/
def hv (env : Nat → α) (x : α) : List PE → α
  | [] => S.zero
  | a :: l => S.add (eval S env a) (S.mul x (hv env x l))

theorem dv_czero : S.r (dv S ⟨⟨0, 0⟩, 0⟩) S.zero := by
  show S.r (S.mul (S.add S.zero (S.neg S.zero)) S.one) S.zero
  cr_ring S.toCR

theorem dv_cone : S.r (dv S ⟨⟨1, 0⟩, 0⟩) S.one := by
  show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) S.one
  cr_ring S.toCR

section
variable (env : Nat → α) (x : α)

theorem hv_lzip : ∀ p q : List PE, S.r (hv S env x (lzip p q)) (S.add (hv S env x p) (hv S env x q))
  | [], q => by show S.r (hv S env x q) (S.add S.zero (hv S env x q)); cr_ring S.toCR
  | a :: p, [] => by
      show S.r (hv S env x (a :: p)) (S.add (hv S env x (a :: p)) S.zero); cr_ring S.toCR
  | a :: p, b :: q => by
      have ih := hv_lzip p q
      show S.r (S.add (S.add (eval S env a) (eval S env b)) (S.mul x (hv S env x (lzip p q))))
        (S.add (S.add (eval S env a) (S.mul x (hv S env x p))) (S.add (eval S env b) (S.mul x (hv S env x q))))
      exact S.trans (S.add_congr (S.refl _) (S.mul_congr (S.refl _) ih)) (by cr_ring S.toCR)

theorem hv_lneg : ∀ q : List PE, S.r (hv S env x (lneg q)) (S.neg (hv S env x q))
  | [] => by show S.r S.zero (S.neg S.zero); cr_ring S.toCR
  | a :: q => by
      have ih := hv_lneg q
      have z := dv_czero S
      show S.r (S.add (S.add (dv S ⟨⟨0, 0⟩, 0⟩) (S.neg (eval S env a))) (S.mul x (hv S env x (lneg q))))
        (S.neg (S.add (eval S env a) (S.mul x (hv S env x q))))
      exact S.trans (S.add_congr (S.add_congr z (S.refl _)) (S.mul_congr (S.refl _) ih)) (by cr_ring S.toCR)

theorem hv_lsc (a : PE) : ∀ q : List PE, S.r (hv S env x (lsc a q)) (S.mul (eval S env a) (hv S env x q))
  | [] => by show S.r S.zero (S.mul (eval S env a) S.zero); cr_ring S.toCR
  | b :: q => by
      have ih := hv_lsc a q
      show S.r (S.add (S.mul (eval S env a) (eval S env b)) (S.mul x (hv S env x (lsc a q))))
        (S.mul (eval S env a) (S.add (eval S env b) (S.mul x (hv S env x q))))
      exact S.trans (S.add_congr (S.refl _) (S.mul_congr (S.refl _) ih)) (by cr_ring S.toCR)

theorem hv_conv : ∀ p q : List PE, S.r (hv S env x (conv p q)) (S.mul (hv S env x p) (hv S env x q))
  | [], q => by show S.r S.zero (S.mul S.zero (hv S env x q)); cr_ring S.toCR
  | a :: p, q => by
      have ih := hv_conv p q
      have l1 := hv_lzip S env x (lsc a q) (czero :: conv p q)
      have l2 := hv_lsc S env x a q
      have z := dv_czero S
      have e3 : S.r (hv S env x (czero :: conv p q))
          (S.add (dv S ⟨⟨0, 0⟩, 0⟩) (S.mul x (hv S env x (conv p q)))) := S.refl _
      show S.r (hv S env x (lzip (lsc a q) (czero :: conv p q)))
        (S.mul (S.add (eval S env a) (S.mul x (hv S env x p))) (hv S env x q))
      refine S.trans l1 (S.trans (S.add_congr l2 (S.trans e3 (S.add_congr z (S.mul_congr (S.refl _) ih)))) ?_)
      cr_ring S.toCR

theorem hv_lpow (l : List PE) : ∀ k, S.r (hv S env x (lpow l k)) (powS S (hv S env x l) k)
  | 0 => by
      have o := dv_cone S
      show S.r (S.add (dv S ⟨⟨1, 0⟩, 0⟩) (S.mul x S.zero)) S.one
      exact S.trans (S.add_congr o (S.refl _)) (by cr_ring S.toCR)
  | k + 1 => S.trans (hv_conv S env x l (lpow l k)) (S.mul_congr (S.refl _) (hv_lpow l k))

/-- THE DECOMPOSITION: `e = Σ_j q_j · x_vʲ`, at every point, in every `OH`. -/
theorem eval_cl (v : Nat) : ∀ e : PE, S.r (eval S env e) (hv S env (env v) (cl v e))
  | .var i => by
      show S.r (env i) (hv S env (env v) (cond (Nat.beq i v) [czero, cone] [.var i]))
      cases h : Nat.beq i v with
      | true =>
          have e := Nat.eq_of_beq_eq_true h
          subst e
          have z := dv_czero S
          have o := dv_cone S
          show S.r (env i) (S.add (dv S ⟨⟨0, 0⟩, 0⟩) (S.mul (env i) (S.add (dv S ⟨⟨1, 0⟩, 0⟩) (S.mul (env i) S.zero))))
          refine S.trans ?_ (S.symm (S.add_congr z (S.mul_congr (S.refl _) (S.add_congr o (S.refl _)))))
          cr_ring S.toCR
      | false =>
          show S.r (env i) (S.add (env i) (S.mul (env v) S.zero))
          cr_ring S.toCR
  | .cst c => by
      show S.r (dv S c) (S.add (dv S c) (S.mul (env v) S.zero))
      cr_ring S.toCR
  | .add p q => S.trans (S.add_congr (eval_cl v p) (eval_cl v q)) (S.symm (hv_lzip S env _ _ _))
  | .sub p q => S.trans (S.add_congr (eval_cl v p) (S.neg_congr (eval_cl v q)))
      (S.symm (S.trans (hv_lzip S env _ _ _) (S.add_congr (S.refl _) (hv_lneg S env _ _))))
  | .mul p q => S.trans (S.mul_congr (eval_cl v p) (eval_cl v q)) (S.symm (hv_conv S env _ _ _))
  | .pow p k => S.trans (powS_congr S (eval_cl v p) k) (S.symm (hv_lpow S env _ _ k))

end


/-! ## The integer evaluation is the evaluation -/

theorem zv_zpw (z : BZ) : ∀ k, S.r (zv S (zpw z k)) (powS S (zv S z) k)
  | 0 => by
      show S.r (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one
      cr_ring S.toCR
  | k + 1 => S.trans (zv_norm S _) (S.trans (zv_mul S _ _) (S.mul_congr (S.refl _) (zv_zpw z k)))

theorem gd_and {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := and_true_split h

theorem evZ_sound (n : Nat) (x : Nat → BZ) : ∀ e : PE, gd n e = true →
    S.r (zv S (evZ x e)) (eval S (fun i => zv S (x i)) e)
  | .var _, _ => S.refl _
  | .cst c, h => by
      have h0 : c.e = 0 := Nat.eq_of_beq_eq_true h
      show S.r (zv S c.m) (S.mul (zv S c.m) (hp S c.e))
      rw [h0]
      show S.r (zv S c.m) (S.mul (zv S c.m) S.one)
      cr_ring S.toCR
  | .add p q, h => by
      obtain ⟨hp', hq⟩ := gd_and h
      exact S.trans (zv_norm S _) (S.trans (zv_add S _ _) (S.add_congr (evZ_sound n x p hp') (evZ_sound n x q hq)))
  | .sub p q, h => by
      obtain ⟨hp', hq⟩ := gd_and h
      exact S.trans (zv_norm S _) (S.trans (zv_add S _ _)
        (S.add_congr (evZ_sound n x p hp') (S.trans (zv_neg S _) (S.neg_congr (evZ_sound n x q hq)))))
  | .mul p q, h => by
      obtain ⟨hp', hq⟩ := gd_and h
      exact S.trans (zv_norm S _) (S.trans (zv_mul S _ _) (S.mul_congr (evZ_sound n x p hp') (evZ_sound n x q hq)))
  | .pow p k, h => S.trans (zv_zpw S _ k) (powS_congr S (evZ_sound n x p h) k)

/-! ## Bounds: `|e(x)| ≤ |e|(y)` when `|xᵢ| ≤ yᵢ` -/

def Bd (a A : α) : Prop := S.le (S.neg A) a ∧ S.le a A

theorem bd_congr {a a' A A' : α} (h1 : S.r a a') (h2 : S.r A A') (h : Bd S a A) : Bd S a' A' :=
  ⟨S.le_respects (S.neg_congr h2) h1 h.1, S.le_respects h1 h2 h.2⟩

theorem bd_add {a b A B : α} (ha : Bd S a A) (hb : Bd S b B) : Bd S (S.add a b) (S.add A B) := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  exact ⟨by cr_linarith S.toOCR [a1, b1], by cr_linarith S.toOCR [a2, b2]⟩

theorem bd_neg {a A : α} (ha : Bd S a A) : Bd S (S.neg a) A := by
  obtain ⟨a1, a2⟩ := ha
  exact ⟨by cr_linarith S.toOCR [a2], by cr_linarith S.toOCR [a1]⟩

theorem bd_mul {a b A B : α} (ha : Bd S a A) (hb : Bd S b B) : Bd S (S.mul a b) (S.mul A B) := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  have u1 := OCR.sub_nonneg_of_le S.toOCR a2
  have u2 := OCR.sub_nonneg_of_le S.toOCR a1
  have v1 := OCR.sub_nonneg_of_le S.toOCR b2
  have v2 := OCR.sub_nonneg_of_le S.toOCR b1
  have p1 := S.mul_nonneg u1 v1
  have p2 := S.mul_nonneg u2 v2
  have p3 := S.mul_nonneg u1 v2
  have p4 := S.mul_nonneg u2 v1
  have l : S.le S.zero (S.mul (S.add S.one (S.add S.one S.zero)) (S.add (S.mul A B) (S.mul a b))) :=
    S.le_respects (S.refl _) (by cr_ring S.toCR) (OCR.nonneg_add S.toOCR p1 p2)
  have r : S.le S.zero (S.mul (S.add S.one (S.add S.one S.zero)) (S.add (S.mul A B) (S.neg (S.mul a b)))) :=
    S.le_respects (S.refl _) (by cr_ring S.toCR) (OCR.nonneg_add S.toOCR p3 p4)
  have l' := S.le_of_smul 1 l
  have r' := S.le_of_smul 1 r
  exact ⟨by cr_linarith S.toOCR [l'], by cr_linarith S.toOCR [r']⟩

theorem bd_pow {a A : α} (ha : Bd S a A) : ∀ k, Bd S (powS S a k) (powS S A k)
  | 0 => by
      show Bd S S.one S.one
      exact ⟨by have := S.zero_le_one; cr_linarith S.toOCR [this], S.le_refl _⟩
  | k + 1 => bd_mul S ha (bd_pow ha k)

theorem nI_pow (a : Nat) : ∀ k, S.r (nI S (a ^ k)) (powS S (nI S a) k)
  | 0 => by show S.r (nI S 1) S.one; show S.r (S.add S.one S.zero) S.one; cr_ring S.toCR
  | k + 1 => by
      show S.r (nI S (a ^ k * a)) (S.mul (nI S a) (powS S (nI S a) k))
      exact S.trans (nI_mul S (a ^ k) a) (S.trans (S.mul_congr (nI_pow a k) (S.refl _)) (by cr_ring S.toCR))

theorem lt_of_blt {i n : Nat} (h : Nat.blt i n = true) : i < n := Nat.le_of_ble_eq_true h

theorem eval_bd (n : Nat) (env : Nat → α) (y : Nat → Nat) (hy : ∀ i, i < n → Bd S (env i) (nI S (y i))) :
    ∀ e : PE, gd n e = true → Bd S (eval S env e) (nI S (evA y e))
  | .var i, h => hy i (lt_of_blt h)
  | .cst c, h => by
      have h0 : c.e = 0 := Nat.eq_of_beq_eq_true h
      have e1 := nI_add S c.m.p c.m.n
      have q1 := nI_nonneg S c.m.p
      have q2 := nI_nonneg S c.m.n
      show Bd S (S.mul (zv S c.m) (hp S c.e)) (nI S (c.m.p + c.m.n))
      rw [h0]
      show Bd S (S.mul (S.add (nI S c.m.p) (S.neg (nI S c.m.n))) S.one) (nI S (c.m.p + c.m.n))
      exact ⟨by cr_linarith S.toOCR [e1, q1, q2], by cr_linarith S.toOCR [e1, q1, q2]⟩
  | .add p q, h => by
      obtain ⟨hp', hq⟩ := gd_and h
      exact bd_congr S (S.refl _) (S.symm (nI_add S _ _)) (bd_add S (eval_bd n env y hy p hp') (eval_bd n env y hy q hq))
  | .sub p q, h => by
      obtain ⟨hp', hq⟩ := gd_and h
      exact bd_congr S (S.refl _) (S.symm (nI_add S _ _))
        (bd_add S (eval_bd n env y hy p hp') (bd_neg S (eval_bd n env y hy q hq)))
  | .mul p q, h => by
      obtain ⟨hp', hq⟩ := gd_and h
      exact bd_congr S (S.refl _) (S.symm (nI_mul S _ _)) (bd_mul S (eval_bd n env y hy p hp') (eval_bd n env y hy q hq))
  | .pow p k, h => bd_congr S (S.refl _) (S.symm (nI_pow S _ k)) (bd_pow S (eval_bd n env y hy p h) k)


/-! ## Lists of coefficients: every coefficient is again good, one variable fewer -/

def AllL (P : PE → Prop) : List PE → Prop
  | [] => True
  | a :: l => P a ∧ AllL P l

theorem allL_imp {P Q : PE → Prop} (h : ∀ q, P q → Q q) : ∀ l, AllL P l → AllL Q l
  | [], _ => trivial
  | _ :: l, ⟨a, r⟩ => ⟨h _ a, allL_imp h l r⟩

theorem allL_and {P Q R : PE → Prop} (h : ∀ q, P q → Q q → R q) : ∀ l, AllL P l → AllL Q l → AllL R l
  | [], _, _ => trivial
  | _ :: l, ⟨a, r⟩, ⟨b, t⟩ => ⟨h _ a b, allL_and h l r t⟩

theorem allL_forall {P : Nat → PE → Prop} (n : Nat) :
    ∀ l, (∀ i, i < n → AllL (P i) l) → AllL (fun q => ∀ i, i < n → P i q) l
  | [], _ => trivial
  | _ :: l, h => ⟨fun i hi => (h i hi).1, allL_forall n l (fun i hi => (h i hi).2)⟩

section
variable (n : Nat)
def G (q : PE) : Prop := gd n q = true

theorem g_bin {a b : PE} (ha : gd n a = true) (hb : gd n b = true) : (gd n a && gd n b) = true := by
  rw [ha, hb]; rfl

theorem g_lzip : ∀ p q, AllL (G n) p → AllL (G n) q → AllL (G n) (lzip p q)
  | [], _, _, hq => hq
  | _ :: _, [], hp, _ => hp
  | _ :: p, _ :: q, ⟨a, hp⟩, ⟨b, hq⟩ => ⟨g_bin n a b, g_lzip p q hp hq⟩

theorem g_lneg : ∀ q, AllL (G n) q → AllL (G n) (lneg q)
  | [], _ => trivial
  | _ :: q, ⟨a, hq⟩ => ⟨g_bin n (rfl : gd n czero = true) a, g_lneg q hq⟩

theorem g_lsc {a : PE} (ha : G n a) : ∀ q, AllL (G n) q → AllL (G n) (lsc a q)
  | [], _ => trivial
  | _ :: q, ⟨b, hq⟩ => ⟨g_bin n ha b, g_lsc ha q hq⟩

theorem g_conv : ∀ p q, AllL (G n) p → AllL (G n) q → AllL (G n) (conv p q)
  | [], _, _, _ => trivial
  | _ :: p, q, ⟨a, hp⟩, hq => g_lzip n _ _ (g_lsc n a q hq) ⟨(rfl : gd n czero = true), g_conv p q hp hq⟩

theorem g_lpow (l : List PE) (hl : AllL (G n) l) : ∀ k, AllL (G n) (lpow l k)
  | 0 => ⟨(rfl : gd n cone = true), trivial⟩
  | k + 1 => g_conv n l _ hl (g_lpow l hl k)

theorem g_cl : ∀ e : PE, gd (n + 1) e = true → AllL (G n) (cl n e)
  | .var i, h => by
      show AllL (G n) (cond (Nat.beq i n) [czero, cone] [.var i])
      cases hb : Nat.beq i n with
      | true => exact ⟨(rfl : gd n czero = true), (rfl : gd n cone = true), trivial⟩
      | false =>
          have h1 : i ≤ n := Nat.le_of_succ_le_succ (Nat.le_of_ble_eq_true h)
          have h2 : i < n := Nat.lt_of_le_of_ne h1 (Nat.ne_of_beq_eq_false hb)
          exact ⟨(Nat.ble_eq_true_of_le h2 : gd n (.var i) = true), trivial⟩
  | .cst _, h => ⟨h, trivial⟩
  | .add p q, h => by
      obtain ⟨a, b⟩ := gd_and h
      exact g_lzip n _ _ (g_cl p a) (g_cl q b)
  | .sub p q, h => by
      obtain ⟨a, b⟩ := gd_and h
      exact g_lzip n _ _ (g_cl p a) (g_lneg n _ (g_cl q b))
  | .mul p q, h => by
      obtain ⟨a, b⟩ := gd_and h
      exact g_conv n _ _ (g_cl p a) (g_cl q b)
  | .pow p k, h => g_lpow n _ (g_cl p h) k
end

/-! ## The absolute values of the coefficients add up to the absolute value (last variable at 1) -/

def sumA (y : Nat → Nat) : List PE → Nat
  | [] => 0
  | a :: l => evA y a + sumA y l

theorem add4 (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d, Nat.add_comm b c, Nat.add_assoc c b d,
    ← Nat.add_assoc a c (b + d)]

theorem mul_add_r (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

section
variable (y : Nat → Nat)

theorem sumA_lzip : ∀ p q, sumA y (lzip p q) = sumA y p + sumA y q
  | [], q => (Nat.zero_add _).symm
  | _ :: _, [] => rfl
  | a :: p, b :: q => by
      show (evA y a + evA y b) + sumA y (lzip p q) = (evA y a + sumA y p) + (evA y b + sumA y q)
      rw [sumA_lzip p q, add4]

theorem sumA_lneg : ∀ q, sumA y (lneg q) = sumA y q
  | [] => rfl
  | a :: q => by
      show (0 + 0 + evA y a) + sumA y (lneg q) = evA y a + sumA y q
      rw [sumA_lneg q, show (0 : Nat) + 0 = 0 from rfl, Nat.zero_add]

theorem sumA_lsc (a : PE) : ∀ q, sumA y (lsc a q) = evA y a * sumA y q
  | [] => rfl
  | b :: q => by
      show evA y a * evA y b + sumA y (lsc a q) = evA y a * (evA y b + sumA y q)
      rw [sumA_lsc a q, Nat.mul_add]

theorem sumA_conv : ∀ p q, sumA y (conv p q) = sumA y p * sumA y q
  | [], q => (Nat.zero_mul _).symm
  | a :: p, q => by
      show sumA y (lzip (lsc a q) (czero :: conv p q)) = (evA y a + sumA y p) * sumA y q
      rw [sumA_lzip, sumA_lsc]
      show evA y a * sumA y q + (0 + 0 + sumA y (conv p q)) = (evA y a + sumA y p) * sumA y q
      rw [sumA_conv p q, mul_add_r, show (0 : Nat) + 0 = 0 from rfl, Nat.zero_add]

theorem sumA_lpow (l : List PE) : ∀ k, sumA y (lpow l k) = sumA y l ^ k
  | 0 => rfl
  | k + 1 => by
      show sumA y (conv l (lpow l k)) = sumA y l ^ k * sumA y l
      rw [sumA_conv, sumA_lpow l k, Nat.mul_comm]

theorem sumA_cl (v : Nat) (hy : y v = 1) : ∀ e : PE, sumA y (cl v e) = evA y e
  | .var i => by
      show sumA y (cond (Nat.beq i v) [czero, cone] [.var i]) = y i
      cases hb : Nat.beq i v with
      | true =>
          have e := Nat.eq_of_beq_eq_true hb
          subst e
          rw [hy]; rfl
      | false => rfl
  | .cst _ => rfl
  | .add p q => by
      show sumA y (lzip (cl v p) (cl v q)) = evA y p + evA y q
      rw [sumA_lzip, sumA_cl v hy p, sumA_cl v hy q]
  | .sub p q => by
      show sumA y (lzip (cl v p) (lneg (cl v q))) = evA y p + evA y q
      rw [sumA_lzip, sumA_lneg, sumA_cl v hy p, sumA_cl v hy q]
  | .mul p q => by
      show sumA y (conv (cl v p) (cl v q)) = evA y p * evA y q
      rw [sumA_conv, sumA_cl v hy p, sumA_cl v hy q]
  | .pow p k => by
      show sumA y (lpow (cl v p) k) = evA y p ^ k
      rw [sumA_lpow, sumA_cl v hy p]

theorem le_of_sumA : ∀ (l : List PE) (M : Nat), sumA y l ≤ M → AllL (fun q => evA y q ≤ M) l
  | [], _, _ => trivial
  | a :: l, M, h => ⟨Nat.le_trans (Nat.le_add_right _ _) h, le_of_sumA l M (Nat.le_trans (Nat.le_add_left _ _) h)⟩

end

/-! ## Digits: `Σ c_j·Bʲ = 0` with every `|c_j| < B` -/

/-- `Σ_j evZ(q_j)·Bʲ`, an integer. -/
def hzP (x : Nat → BZ) (B : Nat) : List PE → BZ
  | [] => ⟨0, 0⟩
  | q :: l => zadd (evZ x q) (zmul (zofNat B) (hzP x B l))

theorem hv_hzP (n : Nat) (x : Nat → BZ) (B : Nat) {X : α} (hX : S.r X (nI S B)) :
    ∀ l, AllL (G n) l → S.r (hv S (fun i => zv S (x i)) X l) (zv S (hzP x B l))
  | [], _ => by show S.r S.zero (S.add S.zero (S.neg S.zero)); cr_ring S.toCR
  | q :: l, ⟨a, r⟩ => by
      have ih := hv_hzP n x B hX l r
      have e1 := evZ_sound S n x q a
      refine S.symm (S.trans (zv_add S _ _) (S.add_congr e1 (S.trans (zv_mul S _ _) ?_)))
      exact S.mul_congr (S.trans (zv_ofNat S B) (S.symm hX)) (S.symm ih)

theorem zv_zero_of_eq {z : BZ} (h : z.p = z.n) : S.r (zv S z) S.zero := by
  show S.r (S.add (nI S z.p) (S.neg (nI S z.n))) S.zero
  rw [h]; exact S.add_neg _

theorem digits (x : Nat → BZ) (M B : Nat) (hMB : M < B) :
    ∀ l, AllL (fun q => Bd S (zv S (evZ x q)) (nI S M)) l → S.r (zv S (hzP x B l)) S.zero →
      AllL (fun q => S.r (zv S (evZ x q)) S.zero) l
  | [], _, _ => trivial
  | q :: l, ⟨⟨c1, c2⟩, hl⟩, hz => by
      have s1 : S.r (zv S (hzP x B (q :: l)))
          (S.add (zv S (evZ x q)) (S.mul (nI S B) (zv S (hzP x B l)))) :=
        S.trans (zv_add S _ _) (S.add_congr (S.refl _) (S.trans (zv_mul S _ _) (S.mul_congr (zv_ofNat S B) (S.refl _))))
      have s2 := S.trans (S.symm s1) hz
      have mb : S.le (S.add (nI S M) S.one) (nI S B) := by
        have := nI_le S (Nat.succ_le_of_lt hMB)
        exact S.le_respects (by show S.r (S.add S.one (nI S M)) _; cr_ring S.toCR) (S.refl _) this
      have b0 := nI_nonneg S B
      -- the rest is an integer: zero, or at least one in size
      cases Nat.lt_or_ge (hzP x B l).p (hzP x B l).n with
      | inl lt =>
          have h1 := nI_le S (Nat.succ_le_of_lt lt)
          have h1' : S.le (S.add (nI S (hzP x B l).p) S.one) (nI S (hzP x B l).n) :=
            S.le_respects (by show S.r (S.add S.one (nI S (hzP x B l).p)) _; cr_ring S.toCR) (S.refl _) h1
          have nn : S.le S.zero (S.add (S.neg S.one) (S.neg (zv S (hzP x B l)))) := by
            show S.le S.zero (S.add (S.neg S.one) (S.neg (S.add (nI S (hzP x B l).p) (S.neg (nI S (hzP x B l).n)))))
            cr_linarith S.toOCR [h1']
          have pm := S.mul_nonneg b0 nn
          exact absurd (by cr_linarith S.toOCR [pm, s2, c2, mb] : S.le S.one S.zero) S.one_pos
      | inr ge =>
          cases Nat.lt_or_ge (hzP x B l).n (hzP x B l).p with
          | inl lt =>
              have h1 := nI_le S (Nat.succ_le_of_lt lt)
              have h1' : S.le (S.add (nI S (hzP x B l).n) S.one) (nI S (hzP x B l).p) :=
                S.le_respects (by show S.r (S.add S.one (nI S (hzP x B l).n)) _; cr_ring S.toCR) (S.refl _) h1
              have nn : S.le S.zero (S.add (zv S (hzP x B l)) (S.neg S.one)) := by
                show S.le S.zero (S.add (S.add (nI S (hzP x B l).p) (S.neg (nI S (hzP x B l).n))) (S.neg S.one))
                cr_linarith S.toOCR [h1']
              have pm := S.mul_nonneg b0 nn
              exact absurd (by cr_linarith S.toOCR [pm, s2, c1, mb] : S.le S.one S.zero) S.one_pos
          | inr ge2 =>
              have z := zv_zero_of_eq S (Nat.le_antisymm ge2 ge)
              have pz : S.r (S.mul (nI S B) (zv S (hzP x B l))) S.zero :=
                S.trans (S.mul_congr (S.refl _) z) (by cr_ring S.toCR)
              have cz : S.r (zv S (evZ x q)) S.zero :=
                S.trans (by cr_ring S.toCR) (S.trans (S.add_congr (S.refl _) (S.symm pz)) s2)
              exact ⟨cz, digits x M B hMB l hl z⟩


/-! ## The induction on the number of variables -/

theorem hv_zero (env : Nat → α) (X : α) : ∀ l, AllL (fun q => S.r (eval S env q) S.zero) l → S.r (hv S env X l) S.zero
  | [], _ => S.refl _
  | _ :: l, ⟨a, r⟩ => by
      have ih := hv_zero env X l r
      exact S.trans (S.add_congr a (S.mul_congr (S.refl _) ih)) (by cr_ring S.toCR)

theorem eval_indep0 (env env' : Nat → α) : ∀ e : PE, gd 0 e = true → S.r (eval S env e) (eval S env' e)
  | .var i, h => by have h' : false = true := h; cases h'
  | .cst _, _ => S.refl _
  | .add p q, h => by
      obtain ⟨a, b⟩ := gd_and h; exact S.add_congr (eval_indep0 env env' p a) (eval_indep0 env env' q b)
  | .sub p q, h => by
      obtain ⟨a, b⟩ := gd_and h
      exact S.add_congr (eval_indep0 env env' p a) (S.neg_congr (eval_indep0 env env' q b))
  | .mul p q, h => by
      obtain ⟨a, b⟩ := gd_and h; exact S.mul_congr (eval_indep0 env env' p a) (eval_indep0 env env' q b)
  | .pow p k, h => powS_congr S (eval_indep0 env env' p h) k

theorem blt_self (n : Nat) : Nat.blt n n = false := by
  cases h : Nat.blt n n with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_succ_le_self n)

theorem blt_false_of_le {i n : Nat} (h : i ≤ n) : Nat.blt n i = false := by
  cases hb : Nat.blt n i with
  | false => rfl
  | true => exact absurd (Nat.le_trans (Nat.le_of_ble_eq_true hb) h) (Nat.not_succ_le_self n)

/-- THE MAIN LEMMA: integer constants, variables below `n`, points `Bᵢ` above the absolute value at
`(B_<i, 1, …)`, the value at the points zero — then the expression is zero everywhere, in every `OH`. -/
theorem main : ∀ (n : Nat) (e : PE) (B : Nat → Nat), gd n e = true →
    (∀ i, i < n → evA (fun j => cond (Nat.blt j i) (B j) 1) e < B i) →
    S.r (zv S (evZ (fun j => zofNat (B j)) e)) S.zero →
    ∀ env : Nat → α, S.r (eval S env e) S.zero
  | 0, e, B, hg, _, hz, env =>
      S.trans (eval_indep0 S env (fun i => zv S (zofNat (B i))) e hg)
        (S.trans (S.symm (evZ_sound S 0 _ e hg)) hz)
  | n + 1, e, B, hg, hb, hz, env => by
      have hl := g_cl n e hg
      -- the coefficient values are bounded by M = |e|(B_<n, 1) < B_n
      have hM := hb n (Nat.lt_succ_self n)
      have hyn : (fun j => cond (Nat.blt j n) (B j) 1) n = 1 := by show cond (Nat.blt n n) (B n) 1 = 1; rw [blt_self]; rfl
      have sl := sumA_cl (fun j => cond (Nat.blt j n) (B j) 1) n hyn e
      have le1 := le_of_sumA (fun j => cond (Nat.blt j n) (B j) 1) (cl n e) _ (Nat.le_of_eq sl)
      have hy : ∀ i, i < n → Bd S (zv S (zofNat (B i))) (nI S ((fun j => cond (Nat.blt j n) (B j) 1) i)) := by
        intro i hi
        have t : Nat.blt i n = true := Nat.ble_eq_true_of_le hi
        show Bd S (zv S (zofNat (B i))) (nI S (cond (Nat.blt i n) (B i) 1))
        rw [t]
        show Bd S (zv S (zofNat (B i))) (nI S (B i))
        have b0 := nI_nonneg S (B i)
        exact bd_congr S (S.symm (zv_ofNat S (B i))) (S.refl _) ⟨by cr_linarith S.toOCR [b0], S.le_refl _⟩
      have bds : AllL (fun q => Bd S (zv S (evZ (fun j => zofNat (B j)) q))
          (nI S (evA (fun j => cond (Nat.blt j n) (B j) 1) e))) (cl n e) :=
        allL_and (fun q gq lq => by
          have b := eval_bd S n (fun i => zv S (zofNat (B i))) _ hy q gq
          obtain ⟨b1, b2⟩ := bd_congr S (S.symm (evZ_sound S n _ q gq)) (S.refl _) b
          have l2 := nI_le S lq
          exact ⟨by cr_linarith S.toOCR [b1, l2], by cr_linarith S.toOCR [b2, l2]⟩) _ hl le1
      -- the value at the points is Σ q_j(B_<)·B_nʲ, an integer combination
      have hv0 : S.r (zv S (hzP (fun j => zofNat (B j)) (B n) (cl n e))) S.zero := by
        have d := eval_cl S (fun i => zv S (zofNat (B i))) n e
        have k := hv_hzP S n (fun j => zofNat (B j)) (B n) (zv_ofNat S (B n)) (cl n e) hl
        exact S.trans (S.symm k) (S.trans (S.symm d) (S.trans (S.symm (evZ_sound S (n + 1) _ e hg)) hz))
      have dz := digits S (fun j => zofNat (B j)) _ (B n) hM (cl n e) bds hv0
      -- every coefficient: the same hypotheses, one variable fewer
      have bnd : AllL (fun q => ∀ i, i < n → evA (fun j => cond (Nat.blt j i) (B j) 1) q < B i) (cl n e) :=
        allL_forall n (cl n e) (fun i hi =>
          let yi := fun j => cond (Nat.blt j i) (B j) 1
          have h1 : yi n = 1 := by
            show cond (Nat.blt n i) (B n) 1 = 1
            rw [blt_false_of_le (Nat.le_of_lt hi)]; rfl
          allL_imp (fun q (hq : evA yi q ≤ evA yi e) => Nat.lt_of_le_of_lt hq (hb i (Nat.le_succ_of_le hi)))
            _ (le_of_sumA yi (cl n e) _ (Nat.le_of_eq (sumA_cl yi n h1 e))))
      have gb : AllL (fun q => gd n q = true ∧ ∀ i, i < n → evA (fun j => cond (Nat.blt j i) (B j) 1) q < B i)
          (cl n e) := allL_and (fun _ a b => ⟨a, b⟩) _ hl bnd
      have all : AllL (fun q => S.r (eval S env q) S.zero) (cl n e) :=
        allL_and (fun q gbq z => main n q B gbq.1 gbq.2 z env) _ gb dz
      exact S.trans (eval_cl S env n e) (hv_zero S env (env n) _ all)


/-! ## The computed points satisfy the hypotheses -/

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

section
variable (e : PE)

theorem pt_one : ∀ i j, i ≤ j → pt e i j = 1
  | 0, _, _ => rfl
  | i + 1, j, h => by
      show cond (Nat.beq j i) (evA (pt e i) e + 1) (pt e i j) = 1
      cases hb : Nat.beq j i with
      | true =>
          have := Nat.eq_of_beq_eq_true hb
          subst this
          exact absurd h (Nat.not_succ_le_self j)
      | false => exact pt_one i j (Nat.le_trans (Nat.le_succ i) h)

theorem pt_set : ∀ i j, j < i → pt e i j = pt e (j + 1) j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | i + 1, j, h => by
      cases hb : Nat.beq j i with
      | true =>
          have := Nat.eq_of_beq_eq_true hb
          subst this
          rfl
      | false =>
          show cond (Nat.beq j i) (evA (pt e i) e + 1) (pt e i j) = pt e (j + 1) j
          rw [hb]
          exact pt_set i j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) (Nat.ne_of_beq_eq_false hb))

theorem pt_val (j : Nat) : pt e (j + 1) j = evA (pt e j) e + 1 := by
  show cond (Nat.beq j j) (evA (pt e j) e + 1) (pt e j j) = evA (pt e j) e + 1
  rw [beq_self j]; rfl
end

theorem evA_congr {y y' : Nat → Nat} (h : ∀ j, y j = y' j) : ∀ e : PE, evA y e = evA y' e
  | .var i => h i
  | .cst _ => rfl
  | .add p q => by show evA y p + evA y q = evA y' p + evA y' q; rw [evA_congr h p, evA_congr h q]
  | .sub p q => by show evA y p + evA y q = evA y' p + evA y' q; rw [evA_congr h p, evA_congr h q]
  | .mul p q => by show evA y p * evA y q = evA y' p * evA y' q; rw [evA_congr h p, evA_congr h q]
  | .pow p k => by show evA y p ^ k = evA y' p ^ k; rw [evA_congr h p]

/-- **SOUNDNESS OF THE KRONECKER TEST.** -/
theorem kron_sound {n : Nat} {e : PE} (h : kron n e = true) (env : Nat → α) : S.r (eval S env e) S.zero := by
  obtain ⟨hg, hz⟩ := and_true_split h
  refine main S n e (pt e n) hg (fun i hi => ?_) (zv_zero_of_eq S (Nat.eq_of_beq_eq_true hz)) env
  have ey : ∀ j, cond (Nat.blt j i) (pt e n j) 1 = pt e i j := by
    intro j
    cases hb : Nat.blt j i with
    | true =>
        have ji := lt_of_blt hb
        show pt e n j = pt e i j
        rw [pt_set e n j (Nat.lt_trans ji hi), pt_set e i j ji]
    | false =>
        cases Nat.lt_or_ge j i with
        | inl lt =>
            have t : Nat.blt j i = true := Nat.ble_eq_true_of_le lt
            rw [t] at hb; cases hb
        | inr ge => exact (pt_one e i j ge).symm
  rw [evA_congr ey e, pt_set e n i hi, pt_val e i]
  exact Nat.lt_succ_self _

/-! ## Identities -/

/-- One more than the largest variable index. -/
def nv : PE → Nat
  | .var i => i + 1
  | .cst _ => 0
  | .add p q => Nat.max (nv p) (nv q)
  | .sub p q => Nat.max (nv p) (nv q)
  | .mul p q => Nat.max (nv p) (nv q)
  | .pow p _ => nv p

/-- `e₁ = e₂` by one integer evaluation. -/
def identK (e₁ e₂ : PE) : Bool := kron (nv (.sub e₁ e₂)) (.sub e₁ e₂)

theorem identK_sound {e₁ e₂ : PE} (h : identK e₁ e₂ = true) (env : Nat → α) :
    S.r (eval S env e₁) (eval S env e₂) := by
  have d := kron_sound S h env
  have d' : S.r (S.add (eval S env e₁) (S.neg (eval S env e₂))) S.zero := d
  exact S.trans (by cr_ring S.toCR) (S.trans (S.add_congr d' (S.refl (eval S env e₂))) (by cr_ring S.toCR))

end ZKron

namespace ZKron
open ZPoly
private def X : PE := .var 0
private def Y : PE := .var 1
private def Z : PE := .var 2
private def c (k : Nat) : PE := .cst ⟨⟨k, 0⟩, 0⟩
/-! Both ways: `(x + y)² = x² + 2xy + y²` accepted, `(x + y)² = x² + y²` refused; three variables:
`(x − y)(y − z)(z − x)` against its expansion accepted, against the expansion with one sign flipped refused. -/
example : identK (.pow (.add X Y) 2) (.add (.add (.pow X 2) (.mul (c 2) (.mul X Y))) (.pow Y 2)) = true := by decide +kernel
example : identK (.pow (.add X Y) 2) (.add (.pow X 2) (.pow Y 2)) = false := by decide +kernel
private def L3 : PE := .mul (.mul (.sub X Y) (.sub Y Z)) (.sub Z X)
private def R3 : PE := .sub (.sub (.add (.add (.mul (.pow X 2) Z) (.mul (.pow Y 2) X)) (.mul (.pow Z 2) Y))
  (.add (.mul (.pow X 2) Y) (.mul (.pow Y 2) Z))) (.mul (.pow Z 2) X)
private def R3bad : PE := .sub (.add (.add (.add (.mul (.pow X 2) Z) (.mul (.pow Y 2) X)) (.mul (.pow Z 2) Y))
  (.add (.mul (.pow X 2) Y) (.mul (.pow Y 2) Z))) (.mul (.pow Z 2) X)
example : identK L3 R3 = true := by decide +kernel
example : identK L3 R3bad = false := by decide +kernel
end ZKron

#print axioms ZKron.kron_sound
#print axioms ZKron.identK_sound

#print axioms ZKron.main

#print axioms ZKron.g_cl
#print axioms ZKron.sumA_cl
#print axioms ZKron.digits

#print axioms ZKron.evZ_sound
#print axioms ZKron.eval_bd

#print axioms ZKron.eval_cl
