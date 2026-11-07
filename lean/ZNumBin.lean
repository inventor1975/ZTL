import VR.Meta.CSRNorm
/-!
# ZNumBin — binary numbers the kernel computes with, read into any ordered ring with a half. Zero axioms.

Module 1 of the Lean-checked `check_none` (curator, 2026-11-07: "Б"). VR's numbers are UNARY (`VRObj.base`,
`VRObj.succ`): a certificate's 2⁶² cannot be computed on them. So the kernel computes on core `Nat` (binary,
GMP-backed in the kernel), and every number is READ into an abstract structure `OH` — VR's ordered ring `OCR`
(no totality: nothing here decides `x ≤ y` for the target) with a half and products of non-negatives
non-negative. VR's operational numbers and Mathlib's ℝ are both instances (later modules).

THE DISCIPLINE. Core lemmas about `Nat` division and subtraction carry `propext` on this toolchain (probed
2026-11-07: `Nat.div_add_mod`, `Nat.sub_add_cancel`, `Nat.add_sub_of_le`, `Nat.pow_add`, `Nat.right_distrib`,
`Nat.mul_assoc`; `omega` too). So the kernel COMPUTES a quotient or a difference however it likes, and then
CHECKS a plain relation by `Nat.beq` / `Nat.ble` (`q * 2^k ≤ m`, `(p - n) + n = p`); proofs rest on the check
(`Nat.eq_of_beq_eq_true`, `Nat.le_of_ble_eq_true`: no axioms), never on a division lemma. A failed check
falls back to an exact (unrounded, unnormalised) value: sound always, merely bigger.

What is here:
  * `nI` — a natural read into the ring (VR's `CR.numeral`), with `+`, `×`, `≤` carried over;
  * `BZ` — signed integers as (positive, negative) pairs of `Nat`; `+ − ×`, normalisation, `≤`;
  * `D`  — dyadics `m · ½ᵉ`; `+ − ×`, outward rounding to `P` bits (`rdn ≤ x ≤ rup`), `≤`.
-/

namespace ZNumBin
open VR.CSR

/-- VR's ordered commutative ring (up to its equivalence `r`), plus a half and the product law. -/
structure OH (α : Type) extends OCR α where
  half : α
  half_spec : r (add half half) one
  mul_nonneg : ∀ {a b : α}, le zero a → le zero b → le zero (mul a b)

variable {α : Type} (S : OH α)

/-! ## §1. Naturals read into the ring -/

/-- `n` read into the ring. -/
def nI (n : Nat) : α := CR.numeral S.toCR n

theorem nI_add (a b : Nat) : S.r (nI S (a + b)) (S.add (nI S a) (nI S b)) := CR.numeral_add S.toCR a b
theorem nI_mul (a b : Nat) : S.r (nI S (a * b)) (S.mul (nI S a) (nI S b)) := CR.numeral_mul S.toCR a b
theorem nI_nonneg (n : Nat) : S.le S.zero (nI S n) := OCR.nonneg_numeral S.toOCR n
theorem nI_zero : S.r (nI S 0) S.zero := S.refl _

theorem nI_le {a b : Nat} (h : a ≤ b) : S.le (nI S a) (nI S b) := by
  induction h with
  | refl => exact S.le_refl _
  | @step m _ ih =>
      refine S.le_trans ih ?_
      have e : S.r (nI S (m + 1)) (S.add S.one (nI S m)) := S.refl _
      refine S.le_respects (S.refl _) (S.symm e) ?_
      have h1 := S.zero_le_one
      cr_linarith S.toOCR [h1]

/-- The kernel's comparison, read into the ring. -/
theorem nI_le_of_ble {a b : Nat} (h : Nat.ble a b = true) : S.le (nI S a) (nI S b) :=
  nI_le S (Nat.le_of_ble_eq_true h)

theorem nI_congr {a b : Nat} (h : a = b) : S.r (nI S a) (nI S b) := h ▸ S.refl _

/-! ## §2. Two facts of the ring used below -/

/-- Multiplying by a non-negative keeps `≤`. -/
theorem le_mul_right {a b c : α} (hab : S.le a b) (hc : S.le S.zero c) : S.le (S.mul a c) (S.mul b c) := by
  have h1 := OCR.sub_nonneg_of_le S.toOCR hab
  have h2 := S.mul_nonneg h1 hc
  cr_linarith S.toOCR [h2]

theorem half_nonneg : S.le S.zero S.half := by
  apply S.le_of_smul 1
  have h := S.half_spec
  have h0 := S.zero_le_one
  have e : S.r (S.mul (CR.numeral S.toCR (1 + 1)) S.half) S.one := by
    show S.r (S.mul (S.add S.one (S.add S.one S.zero)) S.half) S.one
    exact S.trans (by cr_ring S.toCR) h
  exact S.le_respects (S.refl _) (S.symm e) h0

/-! ## §3. Signed integers: a pair (positive part, negative part) -/

structure BZ where
  p : Nat
  n : Nat
deriving Repr

/-- `p − n`, read into the ring. -/
def zv (z : BZ) : α := S.add (nI S z.p) (S.neg (nI S z.n))

def zadd (z w : BZ) : BZ := ⟨z.p + w.p, z.n + w.n⟩
def zneg (z : BZ) : BZ := ⟨z.n, z.p⟩
def zmul (z w : BZ) : BZ := ⟨z.p * w.p + z.n * w.n, z.p * w.n + z.n * w.p⟩
def zofNat (k : Nat) : BZ := ⟨k, 0⟩
/-- Normalise to one zero part: the difference computed, then CHECKED by `Nat.beq`. -/
def znorm (z : BZ) : BZ :=
  if Nat.beq ((z.p - z.n) + z.n) z.p then ⟨z.p - z.n, 0⟩
  else if Nat.beq ((z.n - z.p) + z.p) z.n then ⟨0, z.n - z.p⟩ else z
/-- The kernel's `≤` on signed integers. -/
def zle (z w : BZ) : Bool := Nat.ble (z.p + w.n) (w.p + z.n)

theorem zv_add (z w : BZ) : S.r (zv S (zadd z w)) (S.add (zv S z) (zv S w)) := by
  have h1 := nI_add S z.p w.p
  have h2 := nI_add S z.n w.n
  show S.r (S.add (nI S (z.p + w.p)) (S.neg (nI S (z.n + w.n))))
    (S.add (S.add (nI S z.p) (S.neg (nI S z.n))) (S.add (nI S w.p) (S.neg (nI S w.n))))
  exact S.trans (S.add_congr h1 (S.neg_congr h2)) (by cr_ring S.toCR)

theorem zv_neg (z : BZ) : S.r (zv S (zneg z)) (S.neg (zv S z)) := by
  show S.r (S.add (nI S z.n) (S.neg (nI S z.p))) (S.neg (S.add (nI S z.p) (S.neg (nI S z.n))))
  cr_ring S.toCR

theorem zv_mul (z w : BZ) : S.r (zv S (zmul z w)) (S.mul (zv S z) (zv S w)) := by
  have a1 := nI_add S (z.p * w.p) (z.n * w.n)
  have a2 := nI_add S (z.p * w.n) (z.n * w.p)
  have m1 := nI_mul S z.p w.p
  have m2 := nI_mul S z.n w.n
  have m3 := nI_mul S z.p w.n
  have m4 := nI_mul S z.n w.p
  show S.r (S.add (nI S (z.p * w.p + z.n * w.n)) (S.neg (nI S (z.p * w.n + z.n * w.p))))
    (S.mul (S.add (nI S z.p) (S.neg (nI S z.n))) (S.add (nI S w.p) (S.neg (nI S w.n))))
  exact S.trans (S.add_congr (S.trans a1 (S.add_congr m1 m2)) (S.neg_congr (S.trans a2 (S.add_congr m3 m4))))
    (by cr_ring S.toCR)

theorem zv_ofNat (k : Nat) : S.r (zv S (zofNat k)) (nI S k) := by
  show S.r (S.add (nI S k) (S.neg (CR.numeral S.toCR 0))) (nI S k)
  show S.r (S.add (nI S k) (S.neg S.zero)) (nI S k)
  cr_ring S.toCR

theorem zv_norm (z : BZ) : S.r (zv S (znorm z)) (zv S z) := by
  unfold znorm
  split
  · next h =>
    have e := nI_congr S (Nat.eq_of_beq_eq_true h)
    have a := nI_add S (z.p - z.n) z.n
    show S.r (S.add (nI S (z.p - z.n)) (S.neg S.zero)) (S.add (nI S z.p) (S.neg (nI S z.n)))
    have e2 := S.trans (S.symm e) a
    refine S.trans ?_ (S.add_congr (S.symm e2) (S.refl _))
    cr_ring S.toCR
  · split
    · next _ h =>
      have e := nI_congr S (Nat.eq_of_beq_eq_true h)
      have a := nI_add S (z.n - z.p) z.p
      show S.r (S.add S.zero (S.neg (nI S (z.n - z.p)))) (S.add (nI S z.p) (S.neg (nI S z.n)))
      have e2 := S.trans (S.symm e) a
      refine S.trans ?_ (S.add_congr (S.refl _) (S.neg_congr (S.symm e2)))
      cr_ring S.toCR
    · exact S.refl _

theorem zle_sound {z w : BZ} (h : zle z w = true) : S.le (zv S z) (zv S w) := by
  have h1 := nI_le_of_ble S h
  have a1 := nI_add S z.p w.n
  have a2 := nI_add S w.p z.n
  have h2 := S.le_respects a1 a2 h1
  show S.le (S.add (nI S z.p) (S.neg (nI S z.n))) (S.add (nI S w.p) (S.neg (nI S w.n)))
  cr_linarith S.toOCR [h2]

/-! ## §4. Powers of the half -/

def hp : Nat → α
  | 0 => S.one
  | k + 1 => S.mul S.half (hp k)

theorem hp_nonneg : ∀ k, S.le S.zero (hp S k)
  | 0 => S.zero_le_one
  | k + 1 => S.mul_nonneg (half_nonneg S) (hp_nonneg k)

theorem hp_add (a : Nat) : ∀ b, S.r (hp S (a + b)) (S.mul (hp S a) (hp S b))
  | 0 => by show S.r (hp S a) (S.mul (hp S a) S.one); cr_ring S.toCR
  | b + 1 => by
      show S.r (S.mul S.half (hp S (a + b))) (S.mul (hp S a) (S.mul S.half (hp S b)))
      exact S.trans (S.mul_congr (S.refl _) (hp_add a b)) (by cr_ring S.toCR)

/-- `2ᵏ · ½ᵏ = 1`. -/
theorem two_hp : ∀ k, S.r (S.mul (nI S (2 ^ k)) (hp S k)) S.one
  | 0 => by show S.r (S.mul (CR.numeral S.toCR 1) S.one) S.one; show S.r (S.mul (S.add S.one S.zero) S.one) S.one; cr_ring S.toCR
  | k + 1 => by
      have e1 : S.r (nI S (2 ^ (k + 1))) (S.mul (nI S (2 ^ k)) (nI S 2)) := by
        rw [Nat.pow_succ]; exact nI_mul S _ _
      have ih := two_hp k
      have hs := S.half_spec
      have e2 : S.r (nI S 2) (S.add S.one (S.add S.one S.zero)) := S.refl _
      show S.r (S.mul (nI S (2 ^ (k + 1))) (S.mul S.half (hp S k))) S.one
      refine S.trans (S.mul_congr (S.trans e1 (S.mul_congr (S.refl _) e2)) (S.refl _)) ?_
      have e3 : S.r (S.mul (S.mul (nI S (2 ^ k)) (S.add S.one (S.add S.one S.zero))) (S.mul S.half (hp S k)))
          (S.mul (S.mul (nI S (2 ^ k)) (hp S k)) (S.add S.half S.half)) := by cr_ring S.toCR
      exact S.trans e3 (S.trans (S.mul_congr ih hs) (by cr_ring S.toCR))

/-! ## §5. Dyadics `m · ½ᵉ` -/

structure D where
  m : BZ
  e : Nat
deriving Repr

/-- `m · ½ᵉ`, read into the ring. -/
def dv (d : D) : α := S.mul (zv S d.m) (hp S d.e)

def dofBZ (z : BZ) : D := ⟨z, 0⟩
def dneg (d : D) : D := ⟨zneg d.m, d.e⟩
def dmul (a b : D) : D := ⟨zmul a.m b.m, a.e + b.e⟩
/-- Exact sum at the exponent `a.e + b.e` (the fallback; always sound). -/
def daddX (a b : D) : D := ⟨zadd (zmul a.m (zofNat (2 ^ b.e))) (zmul b.m (zofNat (2 ^ a.e))), a.e + b.e⟩
/-- `a` lifted to exponent `a.e + k`. -/
def lift (a : D) (k : Nat) : D := ⟨zmul a.m (zofNat (2 ^ k)), a.e + k⟩
/-- Sum aligned to the larger exponent: the gap computed, then CHECKED (`gap + small = large`). -/
def dadd (a b : D) : D :=
  if Nat.beq ((b.e - a.e) + a.e) b.e then ⟨zadd (lift a (b.e - a.e)).m b.m, b.e⟩
  else if Nat.beq ((a.e - b.e) + b.e) a.e then ⟨zadd a.m (lift b (a.e - b.e)).m, a.e⟩
  else daddX a b
/-- The kernel's `≤` on dyadics. -/
def dle (a b : D) : Bool := zle (zmul a.m (zofNat (2 ^ b.e))) (zmul b.m (zofNat (2 ^ a.e)))

theorem dv_neg (d : D) : S.r (dv S (dneg d)) (S.neg (dv S d)) := by
  show S.r (S.mul (zv S (zneg d.m)) (hp S d.e)) (S.neg (S.mul (zv S d.m) (hp S d.e)))
  exact S.trans (S.mul_congr (zv_neg S d.m) (S.refl _)) (by cr_ring S.toCR)

theorem dv_mul (a b : D) : S.r (dv S (dmul a b)) (S.mul (dv S a) (dv S b)) := by
  show S.r (S.mul (zv S (zmul a.m b.m)) (hp S (a.e + b.e)))
    (S.mul (S.mul (zv S a.m) (hp S a.e)) (S.mul (zv S b.m) (hp S b.e)))
  exact S.trans (S.mul_congr (zv_mul S a.m b.m) (hp_add S a.e b.e)) (by cr_ring S.toCR)

/-- Lifting does not change the value: `m·2ᵏ · ½^(e+k) = m · ½ᵉ`. -/
theorem dv_lift (a : D) (k : Nat) : S.r (dv S (lift a k)) (dv S a) := by
  show S.r (S.mul (zv S (zmul a.m (zofNat (2 ^ k)))) (hp S (a.e + k))) (S.mul (zv S a.m) (hp S a.e))
  have e1 := S.trans (zv_mul S a.m (zofNat (2 ^ k))) (S.mul_congr (S.refl _) (zv_ofNat S (2 ^ k)))
  have e2 := hp_add S a.e k
  have t := two_hp S k
  refine S.trans (S.mul_congr e1 e2) ?_
  have e3 : S.r (S.mul (S.mul (zv S a.m) (nI S (2 ^ k))) (S.mul (hp S a.e) (hp S k)))
      (S.mul (S.mul (zv S a.m) (hp S a.e)) (S.mul (nI S (2 ^ k)) (hp S k))) := by cr_ring S.toCR
  exact S.trans e3 (S.trans (S.mul_congr (S.refl _) t) (by cr_ring S.toCR))

theorem dv_addX (a b : D) : S.r (dv S (daddX a b)) (S.add (dv S a) (dv S b)) := by
  have la := dv_lift S a b.e
  have lb := dv_lift S b a.e
  show S.r (S.mul (zv S (zadd (zmul a.m (zofNat (2 ^ b.e))) (zmul b.m (zofNat (2 ^ a.e))))) (hp S (a.e + b.e)))
    (S.add (dv S a) (dv S b))
  have hb : S.r (hp S (a.e + b.e)) (hp S (b.e + a.e)) := by rw [Nat.add_comm]; exact S.refl _
  refine S.trans (S.mul_congr (zv_add S _ _) (S.refl _)) ?_
  have e3 : S.r (S.mul (S.add (zv S (zmul a.m (zofNat (2 ^ b.e)))) (zv S (zmul b.m (zofNat (2 ^ a.e))))) (hp S (a.e + b.e)))
      (S.add (S.mul (zv S (zmul a.m (zofNat (2 ^ b.e)))) (hp S (a.e + b.e)))
             (S.mul (zv S (zmul b.m (zofNat (2 ^ a.e)))) (hp S (a.e + b.e)))) := by cr_ring S.toCR
  refine S.trans e3 (S.add_congr la (S.trans (S.mul_congr (S.refl _) hb) lb))

theorem dv_add (a b : D) : S.r (dv S (dadd a b)) (S.add (dv S a) (dv S b)) := by
  unfold dadd
  split
  · next h =>
    have g := Nat.eq_of_beq_eq_true h
    have la := dv_lift S a (b.e - a.e)
    show S.r (S.mul (zv S (zadd (lift a (b.e - a.e)).m b.m)) (hp S b.e)) (S.add (dv S a) (dv S b))
    have he : S.r (hp S b.e) (hp S ((lift a (b.e - a.e)).e)) := by
      show S.r (hp S b.e) (hp S (a.e + (b.e - a.e))); rw [Nat.add_comm a.e, g]; exact S.refl _
    refine S.trans (S.mul_congr (zv_add S _ _) (S.refl _)) ?_
    have e3 : S.r (S.mul (S.add (zv S (lift a (b.e - a.e)).m) (zv S b.m)) (hp S b.e))
        (S.add (S.mul (zv S (lift a (b.e - a.e)).m) (hp S b.e)) (S.mul (zv S b.m) (hp S b.e))) := by cr_ring S.toCR
    exact S.trans e3 (S.add_congr (S.trans (S.mul_congr (S.refl _) he) la) (S.refl _))
  · split
    · next _ h =>
      have g := Nat.eq_of_beq_eq_true h
      have lb := dv_lift S b (a.e - b.e)
      show S.r (S.mul (zv S (zadd a.m (lift b (a.e - b.e)).m)) (hp S a.e)) (S.add (dv S a) (dv S b))
      have he : S.r (hp S a.e) (hp S ((lift b (a.e - b.e)).e)) := by
        show S.r (hp S a.e) (hp S (b.e + (a.e - b.e))); rw [Nat.add_comm b.e, g]; exact S.refl _
      refine S.trans (S.mul_congr (zv_add S _ _) (S.refl _)) ?_
      have e3 : S.r (S.mul (S.add (zv S a.m) (zv S (lift b (a.e - b.e)).m)) (hp S a.e))
          (S.add (S.mul (zv S a.m) (hp S a.e)) (S.mul (zv S (lift b (a.e - b.e)).m) (hp S a.e))) := by cr_ring S.toCR
      exact S.trans e3 (S.add_congr (S.refl _) (S.trans (S.mul_congr (S.refl _) he) lb))
    · exact dv_addX S a b

theorem dle_sound {a b : D} (h : dle a b = true) : S.le (dv S a) (dv S b) := by
  have h1 := zle_sound S h
  have h2 := le_mul_right S h1 (hp_nonneg S (a.e + b.e))
  have la := dv_lift S a b.e
  have lb := dv_lift S b a.e
  have hb : S.r (hp S (a.e + b.e)) (hp S (b.e + a.e)) := by rw [Nat.add_comm]; exact S.refl _
  have ea : S.r (S.mul (zv S (zmul a.m (zofNat (2 ^ b.e)))) (hp S (a.e + b.e))) (dv S a) := la
  have eb : S.r (S.mul (zv S (zmul b.m (zofNat (2 ^ a.e)))) (hp S (a.e + b.e))) (dv S b) :=
    S.trans (S.mul_congr (S.refl _) hb) lb
  exact S.le_respects ea eb h2

/-! ## §6. Outward rounding to `P` bits -/

/-- `&&` split by cases (the `simp` lemma `Bool.and_eq_true` rewrites an `↔` and carries `propext`). -/
theorem and_true_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact ⟨rfl, rfl⟩

def P : Nat := 62
/-- How many bits to drop: never more than the exponent, never below `P` significant bits. -/
def dropK (d : D) : Nat := Nat.min d.e ((Nat.max d.m.p d.m.n).log2 - P)
/-- `⌊m / 2ᵏ⌋` and `⌈m / 2ᵏ⌉` for a normalised `m` (computed any way; checked below). -/
def qdn (z : BZ) (k : Nat) : BZ := if z.n == 0 then ⟨z.p / 2 ^ k, 0⟩ else ⟨0, (z.n + 2 ^ k - 1) / 2 ^ k⟩
def qup (z : BZ) (k : Nat) : BZ := if z.n == 0 then ⟨(z.p + 2 ^ k - 1) / 2 ^ k, 0⟩ else ⟨0, z.n / 2 ^ k⟩

/-- Round down: `⟨q, e − k⟩` with `q·2ᵏ ≤ m` CHECKED; otherwise the value unchanged. -/
def rdn (d : D) : D :=
  let z := znorm d.m
  let k := dropK ⟨z, d.e⟩
  let q := qdn z k
  if zle (zmul q (zofNat (2 ^ k))) z && Nat.beq ((d.e - k) + k) d.e then ⟨q, d.e - k⟩ else d
/-- Round up: `⟨q, e − k⟩` with `m ≤ q·2ᵏ` CHECKED. -/
def rup (d : D) : D :=
  let z := znorm d.m
  let k := dropK ⟨z, d.e⟩
  let q := qup z k
  if zle z (zmul q (zofNat (2 ^ k))) && Nat.beq ((d.e - k) + k) d.e then ⟨q, d.e - k⟩ else d

/-- The value of `⟨q·2ᵏ, e⟩` is that of `⟨q, e − k⟩` when `(e − k) + k = e`. -/
theorem dv_shift {q : BZ} {k e : Nat} (g : (e - k) + k = e) :
    S.r (dv S ⟨zmul q (zofNat (2 ^ k)), e⟩) (dv S ⟨q, e - k⟩) := by
  have l := dv_lift S ⟨q, e - k⟩ k
  have he : S.r (hp S e) (hp S ((e - k) + k)) := by rw [g]; exact S.refl _
  exact S.trans (S.mul_congr (S.refl _) he) l

theorem rdn_le (d : D) : S.le (dv S (rdn d)) (dv S d) := by
  unfold rdn
  simp only []
  split
  · next h =>
    have hh := and_true_split h
    have g := Nat.eq_of_beq_eq_true hh.2
    have c := le_mul_right S (zle_sound S hh.1) (hp_nonneg S d.e)
    have e1 := dv_shift S (q := qdn (znorm d.m) (dropK ⟨znorm d.m, d.e⟩)) g
    have e2 : S.r (S.mul (zv S (znorm d.m)) (hp S d.e)) (dv S d) := S.mul_congr (zv_norm S d.m) (S.refl _)
    exact S.le_respects e1 e2 c
  · exact S.le_refl _

theorem le_rup (d : D) : S.le (dv S d) (dv S (rup d)) := by
  unfold rup
  simp only []
  split
  · next h =>
    have hh := and_true_split h
    have g := Nat.eq_of_beq_eq_true hh.2
    have c := le_mul_right S (zle_sound S hh.1) (hp_nonneg S d.e)
    have e1 := dv_shift S (q := qup (znorm d.m) (dropK ⟨znorm d.m, d.e⟩)) g
    have e2 : S.r (S.mul (zv S (znorm d.m)) (hp S d.e)) (dv S d) := S.mul_congr (zv_norm S d.m) (S.refl _)
    exact S.le_respects e2 e1 c
  · exact S.le_refl _


/-! ## Rounding at a chosen precision (for long chains of squarings, where errors double each step) -/

def dropKP (q : Nat) (d : D) : Nat := Nat.min d.e ((Nat.max d.m.p d.m.n).log2 - q)
def rdnP (q : Nat) (d : D) : D :=
  let z := znorm d.m
  let k := dropKP q ⟨z, d.e⟩
  let t := qdn z k
  if zle (zmul t (zofNat (2 ^ k))) z && Nat.beq ((d.e - k) + k) d.e then ⟨t, d.e - k⟩ else d
def rupP (q : Nat) (d : D) : D :=
  let z := znorm d.m
  let k := dropKP q ⟨z, d.e⟩
  let t := qup z k
  if zle z (zmul t (zofNat (2 ^ k))) && Nat.beq ((d.e - k) + k) d.e then ⟨t, d.e - k⟩ else d

theorem rdnP_le (q : Nat) (d : D) : S.le (dv S (rdnP q d)) (dv S d) := by
  unfold rdnP
  simp only []
  split
  · next h =>
    have hh := and_true_split h
    have g := Nat.eq_of_beq_eq_true hh.2
    have c := le_mul_right S (zle_sound S hh.1) (hp_nonneg S d.e)
    have e1 := dv_shift S (q := qdn (znorm d.m) (dropKP q ⟨znorm d.m, d.e⟩)) g
    have e2 : S.r (S.mul (zv S (znorm d.m)) (hp S d.e)) (dv S d) := S.mul_congr (zv_norm S d.m) (S.refl _)
    exact S.le_respects e1 e2 c
  · exact S.le_refl _

theorem le_rupP (q : Nat) (d : D) : S.le (dv S d) (dv S (rupP q d)) := by
  unfold rupP
  simp only []
  split
  · next h =>
    have hh := and_true_split h
    have g := Nat.eq_of_beq_eq_true hh.2
    have c := le_mul_right S (zle_sound S hh.1) (hp_nonneg S d.e)
    have e1 := dv_shift S (q := qup (znorm d.m) (dropKP q ⟨znorm d.m, d.e⟩)) g
    have e2 : S.r (S.mul (zv S (znorm d.m)) (hp S d.e)) (dv S d) := S.mul_congr (zv_norm S d.m) (S.refl _)
    exact S.le_respects e2 e1 c
  · exact S.le_refl _

/-! ## Rounding to 62 significant bits AND at most 80 fractional bits (tiny values snap to a coarse grid) -/

def dropKA (d : D) : Nat := Nat.min d.e (Nat.max ((Nat.max d.m.p d.m.n).log2 - 62) (d.e - 80))
def rdnA (d : D) : D :=
  let z := znorm d.m
  let k := dropKA ⟨z, d.e⟩
  let t := qdn z k
  if zle (zmul t (zofNat (2 ^ k))) z && Nat.beq ((d.e - k) + k) d.e then ⟨t, d.e - k⟩ else d
def rupA (d : D) : D :=
  let z := znorm d.m
  let k := dropKA ⟨z, d.e⟩
  let t := qup z k
  if zle z (zmul t (zofNat (2 ^ k))) && Nat.beq ((d.e - k) + k) d.e then ⟨t, d.e - k⟩ else d

theorem rdnA_le (d : D) : S.le (dv S (rdnA d)) (dv S d) := by
  unfold rdnA
  simp only []
  split
  · next h =>
    have hh := and_true_split h
    have g := Nat.eq_of_beq_eq_true hh.2
    have c := le_mul_right S (zle_sound S hh.1) (hp_nonneg S d.e)
    have e1 := dv_shift S (q := qdn (znorm d.m) (dropKA ⟨znorm d.m, d.e⟩)) g
    have e2 : S.r (S.mul (zv S (znorm d.m)) (hp S d.e)) (dv S d) := S.mul_congr (zv_norm S d.m) (S.refl _)
    exact S.le_respects e1 e2 c
  · exact S.le_refl _

theorem le_rupA (d : D) : S.le (dv S d) (dv S (rupA d)) := by
  unfold rupA
  simp only []
  split
  · next h =>
    have hh := and_true_split h
    have g := Nat.eq_of_beq_eq_true hh.2
    have c := le_mul_right S (zle_sound S hh.1) (hp_nonneg S d.e)
    have e1 := dv_shift S (q := qup (znorm d.m) (dropKA ⟨znorm d.m, d.e⟩)) g
    have e2 : S.r (S.mul (zv S (znorm d.m)) (hp S d.e)) (dv S d) := S.mul_congr (zv_norm S d.m) (S.refl _)
    exact S.le_respects e2 e1 c
  · exact S.le_refl _
end ZNumBin

/-! The kernel on real-size numbers: `3⁸⁰ · ½⁷` rounded both ways encloses the value, with fewer bits. -/
example : ZNumBin.dle (ZNumBin.rdn ⟨⟨3 ^ 80, 0⟩, 7⟩) ⟨⟨3 ^ 80, 0⟩, 7⟩ = true ∧
          ZNumBin.dle ⟨⟨3 ^ 80, 0⟩, 7⟩ (ZNumBin.rup ⟨⟨3 ^ 80, 0⟩, 7⟩) = true := by decide

#print axioms ZNumBin.nI_le_of_ble
#print axioms ZNumBin.le_mul_right
#print axioms ZNumBin.half_nonneg
#print axioms ZNumBin.zv_add
#print axioms ZNumBin.zv_neg
#print axioms ZNumBin.zv_mul
#print axioms ZNumBin.zv_norm
#print axioms ZNumBin.zle_sound
#print axioms ZNumBin.hp_add
#print axioms ZNumBin.two_hp
#print axioms ZNumBin.dv_neg
#print axioms ZNumBin.dv_mul
#print axioms ZNumBin.dv_lift
#print axioms ZNumBin.dv_add
#print axioms ZNumBin.dle_sound
#print axioms ZNumBin.rdn_le
#print axioms ZNumBin.le_rup
#print axioms ZNumBin.rdnP_le
#print axioms ZNumBin.le_rupP
#print axioms ZNumBin.rdnA_le
#print axioms ZNumBin.le_rupA
