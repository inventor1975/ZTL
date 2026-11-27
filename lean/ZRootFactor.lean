import ZField

/-!
# ZRootFactor — a root of (x − r)^m·q where q has none is r. Zero axioms.

The last step of `inventory/zsturm_lean_bridge.py` for rational roots: the kernel checks p = (x − r)^m·q (`identX`)
and that q has no root in a gap (`ZNone.chk`); this file closes the argument the bridge stated in words —
"a product is 0 only if a factor is" — constructively, in every constructive ordered field `CF`:
if p ≈ a^m·q, p ≈ 0, and q ≈ 0 is impossible, then a ≈ 0 (`root_factor`). A apart from 0 would make a^m apart from 0
(`ap_pow`), hence invertible, hence q ≈ 0; so a is not apart from 0, and apartness is tight.
-/

namespace ZRootFactor
open VR.CSR ZNumBin ZField

variable {α : Type} (S : CF α)

def pw (x : α) : Nat → α
  | 0 => S.one
  | n + 1 => S.mul x (pw x n)

theorem ap_mul2 {a b : α} (ha : ap S a) (hb : ap S b) : ap S (S.mul a b) := by
  cases ha with
  | inl pa => cases hb with
    | inl pb => exact Or.inl (S.pos_mul pa pb)
    | inr nb => exact Or.inr (S.pos_congr (by cr_ring S.toCR) (S.pos_mul pa nb))
  | inr na => cases hb with
    | inl pb => exact Or.inr (S.pos_congr (by cr_ring S.toCR) (S.pos_mul na pb))
    | inr nb => exact Or.inl (S.pos_congr (by cr_ring S.toCR) (S.pos_mul na nb))

theorem ap_pow {a : α} (ha : ap S a) : ∀ m, ap S (pw S a m)
  | 0 => Or.inl (pos_one S)
  | m + 1 => ap_mul2 S ha (ap_pow ha m)

/-- **THE FACTOR.** p ≈ a^m·q, p ≈ 0, and q has no zero here ⇒ a ≈ 0. -/
theorem root_factor (a q p : α) (m : Nat) (hid : S.r p (S.mul (pw S a m) q)) (hp : S.r p S.zero)
    (hq : S.r q S.zero → False) : S.r a S.zero := by
  apply S.ap_tight
  intro ha
  obtain ⟨c, hc⟩ := S.inv (ap_pow S ha m)
  apply hq
  -- q ≈ (a^m·c)·q ≈ c·(a^m·q) ≈ c·p ≈ c·0 ≈ 0
  have e1 : S.r q (S.mul (S.mul (pw S a m) c) q) :=
    S.trans (S.symm (S.one_mul q)) (S.mul_congr (S.symm hc) (S.refl q))
  have e2 : S.r (S.mul (S.mul (pw S a m) c) q) (S.mul c (S.mul (pw S a m) q)) := by cr_ring S.toCR
  have e3 : S.r (S.mul c (S.mul (pw S a m) q)) (S.mul c S.zero) :=
    S.mul_congr (S.refl c) (S.trans (S.symm hid) hp)
  exact S.trans e1 (S.trans e2 (S.trans e3 (CSR.mul_zero S.toCSR c)))

end ZRootFactor

#print axioms ZRootFactor.ap_mul2
#print axioms ZRootFactor.ap_pow
#print axioms ZRootFactor.root_factor
