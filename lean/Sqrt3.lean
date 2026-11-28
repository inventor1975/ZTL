import Sqrt2

/-!
# Sqrt3 — √3 is not a fraction: over the canonical rationals `QOF.QC`, x·x = 3·(y·y) forces y = 0. Zero axioms.
Written with AI (Logik2), 2026-11-28, at Logik1's request (the one premise of the instance Q(√3) of his QZ19).

Part 1, the descent on `Nat` (`desc3`: m·m = 3·(n·n) → n = 0): the residue mod 3 by recursion (`r3`, three values;
`Nat.mod` carries `propext`, and so do `omega`, `Nat.mul_assoc` and `Nat.right_distrib` here — MEASURED 2026-11-28), a square is
0 mod 3 only if its root is, `Nat.eq_of_mul_eq_mul_left` (no axioms), `Nat.strongRecOn`. Part 2, the bridge: as in
`Sqrt2.no_sqrt2` (its helpers are reused), with 1 + 1 + 1 in place of 1 + 1.
-/

namespace Sqrt3
open Sqrt2

/-- a residue mod 3 -/
inductive R3 | z | o | t

def nx : R3 → R3
  | .z => .o | .o => .t | .t => .z
def add3 : R3 → R3 → R3
  | .z, y => y | .o, y => nx y | .t, y => nx (nx y)
def mul3 : R3 → R3 → R3
  | .z, _ => .z | .o, y => y | .t, y => add3 y y

/-- the residue mod 3, by recursion -/
def r3 : Nat → R3
  | 0 => .z
  | n + 1 => nx (r3 n)

theorem add3_nx : ∀ x y : R3, add3 x (nx y) = nx (add3 x y) := by
  intro x y; cases x <;> cases y <;> rfl
theorem mul3_nx : ∀ x y : R3, add3 (mul3 x y) x = mul3 x (nx y) := by
  intro x y; cases x <;> cases y <;> rfl
theorem add3_z : ∀ x : R3, add3 x .z = x := by
  intro x; cases x <;> rfl
theorem mul3_z : ∀ x : R3, mul3 x .z = .z := by
  intro x; cases x <;> rfl
theorem sq3 : ∀ x : R3, mul3 x x = .z → x = .z := by
  intro x h; cases x with
  | z => rfl
  | o => exact R3.noConfusion h
  | t => exact R3.noConfusion h

theorem r3_add (a : Nat) : ∀ b, r3 (a + b) = add3 (r3 a) (r3 b)
  | 0 => (add3_z _).symm
  | b + 1 => by
    show nx (r3 (a + b)) = add3 (r3 a) (nx (r3 b))
    rw [r3_add a b, add3_nx]

theorem r3_mul (a : Nat) : ∀ b, r3 (a * b) = mul3 (r3 a) (r3 b)
  | 0 => (mul3_z _).symm
  | b + 1 => by
    show r3 (a * b + a) = mul3 (r3 a) (nx (r3 b))
    rw [r3_add, r3_mul a b, mul3_nx]

/-- a multiple of 3 is 0 mod 3 -/
theorem r3_three (k : Nat) : r3 (3 * k) = .z := by
  rw [r3_mul]; rfl

/-- the three classes -/
theorem thirds : ∀ m : Nat, (r3 m = .z → ∃ c, m = 3 * c) ∧ (r3 m = .o → ∃ c, m = 3 * c + 1) ∧
    (r3 m = .t → ∃ c, m = 3 * c + 2)
  | 0 => ⟨fun _ => ⟨0, rfl⟩, fun h => R3.noConfusion h, fun h => R3.noConfusion h⟩
  | m + 1 => by
    have ih := thirds m
    have hs : r3 (m + 1) = nx (r3 m) := rfl
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have hm : r3 m = .t := by
        rw [hs] at h; revert h; cases r3 m <;> intro h <;> first | rfl | exact R3.noConfusion h
      obtain ⟨c, hc⟩ := ih.2.2 hm
      exact ⟨c + 1, by rw [hc]; rfl⟩
    · have hm : r3 m = .z := by
        rw [hs] at h; revert h; cases r3 m <;> intro h <;> first | rfl | exact R3.noConfusion h
      obtain ⟨c, hc⟩ := ih.1 hm
      exact ⟨c, by rw [hc]⟩
    · have hm : r3 m = .o := by
        rw [hs] at h; revert h; cases r3 m <;> intro h <;> first | rfl | exact R3.noConfusion h
      obtain ⟨c, hc⟩ := ih.2.1 hm
      exact ⟨c, by rw [hc]⟩

/-- if m·m is a multiple of 3, so is m -/
theorem root3 {m k : Nat} (h : m * m = 3 * k) : ∃ c, m = 3 * c := by
  have e := congrArg r3 h
  rw [r3_mul, r3_three] at e
  exact (thirds m).1 (sq3 _ e)

/-- associativity by recursion (`Nat.mul_assoc` carries `propext` in this toolchain, MEASURED 2026-11-28) -/
theorem massoc (a b : Nat) : ∀ c, a * b * c = a * (b * c)
  | 0 => rfl
  | c + 1 => by
    show a * b * c + a * b = a * (b * c + b)
    rw [massoc a b c, Nat.left_distrib]

theorem sq_three (c : Nat) : (3 * c) * (3 * c) = 3 * (3 * (c * c)) :=
  (massoc 3 c (3 * c)).trans (congrArg (3 * ·)
    (((massoc c 3 c).symm.trans (congrArg (· * c) (Nat.mul_comm c 3))).trans (massoc 3 c c)))

theorem three_cancel {x y : Nat} (h : 3 * x = 3 * y) : x = y := Nat.eq_of_mul_eq_mul_left (by decide) h

theorem lt_three (d : Nat) : d + 1 < 3 * (d + 1) :=
  Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.le_succ_of_le (Nat.le_mul_of_pos_left d (by decide : 0 < 3))))

/-- THE DESCENT: m·m = 3·(n·n) forces n = 0 (no axioms). -/
theorem desc3 (n : Nat) : ∀ m : Nat, m * m = 3 * (n * n) → n = 0 :=
  Nat.strongRecOn (motive := fun n => ∀ m : Nat, m * m = 3 * (n * n) → n = 0) n (fun n ih m h => by
    obtain ⟨c, hc⟩ := root3 h
    subst hc
    rw [sq_three] at h
    have h2 : 3 * (c * c) = n * n := three_cancel h
    obtain ⟨d, hd⟩ := root3 h2.symm
    subst hd
    cases d with
    | zero => rfl
    | succ d =>
      rw [sq_three] at h2
      have h3 : c * c = 3 * ((d + 1) * (d + 1)) := three_cancel h2
      have := ih (d + 1) (lt_three d) c h3
      exact Nat.noConfusion this)

/-! ## Part 2: from the canonical rationals to the descent -/

open VR VR.Numbers ZExp QOF

theorem qN_three : qEq (qN 3) (qadd (qadd qone qone) qone) :=
  qEq_trans (qN_add 2 1) (qadd_respects (qEq_trans (qN_add 1 1) (qadd_respects qN_one qN_one)) qN_one)

/-- THE THEOREM: no canonical rational squares to three times a nonzero square — √3 is not in `QC`. -/
theorem no_sqrt3 : ∀ x y : QOF.QC,
    qOF.mul x x = qOF.mul (qOF.add (qOF.add qOF.one qOF.one) qOF.one) (qOF.mul y y) → y = qOF.zero := by
  intro x y h
  obtain ⟨⟨dx, kx, sx⟩, hx⟩ := rep x
  obtain ⟨⟨dy, ky, sy⟩, hy⟩ := rep y
  -- the equation on pre-rationals
  have two : qEq (mk' (qadd (mk' qone).1 (mk' qone).1)).1 (qadd qone qone) :=
    qEq_trans (valC _) (qadd_respects (valC qone) (valC qone))
  have three : qEq (mk' (qadd (mk' (qadd (mk' qone).1 (mk' qone).1)).1 (mk' qone).1)).1 (qadd (qadd qone qone) qone) :=
    qEq_trans (valC _) (qadd_respects two (valC qone))
  have H : qEq (qmul x.1 x.1) (qmul (qadd (qadd qone qone) qone) (qmul y.1 y.1)) :=
    qEq_trans (qEq_symm (valC _)) (qEq_trans (valE h) (qEq_trans (valC _) (qmul_respects three (valC _))))
  rw [hx, hy] at H
  have cx := toQ_cross (dx, kx, sx)
  have cy := toQ_cross (dy, ky, sy)
  generalize toQ (dx, kx, sx) = X at H cx
  generalize toQ (dy, ky, sy) = Y at H cy
  have sx2 := sgq_sq sx (qN kx)
  have sy2 := sgq_sq sy (qN ky)
  generalize sgq sx (qN kx) = SX at cx sx2
  generalize sgq sy (qN ky) = SY at cy sy2
  -- (X·B)² (D²) = 3 (Y·D)² (B²)  ⇒  A²D² = 3·C²B², with A = kx, B = dx+1, C = ky, D = dy+1 (as n/1)
  have k1 : qEq (qmul (qmul (qmul X (qN (dx + 1))) (qmul X (qN (dx + 1)))) (qmul (qN (dy + 1)) (qN (dy + 1))))
      (qmul (qmul X X) (qmul (qmul (qN (dx + 1)) (qN (dx + 1))) (qmul (qN (dy + 1)) (qN (dy + 1))))) := by q_ring
  have k2 : qEq (qmul (qadd (qadd qone qone) qone) (qmul (qmul (qmul Y (qN (dy + 1))) (qmul Y (qN (dy + 1)))) (qmul (qN (dx + 1)) (qN (dx + 1)))))
      (qmul (qmul (qadd (qadd qone qone) qone) (qmul Y Y)) (qmul (qmul (qN (dx + 1)) (qN (dx + 1))) (qmul (qN (dy + 1)) (qN (dy + 1))))) := by q_ring
  have L : qEq (qmul (qmul (qN kx) (qN kx)) (qmul (qN (dy + 1)) (qN (dy + 1))))
      (qmul (qadd (qadd qone qone) qone) (qmul (qmul (qN ky) (qN ky)) (qmul (qN (dx + 1)) (qN (dx + 1))))) := by
    refine qEq_trans (qmul_respects (qEq_symm sx2) (qEq_refl _)) ?_
    refine qEq_trans (qmul_respects (qmul_respects (qEq_symm cx) (qEq_symm cx)) (qEq_refl _)) ?_
    refine qEq_trans k1 ?_
    refine qEq_trans (qmul_respects H (qEq_refl _)) ?_
    refine qEq_trans (qEq_symm k2) ?_
    refine qEq_trans (qmul_respects (qEq_refl _) (qmul_respects (qmul_respects cy cy) (qEq_refl _))) ?_
    exact qmul_respects (qEq_refl _) (qmul_respects sy2 (qEq_refl _))
  -- read back into Nat: m = kx·(dy+1), n = ky·(dx+1), m·m = 3·(n·n)
  have em : qEq (qN ((kx * (dy + 1)) * (kx * (dy + 1)))) (qmul (qmul (qN kx) (qN kx)) (qmul (qN (dy + 1)) (qN (dy + 1)))) := by
    refine qEq_trans (qN_mul _ _) ?_
    refine qEq_trans (qmul_respects (qN_mul _ _) (qN_mul _ _)) ?_
    q_ring
  have en : qEq (qN (3 * ((ky * (dx + 1)) * (ky * (dx + 1)))))
      (qmul (qadd (qadd qone qone) qone) (qmul (qmul (qN ky) (qN ky)) (qmul (qN (dx + 1)) (qN (dx + 1))))) := by
    refine qEq_trans (qN_mul _ _) ?_
    refine qEq_trans (qmul_respects qN_three (qEq_trans (qN_mul _ _) (qmul_respects (qN_mul _ _) (qN_mul _ _)))) ?_
    q_ring
  have nat_eq := qN_inj (qEq_trans em (qEq_trans L (qEq_symm en)))
  have n0 := desc3 (ky * (dx + 1)) (kx * (dy + 1)) nat_eq
  have ky0 : ky = 0 := mul_succ_zero n0
  subst ky0
  have hy0 : qEq y.1 qzero := by
    rw [hy]
    exact (qEq_zero_iff _).mpr (by cases sy <;> exact intEq_refl _)
  exact eqC (qEq_trans hy0 (qEq_symm (valC qzero)))

end Sqrt3

#print axioms Sqrt3.desc3
#print axioms Sqrt3.no_sqrt3
