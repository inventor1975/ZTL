import QOF

/-!
# Sqrt2 — √2 is not a fraction: over the canonical rationals `QOF.QC`, x·x = 2·(y·y) forces y = 0. Zero axioms.
Written with AI (Logik2), 2026-11-28, at Logik1's request (the one premise of his F[√2] as a `ZNet.OF`).

Part 1, the descent on `Nat` (`desc`: m·m = 2·(n·n) → n = 0): parity by recursion (`ev`; `Nat.mod` carries `propext`,
MEASURED), doubling is injective, `Nat.strongRecOn`. Part 2, the bridge: every element of `QC` is an explicit
fraction ±k/(d+1) (`QOF.rep`); clearing denominators by `q_ring` on VR's pre-rationals and reading the one resulting
equation of embedded naturals back into `Nat` (`nI_inj`).
-/

namespace Sqrt2

/-- parity, by recursion (Nat.mod carries `propext`, MEASURED) -/
def ev : Nat → Bool
  | 0 => true
  | n + 1 => !ev n

theorem b_eq_true : ∀ x : Bool, x = (x == true) := by decide
theorem b_not_beq : ∀ x y : Bool, (!(x == y)) = (x == !y) := by decide
theorem b_or_true : ∀ x : Bool, true = (x || true) := by decide
theorem b_or_beq : ∀ x y : Bool, ((x || y) == x) = (x || !y) := by decide
theorem b_or_self : ∀ x : Bool, (x || x) = x := by decide
theorem b_not_true : ∀ x : Bool, (!x) = true → x = false := by decide
theorem b_not_false : ∀ x : Bool, (!x) = false → x = true := by decide
theorem b_beq_self : ∀ x : Bool, (x == x) = true := by decide

theorem ev_add (a : Nat) : ∀ b, ev (a + b) = (ev a == ev b)
  | 0 => b_eq_true (ev a)
  | b + 1 => by
    show (!ev (a + b)) = (ev a == !ev b)
    rw [ev_add a b]; exact b_not_beq _ _

theorem ev_mul (a : Nat) : ∀ b, ev (a * b) = (ev a || ev b)
  | 0 => b_or_true (ev a)
  | b + 1 => by
    show ev (a * b + a) = (ev a || !ev b)
    rw [ev_add, ev_mul a b]; exact b_or_beq _ _

theorem ev_sq (m : Nat) : ev (m * m) = ev m := by rw [ev_mul]; exact b_or_self _

theorem half : ∀ m : Nat, (ev m = true → ∃ c, m = c + c) ∧ (ev m = false → ∃ c, m = c + c + 1)
  | 0 => ⟨fun _ => ⟨0, rfl⟩, fun h => Bool.noConfusion h⟩
  | m + 1 => by
    have ih := half m
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨c, hc⟩ := ih.2 (b_not_true _ h)
      refine ⟨c + 1, ?_⟩
      rw [hc]; exact congrArg (· + 1) (Nat.succ_add c c).symm
    · obtain ⟨c, hc⟩ := ih.1 (b_not_false _ h)
      exact ⟨c, by rw [hc]⟩

theorem dbl_inj : ∀ x y : Nat, x + x = y + y → x = y
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Nat.noConfusion h
  | _ + 1, 0, h => Nat.noConfusion h
  | x + 1, y + 1, h => by
    have h1 : x + 1 + x = y + 1 + y := by injection h
    rw [Nat.succ_add, Nat.succ_add] at h1
    have h2 : x + x = y + y := by injection h1
    rw [dbl_inj x y h2]

theorem sqd (c : Nat) : (c + c) * (c + c) = (c * c + c * c) + (c * c + c * c) := by
  rw [Nat.left_distrib, Nat.mul_comm (c + c) c, Nat.left_distrib]

/-- THE DESCENT: m·m = 2·(n·n) forces n = 0 (no axioms). -/
theorem desc (n : Nat) : ∀ m : Nat, m * m = 2 * (n * n) → n = 0 :=
  Nat.strongRecOn (motive := fun n => ∀ m : Nat, m * m = 2 * (n * n) → n = 0) n (fun n ih m h => by
    have hm : ev m = true := by
      have := congrArg ev h
      rw [ev_sq, ev_mul] at this
      exact this
    obtain ⟨c, hc⟩ := (half m).1 hm
    subst hc
    rw [sqd, Nat.two_mul] at h
    have h2 := dbl_inj _ _ h
    have hn : ev n = true := by
      have := congrArg ev h2
      rw [ev_add, ev_sq, ev_sq] at this
      exact this.symm.trans (b_beq_self _)
    obtain ⟨d, hd⟩ := (half n).1 hn
    subst hd
    cases d with
    | zero => rfl
    | succ d =>
      rw [sqd] at h2
      have h3 : c * c = 2 * ((d + 1) * (d + 1)) := by rw [Nat.two_mul]; exact dbl_inj _ _ h2
      have := ih (d + 1) (Nat.lt_add_of_pos_right (Nat.zero_lt_succ d)) c h3
      exact Nat.noConfusion this)


/-! ## Part 2: from the canonical rationals to the descent -/

open VR VR.Numbers ZExp QOF

/-- a natural number as an integer pair -/
def nI (a : Nat) : IntExpr := IntExpr.mk (O a) VRObj.base

theorem nI_add (a b : Nat) : intEq (nI (a + b)) (iadd (nI a) (nI b)) := by
  show intEq (IntExpr.mk (O (a + b)) VRObj.base) (IntExpr.mk (vadd (O a) (O b)) VRObj.base)
  rw [O_add]; exact intEq_refl _

theorem nI_mul (a b : Nat) : intEq (nI (a * b)) (imul (nI a) (nI b)) := by
  show intEq (IntExpr.mk (O (a * b)) VRObj.base)
    (IntExpr.mk (vmul (O a) (O b)) (vadd VRObj.base (vmul VRObj.base (O b))))
  rw [vmul_zero_left, O_mul]; exact intEq_refl _

theorem nI_inj {a b : Nat} (h : intEq (nI a) (nI b)) : a = b := by
  have h' : vadd (O a) VRObj.base = vadd VRObj.base (O b) := h
  rw [vadd_zero_left] at h'
  have e : O a = O b := h'
  rw [← O_left_inv a, ← O_left_inv b, e]

theorem qofInt_inj {e f : IntExpr} (h : qEq (qofInt e) (qofInt f)) : intEq e f :=
  intEq_trans _ _ _ (intEq_symm _ _ (imul_one e)) (intEq_trans _ _ _ h (imul_one f))

/-- `n ↦ n/1`, multiplicative and additive -/
def qN (a : Nat) : QExpr := qofInt (nI a)
theorem qN_mul (a b : Nat) : qEq (qN (a * b)) (qmul (qN a) (qN b)) :=
  qEq_trans (qofInt_respects (nI_mul a b)) (qofInt_mul _ _)
theorem qN_add (a b : Nat) : qEq (qN (a + b)) (qadd (qN a) (qN b)) :=
  qEq_trans (qofInt_respects (nI_add a b)) (qofInt_add _ _)
theorem qN_one : qEq (qN 1) qone := qEq_refl _
theorem qN_inj {a b : Nat} (h : qEq (qN a) (qN b)) : a = b := nI_inj (qofInt_inj h)

/-- the sign of an item, as an operation on pre-rationals -/
def sgq : Bool → QExpr → QExpr
  | true, q => q
  | false, q => qneg q

theorem sgq_sq (s : Bool) (q : QExpr) : qEq (qmul (sgq s q) (sgq s q)) (qmul q q) := by
  cases s with
  | true => exact qEq_refl _
  | false => show qEq (qmul (qneg q) (qneg q)) (qmul q q); q_ring

/-- clearing the denominator of an explicit fraction: (±k/(d+1))·(d+1) = ±k -/
theorem toQ_cross (i : QSearch.Item) : qEq (qmul (toQ i) (qN (i.1 + 1))) (sgq i.2.2 (qN i.2.1)) := by
  obtain ⟨d, k, s⟩ := i
  cases s with
  | true =>
    show intEq (imul (imul (IntExpr.mk (O k) VRObj.base) (IntExpr.mk (VRObj.succ (O d)) VRObj.base)) oneI)
      (imul (IntExpr.mk (O k) VRObj.base) (imul (IntExpr.mk (VRObj.succ (O d)) VRObj.base) oneI))
    exact intEq_trans _ _ _ (imul_one _) (intEq_symm _ _ (imul_congr_right (imul_one _)))
  | false =>
    show intEq (imul (imul (IntExpr.mk VRObj.base (O k)) (IntExpr.mk (VRObj.succ (O d)) VRObj.base)) oneI)
      (imul (IntExpr.mk VRObj.base (O k)) (imul (IntExpr.mk (VRObj.succ (O d)) VRObj.base) oneI))
    exact intEq_trans _ _ _ (imul_one _) (intEq_symm _ _ (imul_congr_right (imul_one _)))

theorem mul_succ_zero {a b : Nat} (h : a * (b + 1) = 0) : a = 0 := by
  cases a with
  | zero => rfl
  | succ c => exact Nat.noConfusion h

/-- THE THEOREM: no canonical rational squares to twice a nonzero square — √2 is not in `QC`. -/
theorem no_sqrt2 : ∀ x y : QOF.QC, qOF.mul x x = qOF.mul (qOF.add qOF.one qOF.one) (qOF.mul y y) → y = qOF.zero := by
  intro x y h
  obtain ⟨⟨dx, kx, sx⟩, hx⟩ := rep x
  obtain ⟨⟨dy, ky, sy⟩, hy⟩ := rep y
  -- the equation on pre-rationals
  have two : qEq (mk' (qadd (mk' qone).1 (mk' qone).1)).1 (qadd qone qone) :=
    qEq_trans (valC _) (qadd_respects (valC qone) (valC qone))
  have H : qEq (qmul x.1 x.1) (qmul (qadd qone qone) (qmul y.1 y.1)) :=
    qEq_trans (qEq_symm (valC _)) (qEq_trans (valE h) (qEq_trans (valC _) (qmul_respects two (valC _))))
  rw [hx, hy] at H
  have cx := toQ_cross (dx, kx, sx)
  have cy := toQ_cross (dy, ky, sy)
  -- abbreviations: X Y the fractions, A = kx, B = dx+1, C = ky, D = dy+1 (as n/1)
  generalize toQ (dx, kx, sx) = X at H cx
  generalize toQ (dy, ky, sy) = Y at H cy
  have sx2 := sgq_sq sx (qN kx)
  have sy2 := sgq_sq sy (qN ky)
  generalize sgq sx (qN kx) = SX at cx sx2
  generalize sgq sy (qN ky) = SY at cy sy2
  -- (X·B)² (D²) = 2 (Y·D)² (B²)  ⇒  A²D² = 2·C²B², with A = kx, B = dx+1, C = ky, D = dy+1 (as n/1)
  have k1 : qEq (qmul (qmul (qmul X (qN (dx + 1))) (qmul X (qN (dx + 1)))) (qmul (qN (dy + 1)) (qN (dy + 1))))
      (qmul (qmul X X) (qmul (qmul (qN (dx + 1)) (qN (dx + 1))) (qmul (qN (dy + 1)) (qN (dy + 1))))) := by q_ring
  have k2 : qEq (qmul (qadd qone qone) (qmul (qmul (qmul Y (qN (dy + 1))) (qmul Y (qN (dy + 1)))) (qmul (qN (dx + 1)) (qN (dx + 1)))))
      (qmul (qmul (qadd qone qone) (qmul Y Y)) (qmul (qmul (qN (dx + 1)) (qN (dx + 1))) (qmul (qN (dy + 1)) (qN (dy + 1))))) := by q_ring
  have L : qEq (qmul (qmul (qN kx) (qN kx)) (qmul (qN (dy + 1)) (qN (dy + 1))))
      (qmul (qadd qone qone) (qmul (qmul (qN ky) (qN ky)) (qmul (qN (dx + 1)) (qN (dx + 1))))) := by
    refine qEq_trans (qmul_respects (qEq_symm sx2) (qEq_refl _)) ?_
    refine qEq_trans (qmul_respects (qmul_respects (qEq_symm cx) (qEq_symm cx)) (qEq_refl _)) ?_
    refine qEq_trans k1 ?_
    refine qEq_trans (qmul_respects H (qEq_refl _)) ?_
    refine qEq_trans (qEq_symm k2) ?_
    refine qEq_trans (qmul_respects (qEq_refl _) (qmul_respects (qmul_respects cy cy) (qEq_refl _))) ?_
    exact qmul_respects (qEq_refl _) (qmul_respects sy2 (qEq_refl _))
  -- read back into Nat: m = kx·(dy+1), n = ky·(dx+1), m·m = 2·(n·n)
  have em : qEq (qN ((kx * (dy + 1)) * (kx * (dy + 1)))) (qmul (qmul (qN kx) (qN kx)) (qmul (qN (dy + 1)) (qN (dy + 1)))) := by
    refine qEq_trans (qN_mul _ _) ?_
    refine qEq_trans (qmul_respects (qN_mul _ _) (qN_mul _ _)) ?_
    q_ring
  have en : qEq (qN (2 * ((ky * (dx + 1)) * (ky * (dx + 1)))))
      (qmul (qadd qone qone) (qmul (qmul (qN ky) (qN ky)) (qmul (qN (dx + 1)) (qN (dx + 1))))) := by
    refine qEq_trans (qN_mul _ _) ?_
    refine qEq_trans (qmul_respects (qN_add 1 1) (qEq_trans (qN_mul _ _) (qmul_respects (qN_mul _ _) (qN_mul _ _)))) ?_
    refine qEq_trans (qmul_respects (qadd_respects qN_one qN_one) (qEq_refl _)) ?_
    q_ring
  have nat_eq := qN_inj (qEq_trans em (qEq_trans L (qEq_symm en)))
  have n0 := desc (ky * (dx + 1)) (kx * (dy + 1)) nat_eq
  have ky0 : ky = 0 := mul_succ_zero n0
  subst ky0
  -- so y is 0
  have hy0 : qEq y.1 qzero := by
    rw [hy]
    exact (qEq_zero_iff _).mpr (by cases sy <;> exact intEq_refl _)
  exact eqC (qEq_trans hy0 (qEq_symm (valC qzero)))

end Sqrt2

#print axioms Sqrt2.desc
#print axioms Sqrt2.no_sqrt2
