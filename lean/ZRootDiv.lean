import ZRootExp
import ZRAtan
/-!
# ZRootDiv — roots of laws WITH DIVISION AND `ln` (so fractional powers `xᵏ = exp(k·ln x)`) on VR's continuum.
Zero axioms.

Step 2b of the root programme. `ZRootExp` read the slopes of `/` and `ln` (any `CF`); here the law becomes a
TOTAL function on VR's continuum and its rational oracle converges uniformly.

* TOTALITY BY A CLAMP: `1/y` and `ln y` are partial (they need `y` apart from 0 / `y > 0`). The law reads them at
  `max(y, 2⁻⁶⁴)` (`rcl`), which is positive by construction; the certificate CHECKS that the value reading of
  every denominator and every `ln` argument is `≥ 2⁻⁶⁴` on the box (`posOK`), so on `[a, b]` the clamp changes
  nothing (`rcl_eq`) and the values are values in the sense of `ZXE.Val` (`val_evR`). Only POSITIVE denominators
  are read (a negative one: write `−(a/(−b))`).
* THE ORACLE: `1/y ↦ 1/max(y, 2⁻⁶⁴)` termwise (Lipschitz `2¹²⁸`), `ln y ↦ lnseq(max(y, 2⁻⁶⁴), n)` — VR's own
  grid answers; uniform convergence by a uniform copy of `ZLn.ln_cauchy` (`ln_unif`).
-/

namespace ZRootDiv
open VR VR.Numbers VR.CSR ZNumBin ZField ZPoly ZIv ZDivIv ZExpLaw ZExpIv ZXE ZRealCF ZExp ZRealExp ZLn ZRootExp ZRAtan

/-! ## The clamp -/

/-- The larger of two rationals (decided by `qle`). -/
def qmax (a b : QExpr) : QExpr :=
  match qle.decidable a b with
  | .isTrue _ => b
  | .isFalse _ => a

theorem qmax_cases (a b : QExpr) : (qmax a b = b ∧ qle a b) ∨ (qmax a b = a ∧ qle b a) := by
  unfold qmax
  cases qle.decidable a b with
  | isTrue h => exact Or.inl ⟨rfl, h⟩
  | isFalse h =>
      cases qle_total a b with
      | inl h' => exact absurd h' h
      | inr h' => exact Or.inr ⟨rfl, h'⟩

theorem qmax_ge_l (a b : QExpr) : qle a (qmax a b) := by
  rcases qmax_cases a b with ⟨e, h⟩ | ⟨e, _⟩ <;> rw [e]
  · exact h
  · exact qle_refl _

theorem qmax_ge_r (a b : QExpr) : qle b (qmax a b) := by
  rcases qmax_cases a b with ⟨e, _⟩ | ⟨e, h⟩ <;> rw [e]
  · exact qle_refl _
  · exact h

theorem qmax_close {a a' b b' e : QExpr} (ha : qclose a a' e) (hb : qclose b b' e) :
    qclose (qmax a b) (qmax a' b') e := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold qsub at a1 a2 b1 b2
  rcases qmax_cases a b with ⟨e1, h1⟩ | ⟨e1, h1⟩ <;> rcases qmax_cases a' b' with ⟨e2, h2⟩ | ⟨e2, h2⟩ <;>
    rw [e1, e2] <;> (constructor <;> (unfold qsub; rat_linarith))

theorem qmax_congr {a a' b b' : QExpr} (ha : qEq a a') (hb : qEq b b') : qEq (qmax a b) (qmax a' b') := by
  rcases qmax_cases a b with ⟨e1, h1⟩ | ⟨e1, h1⟩ <;> rcases qmax_cases a' b' with ⟨e2, h2⟩ | ⟨e2, h2⟩ <;>
    rw [e1, e2] <;> exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem qmax_le {a b c : QExpr} (ha : qle a c) (hb : qle b c) : qle (qmax a b) c := by
  rcases qmax_cases a b with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
  · exact hb
  · exact ha

/-- The clamp level `2⁻⁶⁴` as a dyadic. -/
def δD : D := ⟨⟨1, 0⟩, 64⟩

theorem qD_delta : qEq (qD δD) (qeps 64) := by
  have e1 := qnat_succ 0
  have e0 := qnat_zero
  have h : qEq (qsub (qnat 1) (qnat 0)) qone := by unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  exact qEq_trans (qmul_respects h (qEq_refl _)) (qone_mul _)

/-- `max(y, 2⁻⁶⁴)`, termwise. -/
def rcl (x : RExpr) : RExpr := ⟨fun n => qmax (x.seq n) (qeps 64), fun k => by
  obtain ⟨N, h⟩ := x.cauchy k
  exact ⟨N, fun m n hm hn => qmax_close (h m n hm hn) (qclose_refl _ _ (qeps_nonneg k))⟩⟩

theorem rcl_pw (x : RExpr) : PosWitness (rcl x) 64 0 := fun _ _ => qmax_ge_r _ _

theorem rcl_pos (x : RExpr) : rlt rzero (rcl x) := (rlt_zero_iff _).mpr ⟨64, 0, rcl_pw x⟩

/-- Above the clamp level the clamp changes nothing. -/
theorem rcl_eq {x : RExpr} (h : rle (dv rOH δD) x) : rEq (rcl x) x := by
  refine rle_antisymm (fun k => ?_) (rle_of_eventually 0 fun n _ => qmax_ge_l _ _)
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have d1 := dv_seq δD n
  have d2 := qD_delta
  have h0 := qeps_nonneg k
  change qle (qsub (qmax (x.seq n) (qeps 64)) (x.seq n)) (qeps k)
  rcases qmax_cases (x.seq n) (qeps 64) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> (unfold qsub at *; rat_linarith)

/-- `1/max(y, 2⁻⁶⁴)` and `ln max(y, 2⁻⁶⁴)`: total on VR's continuum. -/
def rinvT (x : RExpr) : RExpr := rinvPos (rcl x) 64 0 (rcl_pw x)
def rlnT (x : RExpr) : RExpr := rln (rcl x) (rcl_pos x)

/-! ## The law as a total function, and its values -/

/-- (Ring steps are proved over any `CF` and instantiated: `cr_ring` does not see through `rCF`'s fields.) -/
theorem mul_swap {α : Type} (S : CF α) (a b c : α) : S.r (S.mul a (S.mul b c)) (S.mul b (S.mul a c)) := by
  cr_ring S.toCR

/-- The law on VR's continuum (division and `ln` through the clamp). -/
def evR (x : Nat → RExpr) : XE → RExpr
  | .var i => x i
  | .cst c => dv rOH c
  | .add a b => radd (evR x a) (evR x b)
  | .sub a b => radd (evR x a) (rneg (evR x b))
  | .mul a b => rmul (evR x a) (evR x b)
  | .pow a k => powS rOH (evR x a) k
  | .exp a => rexpR (evR x a)
  | .div a b => rmul (evR x a) (rinvT (evR x b))
  | .ln a => rlnT (evR x a)
  | .atan _ => rzero

/-- Every denominator and every `ln` argument reads `≥ 2⁻⁶⁴` on the box. -/
def posOK (B : Box) : XE → Bool
  | .var _ => true
  | .cst _ => true
  | .add a b => posOK B a && posOK B b
  | .sub a b => posOK B a && posOK B b
  | .mul a b => posOK B a && posOK B b
  | .pow a _ => posOK B a
  | .exp a => posOK B a
  | .div a b => posOK B a && posOK B b && optB (ivX B b) (fun V => dle δD V.1)
  | .ln a => posOK B a && optB (ivX B a) (fun V => dle δD V.1)
  | .atan _ => false

theorem above_clamp {B : Box} {x : Nat → RExpr} {e : XE} {v : RExpr} (hx : InBox rCF B x)
    (hv : Val rCF rexpR ratan x e v) (h : optB (ivX B e) (fun V => dle δD V.1) = true) :
    rle (dv rOH δD) v := by
  obtain ⟨V, hV, hδ⟩ := optB_some h
  exact rCF.le_trans (dle_sound rOH hδ) (ivX_sound rCF hx hv V hV).1

/-- **THE TOTAL LAW HAS THE LAW'S VALUES** on the box. -/
theorem val_evR {B : Box} {x : Nat → RExpr} (hx : InBox rCF B x) :
    ∀ e : XE, posOK B e = true → Val rCF rexpR ratan x e (evR x e)
  | .var _, _ => .var (rCF.refl _)
  | .cst _, _ => .cst (rCF.refl _)
  | .add a b, h => .add (val_evR hx a (and2 h).1) (val_evR hx b (and2 h).2) (rCF.refl _)
  | .sub a b, h => .sub (val_evR hx a (and2 h).1) (val_evR hx b (and2 h).2) (rCF.refl _)
  | .mul a b, h => .mul (val_evR hx a (and2 h).1) (val_evR hx b (and2 h).2) (rCF.refl _)
  | .pow a k, h => .pow k (val_evR hx a h) (rCF.refl _)
  | .exp a, h => .exp rExpLaws (val_evR hx a h) (rCF.refl _)
  | .div a b, h => by
      obtain ⟨h12, h3⟩ := and2 h
      obtain ⟨h1, h2⟩ := and2 h12
      have Va := val_evR hx a h1
      have Vb := val_evR hx b h2
      have ceq := rcl_eq (above_clamp hx Vb h3)
      have hpos : rCF.pos (evR x b) := rCF.pos_congr ceq (rcl_pos _)
      have hm := rinvPos_mul (rcl (evR x b)) 64 0 (rcl_pw _)
      refine .div Va Vb (Or.inl hpos) ?_
      show rCF.r (rCF.mul (evR x b) (rCF.mul (evR x a) (rinvT (evR x b)))) (evR x a)
      have r1 : rCF.r (rCF.mul (evR x b) (rCF.mul (evR x a) (rinvT (evR x b))))
          (rCF.mul (evR x a) (rCF.mul (evR x b) (rinvT (evR x b)))) := mul_swap rCF _ _ _
      refine rCF.trans r1 ?_
      refine rCF.trans (rCF.mul_congr (rCF.refl _) (rCF.mul_congr (rCF.symm ceq) (rCF.refl _))) ?_
      exact rCF.trans (rCF.mul_congr (rCF.refl _) hm) (rCF.trans (rCF.mul_comm _ _) (rCF.one_mul _))
  | .ln a, h => by
      obtain ⟨h1, h3⟩ := and2 h
      have Va := val_evR hx a h1
      have ceq := rcl_eq (above_clamp hx Va h3)
      exact .ln rExpLaws Va (rCF.pos_congr ceq (rcl_pos _)) (rCF.trans (rexp_rln (rcl (evR x a)) (rcl_pos _)) ceq)
  | .atan _, h => by cases h


/-! ## The oracle -/

theorem cnt_congr {y y' : QExpr} (h : qEq y y') (n : Nat) : ∀ j, cnt y n j = cnt y' n j
  | 0 => rfl
  | j + 1 => by
      cases qle.decidable (eseq (gpt n (j + 1)) n) y with
      | isTrue t =>
          rw [cnt_true t, cnt_true (qle_trans t (qle_of_qEq h)), cnt_congr h n j]
      | isFalse t =>
          have t' : ¬ qle (eseq (gpt n (j + 1)) n) y' := fun u => t (qle_trans u (qle_of_qEq (qEq_symm h)))
          rw [cnt_false t, cnt_false t', cnt_congr h n j]

theorem lnseq_congr {y y' : QExpr} (h : qEq y y') (n : Nat) : qEq (lnseq y n) (lnseq y' n) := by
  unfold lnseq; rw [cnt_congr h n]; exact qEq_refl _

/-- The `n`-th rational reading, division and `ln` through the clamp. -/
def evqD (n : Nat) (q : Nat → QExpr) : XE → QExpr
  | .var i => q i
  | .cst c => qD c
  | .add a b => qadd (evqD n q a) (evqD n q b)
  | .sub a b => qadd (evqD n q a) (qneg (evqD n q b))
  | .mul a b => qmul (evqD n q a) (evqD n q b)
  | .pow a k => qpw (evqD n q a) k
  | .exp a => eseq (evqD n q a) n
  | .div a b => qmul (evqD n q a) (qinv' (qmax (evqD n q b) (qeps 64)))
  | .ln a => lnseq (qmax (evqD n q a) (qeps 64)) n
  | .atan _ => qzero

theorem evqD_respects (n : Nat) {q q' : Nat → QExpr} (h : ∀ i, qEq (q i) (q' i)) :
    ∀ e : XE, qEq (evqD n q e) (evqD n q' e)
  | .var i => h i
  | .cst _ => qEq_refl _
  | .add a b => qadd_respects (evqD_respects n h a) (evqD_respects n h b)
  | .sub a b => qadd_respects (evqD_respects n h a) (qneg_respects (evqD_respects n h b))
  | .mul a b => qmul_respects (evqD_respects n h a) (evqD_respects n h b)
  | .pow a k => qpw_respects (evqD_respects n h a) k
  | .exp a => ZLn.eseq_respects (evqD_respects n h a) n
  | .div a b => qmul_respects (evqD_respects n h a) (qinv'_respects (qmax_congr (evqD_respects n h b) (qEq_refl _)))
  | .ln a => lnseq_congr (qmax_congr (evqD_respects n h a) (qEq_refl _)) n
  | .atan _ => qEq_refl _

/-- The total law's `n`-th term IS the rational reading at the argument's `n`-th term. -/
theorem evR_seq (x : Nat → RExpr) (n : Nat) : ∀ e : XE, qEq ((evR x e).seq n) (evqD n (fun i => (x i).seq n) e)
  | .var _ => qEq_refl _
  | .cst c => dv_seq c n
  | .add a b => qadd_respects (evR_seq x n a) (evR_seq x n b)
  | .sub a b => qadd_respects (evR_seq x n a) (qneg_respects (evR_seq x n b))
  | .mul a b => qmul_respects (evR_seq x n a) (evR_seq x n b)
  | .pow a k => qEq_trans (powS_seq _ n k) (qpw_respects (evR_seq x n a) k)
  | .exp a => ZLn.eseq_respects (evR_seq x n a) n
  | .div a b => qmul_respects (evR_seq x n a) (qinv'_respects (qmax_congr (evR_seq x n b) (qEq_refl _)))
  | .ln a => lnseq_congr (qmax_congr (evR_seq x n a) (qEq_refl _)) n
  | .atan _ => qEq_refl _

theorem inv_close {u v : QExpr} {k j : Nat} (hu : qle (qeps k) u) (hv : qle (qeps k) v)
    (h : qclose u v (qeps (j + (k + k)))) : qclose (qinv' u) (qinv' v) (qeps j) := by
    obtain ⟨im0, im1⟩ := qinv'_bound (hu)
    obtain ⟨in0, in1⟩ := qinv'_bound (hv)
    have hcm := qmul_inv'_cancel (ne_zero_of_eps_le (hu))
    have hcn := qmul_inv'_cancel (ne_zero_of_eps_le (hv))
    obtain ⟨d1, d2⟩ := h
    -- 1/x_m − 1/x_n ≈ (x_n − x_m)·(1/x_m)·(1/x_n)   (using the two cancellations)
    have hid : qEq (qsub (qinv' (u)) (qinv' (v)))
        (qmul (qsub (v) (u)) (qmul (qinv' (u)) (qinv' (v)))) := by
      have e1 : qEq (qinv' (u)) (qmul (qinv' (u)) (qmul (v) (qinv' (v)))) :=
        qEq_symm (qEq_trans (qmul_respects (qEq_refl _) hcn) (qmul_one _))
      have e2 : qEq (qinv' (v)) (qmul (qinv' (v)) (qmul (u) (qinv' (u)))) :=
        qEq_symm (qEq_trans (qmul_respects (qEq_refl _) hcm) (qmul_one _))
      have e3 : qEq (qsub (qinv' (u)) (qinv' (v)))
          (qsub (qmul (qinv' (u)) (qmul (v) (qinv' (v))))
                (qmul (qinv' (v)) (qmul (u) (qinv' (u))))) := by
        unfold qsub; exact qadd_respects e1 (qneg_respects e2)
      refine qEq_trans e3 ?_
      unfold qsub; rat_ring
    -- the product of the two inverses is between 0 and 2^k·2^k
    have hP : qclose (qmul (qinv' (u)) (qinv' (v))) qzero (qmul (qofInt (pow2 k)) (qofInt (pow2 k))) := by
      have hz1 : qEq (qsub (qinv' (u)) qzero) (qinv' (u)) := by unfold qsub; rat_ring
      have hz2 : qEq (qsub (qinv' (v)) qzero) (qinv' (v)) := by unfold qsub; rat_ring
      have hp := qofInt_le (pow2_nonneg k)
      exact qmul_abs_bound ⟨by rat_linarith, by rat_linarith⟩ ⟨by rat_linarith, by rat_linarith⟩
    have hD : qclose (qsub (v) (u)) qzero (qeps (j + (k + k))) := by
      have hz : qEq (qsub (qsub (v) (u)) qzero) (qsub (v) (u)) := by
        unfold qsub; rat_ring
      have hs : qEq (qsub (v) (u)) (qneg (qsub (u) (v))) := by unfold qsub; rat_ring
      exact ⟨by rat_linarith, by rat_linarith⟩
    have hprod := qmul_abs_bound hD hP
    -- ε_{j+2k} · 2^k · 2^k ≈ ε_{j}
    have hm1 : qEq (qmul (qofInt (pow2 k)) (qeps ((j + k) + k))) (qeps (j + k)) := qpow2_mul_eps k (j + k)
    have hm2 : qEq (qmul (qofInt (pow2 k)) (qeps (j + k))) (qeps j) := qpow2_mul_eps k j
    have hidx : j + (k + k) = (j + k) + k := (Nat.add_assoc j k k).symm
    rw [hidx] at hprod
    have hE : qEq (qmul (qeps ((j + k) + k)) (qmul (qofInt (pow2 k)) (qofInt (pow2 k)))) (qeps j) := by
      calc qmul (qeps ((j + k) + k)) (qmul (qofInt (pow2 k)) (qofInt (pow2 k)))
          ≈q qmul (qofInt (pow2 k)) (qmul (qofInt (pow2 k)) (qeps ((j + k) + k))) := by rat_ring
        _ ≈q qmul (qofInt (pow2 k)) (qeps (j + k)) := qmul_respects (qEq_refl _) hm1
        _ ≈q qeps j := hm2
    obtain ⟨p1, p2⟩ := hprod
    have hz : qEq (qsub (qmul (qsub (v) (u)) (qmul (qinv' (u)) (qinv' (v)))) qzero)
        (qmul (qsub (v) (u)) (qmul (qinv' (u)) (qinv' (v)))) := by
      unfold qsub; rat_ring
    constructor <;> rat_linarith

theorem uc_inv {f : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) : UCo (fun n q => qinv' (qmax (f n q) (qeps 64))) := by
  intro R R0
  obtain ⟨_, _, _, cf⟩ := hf R R0
  refine ⟨64, 0, fun n q _ _ => ?_, fun k => ?_⟩
  · obtain ⟨i0, i1⟩ := qinv'_bound (qmax_ge_r (f n q) (qeps 64))
    show qclose (qinv' (qmax (f n q) (qeps 64))) qzero _
    constructor <;> (unfold qsub; rat_linarith)
  · obtain ⟨N, _, h⟩ := cf (k + (64 + 64))
    exact ⟨N, Nat.zero_le _, fun m n q hm hn hq => inv_close (qmax_ge_r _ _) (qmax_ge_r _ _)
      (qmax_close (h m n q hm hn hq) (qclose_refl _ _ (qeps_nonneg _)))⟩

/-- `ln`'s grid answers converge UNIFORMLY over a family with a common modulus and common bounds (a copy of
`ZLn.ln_cauchy` with the family's index carried through — every constant there depends only on the bounds). -/
theorem ln_unif {Q : Type} {P : Q → Prop} {y : Q → Nat → QExpr} {hu : QExpr} {Na : Nat}
    (hNa : ∀ q n, Na ≤ n → P q → qle (qeps 64) (y q n) ∧ qle (y q n) hu)
    (hc : ∀ k, ∃ N, ∀ q m n, N ≤ m → N ≤ n → P q → qclose (y q m) (y q n) (qeps k)) (k : Nat) :
    ∃ N, ∀ q m n, N ≤ m → N ≤ n → P q → qclose (lnseq (y q m) m) (lnseq (y q n) n) (qeps k) := by
  have ylo0 : qlt qzero (qeps 64) := qeps_pos 64
  obtain ⟨N0, hN0⟩ := ln_bracket_unif (yhi := qadd hu qone) ylo0
  obtain ⟨Mr, _, hMr0, _, r1, r2, _, _⟩ := ZSlopeExp.bound4 (qadd (qinv' (qeps 64)) qone) (qadd hu qone) qzero qzero
  have hR1 : qle qone (qadd (qadd Mr qone) qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have hR0 : qle qzero (qadd (qadd Mr qone) qone) := qle_trans (qle_of_qlt qone_pos) hR1
  obtain ⟨C, Ng, hgC⟩ := gap_const hR1
  obtain ⟨Nu, hNu⟩ := E_unif hR0 ((k + 1) + C + 2)
  obtain ⟨Ny, hNy⟩ := hc ((k + 1) + C + 2)
  refine ⟨N0 + Na + Nu + Ny + Ng + k + 0 + 2, fun q m n hm hn hq => ?_⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, _⟩ := le7 N0 Na Nu Ny Ng k 0
  -- both indices are of the form _ + 2
  have two : ∀ p, N0 + Na + Nu + Ny + Ng + k + 0 + 2 ≤ p → ∃ p', p = p' + 2 ∧ N0 + Na + Nu + Ny + Ng + k + 0 ≤ p' := by
    intro p hp
    cases p with
    | zero => exact absurd hp (Nat.not_succ_le_zero _)
    | succ p1 =>
        cases p1 with
        | zero => exact absurd (Nat.le_of_succ_le_succ hp) (Nat.not_succ_le_zero _)
        | succ p' => exact ⟨p', rfl, Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hp)⟩
  obtain ⟨m', rfl, hm'⟩ := two m hm
  obtain ⟨n', rfl, hn'⟩ := two n hn
  have upm : ∀ X, X ≤ N0 + Na + Nu + Ny + Ng + k + 0 → X ≤ m' + 2 :=
    fun X h => Nat.le_trans (Nat.le_trans h hm') (Nat.le_add_right m' 2)
  have upn : ∀ X, X ≤ N0 + Na + Nu + Ny + Ng + k + 0 → X ≤ n' + 2 :=
    fun X h => Nat.le_trans (Nat.le_trans h hn') (Nat.le_add_right n' 2)
  obtain ⟨yml, am2⟩ := hNa q (m' + 2) (upm _ q2) hq
  obtain ⟨ynl, an2⟩ := hNa q (n' + 2) (upn _ q2) hq
  have o1' := qle_of_qlt qone_pos
  have ymh : qle (y q (m' + 2)) (qadd hu qone) := by rat_linarith
  have ynh : qle (y q (n' + 2)) (qadd hu qone) := by rat_linarith
  obtain ⟨bm1, bm2⟩ := hN0 (y q (m' + 2)) yml ymh m' (Nat.le_trans q1 hm')
  obtain ⟨bn1, bn2⟩ := hN0 (y q (n' + 2)) ynl ynh n' (Nat.le_trans q1 hn')
  obtain ⟨rm1, rm2⟩ := ln_range ylo0 yml ymh ⟨bm1, bm2⟩
  obtain ⟨rn1, rn2⟩ := ln_range ylo0 ynl ynh ⟨bn1, bn2⟩
  have bm2' : qle (y q (m' + 2)) (eseq (qadd (lnseq (y q (m' + 2)) (m' + 2)) (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total (y q (m' + 2)) (eseq (qadd (lnseq (y q (m' + 2)) (m' + 2)) (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h bm2
  have bn2' : qle (y q (n' + 2)) (eseq (qadd (lnseq (y q (n' + 2)) (n' + 2)) (qeps (n' + 2))) (n' + 2)) := by
    cases qle_total (y q (n' + 2)) (eseq (qadd (lnseq (y q (n' + 2)) (n' + 2)) (qeps (n' + 2))) (n' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h bn2
  show qclose (lnseq (y q (m' + 2)) (m' + 2)) (lnseq (y q (n' + 2)) (n' + 2)) (qeps k)
  generalize lnseq (y q (m' + 2)) (m' + 2) = Xm at bm1 bm2' rm1 rm2 ⊢
  generalize lnseq (y q (n' + 2)) (n' + 2) = Xn at bn1 bn2' rn1 rn2 ⊢
  obtain ⟨u1, u2⟩ := r1
  obtain ⟨v1, v2⟩ := r2
  unfold qsub at u1 u2 v1 v2
  have o1 := qle_of_qlt qone_pos
  have em1 := ZSlopeExp.eps_le_one (m' + 2)
  have en1 := ZSlopeExp.eps_le_one (n' + 2)
  have em0 := qeps_nonneg (m' + 2)
  have en0 := qeps_nonneg (n' + 2)
  have XmR : qclose Xm qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have XnR : qclose Xn qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have XmeR : qclose (qadd Xm (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have XneR : qclose (qadd Xn (qeps (n' + 2))) qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have gm := hgC (m' + 1) (Nat.le_trans (Nat.le_trans q5 hm') (Nat.le_add_right m' 1))
  have gn := hgC (n' + 1) (Nat.le_trans (Nat.le_trans q5 hn') (Nat.le_add_right n' 1))
  have uA := hNu (qadd Xn (qeps (n' + 2))) XneR (m' + 2) (n' + 2) (upm _ q3) (upn _ q3)
  have uB := hNu (qadd Xm (qeps (m' + 2))) XmeR (n' + 2) (m' + 2) (upn _ q3) (upm _ q3)
  have cyA := hNy q (m' + 2) (n' + 2) (upm _ q4) (upn _ q4) hq
  have cyB := hNy q (n' + 2) (m' + 2) (upn _ q4) (upm _ q4) hq
  -- Δ·g = ε_{(k+1)+C} > 2·ε_{(k+1)+C+2}
  have pm := ZLn.qeps_mul (k + 1) C
  have s1 := qeps_succ_add ((k + 1) + C)
  have s2 := qeps_succ_add ((k + 1) + C + 1)
  have pp := qeps_pos ((k + 1) + C + 2)
  have hΔ : qlt (qadd (qeps ((k + 1) + C + 2)) (qeps ((k + 1) + C + 2))) (qmul (qeps (k + 1)) (qeps C)) := by
    obtain ⟨p0, np⟩ := qlt_iff_le_not_le.mp pp
    exact qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => np (by rat_linarith)⟩
  have gC0 := qle_of_qlt (qeps_pos C)
  have d0 := qeps_nonneg (k + 1)
  have sideA := ln_side hR1 XneR XmR gC0 gm bm1 bn2' uA cyA d0 hΔ
  have sideB := ln_side hR1 XmeR XnR gC0 gn bn1 bm2' uB cyB d0 hΔ
  have ek := qeps_succ_add k
  have em := eps_anti (Nat.le_trans (Nat.succ_le_succ (Nat.le_trans q6 hm')) (Nat.le_succ (m' + 1)) : k + 1 ≤ m' + 2)
  have en := eps_anti (Nat.le_trans (Nat.succ_le_succ (Nat.le_trans q6 hn')) (Nat.le_succ (n' + 1)) : k + 1 ≤ n' + 2)
  constructor <;> (unfold qsub; rat_linarith)

theorem two_of {X p : Nat} (hp : X + 2 ≤ p) : ∃ p', p = p' + 2 ∧ X ≤ p' := by
  cases p with
  | zero => exact absurd hp (Nat.not_succ_le_zero _)
  | succ p1 =>
      cases p1 with
      | zero => exact absurd (Nat.le_of_succ_le_succ hp) (Nat.not_succ_le_zero _)
      | succ p' => exact ⟨p', rfl, Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hp)⟩

/-- The grid answers of a family in `[2⁻⁶⁴, hu]` are bounded from some index on. -/
theorem ln_bound {Q : Type} {P : Q → Prop} {y : Q → Nat → QExpr} {hu : QExpr} {Na : Nat}
    (hNa : ∀ q n, Na ≤ n → P q → qle (qeps 64) (y q n) ∧ qle (y q n) hu) :
    ∃ Rb B1, ∀ q n, B1 ≤ n → P q → qclose (lnseq (y q n) n) qzero Rb := by
  have ylo0 := qeps_pos 64
  obtain ⟨N0, hN0⟩ := ln_bracket_unif (yhi := qadd hu qone) ylo0
  refine ⟨qadd (qadd (qinv' (qeps 64)) qone) (qadd hu qone), (N0 + Na) + 2, fun q n hn hq => ?_⟩
  obtain ⟨n', rfl, hn'⟩ := two_of hn
  obtain ⟨yl, yh⟩ := hNa q (n' + 2) (Nat.le_trans (lB hn') (Nat.le_add_right _ 2)) hq
  have o1 := qle_of_qlt qone_pos
  have yh' : qle (y q (n' + 2)) (qadd hu qone) := by rat_linarith
  obtain ⟨b1, b2⟩ := hN0 _ yl yh' n' (lA hn')
  obtain ⟨r1, r2⟩ := ln_range ylo0 yl yh' ⟨b1, b2⟩
  have i0 := qinv'_nonneg_of_pos ylo0
  have e0 := qeps_nonneg 64
  constructor <;> (unfold qsub; rat_linarith)

theorem uc_ln {f : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) : UCo (fun n q => lnseq (qmax (f n q) (qeps 64)) n) := by
  intro R R0
  obtain ⟨Cf, Bf, bf, cf⟩ := hf R R0
  have p0 : qle qzero (qofInt (pow2 Cf)) := qofInt_le (pow2_nonneg Cf)
  have e1 := ZSlopeExp.eps_le_one 64
  have o1 := qle_of_qlt qone_pos
  have hb : ∀ (q : Nat → QExpr) n, Bf ≤ n → (∀ i, qclose (q i) qzero R) →
      qle (qeps 64) (qmax (f n q) (qeps 64)) ∧ qle (qmax (f n q) (qeps 64)) (qadd (qofInt (pow2 Cf)) qone) := by
    intro q n hn hq
    obtain ⟨f1, _⟩ := bf n q hn hq
    unfold qsub at f1
    exact ⟨qmax_ge_r _ _, qmax_le (by rat_linarith) (by rat_linarith)⟩
  have hc : ∀ k, ∃ N, ∀ (q : Nat → QExpr) m n, N ≤ m → N ≤ n → (∀ i, qclose (q i) qzero R) →
      qclose (qmax (f m q) (qeps 64)) (qmax (f n q) (qeps 64)) (qeps k) := by
    intro k
    obtain ⟨N, _, h⟩ := cf k
    exact ⟨N, fun q m n hm hn hq => qmax_close (h m n q hm hn hq) (qclose_refl _ _ (qeps_nonneg k))⟩
  obtain ⟨Rb, B1, hB⟩ := ln_bound (P := fun (q : Nat → QExpr) => ∀ i, qclose (q i) qzero R) (y := fun q n => qmax (f n q) (qeps 64)) hb
  obtain ⟨C, hC⟩ := qexpr_bound Rb
  refine ⟨C, B1, fun n q hn hq => close_up (hB q n hn hq) hC, fun k => ?_⟩
  obtain ⟨N, hN⟩ := ln_unif (P := fun (q : Nat → QExpr) => ∀ i, qclose (q i) qzero R) (y := fun q n => qmax (f n q) (qeps 64)) hb hc k
  exact ⟨N + B1, Nat.le_add_left _ _, fun m n q hm hn hq => hN q m n (lA hm) (lA hn) hq⟩

/-- **THE ORACLE CONVERGES UNIFORMLY** on bounded sets — for every law, division and `ln` included. -/
theorem uc_evqD : ∀ e : XE, UCo (fun n q => evqD n q e)
  | .var i => uc_var i
  | .cst c => uc_const (qD c)
  | .add a b => uc_add (uc_evqD a) (uc_evqD b)
  | .sub a b => uc_add (uc_evqD a) (uc_neg (uc_evqD b))
  | .mul a b => uc_mul (uc_evqD a) (uc_evqD b)
  | .pow a k => uc_pow (uc_evqD a) k
  | .exp a => uc_exp (uc_evqD a)
  | .div a b => uc_mul (uc_evqD a) (uc_inv (uc_evqD b))
  | .ln a => uc_ln (uc_evqD a)
  | .atan _ => uc_const qzero

/-! ## The root -/

/-- The law as a function on VR's continuum. -/
def FR (e : XE) (x : RExpr) : RExpr := evR (fun _ => x) e

theorem orac_D (e : XE) (a b : D) : ∀ j, ∃ N, ∀ n, N ≤ n → ∀ t : D,
    rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
    ZKron.Bd rCF.toOH (radd (FR e (dv rOH t)) (rneg (rofQ (evqD n (fun _ => qD t) e)))) (hp rOH j) := by
  intro j
  obtain ⟨Ca, hCa⟩ := qexpr_bound (qD a)
  obtain ⟨Cb, hCb⟩ := qexpr_bound (qD b)
  have pa : qle qzero (qofInt (pow2 Ca)) := qofInt_le (pow2_nonneg Ca)
  have pb : qle qzero (qofInt (pow2 Cb)) := qofInt_le (pow2_nonneg Cb)
  have p1 := qle_of_qlt qone_pos
  have R00 : qle qzero (qadd (qadd (qofInt (pow2 Ca)) (qofInt (pow2 Cb))) qone) := by rat_linarith
  obtain ⟨_, _, _, cau⟩ := uc_evqD e _ R00
  obtain ⟨N, _, hN⟩ := cau j
  refine ⟨N, fun n hn t hat htb => ?_⟩
  have tq : qclose (qD t) qzero (qadd (qadd (qofInt (pow2 Ca)) (qofInt (pow2 Cb))) qone) := by
    obtain ⟨N1, h1⟩ := hat 0
    obtain ⟨N2, h2⟩ := htb 0
    have a1 := h1 (N1 + N2) (Nat.le_add_right _ _)
    have a2 := h2 (N1 + N2) (Nat.le_add_left _ _)
    have d1 := dv_seq a (N1 + N2)
    have d2 := dv_seq t (N1 + N2)
    have d3 := dv_seq b (N1 + N2)
    have e0 := qeps_zero
    obtain ⟨ca1, ca2⟩ := hCa
    obtain ⟨cb1, cb2⟩ := hCb
    unfold qsub at a1 a2 ca1 ca2 cb1 cb2
    constructor <;> (unfold qsub; rat_linarith)
  have key : ∀ m, N ≤ m → qclose (evqD m (fun _ => qD t) e) (evqD n (fun _ => qD t) e) (qeps j) :=
    fun m hm => hN m n (fun _ => qD t) hm hn (fun _ => tq)
  show rle (rneg (hp rOH j)) _ ∧ rle _ (hp rOH j)
  constructor
  · refine rle_of_eventually N fun m hm => ?_
    have s1 := evR_seq (fun _ => dv rOH t) m e
    have s2 := evqD_respects m (fun _ => dv_seq t m) e
    have s3 := hp_seq j m
    obtain ⟨k1, k2⟩ := key m hm
    change qle (qneg ((hp rOH j).seq m)) (qadd ((evR (fun _ => dv rOH t) e).seq m) (qneg (evqD n (fun _ => qD t) e)))
    unfold qsub at k1 k2
    rat_linarith
  · refine rle_of_eventually N fun m hm => ?_
    have s1 := evR_seq (fun _ => dv rOH t) m e
    have s2 := evqD_respects m (fun _ => dv_seq t m) e
    have s3 := hp_seq j m
    obtain ⟨k1, k2⟩ := key m hm
    change qle (qadd ((evR (fun _ => dv rOH t) e).seq m) (qneg (evqD n (fun _ => qD t) e))) ((hp rOH j).seq m)
    unfold qsub at k1 k2
    rat_linarith

/-- **THE CERTIFICATE**: denominators and `ln` arguments read `≥ 2⁻⁶⁴` on `[a, b]`; slopes read in `[2⁻ˢ, 2ᶜ]`;
`F(a) ≤ 0 ≤ F(b)` read; width `≤ 2ᴮ`. Checked by the kernel. -/
def chkD (e : XE) (a b : D) (s C B : Nat) : Bool :=
  dle a b && posOK (cB a b) e &&
    optB (slX (cB a b) (fun _ => ZIv.one) e) (fun K => dle ⟨⟨1, 0⟩, s⟩ K.1 && dle K.2 ⟨⟨2 ^ C, 0⟩, 0⟩) &&
    optB (ivX (cB a a) e) (fun K => dle K.2 dz0) &&
    optB (ivX (cB b b) e) (fun K => dle dz0 K.1) &&
    dle (dadd b (dneg a)) ⟨⟨2 ^ B, 0⟩, 0⟩

/-- **A CHECKED SIGN CHANGE OF A LAW WITH `exp`, `ln`, DIVISION (HENCE FRACTIONAL POWERS) GIVES ITS ROOT ON VR's
CONTINUUM — and the only one in `[a, b]`.** -/
theorem law_root (e : XE) (a b : D) (s C B : Nat) (h : chkD e a b s C B = true) :
    ∃ x : RExpr, (rle (dv rOH a) x ∧ rle x (dv rOH b)) ∧ rEq (FR e x) rzero ∧
      ∀ y, rle (dv rOH a) y → rle y (dv rOH b) → rEq (FR e y) rzero → rEq y x := by
  obtain ⟨h5, hW⟩ := and2 h
  obtain ⟨h4, hb'⟩ := and2 h5
  obtain ⟨h3, ha'⟩ := and2 h4
  obtain ⟨h2, hK'⟩ := and2 h3
  obtain ⟨hab, hP⟩ := and2 h2
  obtain ⟨K, hK, hKc⟩ := optB_some hK'
  obtain ⟨hc, hL⟩ := and2 hKc
  obtain ⟨Ka, hKa, ha⟩ := optB_some ha'
  obtain ⟨Kb, hKb, hb⟩ := optB_some hb'
  have hab' := dle_sound rOH hab
  have hV : ∀ x, rle (dv rOH a) x → rle x (dv rOH b) → Val rCF rexpR ratan (fun _ => x) e (FR e x) :=
    fun x h1 h2 => val_evR (inbox_c h1 h2) e hP
  have hM : ZRootAbs.Mono rCF (FR e) (dv rOH a) (dv rOH b) (hp rOH s) (nI rOH (2 ^ C)) :=
    mono_of_val rExpLaws r_slope hV hK
      (rCF.le_respects (ZRootPVR.dv_hp s) (rCF.refl _) (dle_sound rOH hc))
      (rCF.le_respects (rCF.refl _) (ZRoot.dv_nat rCF (2 ^ C)) (dle_sound rOH hL))
  have H : ZRootAbs.Fam (fun _ => FR e) (FR e) (fun n q => evqD n (fun _ => q) e) a b s C B 0 := {
    hab := hab
    mono := fun _ _ => hM
    monoP := hM
    ends := fun _ _ => ⟨lo_val (hV _ (rCF.le_refl _) hab') hKa ha, hi_val (hV _ hab' (rCF.le_refl _)) hKb hb⟩
    conv := fun j => ⟨0, fun _ _ x _ _ => ZKron.bd_congr rCF.toOH (rCF.symm (rCF.add_neg _)) (rCF.refl _)
      ⟨ZRootAbs.neg_le_zero rCF (hp_nonneg rOH j), hp_nonneg rOH j⟩⟩
    orac := orac_D e a b
    wid := hW }
  exact ⟨ZRootAbs.froot H, ZRootAbs.froot_in H, ZRootAbs.froot_is_root H,
    fun y h1 h2 hy => ZRootAbs.froot_unique H ⟨h1, h2⟩ (ZRootAbs.froot_in H) hy (ZRootAbs.froot_is_root H)⟩

/-- **THE CLAMP IS NOT A SUBSTITUTE**: under the certificate, on `[a, b]` the total law's value IS a value of the law
in the sense of `ZXE.Val` — each quotient `v` with `b·v = a`, `b` apart from 0; each `ln` with `exp v = a`, `a > 0`. -/
theorem FR_is_value (e : XE) (a b : D) (s C B : Nat) (h : chkD e a b s C B = true) :
    ∀ x, rle (dv rOH a) x → rle x (dv rOH b) → Val rCF rexpR ratan (fun _ => x) e (FR e x) := by
  obtain ⟨h5, _⟩ := and2 h
  obtain ⟨h4, _⟩ := and2 h5
  obtain ⟨h3, _⟩ := and2 h4
  obtain ⟨h2, _⟩ := and2 h3
  obtain ⟨_, hP⟩ := and2 h2
  exact fun x h1 h2 => val_evR (inbox_c h1 h2) e hP

/-! ## Examples -/

def cD (n : Nat) : D := ⟨⟨n, 0⟩, 0⟩
def half : D := ⟨⟨1, 0⟩, 1⟩
/-- `x − 1/(1 + x)` (the golden section `0.618…`). -/
def goldE : XE := .sub (.var 0) (.div (.cst (cD 1)) (.add (.cst (cD 1)) (.var 0)))
/-- `x + ln x` (the omega constant again, now through `ln`). -/
def omegaL : XE := .add (.var 0) (.ln (.var 0))
/-- `x^{4/5} − 2 = exp((4/5)·ln x) − 2` (a fractional power: `2^{5/4} = 2.378…`). -/
def frac : XE := .sub (.exp (.mul (.div (.cst (cD 4)) (.cst (cD 5))) (.ln (.var 0)))) (.cst (cD 2))

/-- **THE GOLDEN SECTION** `x = 1/(1 + x)` has one root in `[0, 1]` (slopes read in `[1.25, 2]`). -/
theorem golden_exists : ∃ x : RExpr, (rle (dv rOH dz0) x ∧ rle x (dv rOH (cD 1))) ∧ rEq (FR goldE x) rzero ∧
    ∀ y, rle (dv rOH dz0) y → rle y (dv rOH (cD 1)) → rEq (FR goldE y) rzero → rEq y x :=
  law_root goldE dz0 (cD 1) 0 1 0 (by decide +kernel)

/-- **`x + ln x = 0`** has one root in `[1/2, 1]` (the omega constant through `ln`; slopes `1 + 1/x ∈ [2, 3]`). -/
theorem omega_ln_exists : ∃ x : RExpr, (rle (dv rOH half) x ∧ rle x (dv rOH (cD 1))) ∧ rEq (FR omegaL x) rzero ∧
    ∀ y, rle (dv rOH half) y → rle y (dv rOH (cD 1)) → rEq (FR omegaL y) rzero → rEq y x :=
  law_root omegaL half (cD 1) 0 2 0 (by decide +kernel)

/-- **A FRACTIONAL POWER**: `x^{4/5} = 2` has one root in `[2, 3]` (slopes read in `[0.46, 0.97]`). -/
theorem frac_exists : ∃ x : RExpr, (rle (dv rOH (cD 2)) x ∧ rle x (dv rOH (cD 3))) ∧ rEq (FR frac x) rzero ∧
    ∀ y, rle (dv rOH (cD 2)) y → rle y (dv rOH (cD 3)) → rEq (FR frac y) rzero → rEq y x :=
  law_root frac (cD 2) (cD 3) 2 0 0 (by decide +kernel)

/-- The other side of the fork: on `[3, 4]` the power has no sign change (`3^{4/5} > 2`) — refused. And `ln` on a box
reaching `0` is refused by `posOK` (`[0, 1]`). -/
example : chkD frac (cD 3) (cD 4) 2 0 0 = false := by decide +kernel
example : chkD omegaL dz0 (cD 1) 0 2 0 = false := by decide +kernel

end ZRootDiv

#print axioms ZRootDiv.val_evR
#print axioms ZRootDiv.uc_evqD
#print axioms ZRootDiv.evR_seq
#print axioms ZRootDiv.ln_unif
#print axioms ZRootDiv.law_root
#print axioms ZRootDiv.FR_is_value
#print axioms ZRootDiv.golden_exists
#print axioms ZRootDiv.omega_ln_exists
#print axioms ZRootDiv.frac_exists
