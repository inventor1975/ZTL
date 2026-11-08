import ZRootExp
import ZRAtan
/-!
# ZRootAtan — VR's `atan` satisfies `ZXE.AtanLaws`, and its grid answers converge uniformly on bounded sets. Zero
axioms.

* `atan_riemann_u`: `ZAtan.atan_riemann` with the bound given — the index depends on `y` only through `|y| ≤ K0`;
* `uc_atan`: the oracle `atseq (f n q) n` is uniformly bounded and uniformly Cauchy when `f` is;
* `r_atanLaws`: `atan 0 = 0`, congruent, and the chord between the bounds of the reading of `ψ` — from
  `ZAtan.atan_window` at each index, the boundary of the interval absorbed by `ψ`'s Lipschitz bound.
-/

namespace ZRootAtan
open VR VR.Numbers VR.CSR ZNumBin ZField ZIv ZXE ZRealCF ZExp ZRealExp ZLn ZRootExp ZRAtan ZAtan ZCertify ZSlope
  ZSlopeExp ZRecip

/-- **UNIFORMLY**: the index `N` after which `atan y`'s grid answers stay near a fixed Riemann sum depends on `y` only
through a bound `K0` (a copy of `ZAtan.atan_riemann` with the bound given, not found). -/
theorem atan_riemann_u (K0 k : Nat) : ∃ N, ∀ ys, ZTrig.Ab ys (qnat K0) → ∃ S, ∀ n, N ≤ n →
    ZTrig.Ab (qsub (atseq ys n) S) (qadd (qadd (qeps k) (qeps k)) (qeps n)) := by
  have Y0 := qnat_nonneg K0
  obtain ⟨H, H0, hst⟩ := ustep_atan Y0 Y0
  obtain ⟨B, hB⟩ := eps_scaledA (qmul_nonneg (qmul_self_nonneg (qnat K0)) H0)
  -- m = k + B; the step tolerance ε_{k+m}
  obtain ⟨N0, hN0⟩ := hst (k + (k + B))
  refine ⟨N0 + (K0 + 2), fun ys hy => ⟨rsum ys (k + B) (2 ^ (k + B)), fun n hn => ?_⟩⟩
  have hn0 : N0 ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hn1 : K0 + 2 ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  generalize hm : k + B = m at *
  have Δab : ZTrig.Ab (qmul ys (qeps m)) (qnat K0) := by
    obtain ⟨y1, y2⟩ := hy
    have q1 := ZTrig.qeps_le_one m
    have e0 := qeps_nonneg m
    have f1 := scale_l y2 e0; have f2 := scale_l y1 e0
    have f3 := ZExp.scale q1 Y0
    have c := qmul_comm ys (qeps m)
    have o := qone_mul (qnat K0)
    have o2 : qEq (qmul (qeps m) (qneg (qnat K0))) (qneg (qmul (qeps m) (qnat K0))) := by rat_ring
    have c2 := qmul_comm (qeps m) (qnat K0)
    generalize qmul ys (qeps m) = P at *; generalize qmul (qeps m) ys = P' at *
    generalize qmul (qeps m) (qnat K0) = Q at *; generalize qmul (qnat K0) (qeps m) = Q2 at *
    generalize qmul (qeps m) (qneg (qnat K0)) = Q' at *; generalize qmul qone (qnat K0) = Y1 at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  -- the induction along the points
  have ind : ∀ i, i ≤ 2 ^ m → ZTrig.Ab (qsub (atseq (rpt ys m i) n) (rsum ys m i))
      (qmul (qnat i) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H))) := by
    intro i
    induction i with
    | zero =>
        intro _
        have z := atseq_zero n
        have e : qEq (qmul (qnat 0) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H))) qzero :=
          qEq_trans (qmul_respects qnat_zero (qEq_refl _)) (by rat_ring)
        show ZTrig.Ab (qsub (atseq qzero n) qzero) _
        generalize qmul (qnat 0) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = Z at *
        unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
    | succ i ih =>
        intro hi
        have ih' := ih (Nat.le_of_succ_le hi)
        have st := hN0 n hn0 (rpt ys m i) (qmul ys (qeps m)) (rpt_ab hy Y0 m (Nat.le_of_succ_le hi)) Δab
        have q := qnat_succ i
        have e : qEq (qmul (qnat (i + 1)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)))
            (qadd (qmul (qnat i) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)))
              (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H))) :=
          qEq_trans (qmul_respects q (qEq_refl _)) (by rat_ring)
        show ZTrig.Ab (qsub (atseq (qadd (rpt ys m i) (qmul ys (qeps m))) n)
          (qadd (rsum ys m i) (qmul (qmul ys (qeps m)) (psi (rpt ys m i))))) _
        generalize qmul (qnat (i + 1)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = T1 at *
        generalize qmul (qnat i) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = T0 at *
        generalize qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H) = T at *
        obtain ⟨a1, a2⟩ := ih'; obtain ⟨b1, b2⟩ := st
        unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have top := ind (2 ^ m) (Nat.le_refl _)
  -- 2^m·ε_{k+m} = ε_k; 2^m·Δ²·H = y*²·H·ε_m ≤ ε_k
  have pe := pow_eps m
  have pk : qEq (qmul (qnat (2 ^ m)) (qeps (k + m))) (qeps k) :=
    qEq_trans (qmul_respects (qnat_pow2 m) (qEq_refl _)) (qpow2_mul_eps m k)
  have sq := sq_le hy
  have hb := hB k
  rw [hm] at hb
  have f1 := ZExp.scale sq H0
  have f2 := scale_l f1 (qeps_nonneg m)
  have e1 : qEq (qmul (qnat (2 ^ m)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)))
      (qadd (qmul (qnat (2 ^ m)) (qeps (k + m)))
        (qmul (qmul (qnat (2 ^ m)) (qeps m)) (qmul (qeps m) (qmul (qmul ys ys) H)))) := by rat_ring
  have e2 : qEq (qmul (qmul (qnat (2 ^ m)) (qeps m)) (qmul (qeps m) (qmul (qmul ys ys) H)))
      (qmul qone (qmul (qeps m) (qmul (qmul ys ys) H))) := qmul_respects pe (qEq_refl _)
  have e3 := qone_mul (qmul (qeps m) (qmul (qmul ys ys) H))
  have e4 : qEq (qmul (qeps m) (qmul (qmul (qnat K0) (qnat K0)) H)) (qmul (qeps m) (qmul (qmul (qnat K0) (qnat K0)) H)) :=
    qEq_refl _
  -- the last point is y* itself
  have last : qEq (rpt ys m (2 ^ m)) ys :=
    qEq_trans (rpt_eq ys m (2 ^ m)) (qEq_trans (qmul_respects pe (qEq_refl _)) (qone_mul ys))
  have nr := atan_near (e := qzero) (inR_of hy hn1) (inR_of (rpt_ab hy Y0 m (Nat.le_refl _)) hn1)
    (by have := qle_of_qEq last; have := qle_of_qEq (qEq_symm last); unfold qsub; rat_linarith)
    (by have := qle_of_qEq last; have := qle_of_qEq (qEq_symm last); unfold qsub; rat_linarith)
  generalize qmul (qnat (2 ^ m)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = T at *
  generalize qmul (qmul (qnat (2 ^ m)) (qeps m)) (qmul (qeps m) (qmul (qmul ys ys) H)) = U at *
  generalize hV : qmul (qeps m) (qmul (qmul ys ys) H) = V at *
  obtain ⟨t1, t2⟩ := top; obtain ⟨r1, r2⟩ := nr
  have v0 : qle qzero V := by rw [← hV]; exact qmul_nonneg (qeps_nonneg m) (qmul_nonneg (qmul_self_nonneg ys) H0)
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩


theorem ab_of_close {x B : QExpr} {C : Nat} (h : qclose x qzero (qofInt (pow2 C))) : ZTrig.Ab x (qnat (2 ^ C)) := by
  obtain ⟨h1, h2⟩ := h
  have e := ZLn.qnat_pow2 C
  unfold qsub at h1 h2
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem fin_step {X em en e2 e4 e0 : QExpr}
    (u : qle X (qadd (qadd (qadd (qadd e4 e4) em) (qadd (qadd e4 e4) en)) (qadd e2 en)))
    (hm : qle em e4) (hn : qle en e4) (le2 : qle e2 (qadd (qadd e4 e4) (qadd e4 e4)))
    (le0 : qle (qadd (qadd (qadd (qadd e4 e4) (qadd e4 e4)) (qadd (qadd e4 e4) (qadd e4 e4)))
      (qadd (qadd (qadd e4 e4) (qadd e4 e4)) (qadd (qadd e4 e4) (qadd e4 e4)))) e0) (p4 : qle qzero e4) : qle X e0 := by
  rat_linarith

theorem fin_close {Am An Bn S0 em en e0 e1 e2 e3 e4 : QExpr}
    (a1 : qle (qneg (qadd (qadd e4 e4) em)) (qadd Am (qneg S0))) (a2 : qle (qadd Am (qneg S0)) (qadd (qadd e4 e4) em))
    (b1 : qle (qneg (qadd (qadd e4 e4) en)) (qadd An (qneg S0))) (b2 : qle (qadd An (qneg S0)) (qadd (qadd e4 e4) en))
    (d1 : qle (qneg (qadd e2 en)) (qadd An (qneg Bn))) (d2 : qle (qadd An (qneg Bn)) (qadd e2 en))
    (hm : qle em e4) (hn : qle en e4) (h1 : qEq (qadd e1 e1) e0) (h2 : qEq (qadd e2 e2) e1)
    (h3 : qEq (qadd e3 e3) e2) (h4 : qEq (qadd e4 e4) e3) (p4 : qle qzero e4) : qclose Am Bn e0 := by
  have E2 : qEq (qadd (qadd e4 e4) (qadd e4 e4)) e2 := qEq_trans (qadd_respects h4 h4) h3
  have E1 := qEq_trans (qadd_respects E2 E2) h2
  have E0 := qEq_trans (qadd_respects E1 E1) h1
  have le2 := qle_of_qEq (qEq_symm E2)
  have le0 := qle_of_qEq E0
  have u : qle (qadd Am (qneg Bn)) (qadd (qadd (qadd (qadd e4 e4) em) (qadd (qadd e4 e4) en)) (qadd e2 en)) := by
    clear le0 E0 E1 E2 le2 h1 h2 h3 h4 a1 b2 d1; rat_linarith
  have l : qle (qneg (qadd (qadd (qadd (qadd e4 e4) em) (qadd (qadd e4 e4) en)) (qadd e2 en))) (qadd Am (qneg Bn)) := by
    clear le0 E0 E1 E2 le2 h1 h2 h3 h4 a2 b1 d2 u; rat_linarith
  have l' : qle (qneg (qadd Am (qneg Bn))) (qadd (qadd (qadd (qadd e4 e4) em) (qadd (qadd e4 e4) en)) (qadd e2 en)) := by
    clear le0 E0 E1 E2 le2 h1 h2 h3 h4 a1 a2 b1 b2 d1 d2 u; rat_linarith
  have f1 := fin_step u hm hn le2 le0 p4
  have f2 := fin_step l' hm hn le2 le0 p4
  constructor
  · unfold qsub; clear a1 a2 b1 b2 d1 d2 l u l' le0 le2 E0 E1 E2; rat_linarith
  · unfold qsub; clear a1 a2 b1 b2 d1 d2 l u l' le0 le2 E0 E1 E2; rat_linarith

/-- **`atan`'s ORACLE CONVERGES UNIFORMLY** when its argument's does. -/
theorem uc_atan {f : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) : UCo (fun n q => atseq (f n q) n) := by
  intro R R0
  obtain ⟨Cf, Bf, bf, cf⟩ := hf R R0
  have hb : ∀ n (q : Nat → QExpr), Bf ≤ n → (∀ i, qclose (q i) qzero R) → ZTrig.Ab (f n q) (qnat (2 ^ Cf)) :=
    fun n q hn hq => ab_of_close (B := qzero) (bf n q hn hq)
  have K0 := qnat_nonneg (2 ^ Cf)
  have h0 : ZTrig.Ab qzero (qnat (2 ^ Cf)) := ⟨by rat_linarith, K0⟩
  obtain ⟨C, hC⟩ := qexpr_bound (qadd (qnat (2 ^ Cf)) qone)
  refine ⟨C, Bf + (2 ^ Cf + 2), fun n q hn hq => ?_, fun k => ?_⟩
  · have y := hb n q (ZRootExp.lA hn) hq
    have r1 := inR_of y (ZRootExp.lB hn)
    have r0 := inR_of h0 (ZRootExp.lB hn)
    obtain ⟨y1, y2⟩ := y
    obtain ⟨a, b⟩ := atan_near (e := qnat (2 ^ Cf)) r1 r0 (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
    have z := atseq_zero n
    have e1 := ZTrig.qeps_le_one n
    refine ZRootExp.close_up (B := qadd (qnat (2 ^ Cf)) qone) ?_ hC
    show qclose (atseq (f n q) n) qzero _
    unfold qsub at a b
    constructor <;> (unfold qsub; rat_linarith)
  · obtain ⟨N1, hN1⟩ := atan_riemann_u (2 ^ Cf) (k + 4)
    obtain ⟨N2, hN2b, h2⟩ := cf (k + 2)
    refine ⟨N1 + N2 + (2 ^ Cf + 2) + (k + 4), ?_, fun m n q hm hn hq => ?_⟩
    · exact Nat.le_trans (Nat.add_le_add hN2b (Nat.le_refl _)) (Nat.le_trans (Nat.add_le_add (Nat.le_add_left _ _)
        (Nat.le_refl _)) (Nat.le_add_right _ _))
    have up : ∀ p, N1 + N2 + (2 ^ Cf + 2) + (k + 4) ≤ p →
        N1 ≤ p ∧ N2 ≤ p ∧ 2 ^ Cf + 2 ≤ p ∧ k + 4 ≤ p ∧ Bf ≤ p := fun p hp =>
      ⟨Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) hp,
       Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) hp,
       Nat.le_trans (Nat.le_trans (Nat.le_add_left _ (N1 + N2)) (Nat.le_add_right _ _)) hp,
       Nat.le_trans (Nat.le_add_left _ _) hp,
       Nat.le_trans hN2b (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ _))
         (Nat.le_add_right _ _)) hp)⟩
    obtain ⟨m1, m2, m3, m4, m5⟩ := up m hm
    obtain ⟨n1, n2, n3, n4, n5⟩ := up n hn
    have ym := hb m q m5 hq
    have yn := hb n q n5 hq
    obtain ⟨S, hS⟩ := hN1 (f m q) ym
    obtain ⟨a1, a2⟩ := hS m m1
    obtain ⟨b1, b2⟩ := hS n n1
    obtain ⟨c1, c2⟩ := h2 m n q m2 n2 hq
    unfold qsub at c1 c2
    obtain ⟨d1, d2⟩ := atan_near (e := qeps (k + 2)) (inR_of ym n3) (inR_of yn n3) (by unfold qsub; rat_linarith)
      (by unfold qsub; rat_linarith)
    have em := ZLn.eps_anti m4
    have en := ZLn.eps_anti n4
    have e1 : qEq (qadd (qeps (k + 1)) (qeps (k + 1))) (qeps k) := qeps_succ_add k
    have e2 : qEq (qadd (qeps (k + 2)) (qeps (k + 2))) (qeps (k + 1)) := qeps_succ_add (k + 1)
    have e3 : qEq (qadd (qeps (k + 3)) (qeps (k + 3))) (qeps (k + 2)) := qeps_succ_add (k + 2)
    have e4 : qEq (qadd (qeps (k + 4)) (qeps (k + 4))) (qeps (k + 3)) := qeps_succ_add (k + 3)
    have p4 := qeps_nonneg (k + 4)
    unfold qsub at a1 a2 b1 b2 d1 d2
    exact fin_close a1 a2 b1 b2 d1 d2 (qle_trans em (qle_refl _)) (qle_trans en (qle_refl _)) e1 e2 e3 e4 p4

/-! ## The laws on VR's continuum -/

theorem ratan_zero : rEq (ratan rzero) rzero := rEq_of_seq (fun n => atseq_zero n)

theorem ab_real (x : RExpr) : ∃ K N, ∀ n, N ≤ n → ZTrig.Ab (x.seq n) (qnat K) := by
  obtain ⟨B, N, h⟩ := rbounded x
  exact ⟨2 ^ B, N, fun n hn => ab_of_close (B := qzero) (h n hn)⟩

theorem ratan_congr {a b : RExpr} (h : rEq a b) : rEq (ratan a) (ratan b) := by
  intro k
  obtain ⟨Ka, Na, ha⟩ := ab_real a
  obtain ⟨Kb, Nb, hb⟩ := ab_real b
  obtain ⟨N, hN⟩ := h (k + 1)
  refine ⟨N + Na + Nb + (Ka + 2) + (Kb + 2) + (k + 1), fun n hn => ?_⟩
  have up : ∀ X, X ≤ N + Na + Nb + (Ka + 2) + (Kb + 2) + (k + 1) → X ≤ n := fun X hX => Nat.le_trans hX hn
  obtain ⟨c1, c2⟩ := hN n (up _ (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N Na)
    (Nat.le_add_right _ Nb)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)))
  have ra := inR_of (ha n (up _ (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left Na N)
    (Nat.le_add_right _ Nb)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _))))
    (up _ (Nat.le_trans (Nat.le_trans (Nat.le_add_left (Ka + 2) _) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)))
  have rb := inR_of (hb n (up _ (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left Nb (N + Na))
    (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _))))
    (up _ (Nat.le_trans (Nat.le_add_left (Kb + 2) _) (Nat.le_add_right _ _)))
  unfold qsub at c1 c2
  obtain ⟨d1, d2⟩ := atan_near (e := qeps (k + 1)) ra rb (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
  have en := ZLn.eps_anti (up _ (Nat.le_add_left (k + 1) _))
  have e1 : qEq (qadd (qeps (k + 1)) (qeps (k + 1))) (qeps k) := qeps_succ_add k
  show qclose (atseq (a.seq n) n) (atseq (b.seq n) n) (qeps k)
  unfold qsub at d1 d2
  constructor <;> (unfold qsub; rat_linarith)

/-- The rational core of the chord: `D·W − Δ ≤ en·Pw + Pl·e` from the window `L·(W − e) ≤ Δ`, `|L − D| ≤ en`. -/
theorem chord_lo {D Δ L W e en Pw Pl : QExpr} (hL1 : qle (qsub D en) L) (hL2 : qle L (qadd D en))
    (lo : qle (qmul L (qsub W e)) Δ) (hW : qclose W qzero Pw) (hL0 : qle qzero L) (hLb : qle L Pl) (he : qle qzero e) :
    qle (qsub (qmul D W) Δ) (qadd (qmul en Pw) (qmul Pl e)) := by
  have c : qclose (qsub D L) qzero en := by constructor <;> (unfold qsub at *; rat_linarith)
  obtain ⟨p1, _⟩ := qmul_abs_bound c hW
  have s1 := ZExp.scale hLb he
  have i1 : qEq (qmul L (qsub W e)) (qsub (qmul L W) (qmul L e)) := by unfold qsub; rat_ring
  have i2 : qEq (qsub (qmul (qsub D L) W) qzero) (qsub (qmul D W) (qmul L W)) := by unfold qsub; rat_ring
  unfold qsub at *; rat_linarith

theorem chord_hi {D Δ L W e en Pw Pl : QExpr} (hL1 : qle (qsub D en) L) (hL2 : qle L (qadd D en))
    (hi : qle Δ (qmul L (qadd W e))) (hW : qclose W qzero Pw) (hL0 : qle qzero L) (hLb : qle L Pl) (he : qle qzero e) :
    qle (qsub Δ (qmul D W)) (qadd (qmul en Pw) (qmul Pl e)) := by
  have c : qclose (qsub L D) qzero en := by constructor <;> (unfold qsub at *; rat_linarith)
  obtain ⟨p1, _⟩ := qmul_abs_bound c hW
  have s1 := ZExp.scale hLb he
  have i1 : qEq (qmul L (qadd W e)) (qadd (qmul L W) (qmul L e)) := by rat_ring
  have i2 : qEq (qsub (qmul (qsub L D) W) qzero) (qsub (qmul L W) (qmul D W)) := by unfold qsub; rat_ring
  unfold qsub at *; rat_linarith

theorem rle_rofQ {a b : QExpr} (h : qle a b) : rle (rofQ a) (rofQ b) := rle_of_eventually 0 (fun _ _ => h)

/-- The bounds of `ψ` near the interval: for `t` within `e` of `I`, `ψ(t)` is within `e` of the reading `W`. -/
theorem psi_near {I W : Iv} (hW : psiI I = some W) (hI : qle (qD I.1) (qD I.2)) {t e : QExpr} (he : qle qzero e)
    (h1 : qle (qsub (qD I.1) e) t) (h2 : qle t (qadd (qD I.2) e)) :
    qle (qsub (qD W.1) e) (psi t) ∧ qle (psi t) (qadd (qD W.2) e) := by
  have tc1 := qmax_ge_l (qD I.1) (qmin t (qD I.2))
  have tc2 : qle (qmax (qD I.1) (qmin t (qD I.2))) (qD I.2) := qmax_le hI (qmin_le_r _ _)
  have hm : Mem rCF (rofQ (qmax (qD I.1) (qmin t (qD I.2)))) I :=
    ⟨rCF.le_respects (rEq_symm (ZRootPVR.dv_rofQ _)) (rCF.refl _) (rle_rofQ tc1),
     rCF.le_respects (rCF.refl _) (rEq_symm (ZRootPVR.dv_rofQ _)) (rle_rofQ tc2)⟩
  obtain ⟨_, _, ct⟩ := psi_facts (qmax (qD I.1) (qmin t (qD I.2)))
  have hw : rCF.r (rCF.mul (rCF.add rCF.one (rCF.mul (rofQ (qmax (qD I.1) (qmin t (qD I.2))))
      (rofQ (qmax (qD I.1) (qmin t (qD I.2)))))) (rofQ (psi (qmax (qD I.1) (qmin t (qD I.2)))))) rCF.one :=
    rEq_of_seq (fun _ => ct)
  have mw := psi_mem rCF hm hW hw
  have w1 := q_of_rle (rCF.le_respects (ZRootPVR.dv_rofQ _) (rCF.refl _) mw.1)
  have w2 := q_of_rle (rCF.le_respects (rCF.refl _) (ZRootPVR.dv_rofQ _) mw.2)
  -- |t − tc| ≤ e
  have d : qle (qsub t (qmax (qD I.1) (qmin t (qD I.2)))) e ∧ qle (qsub (qmax (qD I.1) (qmin t (qD I.2))) t) e := by
    rcases qmax_cases (qD I.1) (qmin t (qD I.2)) with ⟨e1, h1'⟩ | ⟨e1, h1'⟩ <;> rw [e1] <;>
      rcases qmin_cases t (qD I.2) with ⟨e2, h2'⟩ | ⟨e2, h2'⟩ <;> (try rw [e2] at h1') <;> (try rw [e2]) <;>
      (unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩)
  obtain ⟨l1, l2⟩ := psi_lip d.1 d.2
  unfold qsub at l1 l2 h1 w1 w2
  exact ⟨by unfold qsub; rat_linarith, by rat_linarith⟩

theorem le7' {a b c d e f g n : Nat} (h : a + b + c + d + e + f + g ≤ n) :
    a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n ∧ e ≤ n ∧ f ≤ n ∧ g ≤ n := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := le7 a b c d e f g
  exact ⟨Nat.le_trans q1 h, Nat.le_trans q2 h, Nat.le_trans q3 h, Nat.le_trans q4 h, Nat.le_trans q5 h,
    Nat.le_trans q6 h, Nat.le_trans q7 h⟩

/-- The two error terms: `ε_n·2^Cw + Pl·ε_{k+1+Cl} ≤ ε_k`. -/
theorem err_le {n k Cw Cl : Nat} {Pl : QExpr} (hn : k + 1 + Cw ≤ n) (hPl : qle Pl (qofInt (pow2 Cl))) :
    qle (qadd (qmul (qeps n) (qofInt (pow2 Cw))) (qmul Pl (qeps (k + 1 + Cl)))) (qeps k) := by
  have p0 : qle qzero (qofInt (pow2 Cw)) := qofInt_le (pow2_nonneg Cw)
  have a := ZExp.scale (ZLn.eps_anti hn) p0
  have a' := qmul_comm (qeps (k + 1 + Cw)) (qofInt (pow2 Cw))
  have a2 := qpow2_mul_eps Cw (k + 1)
  have b := ZExp.scale hPl (qeps_nonneg (k + 1 + Cl))
  have b' := qmul_comm (qofInt (pow2 Cl)) (qeps (k + 1 + Cl))
  have b2 := qpow2_mul_eps Cl (k + 1)
  have e := qeps_succ_add k
  rat_linarith

/-- **THE CHORD OF VR's `atan`** (termwise ordered arguments): between the bounds of the reading of `ψ`. -/
theorem chord_core {I W : Iv} (hW : psiI I = some W) {x y : RExpr} (hord : ∀ n, qle (x.seq n) (y.seq n))
    (hx : Mem rCF x I) (hy : Mem rCF y I) :
    rle (rmul (radd y (rneg x)) (dv rOH W.1)) (radd (ratan y) (rneg (ratan x))) ∧
    rle (radd (ratan y) (rneg (ratan x))) (rmul (radd y (rneg x)) (dv rOH W.2)) := by
  have hI : qle (qD I.1) (qD I.2) :=
    q_of_rle (rCF.le_respects (ZRootPVR.dv_rofQ _) (ZRootPVR.dv_rofQ _) (rCF.le_trans hx.1 hx.2))
  obtain ⟨Kx, Nx, hbx⟩ := ab_real x
  obtain ⟨Ky, Ny, hby⟩ := ab_real y
  obtain ⟨Cw1, hC1⟩ := qexpr_bound (qD W.1)
  obtain ⟨Cw2, hC2⟩ := qexpr_bound (qD W.2)
  obtain ⟨Cl, hCl, _⟩ := qexpr_bound (qadd (qadd (qnat Kx) (qnat Ky)) qone)
  unfold qsub at hCl
  have hPl : qle (qadd (qadd (qnat Kx) (qnat Ky)) qone) (qofInt (pow2 Cl)) := by rat_linarith
  -- the common index and the facts at it
  have at_n : ∀ k, ∃ N, ∀ n, N ≤ n →
      InR (x.seq n) n ∧ InR (y.seq n) n ∧ ZTrig.Ab (x.seq n) (qnat Kx) ∧ ZTrig.Ab (y.seq n) (qnat Ky) ∧
      qle (qsub (qD I.1) (qeps (k + 1 + Cl))) (x.seq n) ∧ qle (y.seq n) (qadd (qD I.2) (qeps (k + 1 + Cl))) ∧
      k + 1 + Cw1 ≤ n ∧ k + 1 + Cw2 ≤ n := by
    intro k
    obtain ⟨N1, h1⟩ := hx.1 (k + 1 + Cl)
    obtain ⟨N2, h2⟩ := hy.2 (k + 1 + Cl)
    refine ⟨N1 + N2 + Nx + Ny + (Kx + 2) + (Ky + 2) + (k + 1 + Cw1 + Cw2), fun n hn => ?_⟩
    obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := le7' hn
    have ax := hbx n u3
    have ay := hby n u4
    have d1 : qEq ((dv rCF.toOH I.1).seq n) (qD I.1) := dv_seq I.1 n
    have d2 : qEq ((dv rCF.toOH I.2).seq n) (qD I.2) := dv_seq I.2 n
    have g1 := h1 n u1
    have g2 := h2 n u2
    unfold qsub at g1 g2
    refine ⟨inR_of ax u5, inR_of ay u6, ax, ay, by unfold qsub; rat_linarith, by rat_linarith,
      Nat.le_trans (Nat.le_trans (Nat.le_add_right _ Cw2) (Nat.le_refl _)) u7, ?_⟩
    exact Nat.le_trans (Nat.le_trans (Nat.add_le_add_right (Nat.le_add_right (k + 1) Cw1) Cw2) (Nat.le_refl _)) u7
  have Lb : ∀ n L, ZTrig.Ab (x.seq n) (qnat Kx) → ZTrig.Ab (y.seq n) (qnat Ky) →
      qle L (qadd (qsub (y.seq n) (x.seq n)) (qeps n)) → qle L (qadd (qadd (qnat Kx) (qnat Ky)) qone) := by
    intro n L ax ay hL
    obtain ⟨x1, x2⟩ := ax; obtain ⟨y1, y2⟩ := ay
    have e1 := ZTrig.qeps_le_one n
    unfold qsub at hL; rat_linarith
  constructor
  · intro k
    obtain ⟨N, hN⟩ := at_n k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨rx, ry, ax, ay, g1, g2, n1, _⟩ := hN n hn
    have e0 := qeps_nonneg (k + 1 + Cl)
    obtain ⟨L, L0, L1, L2, lo, _⟩ := atan_window (m := qsub (qD W.1) (qeps (k + 1 + Cl)))
      (M := qadd (qD W.2) (qeps (k + 1 + Cl))) rx ry (hord n) (fun t t1 t2 => psi_near hW hI e0 (qle_trans g1 t1) (qle_trans t2 g2))
    have c := chord_lo L1 L2 lo hC1 L0 (Lb n L ax ay L2) e0
    have er := err_le (Pl := qadd (qadd (qnat Kx) (qnat Ky)) qone) n1 hPl
    have dw := dv_seq W.1 n
    have m1 : qEq (qmul (qadd (y.seq n) (qneg (x.seq n))) ((dv rOH W.1).seq n))
        (qmul (qsub (y.seq n) (x.seq n)) (qD W.1)) := qmul_respects (qEq_refl _) dw
    change qle (qsub (qmul (qadd (y.seq n) (qneg (x.seq n))) ((dv rOH W.1).seq n))
      (qadd (atseq (y.seq n) n) (qneg (atseq (x.seq n) n)))) (qeps k)
    unfold qsub at c m1 ⊢
    rat_linarith
  · intro k
    obtain ⟨N, hN⟩ := at_n k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨rx, ry, ax, ay, g1, g2, _, n2⟩ := hN n hn
    have e0 := qeps_nonneg (k + 1 + Cl)
    obtain ⟨L, L0, L1, L2, _, hi⟩ := atan_window (m := qsub (qD W.1) (qeps (k + 1 + Cl)))
      (M := qadd (qD W.2) (qeps (k + 1 + Cl))) rx ry (hord n) (fun t t1 t2 => psi_near hW hI e0 (qle_trans g1 t1) (qle_trans t2 g2))
    have c := chord_hi L1 L2 hi hC2 L0 (Lb n L ax ay L2) e0
    have er := err_le (Pl := qadd (qadd (qnat Kx) (qnat Ky)) qone) n2 hPl
    have dw := dv_seq W.2 n
    have m1 : qEq (qmul (qadd (y.seq n) (qneg (x.seq n))) ((dv rOH W.2).seq n))
        (qmul (qsub (y.seq n) (x.seq n)) (qD W.2)) := qmul_respects (qEq_refl _) dw
    change qle (qsub (qadd (atseq (y.seq n) n) (qneg (atseq (x.seq n) n)))
      (qmul (qadd (y.seq n) (qneg (x.seq n))) ((dv rOH W.2).seq n))) (qeps k)
    unfold qsub at c m1 ⊢
    rat_linarith

/-- **VR's `atan` IS A LAWFUL `atan`.** -/
theorem r_atanLaws : AtanLaws rCF ratan where
  zero := ratan_zero
  congr := fun h => ratan_congr h
  chord := fun I W hW x y hx hy hxy => by
    have e : rEq (rmin x y) x := rmin_eq hxy
    have hx' : Mem rCF (rmin x y) I := ZDivIv.mem_congr rCF e hx
    obtain ⟨l, u⟩ := chord_core hW (x := rmin x y) (y := y) (fun n => qmin_le_r _ _) hx' hy
    have ea := ratan_congr e
    have ed : rCF.r (rCF.add y (rCF.neg (rmin x y))) (rCF.add y (rCF.neg x)) := rCF.add_congr (rCF.refl y) (rCF.neg_congr e)
    have eA : rCF.r (rCF.add (ratan y) (rCF.neg (ratan (rmin x y)))) (rCF.add (ratan y) (rCF.neg (ratan x))) :=
      rCF.add_congr (rCF.refl _) (rCF.neg_congr ea)
    exact ⟨rCF.le_respects (rCF.mul_congr ed (rCF.refl _)) eA l, rCF.le_respects eA (rCF.mul_congr ed (rCF.refl _)) u⟩

end ZRootAtan

#print axioms ZRootAtan.atan_riemann_u
#print axioms ZRootAtan.uc_atan
#print axioms ZRootAtan.ratan_congr
#print axioms ZRootAtan.psi_near
#print axioms ZRootAtan.chord_core
#print axioms ZRootAtan.r_atanLaws
