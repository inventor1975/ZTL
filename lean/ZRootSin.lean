import ZRootExp
import ZRSin
/-!
# ZRootSin — VR's `sin`, `cos` satisfy `ZSinIv.TrigLaws`, and their oracles converge uniformly. Zero axioms.

Every law comes from the full sine (`ZTrig` … `ZTrig13`), at the argument's own index:
  * `sin 0 = 0`, `cos 0 = 1` (`Sn_zero`, `Cn_zero`); congruence from the Lipschitz bound `CS_lip`;
  * THE SECOND-ORDER STEP from `Ev_sin2`, `Ev_cos2` with the trivial readings `[−1, 1]` (`SinHi`/`CosHi` by `1 ≤ 1`);
  * `|sin|, |cos| ≤ 1` from `sin_pm1`, `cos_pm1`; the double angle from `add_lim`; Pythagoras from `pyth`;
  * `uc_sc`: the oracle `S_n(f_n(q))`, `C_n(f_n(q))` is uniformly bounded and Cauchy when `f` is (`CS_unif`,
    `CS_lip`).
-/

namespace ZRootSin
open VR VR.Numbers VR.CSR ZNumBin ZField ZIv ZXE ZRealCF ZExp ZRealExp ZLn ZRootExp ZRSin ZCertify ZSlope
  ZSlopeExp ZRecip ZSinIv ZTrig

theorem close_of_ab {x y e : QExpr} (h : Ab (qsub x y) e) : qclose x y e := ⟨h.2, h.1⟩
theorem ab_of_cl {x y e : QExpr} (h : qclose x y e) : Ab (qsub x y) e := ⟨h.2, h.1⟩

/-- Two operational reals eventually in a common `[−A, A]`. -/
theorem ev_two (x y : RExpr) : ∃ A, qle qzero A ∧ Ev x.seq (qneg A) A ∧ Ev y.seq (qneg A) A := by
  obtain ⟨Kx, Nx, hx⟩ := ab_real x
  obtain ⟨Ky, Ny, hy⟩ := ab_real y
  have a := qnat_nonneg Kx
  have b := qnat_nonneg Ky
  refine ⟨qadd (qnat Kx) (qnat Ky), by rat_linarith, ?_, ?_⟩
  · exact Ev_widen (Ev_of_exact Nx (fun n hn => hx n hn)) (by rat_linarith) (by rat_linarith)
  · exact Ev_widen (Ev_of_exact Ny (fun n hn => hy n hn)) (by rat_linarith) (by rat_linarith)

theorem bnd_real (x : RExpr) : ∃ A, qle qzero A ∧ Bnd x.seq A := by
  obtain ⟨K, N, h⟩ := ab_real x
  exact ⟨qnat K, qnat_nonneg K, N, h⟩

theorem rsin_zero : rEq (rsin rzero) rzero := rEq_of_seq (fun n => Sn_zero n)

theorem rcos_zero : rEq (rcos rzero) rone := fun k => ⟨1, fun n hn => by
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ m =>
      have e := Cn_zero m
      have e0 := qeps_nonneg k
      show qclose (Cn qzero (m + 1)) qone (qeps k)
      constructor <;> (unfold qsub; rat_linarith)⟩

/-- Congruence, both at once: `|S_n(a_n) − S_n(b_n)| ≤ |a_n − b_n|·H`. -/
theorem sc_congr {a b : RExpr} (h : rEq a b) : rEq (rsin a) (rsin b) ∧ rEq (rcos a) (rcos b) := by
  obtain ⟨Ka, Na, ha⟩ := ab_real a
  obtain ⟨Kb, Nb, hb⟩ := ab_real b
  have k0 := qnat_nonneg Ka
  have k1 := qnat_nonneg Kb
  have A0 : qle qzero (qadd (qnat Ka) (qnat Kb)) := by rat_linarith
  obtain ⟨H, hH⟩ := S_bounded A0
  obtain ⟨B, hB, _⟩ := qexpr_bound H
  have hHB : qle H (qofInt (pow2 B)) := by unfold qsub at hB; rat_linarith
  have core : ∀ k, ∃ N, ∀ n, N ≤ n →
      Ab (qsub (Cn (a.seq n) n) (Cn (b.seq n) n)) (qeps k) ∧ Ab (qsub (Sn (a.seq n) n) (Sn (b.seq n) n)) (qeps k) := by
    intro k
    obtain ⟨N, hN⟩ := h (k + B)
    refine ⟨N + Na + Nb, fun n hn => ?_⟩
    have hab := ab_of_cl (hN n (le_l' (le_l' hn)))
    obtain ⟨x1, x2⟩ := ha n (le_r' (le_l' hn))
    obtain ⟨y1, y2⟩ := hb n (le_r' hn)
    have ax : Ab (a.seq n) (qadd (qnat Ka) (qnat Kb)) := ⟨by rat_linarith, by rat_linarith⟩
    have bx : Ab (b.seq n) (qadd (qnat Ka) (qnat Kb)) := ⟨by rat_linarith, by rat_linarith⟩
    obtain ⟨L1, L2⟩ := CS_lip ax bx hab n
    exact ⟨lip_eps L1 (hH n) hHB, lip_eps L2 (hH n) hHB⟩
  exact ⟨fun k => by obtain ⟨N, hN⟩ := core k; exact ⟨N, fun n hn => close_of_ab (hN n hn).2⟩,
         fun k => by obtain ⟨N, hN⟩ := core k; exact ⟨N, fun n hn => close_of_ab (hN n hn).1⟩⟩

/-- THE SECOND-ORDER STEP OF `sin` on VR. -/
theorem r_s2 (x y : RExpr) :
    rCF.le (rCF.neg (Sq rCF x y)) (rCF.add (Rs rCF rsin rcos x y) (Rs rCF rsin rcos x y)) ∧
    rCF.le (rCF.add (Rs rCF rsin rcos x y) (Rs rCF rsin rcos x y)) (Sq rCF x y) := by
  obtain ⟨A, A0, hx, hy⟩ := ev_two x y
  have hlh : qle (qneg A) A := by rat_linarith
  have E := Ev_sin2 (sh := qone) (sl := qneg qone) hx hy hlh (Or.inl (qle_refl _)) (Or.inl (qle_refl _))
  constructor
  · intro k
    obtain ⟨N, hN⟩ := E k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨l, _⟩ := hN n hn
    show qle (qsub (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))))
      (qadd (qadd (qadd (Sn (y.seq n) n) (qneg (Sn (x.seq n) n))) (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (Cn (x.seq n) n))))
        (qadd (qadd (Sn (y.seq n) n) (qneg (Sn (x.seq n) n))) (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (Cn (x.seq n) n))))))
      (qeps k)
    unfold qsub at l ⊢
    have e : qEq (qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg qone))
        (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))))) := by rat_ring
    generalize qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg qone) = P at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))) = Q at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (Cn (x.seq n) n) = T at *
    rat_linarith
  · intro k
    obtain ⟨N, hN⟩ := E k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨_, u⟩ := hN n hn
    show qle (qsub
      (qadd (qadd (qadd (Sn (y.seq n) n) (qneg (Sn (x.seq n) n))) (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (Cn (x.seq n) n))))
        (qadd (qadd (Sn (y.seq n) n) (qneg (Sn (x.seq n) n))) (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (Cn (x.seq n) n)))))
      (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))))) (qeps k)
    unfold qsub at u ⊢
    have e : qEq (qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg (qneg qone)))
        (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) := by rat_ring
    generalize qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg (qneg qone)) = P at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))) = Q at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (Cn (x.seq n) n) = T at *
    rat_linarith

/-- THE SECOND-ORDER STEP OF `cos` on VR. -/
theorem r_c2 (x y : RExpr) :
    rCF.le (rCF.neg (Sq rCF x y)) (rCF.add (Rc rCF rsin rcos x y) (Rc rCF rsin rcos x y)) ∧
    rCF.le (rCF.add (Rc rCF rsin rcos x y) (Rc rCF rsin rcos x y)) (Sq rCF x y) := by
  obtain ⟨A, A0, hx, hy⟩ := ev_two x y
  have hlh : qle (qneg A) A := by rat_linarith
  have E := Ev_cos2 (ch := qone) (cl := qneg qone) hx hy hlh (Or.inl (qle_refl _)) (Or.inl (qle_refl _))
  constructor
  · intro k
    obtain ⟨N, hN⟩ := E k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨l, _⟩ := hN n hn
    show qle (qsub (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))))
      (qadd (qadd (qadd (Cn (y.seq n) n) (qneg (Cn (x.seq n) n))) (qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n)))
        (qadd (qadd (Cn (y.seq n) n) (qneg (Cn (x.seq n) n))) (qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n)))))
      (qeps k)
    unfold qsub at l ⊢
    have e : qEq (qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg qone))
        (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))))) := by rat_ring
    have f : qEq (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qneg (Sn (x.seq n) n))))
        (qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n)) := by rat_ring
    generalize qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg qone) = P at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))) = Q at *
    generalize qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qneg (Sn (x.seq n) n))) = T' at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n) = T at *
    rat_linarith
  · intro k
    obtain ⟨N, hN⟩ := E k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨_, u⟩ := hN n hn
    show qle (qsub
      (qadd (qadd (qadd (Cn (y.seq n) n) (qneg (Cn (x.seq n) n))) (qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n)))
        (qadd (qadd (Cn (y.seq n) n) (qneg (Cn (x.seq n) n))) (qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n))))
      (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))))) (qeps k)
    unfold qsub at u ⊢
    have e : qEq (qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg (qneg qone)))
        (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) := by rat_ring
    have f : qEq (qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qneg (Sn (x.seq n) n))))
        (qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n)) := by rat_ring
    generalize qmul (qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n)))) (qneg (qneg qone)) = P at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (qadd (y.seq n) (qneg (x.seq n))) = Q at *
    generalize qneg (qmul (qadd (y.seq n) (qneg (x.seq n))) (qneg (Sn (x.seq n) n))) = T' at *
    generalize qmul (qadd (y.seq n) (qneg (x.seq n))) (Sn (x.seq n) n) = T at *
    rat_linarith

/-- `|sin|, |cos| ≤ 1` on VR. -/
theorem r_bd (x : RExpr) : (rCF.le (rCF.neg rCF.one) (rsin x) ∧ rCF.le (rsin x) rCF.one) ∧
    (rCF.le (rCF.neg rCF.one) (rcos x) ∧ rCF.le (rcos x) rCF.one) := by
  obtain ⟨A, _, hx, _⟩ := ev_two x x
  refine ⟨⟨fun k => ?_, fun k => ?_⟩, ⟨fun k => ?_, fun k => ?_⟩⟩
  · obtain ⟨N, hN⟩ := sin_pm1 hx k
    exact ⟨N, fun n hn => by
      obtain ⟨a, _⟩ := hN n hn
      show qle (qsub (qneg qone) (Sn (x.seq n) n)) (qeps k)
      unfold qsub; rat_linarith⟩
  · obtain ⟨N, hN⟩ := sin_pm1 hx k
    exact ⟨N, fun n hn => by
      obtain ⟨_, b⟩ := hN n hn
      show qle (qsub (Sn (x.seq n) n) qone) (qeps k)
      unfold qsub; rat_linarith⟩
  · obtain ⟨N, hN⟩ := cos_pm1 hx k
    exact ⟨N, fun n hn => by
      obtain ⟨a, _⟩ := hN n hn
      show qle (qsub (qneg qone) (Cn (x.seq n) n)) (qeps k)
      unfold qsub; rat_linarith⟩
  · obtain ⟨N, hN⟩ := cos_pm1 hx k
    exact ⟨N, fun n hn => by
      obtain ⟨_, b⟩ := hN n hn
      show qle (qsub (Cn (x.seq n) n) qone) (qeps k)
      unfold qsub; rat_linarith⟩

/-- The double angle on VR. -/
theorem r_dbl (x : RExpr) :
    rEq (rsin (radd x x)) (radd (rmul (rsin x) (rcos x)) (rmul (rsin x) (rcos x))) ∧
    rEq (rcos (radd x x)) (radd (rmul (rcos x) (rcos x)) (rneg (rmul (rsin x) (rsin x)))) := by
  obtain ⟨A, A0, hb⟩ := bnd_real x
  obtain ⟨ec, es⟩ := add_lim A0 A0 hb hb
  constructor
  · intro k
    obtain ⟨N, hN⟩ := Eq0_get es k
    refine ⟨N, fun n hn => ?_⟩
    have d := hN n hn
    unfold ZTrig.sn ZTrig.cs at d
    show qclose (Sn (qadd (x.seq n) (x.seq n)) n)
      (qadd (qmul (Sn (x.seq n) n) (Cn (x.seq n) n)) (qmul (Sn (x.seq n) n) (Cn (x.seq n) n))) (qeps k)
    have c := qmul_comm (Cn (x.seq n) n) (Sn (x.seq n) n)
    obtain ⟨d1, d2⟩ := d
    unfold qclose; unfold qsub at d1 d2 ⊢
    generalize qmul (Cn (x.seq n) n) (Sn (x.seq n) n) = P at *
    generalize qmul (Sn (x.seq n) n) (Cn (x.seq n) n) = Q at *
    constructor <;> rat_linarith
  · intro k
    obtain ⟨N, hN⟩ := Eq0_get ec k
    refine ⟨N, fun n hn => ?_⟩
    have d := hN n hn
    unfold ZTrig.sn ZTrig.cs at d
    show qclose (Cn (qadd (x.seq n) (x.seq n)) n)
      (qadd (qmul (Cn (x.seq n) n) (Cn (x.seq n) n)) (qneg (qmul (Sn (x.seq n) n) (Sn (x.seq n) n)))) (qeps k)
    obtain ⟨d1, d2⟩ := d
    unfold qclose; unfold qsub at d1 d2 ⊢
    generalize qmul (Cn (x.seq n) n) (Cn (x.seq n) n) = P at *
    generalize qmul (Sn (x.seq n) n) (Sn (x.seq n) n) = Q at *
    constructor <;> rat_linarith

/-- Pythagoras on VR. -/
theorem r_py (x : RExpr) : rEq (radd (rmul (rsin x) (rsin x)) (rmul (rcos x) (rcos x))) rone := by
  obtain ⟨A, A0, Nb, hb⟩ := bnd_real x
  intro k
  obtain ⟨N0, h0⟩ := corner_small A0 A0 (k + 1)
  refine ⟨N0 + Nb + 1, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd (le_r' hn) (Nat.not_succ_le_zero 0)
  | succ m =>
      have p := pyth (hb (m + 1) (le_r' (le_l' hn))) m
      have c := h0 (m + 1) (le_l' (le_l' hn))
      have e := qeps_succ_add k
      obtain ⟨p1, p2⟩ := p
      show qclose (qadd (qmul (Sn (x.seq (m + 1)) (m + 1)) (Sn (x.seq (m + 1)) (m + 1)))
        (qmul (Cn (x.seq (m + 1)) (m + 1)) (Cn (x.seq (m + 1)) (m + 1)))) qone (qeps k)
      unfold qclose; unfold qsub at p1 p2 ⊢
      generalize corner (tm A) (tm A) (m + 1) = Cr at *
      generalize qmul (Sn (x.seq (m + 1)) (m + 1)) (Sn (x.seq (m + 1)) (m + 1)) = P at *
      generalize qmul (Cn (x.seq (m + 1)) (m + 1)) (Cn (x.seq (m + 1)) (m + 1)) = Q at *
      constructor <;> rat_linarith

/-- **VR's `sin`, `cos` ARE LAWFUL.** -/
theorem r_trigLaws : TrigLaws rCF rsin rcos where
  s0 := rsin_zero
  c0 := rcos_zero
  congr_s := fun h => (sc_congr h).1
  congr_c := fun h => (sc_congr h).2
  s2 := r_s2
  c2 := r_c2
  bs := fun x => (r_bd x).1
  bc := fun x => (r_bd x).2
  ds := fun x => (r_dbl x).1
  dc := fun x => (r_dbl x).2
  py := r_py

/-- **THE ORACLES CONVERGE UNIFORMLY**: `S_n(f_n(q))`, `C_n(f_n(q))` when `f` does. -/
theorem uc_sc {f : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) :
    UCo (fun n q => Sn (f n q) n) ∧ UCo (fun n q => Cn (f n q) n) := by
  have main : ∀ R, qle qzero R → ∃ C B0 : Nat,
      (∀ n (q : Nat → QExpr), B0 ≤ n → (∀ i, qclose (q i) qzero R) →
        qclose (Sn (f n q) n) qzero (qofInt (pow2 C)) ∧ qclose (Cn (f n q) n) qzero (qofInt (pow2 C))) ∧
      ∀ k, ∃ N, B0 ≤ N ∧ ∀ m n (q : Nat → QExpr), N ≤ m → N ≤ n → (∀ i, qclose (q i) qzero R) →
        qclose (Sn (f m q) m) (Sn (f n q) n) (qeps k) ∧ qclose (Cn (f m q) m) (Cn (f n q) n) (qeps k) := by
    intro R R0
    obtain ⟨Cf, Bf, bf, cf⟩ := hf R R0
    have hb : ∀ n (q : Nat → QExpr), Bf ≤ n → (∀ i, qclose (q i) qzero R) → Ab (f n q) (qnat (2 ^ Cf)) :=
      fun n q hn hq => ZRSin.ab_of_close (bf n q hn hq)
    have A0 := qnat_nonneg (2 ^ Cf)
    obtain ⟨N1, hS1⟩ := sin_abs_unif A0 0
    obtain ⟨N1', hC1⟩ := cos_abs_unif A0 0
    obtain ⟨C, hC⟩ := qexpr_bound (qadd qone qone)
    have e0 := qeps_zero
    refine ⟨C, Bf + (N1 + N1'), fun n q hn hq => ?_, fun k => ?_⟩
    · have y := hb n q (le_l' hn) hq
      obtain ⟨s1, s2⟩ := hS1 n (le_l' (le_r' hn)) _ y
      obtain ⟨c1, c2⟩ := hC1 n (le_r' (le_r' hn)) _ y
      refine ⟨ZRootExp.close_up (B := qadd qone qone) ?_ hC, ZRootExp.close_up (B := qadd qone qone) ?_ hC⟩ <;>
        (constructor <;> (unfold qsub; rat_linarith))
    · obtain ⟨M, hM⟩ := CS_unif A0 (k + 1)
      obtain ⟨H, hH⟩ := S_bounded A0
      obtain ⟨B, hB, _⟩ := qexpr_bound H
      have hHB : qle H (qofInt (pow2 B)) := by unfold qsub at hB; rat_linarith
      obtain ⟨N2, hN2b, h2⟩ := cf (k + 1 + B)
      refine ⟨Bf + (N1 + N1') + N2 + M, le_l' (le_l' (Nat.le_refl _)), fun m n q hm hn hq => ?_⟩
      have ym := hb m q (le_l' (le_l' (le_l' hm))) hq
      have yn := hb n q (le_l' (le_l' (le_l' hn))) hq
      obtain ⟨u1, u2⟩ := hM m n (le_r' hm) (le_r' hn) _ ym
      have cl := ab_of_cl (h2 m n q (le_r' (le_l' hm)) (le_r' (le_l' hn)) hq)
      obtain ⟨L1, L2⟩ := CS_lip ym yn cl n
      have l1 := lip_eps L1 (hH n) hHB
      have l2 := lip_eps L2 (hH n) hHB
      have e := qeps_succ_add k
      obtain ⟨a1, a2⟩ := u1; obtain ⟨b1, b2⟩ := u2
      obtain ⟨c1, c2⟩ := l1; obtain ⟨d1, d2⟩ := l2
      unfold qsub at a1 a2 b1 b2 c1 c2 d1 d2
      exact ⟨by constructor <;> (unfold qsub; rat_linarith), by constructor <;> (unfold qsub; rat_linarith)⟩
  refine ⟨fun R R0 => ?_, fun R R0 => ?_⟩ <;> obtain ⟨C, B0, b, c⟩ := main R R0
  · exact ⟨C, B0, fun n q hn hq => (b n q hn hq).1, fun k => by
      obtain ⟨N, hN, h⟩ := c k; exact ⟨N, hN, fun m n q hm hn hq => (h m n q hm hn hq).1⟩⟩
  · exact ⟨C, B0, fun n q hn hq => (b n q hn hq).2, fun k => by
      obtain ⟨N, hN, h⟩ := c k; exact ⟨N, hN, fun m n q hm hn hq => (h m n q hm hn hq).2⟩⟩

end ZRootSin

#print axioms ZRootSin.rsin_zero
#print axioms ZRootSin.rcos_zero
#print axioms ZRootSin.sc_congr
#print axioms ZRootSin.r_s2
#print axioms ZRootSin.r_c2
#print axioms ZRootSin.r_bd
#print axioms ZRootSin.r_dbl
#print axioms ZRootSin.r_py
#print axioms ZRootSin.r_trigLaws
#print axioms ZRootSin.uc_sc
