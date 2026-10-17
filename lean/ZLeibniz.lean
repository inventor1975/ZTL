import ZLimits

/-!
# ZLeibniz — the sign of `dI/dp` with limits that move (`zintegral._limit_sign`), as a finite difference. Zero axioms.

The kernel pins a parameter `p_j` of `I(p) = ∫_{A(p)}^{B(p)} f(x, p) dx` when
`t_j = f(B)·∂B/∂p_j − f(A)·∂A/∂p_j + (B − A)·∂f/∂p_j`, each factor read over the box, keeps a sign; then `I` is
read at a corner. No derivative of `I` is formed here. Between a point `p` of the box and its low corner `c` (each
pinned `p_j` moved to the end where `I` is smallest), two tagged sums that SHARE THEIR MIDDLE (the same tags `M` on
`[max(A(p), A(c)), min(B(p), B(c))]`) differ by
  * `Σ_M w·(f(t, p) − f(t, c))`, telescoped pin by pin, each step a finite difference along `p_j`
    (`ZMonoStep.slope_step`: `Δ_j·[∂f/∂p_j]`);
  * the two ends: `(A(c) − A(p))·φ_A + (B(p) − B(c))·φ_B`, `φ` a value of `f` on the end (read there), the limits'
    shifts telescoped the same way (`Δ_j·[∂A/∂p_j]`, `Δ_j·[∂B/∂p_j]`);
so the difference is `Σ_j Δ_j·t_j ≥ 0` up to `ε` — the sum at `p` is at least the corner's. The limits enter as their
values at an index `m` (rational), the integrand at `n` (tags fixed once `m` is): a double limit, as operational.
This file: the telescoping (`tele_id`), each pin's finite difference with its sign folded in (`step_up`), the
per-pin inequality (`pin_term`).
-/

namespace ZLeibniz

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZIntegral ZIntegralR
  ZMonoStep ZRangePin

/-- The pins are distinct. -/
def Distinct : List Nat → Prop
  | [] => True
  | j :: ns => (∀ m, List.Mem m ns → m ≠ j) ∧ Distinct ns

/-- The low corner's end of pin `j`. -/
def endL (B : Box QExpr) (up : Nat → Bool) (j : Nat) : QExpr := endOf B (!up j) j

/-- `g(p) − g(corner)` as the sum of the pins' steps. -/
def tele (g : Point QExpr → QExpr) (B : Box QExpr) (up : Nat → Bool) : List Nat → Point QExpr → QExpr
  | [], _ => qzero
  | j :: ns, p => qadd (qsub (g p) (g (upd p j (endL B up j)))) (tele g B up ns (upd p j (endL B up j)))

theorem tele_id (g : Point QExpr → QExpr) (B : Box QExpr) (up : Nat → Bool) :
    ∀ (ns : List Nat) (p : Point QExpr),
      qEq (qsub (g p) (g (cornerOn B (fun j => !up j) ns p))) (tele g B up ns p)
  | [], p => by show qEq (qsub (g p) (g p)) qzero; unfold qsub; rat_ring
  | j :: ns, p => by
      have ih := tele_id g B up ns (upd p j (endL B up j))
      show qEq (qsub (g p) (g (cornerOn B (fun j => !up j) ns (upd p j (endOf B (!up j) j)))))
        (qadd (qsub (g p) (g (upd p j (endL B up j)))) (tele g B up ns (upd p j (endL B up j))))
      have e : qEq (qsub (g p) (g (cornerOn B (fun j => !up j) ns (upd p j (endOf B (!up j) j)))))
          (qadd (qsub (g p) (g (upd p j (endL B up j))))
            (qsub (g (upd p j (endL B up j))) (g (cornerOn B (fun j => !up j) ns (upd p j (endL B up j)))))) := by
        unfold endL; unfold qsub; rat_ring
      exact qEq_trans e (qadd_respects (qEq_refl _) ih)

/-- The step's length toward the low corner, `≥ 0`: `p_j − lo` for a rising pin, `hi − p_j` for a falling one. -/
def dlt (B : Box QExpr) (up : Nat → Bool) (j : Nat) (p : Point QExpr) : QExpr :=
  match up j with
  | true => qsub (p j) (B j).1
  | false => qsub (B j).2 (p j)

/-- The derivative's reading with the pin's sign folded in: `[L, U]` rising, `[−U, −L]` falling. -/
def DRd (up : Bool) (L U : QExpr) : QExpr × QExpr :=
  match up with
  | true => (L, U)
  | false => (qneg U, qneg L)

/-- ONE PIN'S STEP: `g(q) − g(q at the low end of p_j)` lies in `dlt·[DRd]` — from the step reading and a box bound of
`D_j g` (`slope_step`), the sign folded so that the length is `≥ 0`. -/
theorem step_up {B : Box QExpr} {g : G} {j : Nat} {up : Nat → Bool} {L U : QExpr} (hS : StepRead B j g)
    (hV : BoxEv B (D j g) L U) {q : Point QExpr} (hq : InBox qOrd B q) :
    qle qzero (dlt B up j q) ∧
    Ev (fun n => qsub (evalN n q g) (evalN n (upd q j (endL B up j)) g))
      (qmul (DRd (up j) L U).1 (dlt B up j q)) (qmul (DRd (up j) L U).2 (dlt B up j q)) := by
  have hqj : qle (B j).1 (q j) ∧ qle (q j) (B j).2 := hq j
  obtain ⟨hj1, hj2⟩ := hqj
  have hself : InBox qOrd B (upd q j (q j)) := fun m => by rw [upd_same_pt]; exact hq m
  unfold dlt DRd endL
  cases up j with
  | true =>
      refine ⟨by show qle qzero (qsub (q j) (B j).1); unfold qsub; rat_linarith, fun k => ?_⟩
      obtain ⟨N, hN⟩ := slope_step hS hV (upd_end_inbox qOrd j false hq) hself hj1 k
      refine ⟨N, fun n hn => ?_⟩
      have h : qle (qsub (qmul L (qsub (q j) (B j).1)) (qeps k))
          (qsub (evalN n (upd q j (q j)) g) (evalN n (upd q j (B j).1) g)) ∧
          qle (qsub (evalN n (upd q j (q j)) g) (evalN n (upd q j (B j).1) g))
            (qadd (qmul U (qsub (q j) (B j).1)) (qeps k)) := hN n hn
      rw [eval_upd_same] at h
      exact h
  | false =>
      refine ⟨by show qle qzero (qsub (B j).2 (q j)); unfold qsub; rat_linarith, fun k => ?_⟩
      obtain ⟨N, hN⟩ := slope_step hS hV hself (upd_end_inbox qOrd j true hq) hj2 k
      refine ⟨N, fun n hn => ?_⟩
      have h : qle (qsub (qmul L (qsub (B j).2 (q j))) (qeps k))
          (qsub (evalN n (upd q j (B j).2) g) (evalN n (upd q j (q j)) g)) ∧
          qle (qsub (evalN n (upd q j (B j).2) g) (evalN n (upd q j (q j)) g))
            (qadd (qmul U (qsub (B j).2 (q j))) (qeps k)) := hN n hn
      rw [eval_upd_same] at h
      obtain ⟨a, b⟩ := h
      have e1 : qEq (qmul (qneg U) (qsub (B j).2 (q j))) (qneg (qmul U (qsub (B j).2 (q j)))) := by rat_ring
      have e2 : qEq (qmul (qneg L) (qsub (B j).2 (q j))) (qneg (qmul L (qsub (B j).2 (q j)))) := by rat_ring
      show qle (qsub (qmul (qneg U) (qsub (B j).2 (q j))) (qeps k)) (qsub (evalN n q g) (evalN n (upd q j (B j).2) g)) ∧
        qle (qsub (evalN n q g) (evalN n (upd q j (B j).2) g)) (qadd (qmul (qneg L) (qsub (B j).2 (q j))) (qeps k))
      generalize qmul U (qsub (B j).2 (q j)) = X at *; generalize qmul L (qsub (B j).2 (q j)) = Y at *
      generalize qmul (qneg U) (qsub (B j).2 (q j)) = X' at *; generalize qmul (qneg L) (qsub (B j).2 (q j)) = Y' at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- Corners with the second factor scaled by `d ≥ 0`. -/
theorem corners_scale_right {m M a1 a2 b1 b2 d : QExpr} (hc : Corners m M a1 a2 b1 b2) (hd : qle qzero d) :
    Corners (qmul m d) (qmul M d) a1 a2 (qmul b1 d) (qmul b2 d) := by
  obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hc
  have r : ∀ x y : QExpr, qEq (qmul (qmul x y) d) (qmul x (qmul y d)) := fun x y => by rat_ring
  exact ⟨⟨qle_respects (qEq_refl _) (r _ _) (ZExp.scale l11 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l12 hd),
          qle_respects (qEq_refl _) (r _ _) (ZExp.scale l21 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l22 hd)⟩,
         ⟨qle_respects (r _ _) (qEq_refl _) (ZExp.scale h11 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h12 hd),
          qle_respects (r _ _) (qEq_refl _) (ZExp.scale h21 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h22 hd)⟩⟩

/-- ONE PIN'S TERM: with `Δ ≥ 0` and the readings folded (`DRd`), the common part `C ≥ W·Δ·dfl − W·ε`, the limits'
shifts `x ∈ Δ·[dl, dh] ± ε`, the end values `φ ∈ [fl, fh] ± ε`, and the kernel's `t = cBl − cAh + cSl ≥ 0`:
`C − xA·φA + xB·φB ≥ −ε·E`, one `E` for every `ε ≤ 1`. -/
theorem pin_term {Δ Sl Sh dfl dfh dAl dAh dBl dBh fAl fAh fBl fBh cSl cSh cAl cAh cBl cBh : QExpr}
    (hΔ : qle qzero Δ) (hS0 : qle qzero Sh) (hdf : qle dfl dfh)
    (cS : Corners cSl cSh Sl Sh dfl dfh) (cA : Corners cAl cAh fAl fAh dAl dAh) (cB : Corners cBl cBh fBl fBh dBl dBh)
    (ht : qle qzero (qadd (qsub cBl cAh) cSl)) :
    ∃ E, qle qzero E ∧ ∀ {ε W C xA xB φA φB : QExpr}, qle qzero ε → qle ε qone →
      qle Sl W → qle W Sh → qle qzero W →
      qle (qsub (qmul W (qmul dfl Δ)) (qmul W ε)) C →
      qle (qsub (qmul dAl Δ) ε) xA → qle xA (qadd (qmul dAh Δ) ε) →
      qle (qsub (qmul dBl Δ) ε) xB → qle xB (qadd (qmul dBh Δ) ε) →
      qle (qsub fAl ε) φA → qle φA (qadd fAh ε) → qle (qsub fBl ε) φB → qle φB (qadd fBh ε) →
      qle (qneg (qmul ε E)) (qadd (qsub C (qmul xA φA)) (qmul xB φB)) := by
  obtain ⟨MA, _, MA0, _, mA1, mA2, mA3, mA4⟩ := bound4 fAl fAh (qmul dAl Δ) (qmul dAh Δ)
  obtain ⟨MB, _, MB0, _, mB1, mB2, mB3, mB4⟩ := bound4 fBl fBh (qmul dBl Δ) (qmul dBh Δ)
  have cA' := corners_scale_right cA hΔ
  have cB' := corners_scale_right cB hΔ
  refine ⟨qadd Sh (qadd (qadd (qadd MA MA) qone) (qadd (qadd MB MB) qone)), by rat_linarith, ?_⟩
  intro ε W C xA xB φA φB e0 e1 w1 w2 w0 hC a1 a2 b1 b2 f1 f2 g1 g2
  -- the common part: C ≥ Δ·cSl − Sh·ε
  have lo1 : qle cSl (qmul W dfl) := mul_lo w1 w2 (qle_refl dfl) hdf cS.1.1 cS.1.2.1 cS.1.2.2.1 cS.1.2.2.2
  have lo2 := ZExp.scale lo1 hΔ
  have lo3 := ZExp.scale w2 e0
  have r1 : qEq (qmul W (qmul dfl Δ)) (qmul (qmul W dfl) Δ) := by rat_ring
  -- the ends, by the corners with ε
  obtain ⟨_, pA⟩ := approx_corner cA' mA1 mA2 mA3 mA4 e0 e1 f1 f2 a1 a2
  obtain ⟨pB, _⟩ := approx_corner cB' mB1 mB2 mB3 mB4 e0 e1 g1 g2 b1 b2
  have cA2 := qmul_comm φA xA
  have cB2 := qmul_comm φB xB
  have tΔ := qmul_nonneg ht hΔ
  have rt : qEq (qmul (qadd (qsub cBl cAh) cSl) Δ) (qadd (qsub (qmul cBl Δ) (qmul cAh Δ)) (qmul cSl Δ)) := by
    unfold qsub; rat_ring
  have rE : qEq (qmul ε (qadd Sh (qadd (qadd (qadd MA MA) qone) (qadd (qadd MB MB) qone))))
      (qadd (qmul Sh ε) (qadd (qmul ε (qadd (qadd MA MA) qone)) (qmul ε (qadd (qadd MB MB) qone)))) := by rat_ring
  have rS : qEq (qmul W ε) (qmul W ε) := qEq_refl _
  generalize qmul W (qmul dfl Δ) = X1 at *
  generalize qmul (qmul W dfl) Δ = X2 at *
  generalize qmul cSl Δ = X3 at *
  generalize qmul W ε = X4 at *
  generalize qmul Sh ε = X5 at *
  generalize qmul φA xA = Y1 at *
  generalize qmul xA φA = Y2 at *
  generalize qmul φB xB = Z1 at *
  generalize qmul xB φB = Z2 at *
  generalize qmul ε (qadd (qadd MA MA) qone) = KA at *
  generalize qmul ε (qadd (qadd MB MB) qone) = KB at *
  generalize qmul ε (qadd Sh (qadd (qadd (qadd MA MA) qone) (qadd (qadd MB MB) qone))) = KE at *
  generalize qmul (qadd (qsub cBl cAh) cSl) Δ = T at *
  generalize qmul cBl Δ = U1 at *; generalize qmul cAh Δ = U2 at *
  unfold qsub at *; rat_linarith

theorem rsum_sub (f g : QExpr → QExpr) :
    ∀ l : List (QExpr × QExpr), qEq (qsub (rsum qSum f l) (rsum qSum g l)) (rsum qSum (fun t => qsub (f t) (g t)) l)
  | [] => by show qEq (qsub qzero qzero) qzero; unfold qsub; rat_ring
  | (w, t) :: rest => by
      have ih := rsum_sub f g rest
      show qEq (qsub (qadd (qmul w (f t)) (rsum qSum f rest)) (qadd (qmul w (g t)) (rsum qSum g rest)))
        (qadd (qmul w (qsub (f t) (g t))) (rsum qSum (fun t => qsub (f t) (g t)) rest))
      have e : qEq (qsub (qadd (qmul w (f t)) (rsum qSum f rest)) (qadd (qmul w (g t)) (rsum qSum g rest)))
          (qadd (qmul w (qsub (f t) (g t))) (qsub (rsum qSum f rest) (rsum qSum g rest))) := by unfold qsub; rat_ring
      exact qEq_trans e (qadd_respects (qEq_refl _) ih)

/-- The middle's sum at `q`, index `n`. -/
def mid (e : G) (i n : Nat) (M : List (QExpr × QExpr)) (q : Point QExpr) : QExpr :=
  rsum qSum (fun t => evalN n (upd q i t) e) M

theorem upd_swap (q : Point QExpr) {i j : Nat} (h : j ≠ i) (t v : QExpr) :
    ∀ m, upd (upd q i t) j v m = upd (upd q j v) i t m := fun m => by
  unfold upd
  cases Nat.decEq m j with
  | isTrue h1 =>
      cases Nat.decEq m i with
      | isTrue h2 => exact absurd (h1.symm.trans h2) h
      | isFalse _ => rfl
  | isFalse _ => rfl

/-- The tags' points stay in the box. -/
theorem tag_inbox {B : Box QExpr} {q : Point QExpr} {i : Nat} {t : QExpr} (hq : InBox qOrd B q)
    (h1 : qle (B i).1 t) (h2 : qle t (B i).2) : InBox qOrd B (upd q i t) := fun m => by
  unfold upd
  cases Nat.decEq m i with
  | isTrue h => subst h; exact ⟨h1, h2⟩
  | isFalse _ => exact hq m

/-- ONE PIN AT A POINT `q`, eventually: the middle's step, the limits' steps and the ends' values combine to at least
`−ε_k·E`. -/
theorem pin_ev {B : Box QExpr} {e A Bn : G} {i j : Nat} {up : Nat → Bool} (hji : j ≠ i)
    {Lf Uf LA UA LB UB Sl Sh fAl fAh fBl fBh cSl cSh cAl cAh cBl cBh : QExpr}
    (sf : StepRead B j e) (vf : BoxEv B (D j e) Lf Uf) (sA : StepRead B j A) (vA : BoxEv B (D j A) LA UA)
    (sB : StepRead B j Bn) (vB : BoxEv B (D j Bn) LB UB) (hS0 : qle qzero Sh) (hSl0 : qle qzero Sl)
    (hdf : qle (DRd (up j) Lf Uf).1 (DRd (up j) Lf Uf).2)
    (cS : Corners cSl cSh Sl Sh (DRd (up j) Lf Uf).1 (DRd (up j) Lf Uf).2)
    (cA : Corners cAl cAh fAl fAh (DRd (up j) LA UA).1 (DRd (up j) LA UA).2)
    (cB : Corners cBl cBh fBl fBh (DRd (up j) LB UB).1 (DRd (up j) LB UB).2)
    (ht : qle qzero (qadd (qsub cBl cAh) cSl)) {q : Point QExpr} (hq : InBox qOrd B q) :
    ∃ E, qle qzero E ∧ ∀ k, ∃ M0, ∀ m, M0 ≤ m → ∀ (Ml : List (QExpr × QExpr)),
      (∀ wt, List.Mem wt Ml → qle qzero wt.1 ∧ qle (B i).1 wt.2 ∧ qle wt.2 (B i).2) →
      qle Sl (wtotal qSum Ml) → qle (wtotal qSum Ml) Sh →
      ∃ N, ∀ n, N ≤ n → ∀ φA φB, qle (qsub fAl (qeps k)) φA → qle φA (qadd fAh (qeps k)) →
        qle (qsub fBl (qeps k)) φB → qle φB (qadd fBh (qeps k)) →
        qle (qneg (qmul (qeps k) E))
          (qadd (qsub (qsub (mid e i n Ml q) (mid e i n Ml (upd q j (endL B up j))))
              (qmul (qsub (evalN m q A) (evalN m (upd q j (endL B up j)) A)) φA))
            (qmul (qsub (evalN m q Bn) (evalN m (upd q j (endL B up j)) Bn)) φB)) := by
  obtain ⟨d0, _⟩ := step_up (up := up) sf vf hq
  obtain ⟨E, E0, hE⟩ := pin_term d0 hS0 hdf cS cA cB ht
  refine ⟨E, E0, fun k => ?_⟩
  obtain ⟨_, eA⟩ := step_up (up := up) sA vA hq
  obtain ⟨_, eB⟩ := step_up (up := up) sB vB hq
  obtain ⟨MA, hMA⟩ := eA k
  obtain ⟨MB, hMB⟩ := eB k
  refine ⟨MA + MB, fun m hm Ml hMl w1 w2 => ?_⟩
  obtain ⟨xa1, xa2⟩ := hMA m (Nat.le_trans (Nat.le_add_right _ _) hm)
  obtain ⟨xb1, xb2⟩ := hMB m (Nat.le_trans (Nat.le_add_left _ _) hm)
  -- the middle: each tag's step along p_j
  obtain ⟨N, hN⟩ := ev_list (fun (wt : QExpr × QExpr) n =>
      qle (qsub (qmul (DRd (up j) Lf Uf).1 (dlt B up j q)) (qeps k))
        (qsub (evalN n (upd q i wt.2) e) (evalN n (upd (upd q j (endL B up j)) i wt.2) e))) Ml
    (fun wt hw => by
      obtain ⟨_, t1, t2⟩ := hMl wt hw
      have hqt := tag_inbox hq t1 t2
      obtain ⟨_, ev⟩ := step_up (up := up) sf vf hqt
      have dl : dlt B up j (upd q i wt.2) = dlt B up j q := by
        unfold dlt; rw [upd_other q i wt.2 j hji]
      obtain ⟨N, hN⟩ := ev k
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨a, _⟩ := hN n hn
      have sw : evalN n (upd (upd q i wt.2) j (endL B up j)) e = evalN n (upd (upd q j (endL B up j)) i wt.2) e :=
        evalN_dep n _ _ e (fun m _ => upd_swap q hji wt.2 _ m)
      rw [dl] at a
      show qle (qsub (qmul (DRd (up j) Lf Uf).1 (dlt B up j q)) (qeps k))
        (qsub (evalN n (upd q i wt.2) e) (evalN n (upd (upd q j (endL B up j)) i wt.2) e))
      rw [← sw]; exact a)
  refine ⟨N, fun n hn φA φB fa1 fa2 fb1 fb2 => ?_⟩
  have pl := piece_lower qSum (fun t => qsub (evalN n (upd q i t) e) (evalN n (upd (upd q j (endL B up j)) i t) e))
    (qsub (qmul (DRd (up j) Lf Uf).1 (dlt B up j q)) (qeps k)) Ml
    (fun wt hw => ⟨(hMl wt hw).1, hN n hn wt hw⟩)
  have rs := rsum_sub (fun t => evalN n (upd q i t) e) (fun t => evalN n (upd (upd q j (endL B up j)) i t) e) Ml
  have hC : qle (qsub (qmul (wtotal qSum Ml) (qmul (DRd (up j) Lf Uf).1 (dlt B up j q))) (qmul (wtotal qSum Ml) (qeps k)))
      (qsub (mid e i n Ml q) (mid e i n Ml (upd q j (endL B up j)))) := by
    have pl' : qle (qmul (qsub (qmul (DRd (up j) Lf Uf).1 (dlt B up j q)) (qeps k)) (wtotal qSum Ml))
        (rsum qSum (fun t => qsub (evalN n (upd q i t) e) (evalN n (upd (upd q j (endL B up j)) i t) e)) Ml) := pl
    have r : qEq (qmul (qsub (qmul (DRd (up j) Lf Uf).1 (dlt B up j q)) (qeps k)) (wtotal qSum Ml))
        (qsub (qmul (wtotal qSum Ml) (qmul (DRd (up j) Lf Uf).1 (dlt B up j q))) (qmul (wtotal qSum Ml) (qeps k))) := by
      unfold qsub; rat_ring
    unfold mid
    exact qle_trans (qle_of_qEq (qEq_symm r)) (qle_trans pl' (qle_of_qEq (qEq_symm rs)))
  have W0 : qle qzero (wtotal qSum Ml) := qle_trans hSl0 w1
  exact hE (qeps_nonneg k) (ZTrig.qeps_le_one k) w1 w2 W0 hC xa1 xa2 xb1 xb2 fa1 fa2 fb1 fb2

/-- ALL THE PINS, telescoped from `q` to its low corner: `Σ_j (middle's step − φA·A's step + φB·B's step) ≥ −ε_k·E`. -/
theorem chain_ev {B : Box QExpr} {e A Bn : G} {i : Nat} {up : Nat → Bool}
    {Lf Uf LA UA LB UB cSl cSh cAl cAh cBl cBh : Nat → QExpr} {Sl Sh fAl fAh fBl fBh : QExpr}
    (hS0 : qle qzero Sh) (hSl0 : qle qzero Sl) :
    ∀ (ns : List Nat), (∀ j, List.Mem j ns →
      j ≠ i ∧ StepRead B j e ∧ BoxEv B (D j e) (Lf j) (Uf j) ∧ StepRead B j A ∧ BoxEv B (D j A) (LA j) (UA j) ∧
      StepRead B j Bn ∧ BoxEv B (D j Bn) (LB j) (UB j) ∧
      qle (DRd (up j) (Lf j) (Uf j)).1 (DRd (up j) (Lf j) (Uf j)).2 ∧
      Corners (cSl j) (cSh j) Sl Sh (DRd (up j) (Lf j) (Uf j)).1 (DRd (up j) (Lf j) (Uf j)).2 ∧
      Corners (cAl j) (cAh j) fAl fAh (DRd (up j) (LA j) (UA j)).1 (DRd (up j) (LA j) (UA j)).2 ∧
      Corners (cBl j) (cBh j) fBl fBh (DRd (up j) (LB j) (UB j)).1 (DRd (up j) (LB j) (UB j)).2 ∧
      qle qzero (qadd (qsub (cBl j) (cAh j)) (cSl j))) →
    ∀ (q : Point QExpr), InBox qOrd B q →
    ∃ E, qle qzero E ∧ ∀ k, ∃ M0, ∀ m, M0 ≤ m → ∀ (Ml : List (QExpr × QExpr)),
      (∀ wt, List.Mem wt Ml → qle qzero wt.1 ∧ qle (B i).1 wt.2 ∧ qle wt.2 (B i).2) →
      qle Sl (wtotal qSum Ml) → qle (wtotal qSum Ml) Sh →
      ∃ N, ∀ n, N ≤ n → ∀ φA φB, qle (qsub fAl (qeps k)) φA → qle φA (qadd fAh (qeps k)) →
        qle (qsub fBl (qeps k)) φB → qle φB (qadd fBh (qeps k)) →
        qle (qneg (qmul (qeps k) E))
          (qadd (qsub (tele (mid e i n Ml) B up ns q) (qmul (tele (fun r => evalN m r A) B up ns q) φA))
            (qmul (tele (fun r => evalN m r Bn) B up ns q) φB))
  | [], _, q, _ => ⟨qzero, qle_refl _, fun k => ⟨0, fun m _ Ml _ _ _ => ⟨0, fun n _ φA φB _ _ _ _ => by
      show qle (qneg (qmul (qeps k) qzero)) (qadd (qsub qzero (qmul qzero φA)) (qmul qzero φB))
      have e1 : qEq (qadd (qsub qzero (qmul qzero φA)) (qmul qzero φB)) qzero := by unfold qsub; rat_ring
      have e2 : qEq (qneg (qmul (qeps k) qzero)) qzero := by rat_ring
      exact qle_of_qEq (qEq_trans e2 (qEq_symm e1))⟩⟩⟩
  | j :: ns, h, q, hq => by
      obtain ⟨hji, sf, vf, sA, vA, sB, vB, hdf, cS, cA, cB, ht⟩ := h j (List.Mem.head ns)
      obtain ⟨E1, E10, h1⟩ := pin_ev (up := up) hji sf vf sA vA sB vB hS0 hSl0 hdf cS cA cB ht hq
      obtain ⟨E2, E20, h2⟩ := chain_ev hS0 hSl0 ns (fun m hm => h m (List.Mem.tail j hm))
        (upd q j (endL B up j)) (upd_end_inbox qOrd j (!up j) hq)
      refine ⟨qadd E1 E2, by rat_linarith, fun k => ?_⟩
      obtain ⟨M1, hM1⟩ := h1 k
      obtain ⟨M2, hM2⟩ := h2 k
      refine ⟨M1 + M2, fun m hm Ml hMl w1 w2 => ?_⟩
      obtain ⟨N1, hN1⟩ := hM1 m (Nat.le_trans (Nat.le_add_right _ _) hm) Ml hMl w1 w2
      obtain ⟨N2, hN2⟩ := hM2 m (Nat.le_trans (Nat.le_add_left _ _) hm) Ml hMl w1 w2
      refine ⟨N1 + N2, fun n hn φA φB a1 a2 b1 b2 => ?_⟩
      have p1 := hN1 n (Nat.le_trans (Nat.le_add_right _ _) hn) φA φB a1 a2 b1 b2
      have p2 := hN2 n (Nat.le_trans (Nat.le_add_left _ _) hn) φA φB a1 a2 b1 b2
      show qle (qneg (qmul (qeps k) (qadd E1 E2)))
        (qadd (qsub (qadd (qsub (mid e i n Ml q) (mid e i n Ml (upd q j (endL B up j))))
              (tele (mid e i n Ml) B up ns (upd q j (endL B up j))))
            (qmul (qadd (qsub (evalN m q A) (evalN m (upd q j (endL B up j)) A))
              (tele (fun r => evalN m r A) B up ns (upd q j (endL B up j)))) φA))
          (qmul (qadd (qsub (evalN m q Bn) (evalN m (upd q j (endL B up j)) Bn))
              (tele (fun r => evalN m r Bn) B up ns (upd q j (endL B up j)))) φB))
      have e1 : qEq (qmul (qeps k) (qadd E1 E2)) (qadd (qmul (qeps k) E1) (qmul (qeps k) E2)) := by rat_ring
      generalize mid e i n Ml q = a at *
      generalize mid e i n Ml (upd q j (endL B up j)) = a' at *
      generalize tele (mid e i n Ml) B up ns (upd q j (endL B up j)) = ta at *
      generalize qsub (evalN m q A) (evalN m (upd q j (endL B up j)) A) = x at *
      generalize tele (fun r => evalN m r A) B up ns (upd q j (endL B up j)) = tx at *
      generalize qsub (evalN m q Bn) (evalN m (upd q j (endL B up j)) Bn) = y at *
      generalize tele (fun r => evalN m r Bn) B up ns (upd q j (endL B up j)) = ty at *
      have r : qEq (qadd (qsub (qadd (qsub a a') ta) (qmul (qadd x tx) φA)) (qmul (qadd y ty) φB))
          (qadd (qadd (qsub (qsub a a') (qmul x φA)) (qmul y φB)) (qadd (qsub ta (qmul tx φA)) (qmul ty φB))) := by
        unfold qsub; rat_ring
      generalize qmul (qeps k) E1 = K1 at *; generalize qmul (qeps k) E2 = K2 at *
      generalize qmul (qeps k) (qadd E1 E2) = K at *
      generalize qadd (qsub (qadd (qsub a a') ta) (qmul (qadd x tx) φA)) (qmul (qadd y ty) φB) = Z at *
      generalize qadd (qsub (qsub a a') (qmul x φA)) (qmul y φB) = Z1 at *
      generalize qadd (qsub ta (qmul tx φA)) (qmul ty φB) = Z2 at *
      rat_linarith

theorem ab_mul' {u v H A : QExpr} (hu : ZTrig.Ab u H) (hv : ZTrig.Ab v A) : ZTrig.Ab (qmul u v) (qmul H A) := by
  obtain ⟨u1, u2⟩ := hu; obtain ⟨v1, v2⟩ := hv
  have H0 : qle qzero H := by rat_linarith
  cases qle_total qzero v with
  | inl hv0 =>
      have f1 := ZExp.scale u2 hv0; have f2 := ZExp.scale u1 hv0
      have f3 := scale_l v2 H0
      have e : qEq (qmul (qneg H) v) (qneg (qmul H v)) := by rat_ring
      exact ⟨by rat_linarith, by rat_linarith⟩
  | inr hv0 =>
      have hv0' : qle qzero (qneg v) := by rat_linarith
      have f1 := ZExp.scale u2 hv0'; have f2 := ZExp.scale u1 hv0'
      have f3 := scale_l (by rat_linarith : qle (qneg v) A) H0
      have e1 : qEq (qmul u (qneg v)) (qneg (qmul u v)) := by rat_ring
      have e2 : qEq (qmul (qneg H) (qneg v)) (qmul H v) := by rat_ring
      have e3 : qEq (qmul H (qneg v)) (qneg (qmul H v)) := by rat_ring
      exact ⟨by rat_linarith, by rat_linarith⟩

theorem wtotal_nonneg : ∀ (l : List (QExpr × QExpr)), (∀ wt, List.Mem wt l → qle qzero wt.1) →
    qle qzero (wtotal qSum l)
  | [], _ => qle_refl _
  | (w, t) :: rest, h => by
      have a := h (w, t) (List.Mem.head rest)
      have b := wtotal_nonneg rest (fun z hz => h z (List.Mem.tail _ hz))
      show qle qzero (qadd w (wtotal qSum rest)); rat_linarith

/-- AN END'S VALUE: a tagged sum with `f ∈ [lo, hi]` at its tags is `W·φ` for one `φ ∈ [lo, hi]`, `W` its weight. -/
theorem end_value {g : QExpr → QExpr} {lo hi : QExpr} (hlh : qle lo hi) (l : List (QExpr × QExpr))
    (h : ∀ wt, List.Mem wt l → qle qzero wt.1 ∧ qle lo (g wt.2) ∧ qle (g wt.2) hi) :
    ∃ φ, qle lo φ ∧ qle φ hi ∧ qEq (rsum qSum g l) (qmul (wtotal qSum l) φ) := by
  have W0 := wtotal_nonneg l (fun wt hw => (h wt hw).1)
  have pl : qle (qmul lo (wtotal qSum l)) (rsum qSum g l) := piece_lower qSum g lo l (fun wt hw => ⟨(h wt hw).1, (h wt hw).2.1⟩)
  have pu : qle (rsum qSum g l) (qmul hi (wtotal qSum l)) := piece_upper qSum g hi l (fun wt hw => ⟨(h wt hw).1, (h wt hw).2.2⟩)
  generalize wtotal qSum l = W at *
  generalize rsum qSum g l = R at *
  cases qle_total W qzero with
  | inl hz =>
      have z : qEq W qzero := qle_antisymm hz W0
      have e1 : qEq (qmul lo W) qzero := qEq_trans (qmul_respects (qEq_refl lo) z) (qmul_zero lo)
      have e2 : qEq (qmul hi W) qzero := qEq_trans (qmul_respects (qEq_refl hi) z) (qmul_zero hi)
      have e3 : qEq (qmul W lo) qzero := qEq_trans (qmul_respects z (qEq_refl lo)) (by rat_ring)
      refine ⟨lo, qle_refl _, hlh, ?_⟩
      generalize qmul lo W = A at *; generalize qmul hi W = A' at *; generalize qmul W lo = A'' at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | inr hp =>
      cases qle.decidable W qzero with
      | isTrue hz =>
          have z : qEq W qzero := qle_antisymm hz W0
          have e1 : qEq (qmul lo W) qzero := qEq_trans (qmul_respects (qEq_refl lo) z) (qmul_zero lo)
          have e2 : qEq (qmul hi W) qzero := qEq_trans (qmul_respects (qEq_refl hi) z) (qmul_zero hi)
          have e3 : qEq (qmul W lo) qzero := qEq_trans (qmul_respects z (qEq_refl lo)) (by rat_ring)
          refine ⟨lo, qle_refl _, hlh, ?_⟩
          generalize qmul lo W = A at *; generalize qmul hi W = A' at *; generalize qmul W lo = A'' at *
          exact qle_antisymm (by rat_linarith) (by rat_linarith)
      | isFalse hnz =>
          have Wp : qlt qzero W := qlt_iff_le_not_le.mpr ⟨W0, hnz⟩
          have nz := ne_zero_of_lt Wp
          have c := qmul_inv'_cancel nz
          have i0 := qinv'_nonneg_of_pos Wp
          refine ⟨qmul R (qinv' W), ?_, ?_, ?_⟩
          · have f := ZExp.scale pl i0
            have r : qEq (qmul (qmul lo W) (qinv' W)) (qmul lo (qmul W (qinv' W))) := by rat_ring
            have r2 := qmul_respects (qEq_refl lo) c
            have r3 := qmul_one lo
            generalize qmul (qmul lo W) (qinv' W) = X at *; generalize qmul lo (qmul W (qinv' W)) = Y at *
            generalize qmul W (qinv' W) = Z at *
            generalize qmul lo qone = V at *
            rat_linarith
          · have f := ZExp.scale pu i0
            have r : qEq (qmul (qmul hi W) (qinv' W)) (qmul hi (qmul W (qinv' W))) := by rat_ring
            have r2 := qmul_respects (qEq_refl hi) c
            have r3 := qmul_one hi
            generalize qmul (qmul hi W) (qinv' W) = X at *; generalize qmul hi (qmul W (qinv' W)) = Y at *
            generalize qmul W (qinv' W) = Z at *
            generalize qmul hi qone = V at *
            rat_linarith
          · have r : qEq (qmul W (qmul R (qinv' W))) (qmul R (qmul W (qinv' W))) := by rat_ring
            exact qEq_symm (qEq_trans r (qEq_trans (qmul_respects (qEq_refl R) c) (qmul_one R)))

/-- ONE END: the extra tags lie on the side that has them (`p`'s or the corner's); either way the ends' difference
is `(a2 − a1)·φ`, `φ` a value of `f` there. -/
theorem side_value {gp gc : QExpr → QExpr} {lo hi a1 a2 : QExpr} (hlh : qle lo hi) {Lp Lc : List (QExpr × QExpr)}
    (hp : ∀ wt, List.Mem wt Lp → qle qzero wt.1 ∧ qle lo (gp wt.2) ∧ qle (gp wt.2) hi)
    (hc : ∀ wt, List.Mem wt Lc → qle qzero wt.1 ∧ qle lo (gc wt.2) ∧ qle (gc wt.2) hi)
    (alt : (Lc = [] ∧ qEq (wtotal qSum Lp) (qsub a2 a1)) ∨ (Lp = [] ∧ qEq (wtotal qSum Lc) (qsub a1 a2))) :
    ∃ φ, qle lo φ ∧ qle φ hi ∧ qEq (qsub (rsum qSum gp Lp) (rsum qSum gc Lc)) (qmul (qsub a2 a1) φ) := by
  cases alt with
  | inl h =>
      obtain ⟨hL, hW⟩ := h
      subst hL
      obtain ⟨φ, f1, f2, e⟩ := end_value hlh Lp hp
      refine ⟨φ, f1, f2, ?_⟩
      show qEq (qsub (rsum qSum gp Lp) qzero) _
      have e2 := qmul_respects hW (qEq_refl φ)
      exact qEq_trans (by unfold qsub; rat_ring) (qEq_trans e e2)
  | inr h =>
      obtain ⟨hL, hW⟩ := h
      subst hL
      obtain ⟨φ, f1, f2, e⟩ := end_value hlh Lc hc
      refine ⟨φ, f1, f2, ?_⟩
      show qEq (qsub qzero (rsum qSum gc Lc)) _
      have e2 := qmul_respects hW (qEq_refl φ)
      have e3 : qEq (qsub qzero (qmul (qsub a1 a2) φ)) (qmul (qsub a2 a1) φ) := by unfold qsub; rat_ring
      exact qEq_trans (qadd_respects (qEq_refl _) (qneg_respects (qEq_trans e e2))) e3

/-- THE LEIBNIZ RULE AS A FINITE DIFFERENCE: at a point `p` of the box and its low corner `c`, two tagged sums sharing
their middle `Ml`, with the ends' extra tags `EpA/EcA`, `EpB/EcB` (on `p`'s side or the corner's) between the limits'
values at index `m` (`ap/ac`, `bp/bc`: `A`'s and `B`'s values at `p` and `c` up to vanishing errors — clamped into
their readings by the caller): the sum at `p` is at least the corner's, up to `ε_k`, once each pin's
`t_j = f(B)·∂B − f(A)·∂A + span·∂f` (folded by the pin's direction) is `≥ 0`. -/
theorem leibniz_low {B : Box QExpr} {e A Bn : G} {i : Nat} {up : Nat → Bool} {ns : List Nat}
    {Lf Uf LA UA LB UB cSl cSh cAl cAh cBl cBh : Nat → QExpr} {Sl Sh fAl fAh fBl fBh ra0 ra1 rb0 rb1 : QExpr}
    (hS0 : qle qzero Sh) (hSl0 : qle qzero Sl)
    (hchain : ∀ j, List.Mem j ns →
      j ≠ i ∧ StepRead B j e ∧ BoxEv B (D j e) (Lf j) (Uf j) ∧ StepRead B j A ∧ BoxEv B (D j A) (LA j) (UA j) ∧
      StepRead B j Bn ∧ BoxEv B (D j Bn) (LB j) (UB j) ∧
      qle (DRd (up j) (Lf j) (Uf j)).1 (DRd (up j) (Lf j) (Uf j)).2 ∧
      Corners (cSl j) (cSh j) Sl Sh (DRd (up j) (Lf j) (Uf j)).1 (DRd (up j) (Lf j) (Uf j)).2 ∧
      Corners (cAl j) (cAh j) fAl fAh (DRd (up j) (LA j) (UA j)).1 (DRd (up j) (LA j) (UA j)).2 ∧
      Corners (cBl j) (cBh j) fBl fBh (DRd (up j) (LB j) (UB j)).1 (DRd (up j) (LB j) (UB j)).2 ∧
      qle qzero (qadd (qsub (cBl j) (cAh j)) (cSl j)))
    {p : Point QExpr} (hp : InBox qOrd B p) (hfA : qle fAl fAh) (hfB : qle fBl fBh)
    (lAp : LeafEv e p i ra0 ra1 fAl fAh) (lAc : LeafEv e (cornerOn B (fun j => !up j) ns p) i ra0 ra1 fAl fAh)
    (lBp : LeafEv e p i rb0 rb1 fBl fBh) (lBc : LeafEv e (cornerOn B (fun j => !up j) ns p) i rb0 rb1 fBl fBh)
    {ap ac bp bc : Nat → QExpr}
    (hrA : ∀ k, ∃ M, ∀ m, M ≤ m → ZTrig.Ab (qsub (qsub (ap m) (evalN m p A))
      (qsub (ac m) (evalN m (cornerOn B (fun j => !up j) ns p) A))) (qeps k))
    (hrB : ∀ k, ∃ M, ∀ m, M ≤ m → ZTrig.Ab (qsub (qsub (bp m) (evalN m p Bn))
      (qsub (bc m) (evalN m (cornerOn B (fun j => !up j) ns p) Bn))) (qeps k)) :
    ∀ k, ∃ M0, ∀ m, M0 ≤ m → ∀ (Ml EpA EcA EpB EcB : List (QExpr × QExpr)),
      (∀ wt, List.Mem wt Ml → qle qzero wt.1 ∧ qle (B i).1 wt.2 ∧ qle wt.2 (B i).2) →
      qle Sl (wtotal qSum Ml) → qle (wtotal qSum Ml) Sh →
      (∀ wt, List.Mem wt EpA → qle qzero wt.1 ∧ qle ra0 wt.2 ∧ qle wt.2 ra1) →
      (∀ wt, List.Mem wt EcA → qle qzero wt.1 ∧ qle ra0 wt.2 ∧ qle wt.2 ra1) →
      (∀ wt, List.Mem wt EpB → qle qzero wt.1 ∧ qle rb0 wt.2 ∧ qle wt.2 rb1) →
      (∀ wt, List.Mem wt EcB → qle qzero wt.1 ∧ qle rb0 wt.2 ∧ qle wt.2 rb1) →
      ((EcA = [] ∧ qEq (wtotal qSum EpA) (qsub (ac m) (ap m))) ∨ (EpA = [] ∧ qEq (wtotal qSum EcA) (qsub (ap m) (ac m)))) →
      ((EcB = [] ∧ qEq (wtotal qSum EpB) (qsub (bp m) (bc m))) ∨ (EpB = [] ∧ qEq (wtotal qSum EcB) (qsub (bc m) (bp m)))) →
      ∃ N, ∀ n, N ≤ n →
        qle (qsub (qadd (qadd (mid e i n Ml (cornerOn B (fun j => !up j) ns p))
              (rsum qSum (fun t => evalN n (upd (cornerOn B (fun j => !up j) ns p) i t) e) EcA))
              (rsum qSum (fun t => evalN n (upd (cornerOn B (fun j => !up j) ns p) i t) e) EcB)) (qeps k))
          (qadd (qadd (mid e i n Ml p) (rsum qSum (fun t => evalN n (upd p i t) e) EpA))
            (rsum qSum (fun t => evalN n (upd p i t) e) EpB)) := by
  intro k
  generalize hc : cornerOn B (fun j => !up j) ns p = c at *
  obtain ⟨E, E0, hch⟩ := chain_ev hS0 hSl0 ns hchain p hp
  obtain ⟨MΦ, _, MΦ0, _, m1, m2, m3, m4⟩ := bound4 fAl fAh fBl fBh
  have o := qle_of_qlt qone_pos
  obtain ⟨B1, hB1⟩ := ZAtan.eps_scaledA E0
  obtain ⟨B2, hB2⟩ := ZAtan.eps_scaledA (by rat_linarith : qle qzero (qadd MΦ qone))
  obtain ⟨M1, hM1⟩ := hch (k + 2 + B1 + B2)
  obtain ⟨M2, hM2⟩ := hrA (k + 2 + B2)
  obtain ⟨M3, hM3⟩ := hrB (k + 2 + B2)
  refine ⟨M1 + (M2 + M3), fun m hm Ml EpA EcA EpB EcB hMl w1 w2 hEpA hEcA hEpB hEcB altA altB => ?_⟩
  obtain ⟨N1, hN1⟩ := hM1 m (Nat.le_trans (Nat.le_add_right _ _) hm) Ml hMl w1 w2
  have rA := hM2 m (Nat.le_trans (Nat.le_trans (Nat.le_add_right M2 M3) (Nat.le_add_left _ M1)) hm)
  have rB := hM3 m (Nat.le_trans (Nat.le_trans (Nat.le_add_left M3 M2) (Nat.le_add_left _ M1)) hm)
  generalize hK : k + 2 + B1 + B2 = K at *
  -- the ends' tags: f read there, eventually
  have tags : ∀ (q : Point QExpr) (lo hi fl fh : QExpr), LeafEv e q i lo hi fl fh → ∀ (L : List (QExpr × QExpr)),
      (∀ wt, List.Mem wt L → qle qzero wt.1 ∧ qle lo wt.2 ∧ qle wt.2 hi) →
      ∃ N, ∀ n, N ≤ n → ∀ wt, List.Mem wt L → qle qzero wt.1 ∧ qle (qsub fl (qeps K)) (evalN n (upd q i wt.2) e) ∧
        qle (evalN n (upd q i wt.2) e) (qadd fh (qeps K)) := by
    intro q lo hi fl fh lf L hL
    obtain ⟨N, hN⟩ := ev_list (fun (wt : QExpr × QExpr) n =>
        qle (qsub fl (qeps K)) (evalN n (upd q i wt.2) e) ∧ qle (evalN n (upd q i wt.2) e) (qadd fh (qeps K))) L
      (fun wt hw => lf wt.2 (hL wt hw).2.1 (hL wt hw).2.2 K)
    exact ⟨N, fun n hn wt hw => ⟨(hL wt hw).1, hN n hn wt hw⟩⟩
  obtain ⟨N2, h2⟩ := tags p ra0 ra1 fAl fAh lAp EpA hEpA
  obtain ⟨N3, h3⟩ := tags c ra0 ra1 fAl fAh lAc EcA hEcA
  obtain ⟨N4, h4⟩ := tags p rb0 rb1 fBl fBh lBp EpB hEpB
  obtain ⟨N5, h5⟩ := tags c rb0 rb1 fBl fBh lBc EcB hEcB
  refine ⟨N1 + (N2 + (N3 + (N4 + N5))), fun n hn => ?_⟩
  have le1 : N1 ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have le2 : N2 ≤ n := ZAtan.le4b (a := N1) (c := N3) (d := N4 + N5) (by
    have : N1 + (N2 + (N3 + (N4 + N5))) = N1 + (N2 + (N3 + (N4 + N5))) := rfl; exact hn)
  have le3 : N3 ≤ n := ZAtan.le4c (a := N1) (b := N2) (d := N4 + N5) hn
  have le45 : N4 + N5 ≤ n := ZAtan.le4d (a := N1) (b := N2) (c := N3) hn
  have le4 : N4 ≤ n := Nat.le_trans (Nat.le_add_right _ _) le45
  have le5 : N5 ≤ n := Nat.le_trans (Nat.le_add_left _ _) le45
  have hlhA : qle (qsub fAl (qeps K)) (qadd fAh (qeps K)) := by have := qeps_nonneg K; unfold qsub; rat_linarith
  have hlhB : qle (qsub fBl (qeps K)) (qadd fBh (qeps K)) := by have := qeps_nonneg K; unfold qsub; rat_linarith
  obtain ⟨φA, a1, a2, eA⟩ := side_value (gp := fun t => evalN n (upd p i t) e) (gc := fun t => evalN n (upd c i t) e)
    hlhA (h2 n le2) (h3 n le3) altA
  obtain ⟨φB, b1, b2, eB⟩ := side_value (gp := fun t => evalN n (upd p i t) e) (gc := fun t => evalN n (upd c i t) e)
    hlhB (h4 n le4) (h5 n le5) altB
  have ch := hN1 n le1 φA φB a1 a2 b1 b2
  have tm := tele_id (mid e i n Ml) B up ns p
  have tA := tele_id (fun r => evalN m r A) B up ns p
  have tB := tele_id (fun r => evalN m r Bn) B up ns p
  rw [hc] at tm tA tB
  -- |φ| ≤ MΦ + 1
  have q1 := ZTrig.qeps_le_one K
  have e0 := qeps_nonneg K
  unfold qclose qsub at m1 m2 m3 m4
  obtain ⟨m1a, m1b⟩ := m1; obtain ⟨m2a, m2b⟩ := m2; obtain ⟨m3a, m3b⟩ := m3; obtain ⟨m4a, m4b⟩ := m4
  have abA : ZTrig.Ab φA (qadd MΦ qone) := by unfold qsub at a1; exact ⟨by rat_linarith, by rat_linarith⟩
  have abB : ZTrig.Ab φB (qadd MΦ qone) := by unfold qsub at b1; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨pa1, pa2⟩ := ab_mul' rA abA
  obtain ⟨pb1, pb2⟩ := ab_mul' rB abB
  have sA := hB2 (k + 2)
  have sB1 := hB1 (k + 2)
  have eK1 : qle (qeps K) (qeps (k + 2 + B1)) := ZAtan.eps_of_le (by rw [← hK]; exact Nat.le_add_right _ _)
  have eKE := ZExp.scale eK1 E0
  have c1 := qmul_comm (qeps (k + 2 + B1)) E
  have c2 := qmul_comm (qeps K) E
  have c3 := qmul_comm (qeps (k + 2 + B2)) (qadd MΦ qone)
  have s1 := qeps_succ_add k; have s2 := qeps_succ_add (k + 1)
  have z2 := qeps_nonneg (k + 2)
  -- the identity: S_p − S_c = chain − rA'·φA + rB'·φB
  generalize mid e i n Ml p = Mp at *
  generalize mid e i n Ml c = Mc at *
  generalize tele (mid e i n Ml) B up ns p = TM at *
  generalize tele (fun r => evalN m r A) B up ns p = TA at *
  generalize tele (fun r => evalN m r Bn) B up ns p = TB at *
  generalize evalN m p A = Ap at *; generalize evalN m c A = Ac at *
  generalize evalN m p Bn = Bp at *; generalize evalN m c Bn = Bc at *
  generalize rsum qSum (fun t => evalN n (upd p i t) e) EpA = RpA at *
  generalize rsum qSum (fun t => evalN n (upd c i t) e) EcA = RcA at *
  generalize rsum qSum (fun t => evalN n (upd p i t) e) EpB = RpB at *
  generalize rsum qSum (fun t => evalN n (upd c i t) e) EcB = RcB at *
  generalize ap m = aP at *; generalize ac m = aC at *; generalize bp m = bP at *; generalize bc m = bC at *
  have key : qEq (qsub (qadd (qadd Mp RpA) RpB) (qadd (qadd Mc RcA) RcB))
      (qadd (qadd (qadd (qsub TM (qmul TA φA)) (qmul TB φB))
        (qneg (qmul (qsub (qsub aP Ap) (qsub aC Ac)) φA)))
        (qmul (qsub (qsub bP Bp) (qsub bC Bc)) φB)) := by
    have i1 : qEq (qsub (qadd (qadd Mp RpA) RpB) (qadd (qadd Mc RcA) RcB))
        (qadd (qadd (qsub Mp Mc) (qsub RpA RcA)) (qsub RpB RcB)) := by unfold qsub; rat_ring
    refine qEq_trans i1 ?_
    have j1 := qadd_respects (qadd_respects (qEq_refl (qsub Mp Mc)) eA) eB
    refine qEq_trans j1 ?_
    have j2 : qEq TA (qsub Ap Ac) := qEq_symm tA
    have j3 : qEq TB (qsub Bp Bc) := qEq_symm tB
    have k1 := qmul_respects j2 (qEq_refl φA)
    have k2 := qmul_respects j3 (qEq_refl φB)
    have l1 : qEq (qadd (qadd (qsub Mp Mc) (qmul (qsub aC aP) φA)) (qmul (qsub bP bC) φB))
        (qadd (qadd (qadd (qsub (qsub Mp Mc) (qmul (qsub Ap Ac) φA)) (qmul (qsub Bp Bc) φB))
          (qneg (qmul (qsub (qsub aP Ap) (qsub aC Ac)) φA)))
          (qmul (qsub (qsub bP Bp) (qsub bC Bc)) φB)) := by unfold qsub; rat_ring
    refine qEq_trans l1 ?_
    have tmq : qEq (qsub Mp Mc) TM := tm
    exact qadd_respects (qadd_respects (qadd_respects (qadd_respects tmq (qneg_respects (qEq_symm k1)))
      (qEq_symm k2)) (qEq_refl _)) (qEq_refl _)
  generalize qmul TA φA = X1 at *; generalize qmul TB φB = X2 at *
  generalize qmul (qsub (qsub aP Ap) (qsub aC Ac)) φA = Y1 at *
  generalize qmul (qsub (qsub bP Bp) (qsub bC Bc)) φB = Y2 at *
  generalize qmul (qeps (k + 2 + B2)) (qadd MΦ qone) = Z1 at *
  generalize qmul (qadd MΦ qone) (qeps (k + 2 + B2)) = Z2 at *
  generalize qmul (qeps K) E = W1 at *; generalize qmul E (qeps K) = W2 at *
  generalize qmul (qeps (k + 2 + B1)) E = W3 at *; generalize qmul E (qeps (k + 2 + B1)) = W4 at *
  unfold qsub at *; rat_linarith

/-- `0 − e`. -/
def ng (e : G) : G := .sub (.const qzero) e

theorem rsum_zero : ∀ (l : List (QExpr × QExpr)), qEq (rsum qSum (fun _ => qzero) l) qzero
  | [] => qEq_refl _
  | (w, _) :: rest => by
      show qEq (qadd (qmul w qzero) (rsum qSum (fun _ => qzero) rest)) qzero
      exact qEq_trans (qadd_respects (qmul_zero w) (rsum_zero rest)) (by rat_ring)

theorem rsum_ng (n i : Nat) (e : G) (q : Point QExpr) (l : List (QExpr × QExpr)) :
    qEq (rsum qSum (fun t => evalN n (upd q i t) (ng e)) l) (qneg (rsum qSum (fun t => evalN n (upd q i t) e) l)) := by
  have h := rsum_sub (fun _ => qzero) (fun t => evalN n (upd q i t) e) l
  have z := rsum_zero l
  have e1 : qEq (rsum qSum (fun t => evalN n (upd q i t) (ng e)) l)
      (rsum qSum (fun t => qsub qzero (evalN n (upd q i t) e)) l) := qEq_refl _
  refine qEq_trans e1 (qEq_trans (qEq_symm h) ?_)
  generalize rsum qSum (fun _ => qzero) l = Z at *
  unfold qsub; exact qEq_trans (qadd_respects z (qEq_refl _)) (by rat_ring)

/-- THE UPPER SIDE: `leibniz_low` for `0 − f` — the sum at `p` is at most the corner's (the caller's flags put that
corner where `I` is largest), up to `ε_k`. -/
theorem leibniz_high {B : Box QExpr} {e A Bn : G} {i : Nat} {up : Nat → Bool} {ns : List Nat}
    {Lf Uf LA UA LB UB cSl cSh cAl cAh cBl cBh : Nat → QExpr} {Sl Sh fAl fAh fBl fBh ra0 ra1 rb0 rb1 : QExpr}
    (hS0 : qle qzero Sh) (hSl0 : qle qzero Sl)
    (hchain : ∀ j, List.Mem j ns →
      j ≠ i ∧ StepRead B j (ng e) ∧ BoxEv B (D j (ng e)) (Lf j) (Uf j) ∧ StepRead B j A ∧ BoxEv B (D j A) (LA j) (UA j) ∧
      StepRead B j Bn ∧ BoxEv B (D j Bn) (LB j) (UB j) ∧
      qle (DRd (up j) (Lf j) (Uf j)).1 (DRd (up j) (Lf j) (Uf j)).2 ∧
      Corners (cSl j) (cSh j) Sl Sh (DRd (up j) (Lf j) (Uf j)).1 (DRd (up j) (Lf j) (Uf j)).2 ∧
      Corners (cAl j) (cAh j) fAl fAh (DRd (up j) (LA j) (UA j)).1 (DRd (up j) (LA j) (UA j)).2 ∧
      Corners (cBl j) (cBh j) fBl fBh (DRd (up j) (LB j) (UB j)).1 (DRd (up j) (LB j) (UB j)).2 ∧
      qle qzero (qadd (qsub (cBl j) (cAh j)) (cSl j)))
    {p : Point QExpr} (hp : InBox qOrd B p) (hfA : qle fAl fAh) (hfB : qle fBl fBh)
    (lAp : LeafEv (ng e) p i ra0 ra1 fAl fAh) (lAc : LeafEv (ng e) (cornerOn B (fun j => !up j) ns p) i ra0 ra1 fAl fAh)
    (lBp : LeafEv (ng e) p i rb0 rb1 fBl fBh) (lBc : LeafEv (ng e) (cornerOn B (fun j => !up j) ns p) i rb0 rb1 fBl fBh)
    {ap ac bp bc : Nat → QExpr}
    (hrA : ∀ k, ∃ M, ∀ m, M ≤ m → ZTrig.Ab (qsub (qsub (ap m) (evalN m p A))
      (qsub (ac m) (evalN m (cornerOn B (fun j => !up j) ns p) A))) (qeps k))
    (hrB : ∀ k, ∃ M, ∀ m, M ≤ m → ZTrig.Ab (qsub (qsub (bp m) (evalN m p Bn))
      (qsub (bc m) (evalN m (cornerOn B (fun j => !up j) ns p) Bn))) (qeps k)) :
    ∀ k, ∃ M0, ∀ m, M0 ≤ m → ∀ (Ml EpA EcA EpB EcB : List (QExpr × QExpr)),
      (∀ wt, List.Mem wt Ml → qle qzero wt.1 ∧ qle (B i).1 wt.2 ∧ qle wt.2 (B i).2) →
      qle Sl (wtotal qSum Ml) → qle (wtotal qSum Ml) Sh →
      (∀ wt, List.Mem wt EpA → qle qzero wt.1 ∧ qle ra0 wt.2 ∧ qle wt.2 ra1) →
      (∀ wt, List.Mem wt EcA → qle qzero wt.1 ∧ qle ra0 wt.2 ∧ qle wt.2 ra1) →
      (∀ wt, List.Mem wt EpB → qle qzero wt.1 ∧ qle rb0 wt.2 ∧ qle wt.2 rb1) →
      (∀ wt, List.Mem wt EcB → qle qzero wt.1 ∧ qle rb0 wt.2 ∧ qle wt.2 rb1) →
      ((EcA = [] ∧ qEq (wtotal qSum EpA) (qsub (ac m) (ap m))) ∨ (EpA = [] ∧ qEq (wtotal qSum EcA) (qsub (ap m) (ac m)))) →
      ((EcB = [] ∧ qEq (wtotal qSum EpB) (qsub (bp m) (bc m))) ∨ (EpB = [] ∧ qEq (wtotal qSum EcB) (qsub (bc m) (bp m)))) →
      ∃ N, ∀ n, N ≤ n →
        qle (qadd (qadd (mid e i n Ml p) (rsum qSum (fun t => evalN n (upd p i t) e) EpA))
            (rsum qSum (fun t => evalN n (upd p i t) e) EpB))
          (qadd (qadd (qadd (mid e i n Ml (cornerOn B (fun j => !up j) ns p))
              (rsum qSum (fun t => evalN n (upd (cornerOn B (fun j => !up j) ns p) i t) e) EcA))
              (rsum qSum (fun t => evalN n (upd (cornerOn B (fun j => !up j) ns p) i t) e) EcB)) (qeps k)) := by
  intro k
  obtain ⟨M0, h⟩ := leibniz_low hS0 hSl0 hchain hp hfA hfB lAp lAc lBp lBc hrA hrB k
  refine ⟨M0, fun m hm Ml EpA EcA EpB EcB a1 a2 a3 a4 a5 a6 a7 a8 a9 => ?_⟩
  obtain ⟨N, hN⟩ := h m hm Ml EpA EcA EpB EcB a1 a2 a3 a4 a5 a6 a7 a8 a9
  refine ⟨N, fun n hn => ?_⟩
  have g := hN n hn
  generalize cornerOn B (fun j => !up j) ns p = c at *
  have n1 := rsum_ng n i e p Ml; have n2 := rsum_ng n i e c Ml
  have n3 := rsum_ng n i e p EpA; have n4 := rsum_ng n i e c EcA
  have n5 := rsum_ng n i e p EpB; have n6 := rsum_ng n i e c EcB
  unfold mid at *
  generalize rsum qSum (fun t => evalN n (upd p i t) (ng e)) Ml = a at *
  generalize rsum qSum (fun t => evalN n (upd c i t) (ng e)) Ml = b at *
  generalize rsum qSum (fun t => evalN n (upd p i t) (ng e)) EpA = c1 at *
  generalize rsum qSum (fun t => evalN n (upd c i t) (ng e)) EcA = c2 at *
  generalize rsum qSum (fun t => evalN n (upd p i t) (ng e)) EpB = c3 at *
  generalize rsum qSum (fun t => evalN n (upd c i t) (ng e)) EcB = c4 at *
  unfold qsub at *; rat_linarith

end ZLeibniz

#print axioms ZLeibniz.tele_id
#print axioms ZLeibniz.step_up
#print axioms ZLeibniz.pin_term
#print axioms ZLeibniz.pin_ev
#print axioms ZLeibniz.chain_ev
#print axioms ZLeibniz.end_value
#print axioms ZLeibniz.side_value
#print axioms ZLeibniz.leibniz_low
#print axioms ZLeibniz.rsum_ng
#print axioms ZLeibniz.leibniz_high
