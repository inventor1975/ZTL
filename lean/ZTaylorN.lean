import ZDeriv

/-!
# ZTaylorN — Taylor of every order, from the derivative step, on a grid. Zero axioms.

Layer 2 of the higher Taylor orders. `Diter i m e` — the `m`-th symbolic derivative (`ZDeriv.D`). The claim, by
induction on `m`: between two points `p`, `q` of a box differing in `x_i` by `Δ`, the remainder after the Taylor
polynomial of degree `m − 1` lies in `Δ^m/m!·[L, U]` (`[L, U]` the reading of `D^m e` over the box), up to `ε`, from
some index on. Order `m + 1` from order `m` of `D e`: along `2^K` grid steps `e(q) − e(p) = Σ δ·De(x_j) + o(1)`
(`ZDeriv.step_sound`), each `De(x_j)` expanded to order `m` at `p`; the sums of powers by Faulhaber's bounds
(`faul_up`, `faul_lo`), the remainders with weights of one sign — no mean value theorem, no intermediate point.

This file, part 1: the sums of powers.
-/

namespace ZTaylorN

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv

theorem gsum_bounds {a b : QExpr} (ha : qle qzero a) (hab : qle a b) : ∀ k,
    qle (qmul (qnat (k + 1)) (qpowN a k)) (gsum a b k) ∧ qle (gsum a b k) (qmul (qnat (k + 1)) (qpowN b k))
  | 0 => by
      have n1 := qnat_succ 0; have n0 := qnat_zero
      have e : qEq (qmul (qnat 1) (qpowN a 0)) qone := by
        show qEq (qmul (qnat 1) qone) qone
        have := qmul_respects (qEq_trans n1 (qadd_respects n0 (qEq_refl qone))) (qEq_refl qone)
        exact qEq_trans this (by rat_ring)
      have e' : qEq (qmul (qnat 1) (qpowN b 0)) qone := by
        show qEq (qmul (qnat 1) qone) qone
        have := qmul_respects (qEq_trans n1 (qadd_respects n0 (qEq_refl qone))) (qEq_refl qone)
        exact qEq_trans this (by rat_ring)
      show qle _ qone ∧ qle qone _
      exact ⟨by rat_linarith, by rat_linarith⟩
  | k + 1 => by
      obtain ⟨l, u⟩ := gsum_bounds ha hab k
      have b0 := qle_trans ha hab
      have pa := powN_nonneg ha k
      have pb := powN_nonneg b0 k
      have nk := qnat_nonneg (k + 1)
      -- lower: b·(k+1)a^k + a^{k+1} ≥ a·(k+1)a^k + a^{k+1} = (k+2)a^{k+1}
      have l1 := scale_l l b0
      have l2 := ZExp.scale hab (qmul_nonneg nk pa)
      have u1 := scale_l u b0
      have u2 := powN_mono ha hab (k + 1)
      have s := qnat_succ (k + 1)
      have ea := qmul_respects s (qEq_refl (qpowN a (k + 1)))
      have eb := qmul_respects s (qEq_refl (qpowN b (k + 1)))
      have ia : qEq (qmul (qadd (qnat (k + 1)) qone) (qpowN a (k + 1)))
          (qadd (qmul a (qmul (qnat (k + 1)) (qpowN a k))) (qpowN a (k + 1))) := by
        show qEq (qmul (qadd (qnat (k + 1)) qone) (qmul (qpowN a k) a)) (qadd (qmul a (qmul (qnat (k + 1)) (qpowN a k))) (qmul (qpowN a k) a))
        rat_ring
      have ib : qEq (qmul (qadd (qnat (k + 1)) qone) (qpowN b (k + 1)))
          (qadd (qmul b (qmul (qnat (k + 1)) (qpowN b k))) (qpowN b (k + 1))) := by
        show qEq (qmul (qadd (qnat (k + 1)) qone) (qmul (qpowN b k) b)) (qadd (qmul b (qmul (qnat (k + 1)) (qpowN b k))) (qmul (qpowN b k) b))
        rat_ring
      have c1 := qmul_comm (qmul (qnat (k + 1)) (qpowN a k)) a
      show qle _ (qadd (qmul b (gsum a b k)) (qpowN a (k + 1))) ∧ qle (qadd (qmul b (gsum a b k)) (qpowN a (k + 1))) _
      generalize qmul (qnat (k + 1 + 1)) (qpowN a (k + 1)) = A1 at *
      generalize qmul (qnat (k + 1 + 1)) (qpowN b (k + 1)) = B1 at *
      generalize qmul (qadd (qnat (k + 1)) qone) (qpowN a (k + 1)) = A2 at *
      generalize qmul (qadd (qnat (k + 1)) qone) (qpowN b (k + 1)) = B2 at *
      generalize qmul b (gsum a b k) = G1 at *
      generalize qmul b (qmul (qnat (k + 1)) (qpowN a k)) = G2 at *
      generalize qmul a (qmul (qnat (k + 1)) (qpowN a k)) = G3 at *
      generalize qmul (qmul (qnat (k + 1)) (qpowN a k)) a = G3' at *
      generalize qmul b (qmul (qnat (k + 1)) (qpowN b k)) = G4 at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- `Σ_{j<G} j^t`. -/
def spow (t G : Nat) : QExpr := ZTrig.bs (fun j => qpowN (qnat j) t) G

/-- FAULHABER FROM ABOVE: `(t + 1)·Σ_{j<G} j^t ≤ G^{t+1}`. -/
theorem faul_up (t : Nat) : ∀ G, qle (qmul (qnat (t + 1)) (spow t G)) (qpowN (qnat G) (t + 1))
  | 0 => by
      show qle (qmul (qnat (t + 1)) qzero) (qmul (qpowN (qnat 0) t) (qnat 0))
      have z := qnat_zero
      have e1 : qEq (qmul (qnat (t + 1)) qzero) qzero := by rat_ring
      have e2 := qmul_respects (qEq_refl (qpowN (qnat 0) t)) z
      have e3 : qEq (qmul (qpowN (qnat 0) t) qzero) qzero := by rat_ring
      generalize qmul (qnat (t + 1)) qzero = P at *; generalize qmul (qpowN (qnat 0) t) (qnat 0) = Q at *
      generalize qmul (qpowN (qnat 0) t) qzero = Q' at *; rat_linarith
  | G + 1 => by
      have ih := faul_up t G
      have d := pow_diff (qnat G) (qnat (G + 1)) t
      have s := qnat_succ G
      have g0 : qle qzero (qnat G) := qnat_nonneg G
      obtain ⟨gl, _⟩ := gsum_bounds g0 (qnat_mono (Nat.le_succ G)) t
      have e1 : qEq (qmul (qsub (qnat (G + 1)) (qnat G)) (gsum (qnat G) (qnat (G + 1)) t)) (gsum (qnat G) (qnat (G + 1)) t) := by
        have := qmul_respects (show qEq (qsub (qnat (G + 1)) (qnat G)) qone by unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)) (qEq_refl (gsum (qnat G) (qnat (G + 1)) t))
        exact qEq_trans this (by rat_ring)
      have e2 : qEq (qmul (qnat (t + 1)) (spow t (G + 1))) (qadd (qmul (qnat (t + 1)) (spow t G)) (qmul (qnat (t + 1)) (qpowN (qnat G) t))) := by
        show qEq (qmul (qnat (t + 1)) (qadd (spow t G) (qpowN (qnat G) t))) _; rat_ring
      generalize qmul (qnat (t + 1)) (spow t (G + 1)) = A at *
      generalize qmul (qnat (t + 1)) (spow t G) = A' at *
      generalize qmul (qnat (t + 1)) (qpowN (qnat G) t) = A'' at *
      generalize qmul (qsub (qnat (G + 1)) (qnat G)) (gsum (qnat G) (qnat (G + 1)) t) = P at *
      generalize gsum (qnat G) (qnat (G + 1)) t = g at *
      unfold qsub at *; rat_linarith

/-- FAULHABER FROM BELOW: `G^{t+1} ≤ (t + 1)·Σ_{j<G+1} j^t`. -/
theorem faul_lo (t : Nat) : ∀ G, qle (qpowN (qnat G) (t + 1)) (qmul (qnat (t + 1)) (spow t (G + 1)))
  | 0 => by
      have z := qnat_zero
      have e2 := qmul_respects (qEq_refl (qpowN (qnat 0) t)) z
      have e3 : qEq (qmul (qpowN (qnat 0) t) qzero) qzero := by rat_ring
      have p := qmul_nonneg (qnat_nonneg (t + 1)) (show qle qzero (spow t 1) by
        show qle qzero (qadd qzero (qpowN (qnat 0) t)); have := powN_nonneg (qnat_nonneg 0) t; rat_linarith)
      show qle (qmul (qpowN (qnat 0) t) (qnat 0)) _
      generalize qmul (qpowN (qnat 0) t) (qnat 0) = Q at *; generalize qmul (qpowN (qnat 0) t) qzero = Q' at *
      rat_linarith
  | G + 1 => by
      have ih := faul_lo t G
      have d := pow_diff (qnat G) (qnat (G + 1)) t
      have g0 : qle qzero (qnat G) := qnat_nonneg G
      obtain ⟨_, gu⟩ := gsum_bounds g0 (qnat_mono (Nat.le_succ G)) t
      have e1 : qEq (qmul (qsub (qnat (G + 1)) (qnat G)) (gsum (qnat G) (qnat (G + 1)) t)) (gsum (qnat G) (qnat (G + 1)) t) := by
        have s := qnat_succ G
        have := qmul_respects (show qEq (qsub (qnat (G + 1)) (qnat G)) qone by unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)) (qEq_refl (gsum (qnat G) (qnat (G + 1)) t))
        exact qEq_trans this (by rat_ring)
      have e2 : qEq (qmul (qnat (t + 1)) (spow t (G + 1 + 1)))
          (qadd (qmul (qnat (t + 1)) (spow t (G + 1))) (qmul (qnat (t + 1)) (qpowN (qnat (G + 1)) t))) := by
        show qEq (qmul (qnat (t + 1)) (qadd (spow t (G + 1)) (qpowN (qnat (G + 1)) t))) _; rat_ring
      generalize qmul (qnat (t + 1)) (spow t (G + 1 + 1)) = A at *
      generalize qmul (qnat (t + 1)) (spow t (G + 1)) = A' at *
      generalize qmul (qnat (t + 1)) (qpowN (qnat (G + 1)) t) = A'' at *
      generalize qmul (qsub (qnat (G + 1)) (qnat G)) (gsum (qnat G) (qnat (G + 1)) t) = P at *
      generalize gsum (qnat G) (qnat (G + 1)) t = g at *
      unfold qsub at *; rat_linarith

/-! ## The Taylor polynomial and the remainder's side -/

/-- `D^m e` (`D` applied first: `Diter (m + 1) e = Diter m (D e)`). -/
def Diter (i : Nat) : Nat → G → G
  | 0, e => e
  | m + 1, e => Diter i m (D i e)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `1/m!`. -/
def cf (m : Nat) : QExpr := qinv' (qnat (fact m))

theorem fact_succ_pred : ∀ n, ∃ k, fact n = k + 1
  | 0 => ⟨0, rfl⟩
  | n + 1 => by
      obtain ⟨k, hk⟩ := fact_succ_pred n
      exact ⟨(n + 1) * k + n, by show (n + 1) * fact n = _; rw [hk, Nat.mul_succ]; rfl⟩

theorem fact_pos (m : Nat) : qlt qzero (qnat (fact m)) := by
  obtain ⟨k, hk⟩ := fact_succ_pred m; rw [hk]; exact qnat_succ_pos k

theorem cf_nonneg (m : Nat) : qle qzero (cf m) := qinv'_nonneg_of_pos (fact_pos m)

/-- `(t + 1)·(1/(t + 1)!) = 1/t!`. -/
theorem cf_succ (t : Nat) : qEq (qmul (qnat (t + 1)) (cf (t + 1))) (cf t) := by
  have m := qnat_mul (t + 1) (fact t)
  have hf : ¬ qEq (qnat (fact t)) qzero := ne_zero_of_lt (fact_pos t)
  have hn : ¬ qEq (qnat (t + 1)) qzero := qnat_ne_zero t
  have im := qinv'_mul hn hf
  have c := qmul_inv'_cancel hn
  unfold cf
  show qEq (qmul (qnat (t + 1)) (qinv' (qnat ((t + 1) * fact t)))) _
  have e1 := qmul_respects (qEq_refl (qnat (t + 1))) (qEq_trans (qinv'_respects m) im)
  have e2 : qEq (qmul (qnat (t + 1)) (qmul (qinv' (qnat (t + 1))) (qinv' (qnat (fact t)))))
      (qmul (qmul (qnat (t + 1)) (qinv' (qnat (t + 1)))) (qinv' (qnat (fact t)))) := by rat_ring
  have e3 := qmul_respects c (qEq_refl (qinv' (qnat (fact t))))
  have e4 : qEq (qmul qone (qinv' (qnat (fact t)))) (qinv' (qnat (fact t))) := by rat_ring
  exact qEq_trans e1 (qEq_trans e2 (qEq_trans e3 e4))

/-- The Taylor polynomial of degree `< m` at `p`, in the step `Δ`, at index `n`. -/
def tpoly (i n : Nat) (p : Point QExpr) (e : G) (Δ : QExpr) (m : Nat) : QExpr :=
  ZTrig.bs (fun t => qmul (evalN n p (Diter i t e)) (qmul (qpowN Δ t) (cf t))) m

/-- `R` lies in `w·[L, U]` (the order by `w`'s sign), within `e`. -/
def Side (R w L U e : QExpr) : Prop :=
  (qle qzero w → qle (qsub (qmul w L) e) R ∧ qle R (qadd (qmul w U) e)) ∧
  (qle w qzero → qle (qsub (qmul w U) e) R ∧ qle R (qadd (qmul w L) e))

/-- At `w ≥ 0` the first branch is enough (at `w = 0` both collapse to `[−e, e]`). -/
theorem side_pos {R w L U e : QExpr} (hw : qle qzero w) (l : qle (qsub (qmul w L) e) R) (u : qle R (qadd (qmul w U) e)) :
    Side R w L U e := by
  refine ⟨fun _ => ⟨l, u⟩, fun h2 => ?_⟩
  have z : qEq w qzero := qle_antisymm h2 hw
  have s1 := qmul_respects z (qEq_refl L); have s2 := qmul_respects z (qEq_refl U)
  have o1 : qEq (qmul qzero L) qzero := by rat_ring
  have o2 : qEq (qmul qzero U) qzero := by rat_ring
  generalize qmul w L = A at *; generalize qmul w U = B at *
  generalize qmul qzero L = C at *; generalize qmul qzero U = D at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem side_neg {R w L U e : QExpr} (hw : qle w qzero) (l : qle (qsub (qmul w U) e) R) (u : qle R (qadd (qmul w L) e)) :
    Side R w L U e := by
  refine ⟨fun h2 => ?_, fun _ => ⟨l, u⟩⟩
  have z : qEq w qzero := qle_antisymm hw h2
  have s1 := qmul_respects z (qEq_refl L); have s2 := qmul_respects z (qEq_refl U)
  have o1 : qEq (qmul qzero L) qzero := by rat_ring
  have o2 : qEq (qmul qzero U) qzero := by rat_ring
  generalize qmul w L = A at *; generalize qmul w U = B at *
  generalize qmul qzero L = C at *; generalize qmul qzero U = D at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `δ·(wX ± e)` rearranged: `(δw)X ± δe`, and `|δe| ≤ a·e`. -/
theorem mul_rearr {δ w X e a : QExpr} (hδ : ZTrig.Ab δ a) (e0 : qle qzero e) :
    qEq (qmul δ (qsub (qmul w X) e)) (qsub (qmul (qmul δ w) X) (qmul δ e)) ∧
    qEq (qmul δ (qadd (qmul w X) e)) (qadd (qmul (qmul δ w) X) (qmul δ e)) ∧ ZTrig.Ab (qmul δ e) (qmul a e) :=
  ⟨by unfold qsub; rat_ring, by rat_ring, ZTrig.mul_abs hδ ⟨by rat_linarith, qle_refl _⟩⟩

/-- Multiplying by `δ` (`|δ| ≤ a`): the side of `δ·R` at the weight `δ·w`, within `a·e`. -/
theorem side_mul {R w L U e δ a : QExpr} (h : Side R w L U e) (hδ : ZTrig.Ab δ a) (e0 : qle qzero e) :
    Side (qmul δ R) (qmul δ w) L U (qmul a e) := by
  obtain ⟨hp, hn⟩ := h
  obtain ⟨rL1, rL2, ab⟩ := mul_rearr (w := w) (X := L) hδ e0
  obtain ⟨rU1, rU2, _⟩ := mul_rearr (w := w) (X := U) hδ e0
  obtain ⟨b1, b2⟩ := ab
  cases qle_total qzero δ with
  | inl hd =>
    cases qle_total qzero w with
    | inl hw =>
      obtain ⟨l, u⟩ := hp hw
      have sl := scale_l l hd; have su := scale_l u hd
      refine side_pos (qmul_nonneg hd hw) ?_ ?_
      · generalize qmul δ (qsub (qmul w L) e) = P at *; generalize qmul (qmul δ w) L = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; unfold qsub at *; rat_linarith
      · generalize qmul δ (qadd (qmul w U) e) = P at *; generalize qmul (qmul δ w) U = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; rat_linarith
    | inr hw =>
      obtain ⟨l, u⟩ := hn hw
      have sl := scale_l l hd; have su := scale_l u hd
      have nw : qle (qmul δ w) qzero := by
        have := qmul_nonneg hd (show qle qzero (qneg w) by rat_linarith)
        have e : qEq (qmul δ (qneg w)) (qneg (qmul δ w)) := by rat_ring
        generalize qmul δ (qneg w) = P at *; generalize qmul δ w = Q at *; rat_linarith
      refine side_neg nw ?_ ?_
      · generalize qmul δ (qsub (qmul w U) e) = P at *; generalize qmul (qmul δ w) U = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; unfold qsub at *; rat_linarith
      · generalize qmul δ (qadd (qmul w L) e) = P at *; generalize qmul (qmul δ w) L = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; rat_linarith
  | inr hd =>
    have nd : qle qzero (qneg δ) := by rat_linarith
    have flip : ∀ x y : QExpr, qle x y → qle (qmul δ y) (qmul δ x) := fun x y h => by
      have s := scale_l h nd
      have e1 : qEq (qmul (qneg δ) x) (qneg (qmul δ x)) := by rat_ring
      have e2 : qEq (qmul (qneg δ) y) (qneg (qmul δ y)) := by rat_ring
      generalize qmul (qneg δ) x = P at *; generalize qmul (qneg δ) y = Q at *
      generalize qmul δ x = P' at *; generalize qmul δ y = Q' at *; rat_linarith
    cases qle_total qzero w with
    | inl hw =>
      obtain ⟨l, u⟩ := hp hw
      have sl := flip _ _ l; have su := flip _ _ u
      have nw : qle (qmul δ w) qzero := by
        have := flip _ _ hw; have e : qEq (qmul δ qzero) qzero := by rat_ring
        generalize qmul δ qzero = P at *; generalize qmul δ w = Q at *; rat_linarith
      refine side_neg nw ?_ ?_
      · generalize qmul δ (qadd (qmul w U) e) = P at *; generalize qmul (qmul δ w) U = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; unfold qsub at *; rat_linarith
      · generalize qmul δ (qsub (qmul w L) e) = P at *; generalize qmul (qmul δ w) L = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; unfold qsub at *; rat_linarith
    | inr hw =>
      obtain ⟨l, u⟩ := hn hw
      have sl := flip _ _ l; have su := flip _ _ u
      have pw : qle qzero (qmul δ w) := by
        have := qmul_nonneg nd (show qle qzero (qneg w) by rat_linarith)
        have e : qEq (qmul (qneg δ) (qneg w)) (qmul δ w) := by rat_ring
        generalize qmul (qneg δ) (qneg w) = P at *; generalize qmul δ w = Q at *; rat_linarith
      refine side_pos pw ?_ ?_
      · generalize qmul δ (qadd (qmul w L) e) = P at *; generalize qmul (qmul δ w) L = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; unfold qsub at *; rat_linarith
      · generalize qmul δ (qsub (qmul w U) e) = P at *; generalize qmul (qmul δ w) U = Q at *
        generalize qmul δ e = T at *; generalize qmul δ R = Z at *; unfold qsub at *; rat_linarith

theorem bs_mulr (F : Nat → QExpr) (c : QExpr) : ∀ G, qEq (ZTrig.bs (fun j => qmul (F j) c) G) (qmul (ZTrig.bs F G) c)
  | 0 => by show qEq qzero (qmul qzero c); rat_ring
  | G + 1 => by
      have ih := bs_mulr F c G
      show qEq (qadd (ZTrig.bs (fun j => qmul (F j) c) G) (qmul (F G) c)) (qmul (qadd (ZTrig.bs F G) (F G)) c)
      have e : qEq (qmul (qadd (ZTrig.bs F G) (F G)) c) (qadd (qmul (ZTrig.bs F G) c) (qmul (F G) c)) := by rat_ring
      generalize ZTrig.bs (fun j => qmul (F j) c) G = A at *; generalize qmul (ZTrig.bs F G) c = B at *
      generalize qmul (qadd (ZTrig.bs F G) (F G)) c = C at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `Σ (W_j·X ∓ e) = (ΣW)·X ∓ G·e`. -/
theorem bs_wx (W : Nat → QExpr) (X e : QExpr) (G : Nat) :
    qEq (ZTrig.bs (fun j => qsub (qmul (W j) X) e) G) (qsub (qmul (ZTrig.bs W G) X) (qmul (qnat G) e)) ∧
    qEq (ZTrig.bs (fun j => qadd (qmul (W j) X) e) G) (qadd (qmul (ZTrig.bs W G) X) (qmul (qnat G) e)) := by
  have s1 := ZTrig.bs_sub (fun j => qmul (W j) X) (fun _ => e) G
  have s2 := ZTrig.bs_add (fun j => qmul (W j) X) (fun _ => e) G
  have m := bs_mulr W X G
  have c := ZTrig.bs_const e G
  generalize ZTrig.bs (fun j => qsub (qmul (W j) X) e) G = A at *
  generalize ZTrig.bs (fun j => qadd (qmul (W j) X) e) G = A' at *
  generalize ZTrig.bs (fun j => qmul (W j) X) G = B at *
  generalize ZTrig.bs (fun _ => e) G = C at *
  generalize qmul (ZTrig.bs W G) X = D at *; generalize qmul (qnat G) e = E at *
  unfold qsub at *; exact ⟨qle_antisymm (by rat_linarith) (by rat_linarith), qle_antisymm (by rat_linarith) (by rat_linarith)⟩

theorem bs_sign (W : Nat → QExpr) : ∀ G, ((∀ j, j < G → qle qzero (W j)) → qle qzero (ZTrig.bs W G)) ∧
    ((∀ j, j < G → qle (W j) qzero) → qle (ZTrig.bs W G) qzero)
  | 0 => ⟨fun _ => qle_refl _, fun _ => qle_refl _⟩
  | G + 1 => by
      obtain ⟨a, b⟩ := bs_sign W G
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := a (fun j hj => h j (Nat.lt_succ_of_lt hj)); have := h G (Nat.lt_succ_self G)
        show qle qzero (qadd (ZTrig.bs W G) (W G)); rat_linarith
      · have := b (fun j hj => h j (Nat.lt_succ_of_lt hj)); have := h G (Nat.lt_succ_self G)
        show qle (qadd (ZTrig.bs W G) (W G)) qzero; rat_linarith

/-- SUMMING SIDES whose weights share a sign. -/
theorem side_sum {r W : Nat → QExpr} {L U e : QExpr} {G : Nat} (h : ∀ j, j < G → Side (r j) (W j) L U e)
    (sg : (∀ j, j < G → qle qzero (W j)) ∨ (∀ j, j < G → qle (W j) qzero)) :
    Side (ZTrig.bs r G) (ZTrig.bs W G) L U (qmul (qnat G) e) := by
  obtain ⟨xl1, xl2⟩ := bs_wx W L e G
  obtain ⟨xu1, xu2⟩ := bs_wx W U e G
  cases sg with
  | inl hp =>
    obtain ⟨l, u⟩ := ZTrig.bs_lohi G (fun j hj => (h j hj).1 (hp j hj))
    have s := (bs_sign W G).1 hp
    refine side_pos s ?_ ?_
    · generalize ZTrig.bs (fun j => qsub (qmul (W j) L) e) G = A at *; generalize ZTrig.bs r G = Rr at *
      generalize qmul (ZTrig.bs W G) L = B at *; generalize qmul (qnat G) e = E at *
      unfold qsub at *; rat_linarith
    · generalize ZTrig.bs (fun j => qadd (qmul (W j) U) e) G = A at *; generalize ZTrig.bs r G = Rr at *
      generalize qmul (ZTrig.bs W G) U = B at *; generalize qmul (qnat G) e = E at *
      rat_linarith
  | inr hn =>
    obtain ⟨l, u⟩ := ZTrig.bs_lohi G (fun j hj => (h j hj).2 (hn j hj))
    have s := (bs_sign W G).2 hn
    refine side_neg s ?_ ?_
    · generalize ZTrig.bs (fun j => qsub (qmul (W j) U) e) G = A at *; generalize ZTrig.bs r G = Rr at *
      generalize qmul (ZTrig.bs W G) U = B at *; generalize qmul (qnat G) e = E at *
      unfold qsub at *; rat_linarith
    · generalize ZTrig.bs (fun j => qadd (qmul (W j) L) e) G = A at *; generalize ZTrig.bs r G = Rr at *
      generalize qmul (ZTrig.bs W G) L = B at *; generalize qmul (qnat G) e = E at *
      rat_linarith

/-- SHIFTING THE WEIGHT: `|W − w'| ≤ η`, the same sign, `|L|, |U| ≤ M`: within `e + η·M`. -/
theorem side_shift {r W w' L U e η M : QExpr} (h : Side r W L U e) (hη : ZTrig.Ab (qsub W w') η)
    (bL : ZTrig.Ab L M) (bU : ZTrig.Ab U M)
    (sg : (qle qzero W ∧ qle qzero w') ∨ (qle W qzero ∧ qle w' qzero)) :
    Side r w' L U (qadd e (qmul η M)) := by
  obtain ⟨a1, a2⟩ := ZTrig.mul_abs hη bL
  obtain ⟨b1, b2⟩ := ZTrig.mul_abs hη bU
  have iL : qEq (qmul (qsub W w') L) (qsub (qmul W L) (qmul w' L)) := by unfold qsub; rat_ring
  have iU : qEq (qmul (qsub W w') U) (qsub (qmul W U) (qmul w' U)) := by unfold qsub; rat_ring
  cases sg with
  | inl hp =>
    obtain ⟨l, u⟩ := h.1 hp.1
    refine side_pos hp.2 ?_ ?_
    · generalize qmul (qsub W w') L = P at *; generalize qmul W L = Q at *; generalize qmul w' L = Q' at *
      generalize qmul η M = E at *; unfold qsub at *; rat_linarith
    · generalize qmul (qsub W w') U = P at *; generalize qmul W U = Q at *; generalize qmul w' U = Q' at *
      generalize qmul η M = E at *; unfold qsub at *; rat_linarith
  | inr hn =>
    obtain ⟨l, u⟩ := h.2 hn.1
    refine side_neg hn.2 ?_ ?_
    · generalize qmul (qsub W w') U = P at *; generalize qmul W U = Q at *; generalize qmul w' U = Q' at *
      generalize qmul η M = E at *; unfold qsub at *; rat_linarith
    · generalize qmul (qsub W w') L = P at *; generalize qmul W L = Q at *; generalize qmul w' L = Q' at *
      generalize qmul η M = E at *; unfold qsub at *; rat_linarith

/-! ## Helpers for the induction step -/

theorem bs_swap (F : Nat → Nat → QExpr) (m : Nat) : ∀ G,
    qEq (ZTrig.bs (fun j => ZTrig.bs (fun t => F j t) m) G) (ZTrig.bs (fun t => ZTrig.bs (fun j => F j t) G) m)
  | 0 => by
      show qEq qzero (ZTrig.bs (fun t => qzero) m)
      have := ZTrig.bs_const qzero m
      have z : qEq (qmul (qnat m) qzero) qzero := by rat_ring
      exact qEq_symm (qEq_trans this z)
  | G + 1 => by
      have ih := bs_swap F m G
      have a := ZTrig.bs_add (fun t => ZTrig.bs (fun j => F j t) G) (fun t => F G t) m
      show qEq (qadd (ZTrig.bs (fun j => ZTrig.bs (fun t => F j t) m) G) (ZTrig.bs (fun t => F G t) m))
        (ZTrig.bs (fun t => qadd (ZTrig.bs (fun j => F j t) G) (F G t)) m)
      generalize ZTrig.bs (fun j => ZTrig.bs (fun t => F j t) m) G = A at *
      generalize ZTrig.bs (fun t => ZTrig.bs (fun j => F j t) G) m = B at *
      generalize ZTrig.bs (fun t => F G t) m = C at *
      generalize ZTrig.bs (fun t => qadd (ZTrig.bs (fun j => F j t) G) (F G t)) m = D at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem powN_mul (a b : QExpr) : ∀ t, qEq (qpowN (qmul a b) t) (qmul (qpowN a t) (qpowN b t))
  | 0 => by show qEq qone (qmul qone qone); rat_ring
  | t + 1 => by
      have ih := powN_mul a b t
      show qEq (qmul (qpowN (qmul a b) t) (qmul a b)) (qmul (qmul (qpowN a t) a) (qmul (qpowN b t) b))
      have e := qmul_respects ih (qEq_refl (qmul a b))
      exact qEq_trans e (by rat_ring)

theorem cf_le_one (m : Nat) : qle (cf m) qone := by
  obtain ⟨k, hk⟩ := fact_succ_pred m
  have o : qle qone (qnat (fact m)) := by rw [hk]; have := qnat_succ k; have := qnat_nonneg k; rat_linarith
  obtain ⟨_, i1⟩ := ZTrig.inv_bound qone_pos o
  have e : qEq (qinv' qone) qone := by
    have c := qmul_inv'_cancel (show ¬ qEq qone qzero from fun h => (qlt_iff_le_not_le.mp qone_pos).2 (qle_of_qEq h))
    have r : qEq (qmul qone (qinv' qone)) (qinv' qone) := by rat_ring
    exact qEq_trans (qEq_symm r) c
  unfold cf; rat_linarith

/-- `Side` absorbs a nearby value: `|r' − r| ≤ η` widens by `η`. -/
theorem side_err {r r' w L U e η : QExpr} (h : Side r w L U e) (hη : ZTrig.Ab (qsub r' r) η) :
    Side r' w L U (qadd e η) := by
  obtain ⟨hp, hn⟩ := h
  obtain ⟨d1, d2⟩ := hη
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨l, u⟩ := hp hw
    generalize qmul w L = A at *; generalize qmul w U = B at *; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  · obtain ⟨l, u⟩ := hn hw
    generalize qmul w L = A at *; generalize qmul w U = B at *; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem side_widen {r w L U e e' : QExpr} (h : Side r w L U e) (he : qle e e') : Side r w L U e' := by
  obtain ⟨hp, hn⟩ := h
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨l, u⟩ := hp hw
    generalize qmul w L = A at *; generalize qmul w U = B at *; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  · obtain ⟨l, u⟩ := hn hw
    generalize qmul w L = A at *; generalize qmul w U = B at *; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- Finitely many bounds are one bound (each monotone in the bound). -/
theorem fin_bound {P : Nat → QExpr → Prop} (mono : ∀ t M M', qle M M' → P t M → P t M') :
    ∀ m, (∀ t, t < m → ∃ M, qle qzero M ∧ P t M) → ∃ M, qle qzero M ∧ ∀ t, t < m → P t M
  | 0, _ => ⟨qzero, qle_refl _, fun t h => absurd h (Nat.not_lt_zero t)⟩
  | m + 1, h => by
      obtain ⟨M1, m10, h1⟩ := fin_bound mono m (fun t ht => h t (Nat.lt_succ_of_lt ht))
      obtain ⟨M2, m20, h2⟩ := h m (Nat.lt_succ_self m)
      refine ⟨qadd M1 M2, by rat_linarith, fun t ht => ?_⟩
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with
      | inl l => exact mono t M1 _ (by rat_linarith) (h1 t l)
      | inr e => subst e; exact mono t M2 _ (by rat_linarith) h2

/-- THE WEIGHTS ON THE GRID: `1/t!·δ^(t+1)·Σ_{j<G} j^t` is `Δ^(t+1)/(t+1)!` within `1/t!·(A·2^−K)·A^t`
(`δ = Δ·2^−K`, `G = 2^K`, `|Δ| ≤ A`). -/
theorem faul_weight {Δ A : QExpr} {K : Nat} (t : Nat) (hΔ : ZTrig.Ab Δ A) (hA : qle qzero A) :
    ZTrig.Ab (qsub (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))) (qmul (qpowN Δ (t + 1)) (cf (t + 1))))
      (qmul (qmul (cf t) (qmul A (qeps K))) (qpowN A t)) := by
  have g := ZTrig.g_one K
  -- X = (t+1)·spow, X − G^(t+1) ∈ [−(t+1)G^t, 0]
  have fu := faul_up t (2 ^ K)
  have fl := faul_lo t (2 ^ K)
  have e1 : qEq (qmul (qnat (t + 1)) (spow t (2 ^ K + 1)))
      (qadd (qmul (qnat (t + 1)) (spow t (2 ^ K))) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t))) := by
    show qEq (qmul (qnat (t + 1)) (qadd (spow t (2 ^ K)) (qpowN (qnat (2 ^ K)) t))) _; rat_ring
  have Gt0 := powN_nonneg (qnat_nonneg (2 ^ K)) t
  have nt0 := qnat_nonneg (t + 1)
  have bX : ZTrig.Ab (qsub (qmul (qnat (t + 1)) (spow t (2 ^ K))) (qpowN (qnat (2 ^ K)) (t + 1)))
      (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t)) := by
    have := qmul_nonneg nt0 Gt0
    generalize qmul (qnat (t + 1)) (spow t (2 ^ K)) = X at *
    generalize qmul (qnat (t + 1)) (spow t (2 ^ K + 1)) = X' at *
    generalize qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t) = Y at *
    unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  -- |δ^(t+1)| ≤ (A·2^−K)^(t+1)
  have hδ : ZTrig.Ab (qmul Δ (qeps K)) (qmul A (qeps K)) :=
    ZTrig.mul_abs hΔ ⟨by have := qeps_nonneg K; rat_linarith, qle_refl _⟩
  have pδ := pow_abs hδ (t + 1)
  obtain ⟨b1, b2⟩ := ZTrig.mul_abs pδ bX
  have cf1 := cf_nonneg (t + 1)
  have s1 := scale_l b2 cf1
  have s2 := scale_l b1 cf1
  -- identities
  have cs := cf_succ t
  have dG : qEq (qmul (qmul Δ (qeps K)) (qnat (2 ^ K))) Δ := by
    have r : qEq (qmul (qmul Δ (qeps K)) (qnat (2 ^ K))) (qmul Δ (qmul (qnat (2 ^ K)) (qeps K))) := by rat_ring
    exact qEq_trans r (qEq_trans (qmul_respects (qEq_refl Δ) g) (by rat_ring))
  have aG : qEq (qmul (qmul A (qeps K)) (qnat (2 ^ K))) A := by
    have r : qEq (qmul (qmul A (qeps K)) (qnat (2 ^ K))) (qmul A (qmul (qnat (2 ^ K)) (qeps K))) := by rat_ring
    exact qEq_trans r (qEq_trans (qmul_respects (qEq_refl A) g) (by rat_ring))
  have pΔ : qEq (qmul (qpowN (qmul Δ (qeps K)) (t + 1)) (qpowN (qnat (2 ^ K)) (t + 1))) (qpowN Δ (t + 1)) :=
    qEq_trans (qEq_symm (powN_mul _ _ (t + 1))) (powN_respects dG (t + 1))
  have pA : qEq (qmul (qpowN (qmul A (qeps K)) t) (qpowN (qnat (2 ^ K)) t)) (qpowN A t) :=
    qEq_trans (qEq_symm (powN_mul _ _ t)) (powN_respects aG t)
  -- the target, rearranged
  have T : qEq (qsub (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))) (qmul (qpowN Δ (t + 1)) (cf (t + 1))))
      (qmul (cf (t + 1)) (qmul (qpowN (qmul Δ (qeps K)) (t + 1))
        (qsub (qmul (qnat (t + 1)) (spow t (2 ^ K))) (qpowN (qnat (2 ^ K)) (t + 1))))) := by
    have r1 := qmul_respects (qmul_respects (qEq_symm cs) (qEq_refl (qpowN (qmul Δ (qeps K)) (t + 1)))) (qEq_refl (spow t (2 ^ K)))
    have r2 := qmul_respects (qEq_symm pΔ) (qEq_refl (cf (t + 1)))
    have r3 : qEq (qsub (qmul (qmul (qmul (qnat (t + 1)) (cf (t + 1))) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K)))
          (qmul (qmul (qpowN (qmul Δ (qeps K)) (t + 1)) (qpowN (qnat (2 ^ K)) (t + 1))) (cf (t + 1))))
        (qmul (cf (t + 1)) (qmul (qpowN (qmul Δ (qeps K)) (t + 1))
          (qsub (qmul (qnat (t + 1)) (spow t (2 ^ K))) (qpowN (qnat (2 ^ K)) (t + 1))))) := by unfold qsub; rat_ring
    generalize qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K)) = P1 at *
    generalize qmul (qpowN Δ (t + 1)) (cf (t + 1)) = P2 at *
    generalize qmul (qmul (qmul (qnat (t + 1)) (cf (t + 1))) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K)) = P3 at *
    generalize qmul (qmul (qpowN (qmul Δ (qeps K)) (t + 1)) (qpowN (qnat (2 ^ K)) (t + 1))) (cf (t + 1)) = P4 at *
    unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  -- the bound, rearranged
  have Bd : qEq (qmul (cf (t + 1)) (qmul (qpowN (qmul A (qeps K)) (t + 1)) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t))))
      (qmul (qmul (cf t) (qmul A (qeps K))) (qpowN A t)) := by
    have r1 : qEq (qmul (cf (t + 1)) (qmul (qpowN (qmul A (qeps K)) (t + 1)) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t))))
        (qmul (qmul (qmul (qnat (t + 1)) (cf (t + 1))) (qmul A (qeps K))) (qmul (qpowN (qmul A (qeps K)) t) (qpowN (qnat (2 ^ K)) t))) := by
      show qEq (qmul (cf (t + 1)) (qmul (qmul (qpowN (qmul A (qeps K)) t) (qmul A (qeps K))) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t)))) _
      rat_ring
    exact qEq_trans r1 (qmul_respects (qmul_respects cs (qEq_refl _)) pA)
  have q1 : qEq (qmul (cf (t + 1)) (qneg (qmul (qpowN (qmul A (qeps K)) (t + 1)) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t)))))
      (qneg (qmul (cf (t + 1)) (qmul (qpowN (qmul A (qeps K)) (t + 1)) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t))))) := by rat_ring
  generalize qsub (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))) (qmul (qpowN Δ (t + 1)) (cf (t + 1))) = L at *
  generalize qmul (cf (t + 1)) (qmul (qpowN (qmul Δ (qeps K)) (t + 1))
        (qsub (qmul (qnat (t + 1)) (spow t (2 ^ K))) (qpowN (qnat (2 ^ K)) (t + 1)))) = R at *
  generalize qmul (cf (t + 1)) (qneg (qmul (qpowN (qmul A (qeps K)) (t + 1)) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t)))) = Qn at *
  generalize qmul (cf (t + 1)) (qmul (qpowN (qmul A (qeps K)) (t + 1)) (qmul (qnat (t + 1)) (qpowN (qnat (2 ^ K)) t))) = Q at *
  generalize qmul (qmul (cf t) (qmul A (qeps K))) (qpowN A t) = W at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem powN_le_add {A : QExpr} (hA : qle qone A) (t : Nat) : ∀ d, qle (qpowN A t) (qpowN A (t + d))
  | 0 => qle_refl _
  | d + 1 => by
      have ih := powN_le_add hA t d
      have a0 : qle qzero A := qle_trans (qle_of_qlt qone_pos) hA
      have p0 := qle_trans (powN_nonneg a0 t) ih
      have s := scale_l hA p0
      have e1 : qEq (qmul (qpowN A (t + d)) qone) (qpowN A (t + d)) := by rat_ring
      have e2 : qEq (qmul (qpowN A (t + d)) A) (qpowN A (t + d + 1)) := qEq_refl _
      show qle (qpowN A t) (qmul (qpowN A (t + d)) A)
      generalize qmul (qpowN A (t + d)) qone = P at *; generalize qmul (qpowN A (t + d)) A = Q at *
      rat_linarith

theorem powN_le_exp {A : QExpr} (hA : qle qone A) {t m : Nat} (h : t ≤ m) : qle (qpowN A t) (qpowN A m) := by
  obtain ⟨d, rfl⟩ := le_ex h
  exact powN_le_add hA t d

/-- `Σ_{j<G} (s_j)^t = δ^t·Σ_{j<G} j^t` when `s_j = j·δ`. -/
theorem sum_offs {s : Nat → QExpr} {δ : QExpr} {G : Nat} (hs : ∀ j, qEq (s j) (qmul (qnat j) δ)) (t : Nat) :
    qEq (ZTrig.bs (fun j => qpowN (s j) t) G) (qmul (qpowN δ t) (spow t G)) := by
  have c := ZTrig.bs_congr (F := fun j => qpowN (s j) t) (G := fun j => qmul (qpowN δ t) (qpowN (qnat j) t))
    (fun j => show qEq (qpowN (s j) t) (qmul (qpowN δ t) (qpowN (qnat j) t)) from
      qEq_trans (powN_respects (hs j) t) (qEq_trans (powN_mul _ _ t) (qmul_comm _ _))) G
  exact qEq_trans c (ZTrig.bs_scale (qpowN δ t) (fun j => qpowN (qnat j) t) G)

/-- THE POLYNOMIAL PART on the grid: `Σ_j δ·Σ_{t<m} c_t s_j^t/t!` is `Σ_{t<m} c_t Δ^(t+1)/(t+1)!` within
`m·M·(A·2^−K)·A^m` (`|c_t| ≤ M`, `|Δ| ≤ A`, `A ≥ 1`). -/
theorem poly_err {c s : Nat → QExpr} {Δ A M : QExpr} {K m : Nat} (hs : ∀ j, qEq (s j) (qmul (qnat j) (qmul Δ (qeps K))))
    (hc : ∀ t, t < m → ZTrig.Ab (c t) M) (hΔ : ZTrig.Ab Δ A) (hA : qle qone A) (hM : qle qzero M) :
    ZTrig.Ab (qsub (ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (c t) (qmul (qpowN (s j) t) (cf t))) m)) (2 ^ K))
        (ZTrig.bs (fun t => qmul (c t) (qmul (qpowN Δ (t + 1)) (cf (t + 1)))) m))
      (qmul (qnat m) (qmul M (qmul (qmul A (qeps K)) (qpowN A m)))) := by
  have a0 : qle qzero A := qle_trans (qle_of_qlt qone_pos) hA
  -- swap: Σ_j δ Σ_t … = Σ_t Σ_j δ c_t s_j^t cf_t = Σ_t c_t cf_t δ^(t+1) spow
  have sw := bs_swap (fun j t => qmul (qmul Δ (qeps K)) (qmul (c t) (qmul (qpowN (s j) t) (cf t)))) m (2 ^ K)
  have inner : ∀ j, qEq (qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (c t) (qmul (qpowN (s j) t) (cf t))) m))
      (ZTrig.bs (fun t => qmul (qmul Δ (qeps K)) (qmul (c t) (qmul (qpowN (s j) t) (cf t)))) m) := fun j =>
    qEq_symm (ZTrig.bs_scale _ _ m)
  have c1 := ZTrig.bs_congr inner (2 ^ K)
  have per : ∀ t, qEq (ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (c t) (qmul (qpowN (s j) t) (cf t)))) (2 ^ K))
      (qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K)))) := fun t => by
    have c2 := ZTrig.bs_congr (F := fun j => qmul (qmul Δ (qeps K)) (qmul (c t) (qmul (qpowN (s j) t) (cf t))))
      (G := fun j => qmul (qmul (qmul Δ (qeps K)) (qmul (c t) (cf t))) (qpowN (s j) t))
      (fun j => show qEq (qmul (qmul Δ (qeps K)) (qmul (c t) (qmul (qpowN (s j) t) (cf t))))
        (qmul (qmul (qmul Δ (qeps K)) (qmul (c t) (cf t))) (qpowN (s j) t)) by rat_ring) (2 ^ K)
    have c3 := ZTrig.bs_scale (qmul (qmul Δ (qeps K)) (qmul (c t) (cf t))) (fun j => qpowN (s j) t) (2 ^ K)
    have c4 := qmul_respects (qEq_refl (qmul (qmul Δ (qeps K)) (qmul (c t) (cf t)))) (sum_offs (G := 2 ^ K) hs t)
    have c5 : qEq (qmul (qmul (qmul Δ (qeps K)) (qmul (c t) (cf t))) (qmul (qpowN (qmul Δ (qeps K)) t) (spow t (2 ^ K))))
        (qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K)))) := by
      show qEq _ (qmul (c t) (qmul (qmul (cf t) (qmul (qpowN (qmul Δ (qeps K)) t) (qmul Δ (qeps K)))) (spow t (2 ^ K)))); rat_ring
    exact qEq_trans c2 (qEq_trans c3 (qEq_trans c4 c5))
  have c6 := ZTrig.bs_congr per m
  -- per-t error
  have tb : ∀ t, t < m → ZTrig.Ab (qsub (qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))))
      (qmul (c t) (qmul (qpowN Δ (t + 1)) (cf (t + 1))))) (qmul M (qmul (qmul A (qeps K)) (qpowN A m))) := fun t ht => by
    have fw := faul_weight (K := K) t hΔ a0
    obtain ⟨p1, p2⟩ := ZTrig.mul_abs (hc t ht) fw
    have r : qEq (qsub (qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))))
        (qmul (c t) (qmul (qpowN Δ (t + 1)) (cf (t + 1)))))
        (qmul (c t) (qsub (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))) (qmul (qpowN Δ (t + 1)) (cf (t + 1))))) := by
      unfold qsub; rat_ring
    -- M·(cf t·(Aε)·A^t) ≤ M·((Aε)·A^m)
    have cf1 := cf_le_one t
    have cf0 := cf_nonneg t
    have aε : qle qzero (qmul A (qeps K)) := qmul_nonneg a0 (qeps_nonneg K)
    have pt := powN_le_exp hA (Nat.le_of_lt ht)
    have w1 := ZExp.scale cf1 (qmul_nonneg aε (powN_nonneg a0 t))
    have w2 := scale_l pt aε
    have w3 : qle (qmul (qmul (cf t) (qmul A (qeps K))) (qpowN A t)) (qmul (qmul A (qeps K)) (qpowN A m)) := by
      have e1 : qEq (qmul (qmul (cf t) (qmul A (qeps K))) (qpowN A t)) (qmul (cf t) (qmul (qmul A (qeps K)) (qpowN A t))) := by rat_ring
      have e2 : qEq (qmul qone (qmul (qmul A (qeps K)) (qpowN A t))) (qmul (qmul A (qeps K)) (qpowN A t)) := by rat_ring
      generalize qmul (cf t) (qmul (qmul A (qeps K)) (qpowN A t)) = P at *
      generalize qmul qone (qmul (qmul A (qeps K)) (qpowN A t)) = Q at *
      generalize qmul (qmul A (qeps K)) (qpowN A t) = R at *
      generalize qmul (qmul (cf t) (qmul A (qeps K))) (qpowN A t) = R' at *
      rat_linarith
    have w4 := scale_l w3 hM
    generalize qsub (qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))))
        (qmul (c t) (qmul (qpowN Δ (t + 1)) (cf (t + 1)))) = L at *
    generalize qmul (c t) (qsub (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))) (qmul (qpowN Δ (t + 1)) (cf (t + 1)))) = L' at *
    generalize qmul M (qmul (qmul (cf t) (qmul A (qeps K))) (qpowN A t)) = B1 at *
    generalize qmul M (qmul (qmul A (qeps K)) (qpowN A m)) = B2 at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  have tot := ZTrig.bs_abs_c m tb
  have ds := ZTrig.bs_sub (fun t => qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))))
    (fun t => qmul (c t) (qmul (qpowN Δ (t + 1)) (cf (t + 1)))) m
  obtain ⟨u1, u2⟩ := tot
  generalize ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (c t) (qmul (qpowN (s j) t) (cf t))) m)) (2 ^ K) = S1 at *
  generalize ZTrig.bs (fun j => ZTrig.bs (fun t => qmul (qmul Δ (qeps K)) (qmul (c t) (qmul (qpowN (s j) t) (cf t)))) m) (2 ^ K) = S2 at *
  generalize ZTrig.bs (fun t => ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (c t) (qmul (qpowN (s j) t) (cf t)))) (2 ^ K)) m = S3 at *
  generalize ZTrig.bs (fun t => qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K)))) m = S4 at *
  generalize ZTrig.bs (fun t => qmul (c t) (qmul (qpowN Δ (t + 1)) (cf (t + 1)))) m = S5 at *
  generalize ZTrig.bs (fun t => qsub (qmul (c t) (qmul (qmul (cf t) (qpowN (qmul Δ (qeps K)) (t + 1))) (spow t (2 ^ K))))
    (qmul (c t) (qmul (qpowN Δ (t + 1)) (cf (t + 1))))) m = S6 at *
  generalize qmul (qnat m) (qmul M (qmul (qmul A (qeps K)) (qpowN A m))) = W at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The weight of each grid term: `δ·s_j^m/m! = (1/m!)·j^m·δ^(m+1)`. -/
theorem wt_form {s : Nat → QExpr} {δ : QExpr} (hs : ∀ j, qEq (s j) (qmul (qnat j) δ)) (m j : Nat) :
    qEq (qmul δ (qmul (qpowN (s j) m) (cf m))) (qmul (qmul (cf m) (qpowN (qnat j) m)) (qpowN δ (m + 1))) := by
  have e := qmul_respects (qEq_refl δ) (qmul_respects (qEq_trans (powN_respects (hs j) m) (powN_mul _ _ m)) (qEq_refl (cf m)))
  refine qEq_trans e ?_
  show qEq _ (qmul (qmul (cf m) (qpowN (qnat j) m)) (qmul (qpowN δ m) δ)); rat_ring

/-- The weights share the sign of `δ^(m+1)`. -/
theorem wt_sign {s : Nat → QExpr} {δ : QExpr} (hs : ∀ j, qEq (s j) (qmul (qnat j) δ)) (m G : Nat) :
    (∀ j, j < G → qle qzero (qmul δ (qmul (qpowN (s j) m) (cf m)))) ∨
    (∀ j, j < G → qle (qmul δ (qmul (qpowN (s j) m) (cf m))) qzero) := by
  have c0 : ∀ j, qle qzero (qmul (cf m) (qpowN (qnat j) m)) := fun j => qmul_nonneg (cf_nonneg m) (powN_nonneg (qnat_nonneg j) m)
  cases qle_total qzero (qpowN δ (m + 1)) with
  | inl h => exact Or.inl (fun j _ => by have := qmul_nonneg (c0 j) h; have e := wt_form hs m j; rat_linarith)
  | inr h => exact Or.inr (fun j _ => by
      have := qmul_nonneg (c0 j) (show qle qzero (qneg (qpowN δ (m + 1))) by rat_linarith)
      have e := wt_form hs m j
      have r : qEq (qmul (qmul (cf m) (qpowN (qnat j) m)) (qneg (qpowN δ (m + 1))))
          (qneg (qmul (qmul (cf m) (qpowN (qnat j) m)) (qpowN δ (m + 1)))) := by rat_ring
      generalize qmul (qmul (cf m) (qpowN (qnat j) m)) (qneg (qpowN δ (m + 1))) = P at *
      generalize qmul (qmul (cf m) (qpowN (qnat j) m)) (qpowN δ (m + 1)) = Q at *
      rat_linarith)

/-- THE REMAINDER'S WEIGHT on the grid: `Σ_j δ·s_j^m/m!` is `Δ^(m+1)/(m+1)!` within `(1/m!)·(A·2^−K)·A^m`,
with the same sign. -/
theorem wt_err {s : Nat → QExpr} {Δ A : QExpr} {K m : Nat} (hs : ∀ j, qEq (s j) (qmul (qnat j) (qmul Δ (qeps K))))
    (hΔ : ZTrig.Ab Δ A) (hA : qle qzero A) :
    ZTrig.Ab (qsub (ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (2 ^ K)) (qmul (qpowN Δ (m + 1)) (cf (m + 1))))
      (qmul (qmul (cf m) (qmul A (qeps K))) (qpowN A m)) ∧
    ((qle qzero (ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (2 ^ K)) ∧
        qle qzero (qmul (qpowN Δ (m + 1)) (cf (m + 1)))) ∨
      (qle (ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (2 ^ K)) qzero ∧
        qle (qmul (qpowN Δ (m + 1)) (cf (m + 1))) qzero)) := by
  have c1 := ZTrig.bs_congr (F := fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m)))
    (G := fun j => qmul (qmul (cf m) (qpowN (qmul Δ (qeps K)) (m + 1))) (qpowN (qnat j) m))
    (fun j => show qEq (qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (qmul (qmul (cf m) (qpowN (qmul Δ (qeps K)) (m + 1))) (qpowN (qnat j) m)) from
      qEq_trans (wt_form hs m j) (by rat_ring)) (2 ^ K)
  have c2 := ZTrig.bs_scale (qmul (cf m) (qpowN (qmul Δ (qeps K)) (m + 1))) (fun j => qpowN (qnat j) m) (2 ^ K)
  have fw := faul_weight (K := K) m hΔ hA
  have sp : qle qzero (spow m (2 ^ K)) := by
    have := (bs_sign (fun j => qpowN (qnat j) m) (2 ^ K)).1 (fun j _ => powN_nonneg (qnat_nonneg j) m); exact this
  -- δ^(m+1) and Δ^(m+1) share a sign: δ^(m+1) = Δ^(m+1)·ε^(m+1)
  have dpow := powN_mul Δ (qeps K) (m + 1)
  have ep := powN_nonneg (qeps_nonneg K) (m + 1)
  have cfm := cf_nonneg m
  have cf1 := cf_nonneg (m + 1)
  have key : qEq (ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (2 ^ K))
      (qmul (qmul (cf m) (qpowN (qmul Δ (qeps K)) (m + 1))) (spow m (2 ^ K))) := qEq_trans c1 c2
  refine ⟨?_, ?_⟩
  · obtain ⟨f1, f2⟩ := fw
    generalize ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (2 ^ K) = S at *
    generalize qmul (qmul (cf m) (qpowN (qmul Δ (qeps K)) (m + 1))) (spow m (2 ^ K)) = T at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  · cases qle_total qzero (qpowN Δ (m + 1)) with
    | inl h =>
      left
      have d0 : qle qzero (qpowN (qmul Δ (qeps K)) (m + 1)) := by have := qmul_nonneg h ep; rat_linarith
      exact ⟨by have := qmul_nonneg (qmul_nonneg cfm d0) sp; rat_linarith, qmul_nonneg h cf1⟩
    | inr h =>
      right
      have d0 : qle (qpowN (qmul Δ (qeps K)) (m + 1)) qzero := by
        have := qmul_nonneg (show qle qzero (qneg (qpowN Δ (m + 1))) by rat_linarith) ep
        have r : qEq (qmul (qneg (qpowN Δ (m + 1))) (qpowN (qeps K) (m + 1))) (qneg (qmul (qpowN Δ (m + 1)) (qpowN (qeps K) (m + 1)))) := by rat_ring
        generalize qmul (qneg (qpowN Δ (m + 1))) (qpowN (qeps K) (m + 1)) = P at *
        generalize qmul (qpowN Δ (m + 1)) (qpowN (qeps K) (m + 1)) = Q at *; rat_linarith
      constructor
      · have := qmul_nonneg (qmul_nonneg cfm (show qle qzero (qneg (qpowN (qmul Δ (qeps K)) (m + 1))) by rat_linarith)) sp
        have r : qEq (qmul (qmul (cf m) (qneg (qpowN (qmul Δ (qeps K)) (m + 1)))) (spow m (2 ^ K)))
            (qneg (qmul (qmul (cf m) (qpowN (qmul Δ (qeps K)) (m + 1))) (spow m (2 ^ K)))) := by rat_ring
        generalize qmul (qmul (cf m) (qneg (qpowN (qmul Δ (qeps K)) (m + 1)))) (spow m (2 ^ K)) = P at *
        generalize qmul (qmul (cf m) (qpowN (qmul Δ (qeps K)) (m + 1))) (spow m (2 ^ K)) = Q at *
        generalize ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (2 ^ K) = S at *
        rat_linarith
      · have := qmul_nonneg (show qle qzero (qneg (qpowN Δ (m + 1))) by rat_linarith) cf1
        have r : qEq (qmul (qneg (qpowN Δ (m + 1))) (cf (m + 1))) (qneg (qmul (qpowN Δ (m + 1)) (cf (m + 1)))) := by rat_ring
        generalize qmul (qneg (qpowN Δ (m + 1))) (cf (m + 1)) = P at *
        generalize qmul (qpowN Δ (m + 1)) (cf (m + 1)) = Q at *; rat_linarith

theorem cf_zero : qEq (cf 0) qone := by
  unfold cf
  show qEq (qinv' (qnat 1)) qone
  have n1 : qEq (qnat 1) qone := qEq_trans (qnat_succ 0) (by have := qnat_zero; exact qle_antisymm (by rat_linarith) (by rat_linarith))
  have h1 : ¬ qEq (qnat 1) qzero := qnat_ne_zero 0
  have c := qmul_inv'_cancel h1
  have r := qmul_respects n1 (qEq_refl (qinv' (qnat 1)))
  have o : qEq (qmul qone (qinv' (qnat 1))) (qinv' (qnat 1)) := by rat_ring
  generalize qmul (qnat 1) (qinv' (qnat 1)) = P at *; generalize qmul qone (qinv' (qnat 1)) = Q at *
  generalize qinv' (qnat 1) = I at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE INDUCTION STEP, at one index, as algebra. -/
theorem step_alg {F DF C s : Nat → QExpr} {fp fq Δ A M ML L U H e1 e2 : QExpr} {K m : Nat}
    (hs : ∀ j, qEq (s j) (qmul (qnat j) (qmul Δ (qeps K))))
    (end0 : ZTrig.Ab (qsub (F 0) fp) e1) (endG : ZTrig.Ab (qsub fq (F (2 ^ K))) e1)
    (steps : ∀ j, j < 2 ^ K → ZTrig.Ab (qsub (qsub (F (j + 1)) (F j)) (qmul (qmul Δ (qeps K)) (DF j)))
      (qadd e1 (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H)))
    (ih : ∀ j, j < 2 ^ K → Side (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))
      (qmul (qpowN (s j) m) (cf m)) L U e2)
    (hc : ∀ t, t < m → ZTrig.Ab (C (t + 1)) M) (hC0 : qEq (C 0) fp)
    (hΔ : ZTrig.Ab Δ A) (hA : qle qone A) (hM : qle qzero M) (bL : ZTrig.Ab L ML) (bU : ZTrig.Ab U ML)
    (e20 : qle qzero e2) :
    Side (qsub fq (ZTrig.bs (fun t => qmul (C t) (qmul (qpowN Δ t) (cf t))) (m + 1))) (qmul (qpowN Δ (m + 1)) (cf (m + 1))) L U
      (qadd (qadd (qmul (qnat (2 ^ K)) (qmul (qmul A (qeps K)) e2)) (qmul (qmul (qmul (cf m) (qmul A (qeps K))) (qpowN A m)) ML))
        (qadd (qadd e1 e1) (qadd (qmul (qnat (2 ^ K)) (qadd e1 (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H)))
          (qmul (qnat m) (qmul M (qmul (qmul A (qeps K)) (qpowN A m))))))) := by
  have a0 : qle qzero A := qle_trans (qle_of_qlt qone_pos) hA
  have hδ : ZTrig.Ab (qmul Δ (qeps K)) (qmul A (qeps K)) :=
    ZTrig.mul_abs hΔ ⟨by have := qeps_nonneg K; rat_linarith, qle_refl _⟩
  -- the remainders' side
  have S1 := side_sum (r := fun j => qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m)))
    (W := fun j => qmul (qmul Δ (qeps K)) (qmul (qpowN (s j) m) (cf m))) (fun j hj => side_mul (ih j hj) hδ e20) (wt_sign hs m (2 ^ K))
  obtain ⟨we, wsg⟩ := wt_err (m := m) hs hΔ a0
  have S2 := side_shift S1 we bL bU wsg
  -- the rest
  have pe := poly_err (c := fun t => C (t + 1)) (m := m) hs hc hΔ hA hM
  obtain ⟨st1, st2⟩ := ZTrig.bs_abs_c (2 ^ K) steps
  have tl := ZTrig.bs_tele F (2 ^ K)
  have sh := ZTrig.bs_shift (fun t => qmul (C t) (qmul (qpowN Δ t) (cf t))) m
  have c0 : qEq (qmul (C 0) (qmul (qpowN Δ 0) (cf 0))) fp := by
    have r := qmul_respects hC0 (qmul_respects (qEq_refl (qpowN Δ 0)) cf_zero)
    exact qEq_trans r (by show qEq (qmul fp (qmul qone qone)) fp; rat_ring)
  -- Σ (F(j+1) − F j) = Σ δ·DF + Σ steps;  δ·DF = δ·poly + δ·R
  have split1 := ZTrig.bs_congr (F := fun j => qsub (F (j + 1)) (F j))
    (G := fun j => qadd (qadd (qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))
        (qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))))
      (qsub (qsub (F (j + 1)) (F j)) (qmul (qmul Δ (qeps K)) (DF j))))
    (fun j => show qEq (qsub (F (j + 1)) (F j))
      (qadd (qadd (qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))
        (qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))))
      (qsub (qsub (F (j + 1)) (F j)) (qmul (qmul Δ (qeps K)) (DF j)))) by unfold qsub; rat_ring) (2 ^ K)
  have a1 := ZTrig.bs_add (fun j => qadd (qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))
        (qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))))
    (fun j => qsub (qsub (F (j + 1)) (F j)) (qmul (qmul Δ (qeps K)) (DF j))) (2 ^ K)
  have a2 := ZTrig.bs_add (fun j => qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))
    (fun j => qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))) (2 ^ K)
  -- the rest is within its bound
  refine side_err S2 ?_
  obtain ⟨p1, p2⟩ := pe
  obtain ⟨x1, x2⟩ := end0; obtain ⟨y1, y2⟩ := endG
  generalize ZTrig.bs (fun j => qsub (F (j + 1)) (F j)) (2 ^ K) = T0 at *
  generalize ZTrig.bs (fun j => qadd (qadd (qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))
        (qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))))
      (qsub (qsub (F (j + 1)) (F j)) (qmul (qmul Δ (qeps K)) (DF j)))) (2 ^ K) = T1 at *
  generalize ZTrig.bs (fun j => qadd (qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))
        (qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m)))) (2 ^ K) = T2 at *
  generalize ZTrig.bs (fun j => qsub (qsub (F (j + 1)) (F j)) (qmul (qmul Δ (qeps K)) (DF j))) (2 ^ K) = T3 at *
  generalize ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m)) (2 ^ K) = T4 at *
  generalize ZTrig.bs (fun j => qmul (qmul Δ (qeps K)) (qsub (DF j) (ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN (s j) t) (cf t))) m))) (2 ^ K) = T5 at *
  generalize ZTrig.bs (fun t => qmul (C t) (qmul (qpowN Δ t) (cf t))) (m + 1) = TP at *
  generalize ZTrig.bs (fun t => qmul (C (t + 1)) (qmul (qpowN Δ (t + 1)) (cf (t + 1)))) m = TS at *
  generalize qmul (C 0) (qmul (qpowN Δ 0) (cf 0)) = T00 at *
  generalize qmul (qnat (2 ^ K)) (qadd e1 (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H)) = B1 at *
  generalize qmul (qnat m) (qmul M (qmul (qmul A (qeps K)) (qpowN A m))) = B2 at *
  clear S1 S2 ih steps hc we wsg
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The grid between two points -/

theorem upd_ne' (p : Point QExpr) (i : Nat) (v : QExpr) {j : Nat} (h : j ≠ i) : upd p i v j = p j := by
  unfold upd
  cases Nat.decEq j i with
  | isTrue e => exact absurd e h
  | isFalse _ => rfl

theorem upd_inbox {B : Box QExpr} {p : Point QExpr} {i : Nat} {v : QExpr} (hp : InBox qOrd B p)
    (h1 : qle (B i).1 v) (h2 : qle v (B i).2) : InBox qOrd B (upd p i v) := by
  intro j
  unfold upd
  cases Nat.decEq j i with
  | isTrue e => subst e; exact ⟨h1, h2⟩
  | isFalse _ => exact hp j

/-- The `j`-th grid point from `p` toward `q` in `x_i`. -/
def gpoint (p q : Point QExpr) (i K j : Nat) : Point QExpr := upd p i (ZTrig.xg (p i) (q i) K j)

theorem gpt_inbox {B : Box QExpr} {p q : Point QExpr} {i K j : Nat} (hp : InBox qOrd B p) (hq : InBox qOrd B q)
    (hj : j ≤ 2 ^ K) : InBox qOrd B (gpoint p q i K j) := by
  obtain ⟨t0, t1⟩ := ZTrig.T_unit hj
  obtain ⟨a1, a2⟩ := hp i; obtain ⟨b1, b2⟩ := hq i
  obtain ⟨c1, c2⟩ := ZTrig.conv t0 t1 a1 a2 b1 b2
  have e := ZTrig.xg_T (p i) (q i) K j
  exact upd_inbox hp (by rat_linarith) (by rat_linarith)

theorem gpt_fix {p q : Point QExpr} {i K j : Nat} (j' : Nat) (h : j' ≠ i) : gpoint p q i K j j' = p j' := upd_ne' p i _ h

theorem gpt_at (p q : Point QExpr) (i K j : Nat) : gpoint p q i K j i = ZTrig.xg (p i) (q i) K j := upd_at p i _

/-- `x_i` along the grid: from `p`, `j·δ`; consecutive, `δ`. -/
theorem gpt_off (p q : Point QExpr) (i K j : Nat) :
    qEq (qsub (gpoint p q i K j i) (p i)) (qmul (qnat j) (qmul (qsub (q i) (p i)) (qeps K))) := by
  rw [gpt_at]; unfold ZTrig.xg qsub; rat_ring

theorem gpt_step (p q : Point QExpr) (i K j : Nat) :
    qEq (qsub (gpoint p q i K (j + 1) i) (gpoint p q i K j i)) (qmul (qsub (q i) (p i)) (qeps K)) := by
  rw [gpt_at, gpt_at]
  have e := ZTrig.xg_succ (p i) (q i) K j
  generalize ZTrig.xg (p i) (q i) K (j + 1) = X at *; generalize ZTrig.xg (p i) (q i) K j = Y at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gpt_end0 (p q : Point QExpr) (i K : Nat) : qEq (qsub (gpoint p q i K 0 i) (p i)) qzero := by
  rw [gpt_at]; have e := ZTrig.xg_zero (p i) (q i) K
  generalize ZTrig.xg (p i) (q i) K 0 = X at *; unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gpt_endG (p q : Point QExpr) (i K : Nat) : qEq (qsub (q i) (gpoint p q i K (2 ^ K) i)) qzero := by
  rw [gpt_at]; have e := ZTrig.xg_top (p i) (q i) K
  generalize ZTrig.xg (p i) (q i) K (2 ^ K) = X at *; unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- A step with a vanishing difference: `|e(q) − e(p)| ≤ ε` when `q_i − p_i ≈ 0`. -/
theorem step_zero {e : G} {i : Nat} {H : QExpr} {p q : Point QExpr} (s : StepAt i e H p q) (h0 : qEq (qsub (q i) (p i)) qzero)
    (k : Nat) : ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qsub (evalN n q e) (evalN n p e)) (qeps k) := by
  obtain ⟨N, hN⟩ := s k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n hn
  have z1 := qmul_respects h0 (qEq_refl (evalN n p (D i e)))
  have z2 := qmul_respects (qmul_respects h0 h0) (qEq_refl H)
  have o1 : qEq (qmul qzero (evalN n p (D i e))) qzero := by rat_ring
  have o2 : qEq (qmul (qmul qzero qzero) H) qzero := by rat_ring
  generalize qmul (qsub (q i) (p i)) (evalN n p (D i e)) = P at *
  generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) H = Q at *
  generalize qmul qzero (evalN n p (D i e)) = P' at *; generalize qmul (qmul qzero qzero) H = Q' at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The step with the difference replaced by an equal one. -/
theorem step_conv {X Y d δ e H : QExpr} (hd : qEq d δ) (h : ZTrig.Ab (qsub X (qmul d Y)) (qadd e (qmul (qmul d d) H))) :
    ZTrig.Ab (qsub X (qmul δ Y)) (qadd e (qmul (qmul δ δ) H)) := by
  have a := qmul_respects hd (qEq_refl Y)
  have b := qmul_respects (qmul_respects hd hd) (qEq_refl H)
  obtain ⟨h1, h2⟩ := h
  generalize qmul d Y = P at *; generalize qmul δ Y = P' at *
  generalize qmul (qmul d d) H = Q at *; generalize qmul (qmul δ δ) H = Q' at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem pow2_eps (K j : Nat) : qEq (qmul (qnat (2 ^ K)) (qeps (j + K))) (qeps j) :=
  qEq_trans (qmul_respects (qnat_pow2 K) (qEq_refl _)) (qpow2_mul_eps K j)

theorem fin_sum_a {V2 V5 T4 U4 EC AE GE GT Ek3 Ek2 : QExpr}
    (h4 : qle T4 U4) (b2 : qle EC Ek2) (i5 : qEq EC (qadd (qadd (qadd V2 V5) U4) AE)) (aε : qle qzero AE)
    (gd : qEq GT (qadd GE T4)) (ge : qEq GE Ek3) : qle (qadd V2 (qadd GT V5)) (qadd Ek2 Ek3) := by
  rat_linarith

theorem fin_sum {T1 V2 V5 T4 U4 EC AE E1 GE GT Ek3 Ek2 Ek1 Ek : QExpr}
    (h1 : qle T1 Ek2) (h4 : qle T4 U4) (b2 : qle EC Ek2) (i5 : qEq EC (qadd (qadd (qadd V2 V5) U4) AE)) (aε : qle qzero AE)
    (gd : qEq GT (qadd GE T4)) (ge : qEq GE Ek3) (ea : qle E1 Ek3) (s2 : qEq (qadd Ek3 Ek3) Ek2)
    (s1 : qEq (qadd Ek2 Ek2) Ek1) (s0 : qEq (qadd Ek1 Ek1) Ek) (p3 : qle qzero Ek3) :
    qle (qadd (qadd T1 V2) (qadd (qadd E1 E1) (qadd GT V5))) Ek := by
  have a := fin_sum_a h4 b2 i5 aε gd ge
  have r : qEq (qadd (qadd T1 V2) (qadd (qadd E1 E1) (qadd GT V5))) (qadd (qadd T1 (qadd E1 E1)) (qadd V2 (qadd GT V5))) := by rat_ring
  generalize qadd V2 (qadd GT V5) = W at *
  generalize qadd (qadd T1 V2) (qadd (qadd E1 E1) (qadd GT V5)) = Tot at *
  clear h4 b2 i5 aε gd ge
  rat_linarith

/-- THE TOTAL of `step_alg`, against `ε_k`, with the precisions chosen. -/
theorem total_le {A Δ M ML H : QExpr} {k BA B1 m : Nat} (hA : qle qone A) (hΔ : ZTrig.Ab Δ A) (hM : qle qzero M)
    (hML : qle qzero ML) (hH : qle qzero H)
    (hBA : ∀ j, qle (qmul (qeps (j + BA)) A) (qeps j))
    (hB1 : ∀ j, qle (qmul (qeps (j + B1)) (qadd (qadd (qmul (qmul (cf m) (qmul A (qpowN A m))) ML)
      (qmul (qnat m) (qmul M (qmul A (qpowN A m))))) (qadd (qmul (qmul A A) H) A))) (qeps j)) :
    qle (qadd (qadd (qmul (qnat (2 ^ ((k + 2) + B1))) (qmul (qmul A (qeps ((k + 2) + B1))) (qeps ((k + 2) + BA))))
        (qmul (qmul (qmul (cf m) (qmul A (qeps ((k + 2) + B1)))) (qpowN A m)) ML))
      (qadd (qadd (qeps ((k + 3) + ((k + 2) + B1))) (qeps ((k + 3) + ((k + 2) + B1))))
        (qadd (qmul (qnat (2 ^ ((k + 2) + B1))) (qadd (qeps ((k + 3) + ((k + 2) + B1)))
          (qmul (qmul (qmul Δ (qeps ((k + 2) + B1))) (qmul Δ (qeps ((k + 2) + B1)))) H)))
          (qmul (qnat m) (qmul M (qmul (qmul A (qeps ((k + 2) + B1))) (qpowN A m)))))))
      (qeps k) := by
  have g := ZTrig.g_one ((k + 2) + B1)
  generalize hK : (k + 2) + B1 = K at *
  have a0 : qle qzero A := qle_trans (qle_of_qlt qone_pos) hA
  have e0 := qeps_nonneg K
  -- T1 = A·e2
  have i1 : qEq (qmul (qnat (2 ^ K)) (qmul (qmul A (qeps K)) (qeps ((k + 2) + BA))))
      (qmul (qmul (qeps ((k + 2) + BA)) A) (qmul (qnat (2 ^ K)) (qeps K))) := by rat_ring
  have i1' := qmul_respects (qEq_refl (qmul (qeps ((k + 2) + BA)) A)) g
  have o1 : qEq (qmul (qmul (qeps ((k + 2) + BA)) A) qone) (qmul (qeps ((k + 2) + BA)) A) := by rat_ring
  have b1 := hBA (k + 2)
  -- G·δδH = ΔΔ·H·ε ≤ AA·H·ε
  have i4 : qEq (qmul (qnat (2 ^ K)) (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H))
      (qmul (qmul (qmul (qmul Δ Δ) H) (qeps K)) (qmul (qnat (2 ^ K)) (qeps K))) := by rat_ring
  have i4' := qmul_respects (qEq_refl (qmul (qmul (qmul Δ Δ) H) (qeps K))) g
  have o4 : qEq (qmul (qmul (qmul (qmul Δ Δ) H) (qeps K)) qone) (qmul (qmul (qmul Δ Δ) H) (qeps K)) := by rat_ring
  obtain ⟨_, dd⟩ := ZTrig.mul_abs hΔ hΔ
  have dH := ZExp.scale (ZExp.scale dd hH) e0
  -- G·e1 = ε_{k+3}; e1 + e1 ≤ ε_{k+2}
  have ge := pow2_eps K (k + 3)
  have ea := eps_anti (show k + 3 ≤ (k + 3) + K from Nat.le_add_right _ _)
  have s2 := qeps_succ_add (k + 2)
  have s1 := qeps_succ_add (k + 1)
  have s0 := qeps_succ_add k
  have p3 := qeps_nonneg (k + 3)
  -- the ε-terms: ε·C1 ≤ ε_{k+2}
  have b2 := hB1 (k + 2)
  rw [hK] at b2
  have i5 : qEq (qmul (qeps K) (qadd (qadd (qmul (qmul (cf m) (qmul A (qpowN A m))) ML)
      (qmul (qnat m) (qmul M (qmul A (qpowN A m))))) (qadd (qmul (qmul A A) H) A)))
      (qadd (qadd (qadd (qmul (qmul (qmul (cf m) (qmul A (qeps K))) (qpowN A m)) ML)
        (qmul (qnat m) (qmul M (qmul (qmul A (qeps K)) (qpowN A m))))) (qmul (qmul (qmul A A) H) (qeps K))) (qmul A (qeps K))) := by
    rat_ring
  have aε := qmul_nonneg a0 e0
  have gd : qEq (qmul (qnat (2 ^ K)) (qadd (qeps ((k + 3) + K)) (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H)))
      (qadd (qmul (qnat (2 ^ K)) (qeps ((k + 3) + K))) (qmul (qnat (2 ^ K)) (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H))) := by
    rat_ring
  generalize qmul (qnat (2 ^ K)) (qmul (qmul A (qeps K)) (qeps ((k + 2) + BA))) = T1 at *
  generalize qmul (qmul (qeps ((k + 2) + BA)) A) (qmul (qnat (2 ^ K)) (qeps K)) = T1' at *
  generalize qmul (qmul (qeps ((k + 2) + BA)) A) qone = T1'' at *
  generalize qmul (qeps ((k + 2) + BA)) A = T1''' at *
  generalize qmul (qnat (2 ^ K)) (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H) = T4 at *
  generalize qmul (qmul (qmul (qmul Δ Δ) H) (qeps K)) (qmul (qnat (2 ^ K)) (qeps K)) = T4' at *
  generalize qmul (qmul (qmul (qmul Δ Δ) H) (qeps K)) qone = T4'' at *
  generalize qmul (qmul (qmul Δ Δ) H) (qeps K) = T4''' at *
  generalize qmul (qmul (qmul A A) H) (qeps K) = U4 at *
  generalize qmul (qnat (2 ^ K)) (qeps ((k + 3) + K)) = GE at *
  generalize qmul (qnat (2 ^ K)) (qadd (qeps ((k + 3) + K)) (qmul (qmul (qmul Δ (qeps K)) (qmul Δ (qeps K))) H)) = GT at *
  generalize qmul (qmul (qmul (cf m) (qmul A (qeps K))) (qpowN A m)) ML = V2 at *
  generalize qmul (qnat m) (qmul M (qmul (qmul A (qeps K)) (qpowN A m))) = V5 at *
  generalize qmul (qeps K) (qadd (qadd (qmul (qmul (cf m) (qmul A (qpowN A m))) ML)
      (qmul (qnat m) (qmul M (qmul A (qpowN A m))))) (qadd (qmul (qmul A A) H) A)) = EC at *
  generalize qmul A (qeps K) = AE at *
  have h1 : qle T1 (qeps (k + 2)) := qle_trans (qle_of_qEq (qEq_trans i1 (qEq_trans i1' o1))) b1
  have h4 : qle T4 U4 := qle_trans (qle_of_qEq (qEq_trans i4 (qEq_trans i4' o4))) dH
  exact fin_sum h1 h4 b2 i5 aε gd ge ea s2 s1 s0 p3

/-- TAYLOR OF EVERY ORDER, ON VR'S OPERATIONAL REALS, WITHOUT THE MEAN VALUE THEOREM. Between two points of a box
differing in `x_i` by `Δ`, the remainder after the Taylor polynomial of degree `< m` lies in `Δ^m/m!·[L, U]`
(`[L, U]` the reading of `D^m e` over the box), within `ε_k`, from some index on. -/
theorem taylor_rem {B : Box QExpr} {i : Nat} : ∀ (m : Nat) (e : G) {L U : QExpr},
    (∀ t, t < m → StepRead B i (Diter i t e)) →
    (∀ t, t < m → ∃ l h, BoxEv B (Diter i (t + 1) e) l h) →
    BoxEv B (Diter i m e) L U →
    ∀ p q, InBox qOrd B p → InBox qOrd B q → (∀ j, j ≠ i → q j = p j) →
    ∀ k, ∃ N, ∀ n, N ≤ n →
      Side (qsub (evalN n q e) (tpoly i n p e (qsub (q i) (p i)) m)) (qmul (qpowN (qsub (q i) (p i)) m) (cf m)) L U (qeps k)
  | 0, e, L, U, _, _, hL, p, q, _, hq, _, k => by
      obtain ⟨N, hN⟩ := hL q hq k
      refine ⟨N, fun n hn => ?_⟩
      have ab : qle (qsub L (qeps k)) (evalN n q e) ∧ qle (evalN n q e) (qadd U (qeps k)) := hN n hn
      obtain ⟨a, b⟩ := ab
      have w1 : qEq (qmul (qpowN (qsub (q i) (p i)) 0) (cf 0)) qone :=
        qEq_trans (qmul_respects (qEq_refl qone) cf_zero) (by rat_ring)
      have wL := qmul_respects w1 (qEq_refl L)
      have wU := qmul_respects w1 (qEq_refl U)
      have oL : qEq (qmul qone L) L := by rat_ring
      have oU : qEq (qmul qone U) U := by rat_ring
      refine side_pos (by have := qle_of_qlt qone_pos; rat_linarith) ?_ ?_
      · show qle _ (qsub (evalN n q e) qzero)
        generalize qmul (qmul (qpowN (qsub (q i) (p i)) 0) (cf 0)) L = P at *; generalize qmul qone L = P' at *
        unfold qsub at *; rat_linarith
      · show qle (qsub (evalN n q e) qzero) _
        generalize qmul (qmul (qpowN (qsub (q i) (p i)) 0) (cf 0)) U = P at *; generalize qmul qone U = P' at *
        unfold qsub at *; rat_linarith
  | m + 1, e, L, U, hS, hV, hL, p, q, hp, hq, hfix, k => by
      have o := qle_of_qlt qone_pos
      obtain ⟨H, H0, hstep⟩ := step_sound (hS 0 (Nat.succ_pos m))
      -- constants
      obtain ⟨MΔ, _, hMΔ0, _, mΔ, _, _, _⟩ := bound4 (qsub (q i) (p i)) (qsub (q i) (p i)) (qsub (q i) (p i)) (qsub (q i) (p i))
      have hA : qle qone (qadd MΔ qone) := by rat_linarith
      have hΔA : ZTrig.Ab (qsub (q i) (p i)) (qadd MΔ qone) := by
        obtain ⟨x1, x2⟩ := mΔ; unfold qsub at x1 x2 ⊢; exact ⟨by rat_linarith, by rat_linarith⟩
      generalize hAd : qadd MΔ qone = A at hA hΔA
      have a0 : qle qzero A := qle_trans o hA
      obtain ⟨M0, _, hM00, _, mL, mU, _, _⟩ := bound4 L U L U
      have bL : ZTrig.Ab L M0 := by obtain ⟨x1, x2⟩ := mL; unfold qsub at x1 x2; exact ⟨by rat_linarith, by rat_linarith⟩
      have bU : ZTrig.Ab U M0 := by obtain ⟨x1, x2⟩ := mU; unfold qsub at x1 x2; exact ⟨by rat_linarith, by rat_linarith⟩
      have cb : ∀ t, t < m → ∃ M, qle qzero M ∧ ∃ N, ∀ n, N ≤ n → ZTrig.Ab (evalN n p (Diter i (t + 1) e)) M :=
        fun t ht => by
          obtain ⟨l, h, r⟩ := hV t (Nat.lt_succ_of_lt ht)
          obtain ⟨M, m0, b⟩ := read_bound r
          exact ⟨M, m0, b p hp⟩
      obtain ⟨M, hM0, hMt⟩ := fin_bound (P := fun t M => ∃ N, ∀ n, N ≤ n → ZTrig.Ab (evalN n p (Diter i (t + 1) e)) M)
        (fun t M M' hMM ⟨N, hN⟩ => ⟨N, fun n hn => by obtain ⟨x1, x2⟩ := hN n hn; exact ⟨by rat_linarith, by rat_linarith⟩⟩) m cb
      obtain ⟨Nc, hNc⟩ := ZTrig.fin_N (P := fun t n => t < m → ZTrig.Ab (evalN n p (Diter i (t + 1) e)) M)
        (fun t => by
          cases Nat.lt_or_ge t m with
          | inl ht => obtain ⟨N, hN⟩ := hMt t ht; exact ⟨N, fun n hn _ => hN n hn⟩
          | inr ht => exact ⟨0, fun _ _ h => absurd h (Nat.not_lt_of_ge ht)⟩) m
      -- precisions
      have C0 : qle qzero (qadd (qadd (qmul (qmul (cf m) (qmul A (qpowN A m))) M0)
          (qmul (qnat m) (qmul M (qmul A (qpowN A m))))) (qadd (qmul (qmul A A) H) A)) := by
        have p1 := qmul_nonneg (qmul_nonneg (cf_nonneg m) (qmul_nonneg a0 (powN_nonneg a0 m))) hM00
        have p2 := qmul_nonneg (qnat_nonneg m) (qmul_nonneg hM0 (qmul_nonneg a0 (powN_nonneg a0 m)))
        have p3 := qmul_nonneg (qmul_nonneg a0 a0) H0
        rat_linarith
      obtain ⟨B1, hB1⟩ := eps_scaled C0
      obtain ⟨BA, hBA⟩ := eps_scaled a0
      have tot := total_le (k := k) hA hΔA hM0 hM00 H0 hBA hB1
      -- |δ| ≤ 1
      have hδ1 : ZTrig.Ab (qmul (qsub (q i) (p i)) (qeps ((k + 2) + B1))) qone := by
        have b := hB1 (k + 2)
        have e1 := ZTrig.qeps_le_one (k + 2)
        obtain ⟨d1, d2⟩ := ZTrig.mul_abs hΔA (show ZTrig.Ab (qeps ((k + 2) + B1)) (qeps ((k + 2) + B1)) from
          ⟨by have := qeps_nonneg ((k + 2) + B1); rat_linarith, qle_refl _⟩)
        have s := scale_l (show qle A (qadd (qadd (qmul (qmul (cf m) (qmul A (qpowN A m))) M0)
          (qmul (qnat m) (qmul M (qmul A (qpowN A m))))) (qadd (qmul (qmul A A) H) A)) by
            have p1 := qmul_nonneg (qmul_nonneg (cf_nonneg m) (qmul_nonneg a0 (powN_nonneg a0 m))) hM00
            have p2 := qmul_nonneg (qnat_nonneg m) (qmul_nonneg hM0 (qmul_nonneg a0 (powN_nonneg a0 m)))
            have p3 := qmul_nonneg (qmul_nonneg a0 a0) H0
            rat_linarith) (qeps_nonneg ((k + 2) + B1))
        have c := qmul_comm A (qeps ((k + 2) + B1))
        generalize qmul (qeps ((k + 2) + B1)) (qadd (qadd (qmul (qmul (cf m) (qmul A (qpowN A m))) M0)
          (qmul (qnat m) (qmul M (qmul A (qpowN A m))))) (qadd (qmul (qmul A A) H) A)) = P at *
        generalize qmul (qeps ((k + 2) + B1)) A = Q at *; generalize qmul A (qeps ((k + 2) + B1)) = Q' at *
        generalize qmul (qsub (q i) (p i)) (qeps ((k + 2) + B1)) = D at *
        exact ⟨by rat_linarith, by rat_linarith⟩
      generalize hK : (k + 2) + B1 = K at tot hδ1
      -- the grid's steps
      have fixg : ∀ j j', j' ≠ i → gpoint p q i K j j' = p j' := fun j j' h => gpt_fix j' h
      obtain ⟨Ns, hNs⟩ := ZTrig.fin_N (P := fun j n => j < 2 ^ K →
          ZTrig.Ab (qsub (qsub (evalN n (gpoint p q i K (j + 1)) e) (evalN n (gpoint p q i K j) e))
            (qmul (qsub (gpoint p q i K (j + 1) i) (gpoint p q i K j i)) (evalN n (gpoint p q i K j) (D i e))))
            (qadd (qeps ((k + 3) + K)) (qmul (qmul (qsub (gpoint p q i K (j + 1) i) (gpoint p q i K j i))
              (qsub (gpoint p q i K (j + 1) i) (gpoint p q i K j i))) H)))
        (fun j => by
          cases Nat.lt_or_ge j (2 ^ K) with
          | inl hj =>
            have st := gpt_step p q i K j
            obtain ⟨N, hN⟩ := hstep (gpoint p q i K j) (gpoint p q i K (j + 1)) (gpt_inbox hp hq (Nat.le_of_lt hj))
              (gpt_inbox hp hq hj) (fun j' h => by rw [fixg, fixg] <;> exact h)
              (by obtain ⟨d1, d2⟩ := hδ1; generalize qsub (gpoint p q i K (j + 1) i) (gpoint p q i K j i) = X at *
                  generalize qmul (qsub (q i) (p i)) (qeps K) = Y at *; exact ⟨by rat_linarith, by rat_linarith⟩) ((k + 3) + K)
            exact ⟨N, fun n hn _ => hN n hn⟩
          | inr hj => exact ⟨0, fun _ _ h => absurd h (Nat.not_lt_of_ge hj)⟩) (2 ^ K)
      -- the ends
      have e0 := gpt_end0 p q i K
      have eG := gpt_endG p q i K
      obtain ⟨N0, h0⟩ := step_zero (hstep p (gpoint p q i K 0) hp (gpt_inbox hp hq (Nat.zero_le _))
        (fun j' h => fixg 0 j' h) (by generalize qsub (gpoint p q i K 0 i) (p i) = X at *; exact ⟨by rat_linarith, by rat_linarith⟩)) e0 ((k + 3) + K)
      obtain ⟨NG, hG⟩ := step_zero (hstep (gpoint p q i K (2 ^ K)) q (gpt_inbox hp hq (Nat.le_refl _)) hq
        (fun j' h => by rw [fixg _ j' h]; exact hfix j' h)
        (by generalize qsub (q i) (gpoint p q i K (2 ^ K) i) = X at *; exact ⟨by rat_linarith, by rat_linarith⟩)) eG ((k + 3) + K)
      -- order m for D e at every grid point
      obtain ⟨Ni, hNi⟩ := ZTrig.fin_N (P := fun j n => j < 2 ^ K →
          Side (qsub (evalN n (gpoint p q i K j) (D i e)) (tpoly i n p (D i e) (qsub (gpoint p q i K j i) (p i)) m))
            (qmul (qpowN (qsub (gpoint p q i K j i) (p i)) m) (cf m)) L U (qeps ((k + 2) + BA)))
        (fun j => by
          cases Nat.lt_or_ge j (2 ^ K) with
          | inl hj =>
            obtain ⟨N, hN⟩ := taylor_rem m (D i e) (fun t ht => hS (t + 1) (Nat.succ_lt_succ ht))
              (fun t ht => hV (t + 1) (Nat.succ_lt_succ ht)) hL p (gpoint p q i K j) hp
              (gpt_inbox hp hq (Nat.le_of_lt hj)) (fun j' h => fixg j j' h) ((k + 2) + BA)
            exact ⟨N, fun n hn _ => hN n hn⟩
          | inr hj => exact ⟨0, fun _ _ h => absurd h (Nat.not_lt_of_ge hj)⟩) (2 ^ K)
      refine ⟨(Ns + Ni) + ((N0 + NG) + Nc), fun n hn => ?_⟩
      have sa := step_alg (F := fun j => evalN n (gpoint p q i K j) e) (DF := fun j => evalN n (gpoint p q i K j) (D i e))
        (C := fun t => evalN n p (Diter i t e)) (s := fun j => qsub (gpoint p q i K j i) (p i))
        (fp := evalN n p e) (fq := evalN n q e) (Δ := qsub (q i) (p i)) (A := A) (M := M) (ML := M0) (H := H)
        (e1 := qeps ((k + 3) + K)) (e2 := qeps ((k + 2) + BA)) (K := K) (m := m)
        (fun j => gpt_off p q i K j)
        (h0 n (ZTrig.le_l' (ZTrig.le_l' (ZTrig.le_r' hn))))
        (hG n (ZTrig.le_r' (ZTrig.le_l' (ZTrig.le_r' hn))))
        (fun j hj => step_conv (gpt_step p q i K j) (hNs n (ZTrig.le_l' (ZTrig.le_l' hn)) j hj hj))
        (fun j hj => hNi n (ZTrig.le_r' (ZTrig.le_l' hn)) j hj hj)
        (fun t ht => hNc n (ZTrig.le_r' (ZTrig.le_r' hn)) t ht ht) (qEq_refl _)
        hΔA hA hM0 bL bU (qeps_nonneg _)
      exact side_widen sa tot

end ZTaylorN

#print axioms ZTaylorN.gsum_bounds
#print axioms ZTaylorN.faul_up
#print axioms ZTaylorN.faul_lo
#print axioms ZTaylorN.cf_succ
#print axioms ZTaylorN.side_mul
#print axioms ZTaylorN.side_sum
#print axioms ZTaylorN.side_shift
#print axioms ZTaylorN.bs_swap
#print axioms ZTaylorN.powN_mul
#print axioms ZTaylorN.cf_le_one
#print axioms ZTaylorN.side_err
#print axioms ZTaylorN.fin_bound
#print axioms ZTaylorN.faul_weight
#print axioms ZTaylorN.poly_err
#print axioms ZTaylorN.wt_sign
#print axioms ZTaylorN.wt_err
#print axioms ZTaylorN.step_alg
#print axioms ZTaylorN.gpt_inbox
#print axioms ZTaylorN.step_zero
#print axioms ZTaylorN.total_le
#print axioms ZTaylorN.taylor_rem
