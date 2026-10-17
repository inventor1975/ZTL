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
