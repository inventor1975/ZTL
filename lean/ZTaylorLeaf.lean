import ZTaylorN
import ZIntegralT

/-!
# ZTaylorLeaf — the Taylor leaf of every even order (`zintegral.py`'s `{"taylor": n}`). Zero axioms.

The leaf on a piece `[m − h, m + h]` encloses the integral by `Σ_{j even < n} 2h^(j+1)/(j+1)·c_j(m)` plus
`2h^(n+1)/(n+1)·[c_n over the piece]`. Here every SYMMETRIC tagged sum `Σ (b − a)·(f(m + s) + f(m − s))` over a
refinement of `[0, h]` with mesh `μ`: by `ZTaylorN.taylor_rem` at `(m, m ± s)` (order `n`, even), the odd terms of
the two Taylor polynomials cancel exactly, the even ones double; the remainders carry the weight `s^n/n! ≥ 0`; the
sums over the cells of `(b − a)·s^t` are `h^(t+1)/(t+1)` within `μ·h^t` (`psum_cells`, Faulhaber's argument per cell).

Part 1: powers of `−s`, pairs, sums over the cells.
-/

namespace ZTaylorLeaf

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZIntegralT ZIntegralR

theorem powN_neg (s : QExpr) : ∀ j, qEq (qpowN (qneg s) (2 * j)) (qpowN s (2 * j)) ∧
    qEq (qpowN (qneg s) (2 * j + 1)) (qneg (qpowN s (2 * j + 1)))
  | 0 => ⟨qEq_refl _, by show qEq (qmul qone (qneg s)) (qneg (qmul qone s)); rat_ring⟩
  | j + 1 => by
      obtain ⟨a, _⟩ := powN_neg s j
      have h2 : 2 * (j + 1) = 2 * j + 1 + 1 := by rw [Nat.mul_succ]
      rw [h2]
      have e1 : qEq (qpowN (qneg s) (2 * j + 1 + 1)) (qmul (qmul (qpowN (qneg s) (2 * j)) (qneg s)) (qneg s)) := qEq_refl _
      have e2 : qEq (qpowN s (2 * j + 1 + 1)) (qmul (qmul (qpowN s (2 * j)) s) s) := qEq_refl _
      have r1 := qmul_respects (qmul_respects a (qEq_refl (qneg s))) (qEq_refl (qneg s))
      have c1 : qEq (qmul (qmul (qpowN s (2 * j)) (qneg s)) (qneg s)) (qmul (qmul (qpowN s (2 * j)) s) s) := by rat_ring
      refine ⟨qEq_trans r1 c1, ?_⟩
      show qEq (qmul (qpowN (qneg s) (2 * j + 1 + 1)) (qneg s)) (qneg (qmul (qpowN s (2 * j + 1 + 1)) s))
      have r2 := qmul_respects (qEq_trans r1 c1) (qEq_refl (qneg s))
      exact qEq_trans r2 (by show qEq (qmul (qmul (qmul (qpowN s (2 * j)) s) s) (qneg s)) (qneg (qmul (qmul (qmul (qpowN s (2 * j)) s) s) s)); rat_ring)

theorem bs_pairs (F : Nat → QExpr) : ∀ r, qEq (ZTrig.bs F (2 * r)) (ZTrig.bs (fun j => qadd (F (2 * j)) (F (2 * j + 1))) r)
  | 0 => qEq_refl _
  | r + 1 => by
      have ih := bs_pairs F r
      have h2 : 2 * (r + 1) = 2 * r + 1 + 1 := by rw [Nat.mul_succ]
      rw [h2]
      show qEq (qadd (qadd (ZTrig.bs F (2 * r)) (F (2 * r))) (F (2 * r + 1)))
        (qadd (ZTrig.bs (fun j => qadd (F (2 * j)) (F (2 * j + 1))) r) (qadd (F (2 * r)) (F (2 * r + 1))))
      generalize ZTrig.bs F (2 * r) = A at *
      generalize ZTrig.bs (fun j => qadd (F (2 * j)) (F (2 * j + 1))) r = B at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- One cell: `(t + 1)·(b − a)·s^t` is `b^(t+1) − a^(t+1)` within `(t + 1)·μ·(b^t − a^t)`. -/
theorem cell_pow {a b s μ : QExpr} (t : Nat) (h0 : qle qzero a) (has : qle a s) (hsb : qle s b) (hw : qle (qsub b a) μ) :
    ZTrig.Ab (qsub (qmul (qnat (t + 1)) (qmul (qsub b a) (qpowN s t))) (qsub (qpowN b (t + 1)) (qpowN a (t + 1))))
      (qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN b t) (qpowN a t))) := by
  have hab : qle a b := qle_trans has hsb
  have s0 : qle qzero s := qle_trans h0 has
  have w0 : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  obtain ⟨g1, g2⟩ := gsum_bounds h0 hab t
  have d := pow_diff a b t
  have p1 := powN_mono h0 has t
  have p2 := powN_mono s0 hsb t
  have n0 := qnat_nonneg (t + 1)
  -- everything is (b − a)·(t + 1)·X with X between a^t and b^t
  have m1 := scale_l (scale_l p1 n0) w0
  have m2 := scale_l (scale_l p2 n0) w0
  have m3 := scale_l g1 w0
  have m4 := scale_l g2 w0
  have dd : qle qzero (qsub (qpowN b t) (qpowN a t)) := by have := powN_mono h0 hab t; unfold qsub; rat_linarith
  have mu := ZExp.scale hw (qmul_nonneg n0 dd)
  have r1 : qEq (qmul (qnat (t + 1)) (qmul (qsub b a) (qpowN s t))) (qmul (qsub b a) (qmul (qnat (t + 1)) (qpowN s t))) := by rat_ring
  have r2 : qEq (qmul (qsub (qsub b a) qzero) qzero) qzero := by rat_ring
  have r3 : qEq (qmul (qsub b a) (qmul (qnat (t + 1)) (qsub (qpowN b t) (qpowN a t))))
      (qsub (qmul (qsub b a) (qmul (qnat (t + 1)) (qpowN b t))) (qmul (qsub b a) (qmul (qnat (t + 1)) (qpowN a t)))) := by
    unfold qsub; rat_ring
  have r4 : qEq (qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN b t) (qpowN a t))) (qmul μ (qmul (qnat (t + 1)) (qsub (qpowN b t) (qpowN a t)))) := by
    rat_ring
  generalize qmul (qnat (t + 1)) (qmul (qsub b a) (qpowN s t)) = X1 at *
  generalize qmul (qsub b a) (qmul (qnat (t + 1)) (qpowN s t)) = X2 at *
  generalize qsub (qpowN b (t + 1)) (qpowN a (t + 1)) = Y1 at *
  generalize qmul (qsub b a) (gsum a b t) = Y2 at *
  generalize qmul (qsub b a) (qmul (qnat (t + 1)) (qpowN a t)) = Z1 at *
  generalize qmul (qsub b a) (qmul (qnat (t + 1)) (qpowN b t)) = Z2 at *
  generalize qmul (qsub b a) (qmul (qnat (t + 1)) (qsub (qpowN b t) (qpowN a t))) = Z3 at *
  generalize qmul (qsub b a) (qmul (qnat (t + 1)) (qpowN a t)) = Z4 at *
  generalize qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN b t) (qpowN a t)) = W at *
  generalize qmul μ (qmul (qnat (t + 1)) (qsub (qpowN b t) (qpowN a t))) = W' at *
  generalize qmul (qsub b a) (qmul (qnat (t + 1)) (qsub (qpowN b t) (qpowN a t))) = W'' at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The cells from `x ≥ 0` to `y`: `(t + 1)·Σ (b − a)s^t` is `y^(t+1) − x^(t+1)` within `(t + 1)·μ·(y^t − x^t)`. -/
theorem psum_cells {μ : QExpr} (t : Nat) : ∀ (cs : List Cell) (x y : QExpr), qle qzero x → Chain x y cs →
    (∀ c, List.Mem c cs → CellOK μ c) →
    ZTrig.Ab (qsub (qmul (qnat (t + 1)) (csum (fun c => qpowN c.2.2 t) cs)) (qsub (qpowN y (t + 1)) (qpowN x (t + 1))))
      (qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN y t) (qpowN x t)))
  | [], x, y, _, h, _ => by
      have e1 := powN_respects h (t + 1)
      have e2 := powN_respects h t
      have z : qEq (qmul (qnat (t + 1)) qzero) qzero := by rat_ring
      have w1 := qmul_respects (qEq_refl (qmul (qnat (t + 1)) μ)) (show qEq (qsub (qpowN y t) (qpowN x t)) qzero by
        unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith))
      have w0 : qEq (qmul (qmul (qnat (t + 1)) μ) qzero) qzero := by rat_ring
      show ZTrig.Ab (qsub (qmul (qnat (t + 1)) qzero) (qsub (qpowN y (t + 1)) (qpowN x (t + 1)))) _
      generalize qmul (qnat (t + 1)) qzero = P at *
      generalize qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN y t) (qpowN x t)) = Q at *
      generalize qmul (qmul (qnat (t + 1)) μ) qzero = Q' at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  | (a, b, s) :: cs, x, y, hx, h, hok => by
      obtain ⟨c0, cas, csb, cw⟩ := hok (a, b, s) (List.Mem.head cs)
      have ha : qEq a x := h.1
      have hb0 : qle qzero b := qle_trans c0 (qle_trans cas csb)
      have ih := psum_cells t cs b y hb0 h.2 (fun z hz => hok z (List.Mem.tail _ hz))
      have ce := cell_pow t c0 cas csb cw
      have e1 := powN_respects ha (t + 1)
      have e2 := powN_respects ha t
      have e3 := qmul_respects (qEq_refl (qmul (qnat (t + 1)) μ)) (show qEq (qsub (qpowN b t) (qpowN a t)) (qsub (qpowN b t) (qpowN x t)) by
        unfold qsub; exact qadd_respects (qEq_refl _) (qneg_respects e2))
      have d1 : qEq (qmul (qnat (t + 1)) (qadd (qmul (qsub b a) (qpowN s t)) (csum (fun c => qpowN c.2.2 t) cs)))
          (qadd (qmul (qnat (t + 1)) (qmul (qsub b a) (qpowN s t))) (qmul (qnat (t + 1)) (csum (fun c => qpowN c.2.2 t) cs))) := by rat_ring
      have d2 : qEq (qadd (qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN b t) (qpowN x t))) (qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN y t) (qpowN b t))))
          (qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN y t) (qpowN x t))) := by unfold qsub; rat_ring
      show ZTrig.Ab (qsub (qmul (qnat (t + 1)) (qadd (qmul (qsub b a) (qpowN s t)) (csum (fun c => qpowN c.2.2 t) cs)))
        (qsub (qpowN y (t + 1)) (qpowN x (t + 1)))) _
      obtain ⟨i1, i2⟩ := ih; obtain ⟨c1, c2⟩ := ce
      generalize qmul (qnat (t + 1)) (qadd (qmul (qsub b a) (qpowN s t)) (csum (fun c => qpowN c.2.2 t) cs)) = L at *
      generalize qmul (qnat (t + 1)) (qmul (qsub b a) (qpowN s t)) = L1 at *
      generalize qmul (qnat (t + 1)) (csum (fun c => qpowN c.2.2 t) cs) = L2 at *
      generalize qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN b t) (qpowN a t)) = W1 at *
      generalize qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN b t) (qpowN x t)) = W1' at *
      generalize qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN y t) (qpowN b t)) = W2 at *
      generalize qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN y t) (qpowN x t)) = W at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE TWO TAYLOR POLYNOMIALS, at `+s` and `−s`, of degree `< 2r`: the odd terms cancel, the even ones double. -/
theorem tsym (C : Nat → QExpr) (s : QExpr) (r : Nat) :
    qEq (qadd (ZTrig.bs (fun t => qmul (C t) (qmul (qpowN s t) (cf t))) (2 * r))
        (ZTrig.bs (fun t => qmul (C t) (qmul (qpowN (qneg s) t) (cf t))) (2 * r)))
      (ZTrig.bs (fun j => qmul (qadd (C (2 * j)) (C (2 * j))) (qmul (qpowN s (2 * j)) (cf (2 * j)))) r) := by
  have p1 := bs_pairs (fun t => qmul (C t) (qmul (qpowN s t) (cf t))) r
  have p2 := bs_pairs (fun t => qmul (C t) (qmul (qpowN (qneg s) t) (cf t))) r
  have a := ZTrig.bs_add (fun j => qadd (qmul (C (2 * j)) (qmul (qpowN s (2 * j)) (cf (2 * j))))
      (qmul (C (2 * j + 1)) (qmul (qpowN s (2 * j + 1)) (cf (2 * j + 1)))))
    (fun j => qadd (qmul (C (2 * j)) (qmul (qpowN (qneg s) (2 * j)) (cf (2 * j))))
      (qmul (C (2 * j + 1)) (qmul (qpowN (qneg s) (2 * j + 1)) (cf (2 * j + 1))))) r
  have c := ZTrig.bs_congr (F := fun j => qadd (qadd (qmul (C (2 * j)) (qmul (qpowN s (2 * j)) (cf (2 * j))))
      (qmul (C (2 * j + 1)) (qmul (qpowN s (2 * j + 1)) (cf (2 * j + 1)))))
      (qadd (qmul (C (2 * j)) (qmul (qpowN (qneg s) (2 * j)) (cf (2 * j))))
        (qmul (C (2 * j + 1)) (qmul (qpowN (qneg s) (2 * j + 1)) (cf (2 * j + 1))))))
    (G := fun j => qmul (qadd (C (2 * j)) (C (2 * j))) (qmul (qpowN s (2 * j)) (cf (2 * j))))
    (fun j => by
      obtain ⟨e0, e1⟩ := powN_neg s j
      have r0 := qmul_respects (qEq_refl (C (2 * j))) (qmul_respects e0 (qEq_refl (cf (2 * j))))
      have r1 := qmul_respects (qEq_refl (C (2 * j + 1))) (qmul_respects e1 (qEq_refl (cf (2 * j + 1))))
      have o : qEq (qmul (C (2 * j + 1)) (qmul (qneg (qpowN s (2 * j + 1))) (cf (2 * j + 1))))
          (qneg (qmul (C (2 * j + 1)) (qmul (qpowN s (2 * j + 1)) (cf (2 * j + 1))))) := by rat_ring
      have d : qEq (qmul (qadd (C (2 * j)) (C (2 * j))) (qmul (qpowN s (2 * j)) (cf (2 * j))))
          (qadd (qmul (C (2 * j)) (qmul (qpowN s (2 * j)) (cf (2 * j)))) (qmul (C (2 * j)) (qmul (qpowN s (2 * j)) (cf (2 * j))))) := by rat_ring
      show qEq (qadd (qadd (qmul (C (2 * j)) (qmul (qpowN s (2 * j)) (cf (2 * j))))
          (qmul (C (2 * j + 1)) (qmul (qpowN s (2 * j + 1)) (cf (2 * j + 1)))))
          (qadd (qmul (C (2 * j)) (qmul (qpowN (qneg s) (2 * j)) (cf (2 * j))))
            (qmul (C (2 * j + 1)) (qmul (qpowN (qneg s) (2 * j + 1)) (cf (2 * j + 1))))))
        (qmul (qadd (C (2 * j)) (C (2 * j))) (qmul (qpowN s (2 * j)) (cf (2 * j))))
      generalize qmul (C (2 * j)) (qmul (qpowN s (2 * j)) (cf (2 * j))) = A at *
      generalize qmul (C (2 * j + 1)) (qmul (qpowN s (2 * j + 1)) (cf (2 * j + 1))) = B at *
      generalize qmul (C (2 * j)) (qmul (qpowN (qneg s) (2 * j)) (cf (2 * j))) = A' at *
      generalize qmul (C (2 * j + 1)) (qmul (qpowN (qneg s) (2 * j + 1)) (cf (2 * j + 1))) = B' at *
      generalize qmul (C (2 * j + 1)) (qmul (qneg (qpowN s (2 * j + 1))) (cf (2 * j + 1))) = B'' at *
      generalize qmul (qadd (C (2 * j)) (C (2 * j))) (qmul (qpowN s (2 * j)) (cf (2 * j))) = D at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)) r
  exact qEq_trans (qadd_respects p1 p2) (qEq_trans (qEq_symm a) c)

theorem tpoly_congr {i n : Nat} {p : Point QExpr} {e : G} {Δ Δ' : QExpr} (h : qEq Δ Δ') (m : Nat) :
    qEq (tpoly i n p e Δ m) (tpoly i n p e Δ' m) :=
  ZTrig.bs_congr (fun t => qmul_respects (qEq_refl _) (qmul_respects (powN_respects h t) (qEq_refl _))) m

/-- ONE CELL OF THE LEAF: at the tag `s ∈ [0, h]`, `f(m + s) + f(m − s)` minus the doubled even Taylor terms lies
in `2·s^n/n!·[L, U]` within `2ε_k`, from some index on (`n = 2(r + 1)`). -/
theorem cell_taylor {B : Box QExpr} {i r : Nat} {e : G} {L U : QExpr} {p : Point QExpr} {m s h : QExpr}
    (hS : ∀ t, t < 2 * (r + 1) → StepRead B i (Diter i t e))
    (hV : ∀ t, t < 2 * (r + 1) → ∃ l h, VRead B (Diter i (t + 1) e) l h)
    (hL : VRead B (Diter i (2 * (r + 1)) e) L U)
    (hB : ∀ t, qle (qsub m h) t → qle t (qadd m h) → InBox qOrd B (upd p i t)) (hs0 : qle qzero s) (hsh : qle s h) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qmul (qadd (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1))))) L)
          (qadd (qeps k) (qeps k)))
        (qsub (qadd (evalN n (upd p i (qadd m s)) e) (evalN n (upd p i (qsub m s)) e))
          (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
            (qmul (qpowN s (2 * j)) (cf (2 * j)))) (r + 1))) ∧
      qle (qsub (qadd (evalN n (upd p i (qadd m s)) e) (evalN n (upd p i (qsub m s)) e))
          (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
            (qmul (qpowN s (2 * j)) (cf (2 * j)))) (r + 1)))
        (qadd (qmul (qadd (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1))))) U)
          (qadd (qeps k) (qeps k))) := by
  intro k
  have h0 : qle qzero h := qle_trans hs0 hsh
  have b0 := hB m (by unfold qsub; rat_linarith) (by rat_linarith)
  have bp := hB (qadd m s) (by unfold qsub; rat_linarith) (by rat_linarith)
  have bm := hB (qsub m s) (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
  obtain ⟨Np, hNp⟩ := taylor_rem (2 * (r + 1)) e hS hV hL (upd p i m) (upd p i (qadd m s)) b0 bp (upd_fix p i m (qadd m s)) k
  obtain ⟨Nm, hNm⟩ := taylor_rem (2 * (r + 1)) e hS hV hL (upd p i m) (upd p i (qsub m s)) b0 bm (upd_fix p i m (qsub m s)) k
  refine ⟨Np + Nm, fun n hn => ?_⟩
  have sp := hNp n (ZTrig.le_l' hn)
  have sm := hNm n (ZTrig.le_r' hn)
  rw [upd_self, upd_self] at sp sm
  have dp : qEq (qsub (qadd m s) m) s := by unfold qsub; rat_ring
  have dm : qEq (qsub (qsub m s) m) (qneg s) := by unfold qsub; rat_ring
  -- the weights: both s^n/n! ≥ 0
  have wp := qmul_respects (powN_respects dp (2 * (r + 1))) (qEq_refl (cf (2 * (r + 1))))
  have wm := qmul_respects (qEq_trans (powN_respects dm (2 * (r + 1))) (powN_neg s (r + 1)).1) (qEq_refl (cf (2 * (r + 1))))
  have w0 := qmul_nonneg (powN_nonneg hs0 (2 * (r + 1))) (cf_nonneg (2 * (r + 1)))
  obtain ⟨lp, up⟩ := sp.1 (by rat_linarith)
  obtain ⟨lm, um⟩ := sm.1 (by rat_linarith)
  have wpL := qmul_respects wp (qEq_refl L); have wpU := qmul_respects wp (qEq_refl U)
  have wmL := qmul_respects wm (qEq_refl L); have wmU := qmul_respects wm (qEq_refl U)
  -- the polynomials
  have tp := tpoly_congr (i := i) (n := n) (p := upd p i m) (e := e) dp (2 * (r + 1))
  have tm' := tpoly_congr (i := i) (n := n) (p := upd p i m) (e := e) dm (2 * (r + 1))
  have ts := tsym (fun t => evalN n (upd p i m) (Diter i t e)) s (r + 1)
  have dd : qEq (qmul (qadd (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1))))) L)
      (qadd (qmul (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) L) (qmul (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) L)) := by rat_ring
  have dU : qEq (qmul (qadd (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1))))) U)
      (qadd (qmul (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) U) (qmul (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) U)) := by rat_ring
  unfold tpoly at tp tm' lp up lm um
  generalize ZTrig.bs (fun t => qmul (evalN n (upd p i m) (Diter i t e)) (qmul (qpowN (qsub (qadd m s) m) t) (cf t))) (2 * (r + 1)) = Tp at *
  generalize ZTrig.bs (fun t => qmul (evalN n (upd p i m) (Diter i t e)) (qmul (qpowN (qsub (qsub m s) m) t) (cf t))) (2 * (r + 1)) = Tm at *
  generalize ZTrig.bs (fun t => qmul (evalN n (upd p i m) (Diter i t e)) (qmul (qpowN s t) (cf t))) (2 * (r + 1)) = Ts at *
  generalize ZTrig.bs (fun t => qmul (evalN n (upd p i m) (Diter i t e)) (qmul (qpowN (qneg s) t) (cf t))) (2 * (r + 1)) = Tn at *
  generalize ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
      (qmul (qpowN s (2 * j)) (cf (2 * j)))) (r + 1) = TT at *
  generalize qmul (qmul (qpowN (qsub (qadd m s) m) (2 * (r + 1))) (cf (2 * (r + 1)))) L = A1 at *
  generalize qmul (qmul (qpowN (qsub (qadd m s) m) (2 * (r + 1))) (cf (2 * (r + 1)))) U = A2 at *
  generalize qmul (qmul (qpowN (qsub (qsub m s) m) (2 * (r + 1))) (cf (2 * (r + 1)))) L = A3 at *
  generalize qmul (qmul (qpowN (qsub (qsub m s) m) (2 * (r + 1))) (cf (2 * (r + 1)))) U = A4 at *
  generalize qmul (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) L = B1 at *
  generalize qmul (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) U = B2 at *
  generalize qmul (qadd (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1))))) L = D1 at *
  generalize qmul (qadd (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN s (2 * (r + 1))) (cf (2 * (r + 1))))) U = D2 at *
  clear hNp hNm sp sm hS hV hL hB b0 bp bm wp wm w0 dp dm hs0 hsh h0
  generalize evalN n (upd p i (qadd m s)) e = Fp at *
  generalize evalN n (upd p i (qsub m s)) e = Fm at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem csum_bs_swap (F : Cell → Nat → QExpr) (R : Nat) : ∀ cs : List Cell,
    qEq (csum (fun c => ZTrig.bs (fun j => F c j) R) cs) (ZTrig.bs (fun j => csum (fun c => F c j) cs) R)
  | [] => by
      show qEq qzero (ZTrig.bs (fun j => qzero) R)
      have := ZTrig.bs_const qzero R
      exact qEq_symm (qEq_trans this (by rat_ring))
  | c :: cs => by
      have ih := csum_bs_swap F R cs
      have sc := ZTrig.bs_scale (qsub c.2.1 c.1) (fun j => F c j) R
      have ad := ZTrig.bs_add (fun j => qmul (qsub c.2.1 c.1) (F c j)) (fun j => csum (fun c => F c j) cs) R
      show qEq (qadd (qmul (qsub c.2.1 c.1) (ZTrig.bs (fun j => F c j) R)) (csum (fun c => ZTrig.bs (fun j => F c j) R) cs))
        (ZTrig.bs (fun j => qadd (qmul (qsub c.2.1 c.1) (F c j)) (csum (fun c => F c j) cs)) R)
      generalize qmul (qsub c.2.1 c.1) (ZTrig.bs (fun j => F c j) R) = A at *
      generalize csum (fun c => ZTrig.bs (fun j => F c j) R) cs = B' at *
      generalize ZTrig.bs (fun j => csum (fun c => F c j) cs) R = C' at *
      generalize ZTrig.bs (fun j => qmul (qsub c.2.1 c.1) (F c j)) R = D' at *
      generalize ZTrig.bs (fun j => qadd (qmul (qsub c.2.1 c.1) (F c j)) (csum (fun c => F c j) cs)) R = E' at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- Dividing a bound by a positive natural number. -/
theorem div_nat {X Y : QExpr} (t : Nat) (h : ZTrig.Ab (qmul (qnat (t + 1)) X) (qmul (qnat (t + 1)) Y)) : ZTrig.Ab X Y := by
  have pos := qnat_succ_pos t
  have i0 := qinv'_nonneg_of_pos pos
  have c := qmul_inv'_cancel (ne_zero_of_lt pos)
  obtain ⟨h1, h2⟩ := h
  have s1 := scale_l h1 i0
  have s2 := scale_l h2 i0
  have e1 : qEq (qmul (qinv' (qnat (t + 1))) (qmul (qnat (t + 1)) X)) (qmul X (qmul (qnat (t + 1)) (qinv' (qnat (t + 1))))) := by rat_ring
  have e2 : qEq (qmul (qinv' (qnat (t + 1))) (qmul (qnat (t + 1)) Y)) (qmul Y (qmul (qnat (t + 1)) (qinv' (qnat (t + 1))))) := by rat_ring
  have e3 : qEq (qmul (qinv' (qnat (t + 1))) (qneg (qmul (qnat (t + 1)) Y))) (qneg (qmul Y (qmul (qnat (t + 1)) (qinv' (qnat (t + 1)))))) := by rat_ring
  have f1 := qmul_respects (qEq_refl X) c
  have f2 := qmul_respects (qEq_refl Y) c
  have o1 : qEq (qmul X qone) X := by rat_ring
  have o2 : qEq (qmul Y qone) Y := by rat_ring
  generalize qmul (qinv' (qnat (t + 1))) (qmul (qnat (t + 1)) X) = P1 at *
  generalize qmul (qinv' (qnat (t + 1))) (qmul (qnat (t + 1)) Y) = P2 at *
  generalize qmul (qinv' (qnat (t + 1))) (qneg (qmul (qnat (t + 1)) Y)) = P3 at *
  generalize qmul X (qmul (qnat (t + 1)) (qinv' (qnat (t + 1)))) = Q1 at *
  generalize qmul Y (qmul (qnat (t + 1)) (qinv' (qnat (t + 1)))) = Q2 at *
  generalize qmul (qnat (t + 1)) X = R1 at *; generalize qmul (qnat (t + 1)) Y = R2 at *
  generalize qmul X qone = O1 at *; generalize qmul Y qone = O2 at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `Σ_cells (b − a)·s^t` against `h^(t+1)/(t+1)` (given as `hp`, `(t + 1)·hp = h^(t+1)`): within `μ·h^t`. -/
theorem qsum_hp {cs : List Cell} {h μ hp : QExpr} (t : Nat) (hch : Chain qzero h cs) (hok : ∀ c, List.Mem c cs → CellOK μ c)
    (hhp : qEq (qmul (qnat (t + 1)) hp) (qpowN h (t + 1))) (hμ : qle qzero μ) :
    ZTrig.Ab (qsub (csum (fun c => qpowN c.2.2 t) cs) hp) (qmul μ (qpowN h t)) := by
  obtain ⟨h0, _⟩ := cells_within cs qzero h hch hok
  have ps := psum_cells t cs qzero h (qle_refl _) hch hok
  have z1 : qEq (qpowN qzero (t + 1)) qzero := by show qEq (qmul (qpowN qzero t) qzero) qzero; rat_ring
  have z0 : qle qzero (qpowN qzero t) := powN_nonneg (qle_refl _) t
  have m := qmul_nonneg (qmul_nonneg (qnat_nonneg (t + 1)) hμ) z0
  apply div_nat t
  have i1 : qEq (qmul (qnat (t + 1)) (qsub (csum (fun c => qpowN c.2.2 t) cs) hp))
      (qsub (qmul (qnat (t + 1)) (csum (fun c => qpowN c.2.2 t) cs)) (qmul (qnat (t + 1)) hp)) := by unfold qsub; rat_ring
  have i2 : qEq (qmul (qnat (t + 1)) (qmul μ (qpowN h t))) (qmul (qmul (qnat (t + 1)) μ) (qpowN h t)) := by rat_ring
  have i3 : qEq (qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN h t) (qpowN qzero t)))
      (qsub (qmul (qmul (qnat (t + 1)) μ) (qpowN h t)) (qmul (qmul (qnat (t + 1)) μ) (qpowN qzero t))) := by unfold qsub; rat_ring
  obtain ⟨a1, a2⟩ := ps
  generalize qmul (qnat (t + 1)) (qsub (csum (fun c => qpowN c.2.2 t) cs) hp) = L at *
  generalize qmul (qnat (t + 1)) (csum (fun c => qpowN c.2.2 t) cs) = S at *
  generalize qmul (qnat (t + 1)) hp = Hp at *
  generalize qmul (qnat (t + 1)) (qmul μ (qpowN h t)) = W at *
  generalize qmul (qmul (qnat (t + 1)) μ) (qpowN h t) = W' at *
  generalize qmul (qmul (qnat (t + 1)) μ) (qsub (qpowN h t) (qpowN qzero t)) = W'' at *
  generalize qmul (qmul (qnat (t + 1)) μ) (qpowN qzero t) = W3 at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `2·C·Q` with `C ∈ [a − ε, b + ε]`, `Q = hp ± d`, `Q ≥ 0`, `|a|, |b| ≤ K`: within `2Kd + 2ε(hp + d)` of
`2a·hp`, `2b·hp`. -/
theorem prod_bound {C Q a b ε hp d K : QExpr} (c1 : qle (qsub a ε) C) (c2 : qle C (qadd b ε))
    (hq : ZTrig.Ab (qsub Q hp) d) (q0 : qle qzero Q) (ba : ZTrig.Ab a K) (bb : ZTrig.Ab b K) (e0 : qle qzero ε) :
    qle (qsub (qmul (qadd a a) hp) (qadd (qmul (qadd K K) d) (qmul (qadd ε ε) (qadd hp d)))) (qmul (qadd C C) Q) ∧
    qle (qmul (qadd C C) Q) (qadd (qmul (qadd b b) hp) (qadd (qmul (qadd K K) d) (qmul (qadd ε ε) (qadd hp d)))) := by
  obtain ⟨q1, q2⟩ := hq
  have s1 := scale_l c1 q0
  have s2 := scale_l c2 q0
  obtain ⟨m1, m2⟩ := ZTrig.mul_abs ba ⟨q1, q2⟩
  obtain ⟨n1, n2⟩ := ZTrig.mul_abs bb ⟨q1, q2⟩
  have eq1 := scale_l (show qle Q (qadd hp d) by unfold qsub at q2; rat_linarith) e0
  have r1 : qEq (qmul Q (qsub a ε)) (qsub (qmul a Q) (qmul ε Q)) := by unfold qsub; rat_ring
  have r2 : qEq (qmul Q (qadd b ε)) (qadd (qmul b Q) (qmul ε Q)) := by rat_ring
  have r3 : qEq (qmul a (qsub Q hp)) (qsub (qmul a Q) (qmul a hp)) := by unfold qsub; rat_ring
  have r4 : qEq (qmul b (qsub Q hp)) (qsub (qmul b Q) (qmul b hp)) := by unfold qsub; rat_ring
  have r5 : qEq (qmul (qadd C C) Q) (qadd (qmul Q C) (qmul Q C)) := by rat_ring
  have r6 : qEq (qmul (qadd a a) hp) (qadd (qmul a hp) (qmul a hp)) := by rat_ring
  have r7 : qEq (qmul (qadd b b) hp) (qadd (qmul b hp) (qmul b hp)) := by rat_ring
  have r8 : qEq (qmul (qadd K K) d) (qadd (qmul K d) (qmul K d)) := by rat_ring
  have r9 : qEq (qmul (qadd ε ε) (qadd hp d)) (qadd (qmul ε (qadd hp d)) (qmul ε (qadd hp d))) := by rat_ring
  generalize qmul Q (qsub a ε) = P1 at *; generalize qmul Q (qadd b ε) = P2 at *; generalize qmul Q C = P3 at *
  generalize qmul a Q = A1 at *; generalize qmul b Q = A2 at *; generalize qmul ε Q = A3 at *
  generalize qmul a (qsub Q hp) = M1 at *; generalize qmul b (qsub Q hp) = M2 at *
  generalize qmul a hp = H1 at *; generalize qmul b hp = H2 at *; generalize qmul K d = KD at *
  generalize qmul ε (qadd hp d) = ED at *
  generalize qmul (qadd C C) Q = LHS at *; generalize qmul (qadd a a) hp = AA at *; generalize qmul (qadd b b) hp = BB at *
  generalize qmul (qadd K K) d = KK at *; generalize qmul (qadd ε ε) (qadd hp d) = EE at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem csum_nonneg {g : Cell → QExpr} : ∀ cs : List Cell, (∀ c, List.Mem c cs → qle c.1 c.2.1 ∧ qle qzero (g c)) →
    qle qzero (csum g cs)
  | [], _ => qle_refl _
  | c :: cs, h => by
      have hc := h c (List.Mem.head cs)
      have ih := csum_nonneg cs (fun z hz => h z (List.Mem.tail c hz))
      have f := qmul_nonneg (show qle qzero (qsub c.2.1 c.1) by unfold qsub; have := hc.1; rat_linarith) hc.2
      show qle qzero (qadd (qmul (qsub c.2.1 c.1) (g c)) (csum g cs)); rat_linarith

/-- THE TAYLOR LEAF OF EVERY EVEN ORDER `n = 2(r + 1)`. The readings `[a_j, b_j]` of `c_{2j} = f^(2j)(m)/(2j)!` at the
midpoint, `[L, U]` of `f^(n)` over the piece, `hp_j = h^(2j+1)/(2j+1)`: every symmetric tagged sum of mesh `μ` lies, to
every precision from some index on, in `Σ_j 2h^(2j+1)/(2j+1)·[a_j, b_j] + 2h^(n+1)/(n+1)·[L, U]/n!` widened by
`ERR = Σ_j (2Kμh^(2j) + 2ε_k(hp_j + μh^(2j))) + 2K_Rμh^n + 2ε_k·h` — which vanishes as `μ → 0`, `k → ∞`. -/
theorem taylorN_leaf {B : Box QExpr} {i r : Nat} {e : G} {L U : QExpr} {p : Point QExpr} {m h μ K KR : QExpr}
    {cs : List Cell} (a b hp : Nat → QExpr)
    (hS : ∀ t, t < 2 * (r + 1) → StepRead B i (Diter i t e))
    (hV : ∀ t, t < 2 * (r + 1) → ∃ l h, VRead B (Diter i (t + 1) e) l h)
    (hL : VRead B (Diter i (2 * (r + 1)) e) L U)
    (hc : ∀ j, j < r + 1 → Ev (fun n => qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) (a j) (b j))
    (hab : ∀ j, j < r + 1 → ZTrig.Ab (a j) K ∧ ZTrig.Ab (b j) K)
    (hRL : ZTrig.Ab (qmul (cf (2 * (r + 1))) L) KR) (hRU : ZTrig.Ab (qmul (cf (2 * (r + 1))) U) KR)
    (hhp : ∀ j, j ≤ r + 1 → qEq (qmul (qnat (2 * j + 1)) (hp j)) (qpowN h (2 * j + 1)))
    (hB : ∀ t, qle (qsub m h) t → qle t (qadd m h) → InBox qOrd B (upd p i t))
    (hch : Chain qzero h cs) (hok : ∀ c, List.Mem c cs → CellOK μ c) (hμ : qle qzero μ) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qadd (ZTrig.bs (fun j => qmul (qadd (a j) (a j)) (hp j)) (r + 1))
            (qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (hp (r + 1))))
          (qadd (ZTrig.bs (fun j => qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
              (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))) (r + 1))
            (qadd (qmul (qadd KR KR) (qmul μ (qpowN h (2 * (r + 1))))) (qmul (qadd (qeps k) (qeps k)) h))))
        (ssum n e p i m cs) ∧
      qle (ssum n e p i m cs)
        (qadd (qadd (ZTrig.bs (fun j => qmul (qadd (b j) (b j)) (hp j)) (r + 1))
            (qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (hp (r + 1))))
          (qadd (ZTrig.bs (fun j => qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
              (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))) (r + 1))
            (qadd (qmul (qadd KR KR) (qmul μ (qpowN h (2 * (r + 1))))) (qmul (qadd (qeps k) (qeps k)) h)))) := by
  intro k
  obtain ⟨hh0, hin⟩ := cells_within cs qzero h hch hok
  -- the cells
  obtain ⟨Nc, hNc⟩ := ev_list _ cs (fun c hc => by
    obtain ⟨c0', cas, csb, _⟩ := hok c hc
    obtain ⟨_, cb⟩ := hin c hc
    exact cell_taylor hS hV hL hB (qle_trans c0' cas) (qle_trans csb cb) k)
  -- the coefficients
  obtain ⟨Nk, hNk⟩ := ZTrig.fin_N (P := fun j n => j < r + 1 →
      qle (qsub (a j) (qeps k)) (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) ∧
      qle (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) (qadd (b j) (qeps k)))
    (fun j => by
      cases Nat.lt_or_ge j (r + 1) with
      | inl hj => obtain ⟨N, hN⟩ := hc j hj k; exact ⟨N, fun n hn _ => hN n hn⟩
      | inr hj => exact ⟨0, fun _ _ h => absurd h (Nat.not_lt_of_ge hj)⟩) (r + 1)
  refine ⟨Nc + Nk, fun n hn => ?_⟩
  have cellb := hNc n (ZTrig.le_l' hn)
  have coefb := hNk n (ZTrig.le_r' hn)
  -- (1) the sum: polynomial parts and remainders
  have s1 := csum_congr (g := fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
    (g' := fun c => qadd (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
        (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1))
      (qsub (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
        (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
          (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1)))) cs (fun c _ => by dsimp only; unfold qsub; rat_ring)
  have s2 := csum_add (fun c => ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
        (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1))
    (fun c => qsub (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
        (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
          (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1))) cs
  -- (2) the polynomial parts: Σ_j (C_j + C_j)·Q_j
  have s3 := csum_bs_swap (fun c j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
        (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1) cs
  have s4 := ZTrig.bs_congr (F := fun j => csum (fun c => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
        (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) cs)
    (G := fun j => qmul (qadd (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))))
      (csum (fun c => qpowN c.2.2 (2 * j)) cs))
    (fun j => by
      have c1 := csum_congr (g := fun c => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
          (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j))))
        (g' := fun c => qmul (qadd (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))))
          (qpowN c.2.2 (2 * j))) cs (fun c _ => by dsimp only; rat_ring)
      exact qEq_trans c1 (csum_scale _ (fun c => qpowN c.2.2 (2 * j)) cs)) (r + 1)
  -- (3) each j
  have pj : ∀ j, j < r + 1 →
      qle (qsub (qmul (qadd (a j) (a j)) (hp j)) (qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
          (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))))
        (qmul (qadd (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))))
          (csum (fun c => qpowN c.2.2 (2 * j)) cs)) ∧
      qle (qmul (qadd (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))))
          (csum (fun c => qpowN c.2.2 (2 * j)) cs))
        (qadd (qmul (qadd (b j) (b j)) (hp j)) (qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
          (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j))))))) := fun j hj => by
    obtain ⟨c1, c2⟩ := coefb j hj hj
    have q := qsum_hp (2 * j) hch hok (hhp j (Nat.le_of_lt hj)) hμ
    have q0 := csum_nonneg (g := fun c => qpowN c.2.2 (2 * j)) cs (fun c hc => by
      obtain ⟨c0', cas, csb, _⟩ := hok c hc
      exact ⟨qle_trans cas csb, powN_nonneg (qle_trans c0' cas) (2 * j)⟩)
    obtain ⟨ba, bb⟩ := hab j hj
    exact prod_bound c1 c2 q q0 ba bb (qeps_nonneg k)
  obtain ⟨L1, U1⟩ := ZTrig.bs_lohi (r + 1) pj
  have bsl := ZTrig.bs_sub (fun j => qmul (qadd (a j) (a j)) (hp j))
    (fun j => qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j)))) (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))) (r + 1)
  have bsu := ZTrig.bs_add (fun j => qmul (qadd (b j) (b j)) (hp j))
    (fun j => qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j)))) (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))) (r + 1)
  -- (4) the remainders
  have rl := csum_mono (g := fun c => qsub (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) L)
      (qadd (qeps k) (qeps k)))
    (g' := fun c => qsub (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
        (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
          (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1))) cs
    (fun c hc => ⟨qle_trans (hok c hc).2.1 (hok c hc).2.2.1, (cellb c hc).1⟩)
  have ru := csum_mono (g := fun c => qsub (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
        (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
          (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1)))
    (g' := fun c => qadd (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) U)
      (qadd (qeps k) (qeps k))) cs
    (fun c hc => ⟨qle_trans (hok c hc).2.1 (hok c hc).2.2.1, (cellb c hc).2⟩)
  have W := width_chain cs qzero h hch
  have Wh : qEq (csum (fun _ => qone) cs) h := qEq_trans W (by unfold qsub; rat_ring)
  have rl2 : qEq (csum (fun c => qsub (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) L)
      (qadd (qeps k) (qeps k))) cs)
      (qadd (qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (csum (fun c => qpowN c.2.2 (2 * (r + 1))) cs))
        (qmul (qneg (qadd (qeps k) (qeps k))) (csum (fun _ => qone) cs))) := by
    have a1 := csum_congr (g := fun c => qsub (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) L)
        (qadd (qeps k) (qeps k)))
      (g' := fun c => qadd (qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (qpowN c.2.2 (2 * (r + 1))))
        (qmul (qneg (qadd (qeps k) (qeps k))) qone)) cs (fun c _ => by dsimp only; unfold qsub; rat_ring)
    have a2 := csum_add (fun c => qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (qpowN c.2.2 (2 * (r + 1))))
      (fun _ => qmul (qneg (qadd (qeps k) (qeps k))) qone) cs
    exact qEq_trans a1 (qEq_trans a2 (qadd_respects (csum_scale _ _ cs) (csum_scale _ _ cs)))
  have ru2 : qEq (csum (fun c => qadd (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) U)
      (qadd (qeps k) (qeps k))) cs)
      (qadd (qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (csum (fun c => qpowN c.2.2 (2 * (r + 1))) cs))
        (qmul (qadd (qeps k) (qeps k)) (csum (fun _ => qone) cs))) := by
    have a1 := csum_congr (g := fun c => qadd (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) U)
        (qadd (qeps k) (qeps k)))
      (g' := fun c => qadd (qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (qpowN c.2.2 (2 * (r + 1))))
        (qmul (qadd (qeps k) (qeps k)) qone)) cs (fun c _ => by dsimp only; rat_ring)
    have a2 := csum_add (fun c => qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (qpowN c.2.2 (2 * (r + 1))))
      (fun _ => qmul (qadd (qeps k) (qeps k)) qone) cs
    exact qEq_trans a1 (qEq_trans a2 (qadd_respects (csum_scale _ _ cs) (csum_scale _ _ cs)))
  have ew1 := qmul_respects (qEq_refl (qneg (qadd (qeps k) (qeps k)))) Wh
  have ew2 := qmul_respects (qEq_refl (qadd (qeps k) (qeps k))) Wh
  have qn := qsum_hp (2 * (r + 1)) hch hok (hhp (r + 1) (Nat.le_refl _)) hμ
  have hRL2 : ZTrig.Ab (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (qadd KR KR) := by
    obtain ⟨x1, x2⟩ := hRL; exact ⟨by rat_linarith, by rat_linarith⟩
  have hRU2 : ZTrig.Ab (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (qadd KR KR) := by
    obtain ⟨x1, x2⟩ := hRU; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨m1, m2⟩ := ZTrig.mul_abs hRL2 qn
  obtain ⟨m3, m4⟩ := ZTrig.mul_abs hRU2 qn
  have dl : qEq (qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (qsub (csum (fun c => qpowN c.2.2 (2 * (r + 1))) cs) (hp (r + 1))))
      (qsub (qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (csum (fun c => qpowN c.2.2 (2 * (r + 1))) cs))
        (qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (hp (r + 1)))) := by unfold qsub; rat_ring
  have du : qEq (qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (qsub (csum (fun c => qpowN c.2.2 (2 * (r + 1))) cs) (hp (r + 1))))
      (qsub (qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (csum (fun c => qpowN c.2.2 (2 * (r + 1))) cs))
        (qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (hp (r + 1)))) := by unfold qsub; rat_ring
  have ew3 : qEq (qmul (qneg (qadd (qeps k) (qeps k))) h) (qneg (qmul (qadd (qeps k) (qeps k)) h)) := by rat_ring
  -- (5) everything
  show qle _ (csum (fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs) ∧
    qle (csum (fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs) _
  generalize csum (fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs = SS at *
  generalize csum (fun c => qadd (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
        (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1))
      (qsub (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
        (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
          (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1)))) cs = SS' at *
  generalize csum (fun c => ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
        (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1)) cs = TT at *
  generalize csum (fun c => qsub (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
        (ZTrig.bs (fun j => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
          (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) (r + 1))) cs = RR at *
  generalize ZTrig.bs (fun j => csum (fun c => qmul (qadd (evalN n (upd p i m) (Diter i (2 * j) e)) (evalN n (upd p i m) (Diter i (2 * j) e)))
        (qmul (qpowN c.2.2 (2 * j)) (cf (2 * j)))) cs) (r + 1) = TT2 at *
  generalize ZTrig.bs (fun j => qmul (qadd (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))) (qmul (evalN n (upd p i m) (Diter i (2 * j) e)) (cf (2 * j))))
      (csum (fun c => qpowN c.2.2 (2 * j)) cs)) (r + 1) = TT3 at *
  generalize ZTrig.bs (fun j => qsub (qmul (qadd (a j) (a j)) (hp j)) (qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
          (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j))))))) (r + 1) = LJ at *
  generalize ZTrig.bs (fun j => qadd (qmul (qadd (b j) (b j)) (hp j)) (qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
          (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j))))))) (r + 1) = UJ at *
  generalize ZTrig.bs (fun j => qmul (qadd (a j) (a j)) (hp j)) (r + 1) = AJ at *
  generalize ZTrig.bs (fun j => qmul (qadd (b j) (b j)) (hp j)) (r + 1) = BJ at *
  generalize ZTrig.bs (fun j => qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
              (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))) (r + 1) = EJ at *
  generalize csum (fun c => qsub (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) L)
      (qadd (qeps k) (qeps k))) cs = RL at *
  generalize csum (fun c => qadd (qmul (qadd (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1)))) (qmul (qpowN c.2.2 (2 * (r + 1))) (cf (2 * (r + 1))))) U)
      (qadd (qeps k) (qeps k))) cs = RU at *
  generalize csum (fun c => qpowN c.2.2 (2 * (r + 1))) cs = Qn at *
  generalize csum (fun (_ : Cell) => qone) cs = Wd at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) Qn = PL at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) Qn = PU at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (hp (r + 1)) = HL at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (hp (r + 1)) = HU at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) L) (qmul (cf (2 * (r + 1))) L)) (qsub Qn (hp (r + 1))) = DL at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) U) (qmul (cf (2 * (r + 1))) U)) (qsub Qn (hp (r + 1))) = DU at *
  generalize qmul (qadd KR KR) (qmul μ (qpowN h (2 * (r + 1)))) = KM at *
  generalize qmul (qneg (qadd (qeps k) (qeps k))) Wd = EW1 at *
  generalize qmul (qadd (qeps k) (qeps k)) Wd = EW2 at *
  generalize qmul (qneg (qadd (qeps k) (qeps k))) h = EH1 at *
  generalize qmul (qadd (qeps k) (qeps k)) h = EH2 at *
  clear hNc hNk cellb coefb pj hc hab hhp hS hV hL hB hok hin
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩


end ZTaylorLeaf

#print axioms ZTaylorLeaf.powN_neg
#print axioms ZTaylorLeaf.bs_pairs
#print axioms ZTaylorLeaf.cell_pow
#print axioms ZTaylorLeaf.psum_cells
#print axioms ZTaylorLeaf.tsym
#print axioms ZTaylorLeaf.cell_taylor
#print axioms ZTaylorLeaf.csum_bs_swap
#print axioms ZTaylorLeaf.qsum_hp
#print axioms ZTaylorLeaf.prod_bound
#print axioms ZTaylorLeaf.taylorN_leaf
