import ZJetClose

/-!
# ZTaylorPt — a value at a point from the Taylor coefficients at another. Zero axioms.

From a coefficient reading over a box (`CRead`, the kernel's own Taylor series of `e` on `[p, q]` along `x_i`) and
readings of the coefficients `J_t(p)` at `p` for `t < m`: the value at `q` lies in
`Σ_{t<m} J_t(p)·d^t + c_m·d^m`, `d = q_i − p_i`, every product read by corners (any sign of `d`). The remainder is
`ZTaylorN.taylor_rem` — its hypotheses (every iterate step-readable and bounded on the box) come from the reading
itself (`ZJetClose.cread_good`). This is how a value with no closed reading is certified: `atan` at a rational point
(`ZAtanCert`), a chain of such steps from `atan 0 = 0`.
-/

namespace ZTaylorPt

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZJet ZJetRead ZJetClose

/-- `x·m!·(1/m!) = x`. -/
theorem fact_cancel (m : Nat) (x : QExpr) : qEq (qmul (qmul x (qnat (fact m))) (cf m)) x := by
  have c := cf_fact m x
  exact qEq_trans (by rat_ring) c

/-- Multiplying an interval by a constant `f ≥ 0`. -/
theorem corners_const {a b f : QExpr} (hab : qle a b) (hf : qle qzero f) :
    Corners (qmul a f) (qmul b f) a b f f := by
  have s := ZExp.scale hab hf
  exact ⟨⟨qle_refl _, qle_refl _, s, s⟩, ⟨s, s, qle_refl _, qle_refl _⟩⟩

/-- The sum of read terms is read in the sum of their intervals. -/
theorem Ev_bs {F : Nat → Nat → QExpr} {T : Nat → QExpr × QExpr} :
    ∀ m, (∀ t, t < m → Ev (fun n => F n t) (T t).1 (T t).2) →
      Ev (fun n => ZTrig.bs (F n) m) (ZTrig.bs (fun t => (T t).1) m) (ZTrig.bs (fun t => (T t).2) m)
  | 0, _ => Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
  | m + 1, h => Ev_add (Ev_bs m (fun t ht => h t (Nat.lt_succ_of_lt ht))) (h m (Nat.lt_succ_self m))

/-- THE VALUE AT `q` FROM THE COEFFICIENTS AT `p`. -/
theorem taylor_value {B : Box QExpr} {i m : Nat} {e : G} {cB : Nat → QExpr × QExpr} (rB : CRead B i m e cB)
    {p q : Point QExpr} (hp : InBox qOrd B p) (hq : InBox qOrd B q) (hfix : ∀ j, j ≠ i → q j = p j)
    {P T : Nat → QExpr × QExpr} {Rl Rh : QExpr}
    (hP : ∀ t, t < m → Ev (fun n => J i n p e t) (P t).1 (P t).2)
    (hT : ∀ t, t < m → Corners (T t).1 (T t).2 (P t).1 (P t).2 (qpowN (qsub (q i) (p i)) t) (qpowN (qsub (q i) (p i)) t))
    (hR : Corners Rl Rh (cB m).1 (cB m).2 (qpowN (qsub (q i) (p i)) m) (qpowN (qsub (q i) (p i)) m)) :
    Ev (fun n => evalN n q e) (qadd (ZTrig.bs (fun t => (T t).1) m) Rl) (qadd (ZTrig.bs (fun t => (T t).2) m) Rh) := by
  obtain ⟨bd, st⟩ := cread_good rB
  generalize hd : qsub (q i) (p i) = d at *
  -- the m-th iterate on the box, from the reading's m-th coefficient
  have fm : qle qzero (qnat (fact m)) := qle_of_qlt (fact_pos m)
  have bm : BoxEv B (Diter i m e) (qmul (cB m).1 (qnat (fact m))) (qmul (cB m).2 (qnat (fact m))) := fun p' hp' => by
    have ej := cread_sound hp' rB m (Nat.le_refl m)
    have o := ev_order ej
    have em := Ev_mul ej (Ev_const (qnat (fact m))) (corners_const o fm)
    refine Ev_congr (fun n => ?_) em
    show qEq (qmul (qmul (evalN n p' (Diter i m e)) (cf m)) (qnat (fact m))) (evalN n p' (Diter i m e))
    have c := cf_fact m (evalN n p' (Diter i m e))
    exact qEq_trans (by rat_ring) c
  have tr := taylor_rem m e (fun t _ => st t) (fun t _ => bd (t + 1)) bm p q hp hq hfix
  rw [hd] at tr
  -- the remainder in [Rl, Rh]
  have eR : Ev (fun n => qsub (evalN n q e) (tpoly i n p e d m)) Rl Rh := fun k => by
    obtain ⟨N, hN⟩ := tr k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s1, s2⟩ := hN n hn
    obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hR
    have w1 : qEq (qmul (qmul (qpowN d m) (cf m)) (qmul (cB m).1 (qnat (fact m)))) (qmul (cB m).1 (qpowN d m)) := by
      have c := cf_fact m (cB m).1
      have r : qEq (qmul (qmul (qpowN d m) (cf m)) (qmul (cB m).1 (qnat (fact m))))
          (qmul (qpowN d m) (qmul (cf m) (qmul (cB m).1 (qnat (fact m))))) := by rat_ring
      exact qEq_trans r (qEq_trans (qmul_respects (qEq_refl _) c) (by rat_ring))
    have w2 : qEq (qmul (qmul (qpowN d m) (cf m)) (qmul (cB m).2 (qnat (fact m)))) (qmul (cB m).2 (qpowN d m)) := by
      have c := cf_fact m (cB m).2
      have r : qEq (qmul (qmul (qpowN d m) (cf m)) (qmul (cB m).2 (qnat (fact m))))
          (qmul (qpowN d m) (qmul (cf m) (qmul (cB m).2 (qnat (fact m))))) := by rat_ring
      exact qEq_trans r (qEq_trans (qmul_respects (qEq_refl _) c) (by rat_ring))
    show qle (qsub Rl (qeps k)) (qsub (evalN n q e) (tpoly i n p e d m)) ∧
      qle (qsub (evalN n q e) (tpoly i n p e d m)) (qadd Rh (qeps k))
    generalize qsub (evalN n q e) (tpoly i n p e d m) = R at *
    generalize qmul (qmul (qpowN d m) (cf m)) (qmul (cB m).1 (qnat (fact m))) = A1 at *
    generalize qmul (qmul (qpowN d m) (cf m)) (qmul (cB m).2 (qnat (fact m))) = A2 at *
    cases qle_total qzero (qmul (qpowN d m) (cf m)) with
    | inl hw => obtain ⟨a, b⟩ := s1 hw; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
    | inr hw => obtain ⟨a, b⟩ := s2 hw; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  -- the polynomial in the sum of the terms' intervals
  have eT := Ev_bs (F := fun n t => qmul (J i n p e t) (qpowN d t)) (T := T) m
    (fun t ht => Ev_mul (hP t ht) (Ev_const _) (hT t ht))
  have eP : Ev (fun n => tpoly i n p e d m) (ZTrig.bs (fun t => (T t).1) m) (ZTrig.bs (fun t => (T t).2) m) :=
    Ev_congr (fun n => ZTrig.bs_congr (fun t => by
      show qEq (qmul (qmul (evalN n p (Diter i t e)) (cf t)) (qpowN d t))
        (qmul (evalN n p (Diter i t e)) (qmul (qpowN d t) (cf t)))
      rat_ring) m) eT
  refine Ev_congr (fun n => ?_) (Ev_add eP eR)
  unfold qsub; rat_ring

end ZTaylorPt

#print axioms ZTaylorPt.Ev_bs
#print axioms ZTaylorPt.taylor_value
