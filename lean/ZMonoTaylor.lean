import ZPowTaylor

/-!
# ZMonoTaylor — a derivative of one sign makes the function monotone, from Taylor's bound alone. Zero axioms.

`zseries.interval` narrows f over [a, b] to the brackets at the ends when the derivative's reading over [a, b] has one
sign ("monotone — the ends bound it"). Classically the mean value theorem; here no calculus: only the Taylor bound of
`ZPowTaylor` (f(y) − f(x) − g(x)(y − x) ≥ −Q·(y − x)², g the derivative series) and g ≥ m > 0 on [a, b].

  `step_up`      x ≤ y in [a, b], Q·(y − x) ≤ m        ⇒ f(x) ≤ f(y)
  `chain_up`     equal steps h, n·h = x − a, Q·h ≤ m    ⇒ f(a) ≤ f(a + n·h)
  `exists_step`  for every x ≥ a there are n, h with n·h = x − a, h ≥ 0, Q·h ≤ m (Archimedes, m > 0)
  `mono_up`      ⇒ f(a) ≤ f(x) for every x in [a, b]  — and the same for f(x) ≤ f(b) (`mono_up_right`)
over VR's pre-rationals, for ANY f, g with those two properties (the series' partial sums have them by `taylor_sum`).
-/

namespace ZMonoTaylor
open VR VR.Numbers ZExp

variable (f g : QExpr → QExpr) (Q m a b : QExpr)

/-- f's Taylor bound on [a, b], from below. -/
def TaylorLow : Prop := ∀ x y, qle a x → qle x b → qle a y → qle y b →
  qle (qneg (qmul Q (qmul (qsub y x) (qsub y x)))) (qsub (qsub (f y) (f x)) (qmul (g x) (qsub y x)))

/-- The derivative's floor on [a, b]. -/
def DerivFloor : Prop := ∀ x, qle a x → qle x b → qle m (g x)

theorem step_up (hT : TaylorLow f g Q a b) (hD : DerivFloor g m a b) (hQ : qle qzero Q) {x y : QExpr}
    (hax : qle a x) (hxb : qle x b) (hay : qle a y) (hyb : qle y b) (hxy : qle x y)
    (hs : qle (qmul Q (qsub y x)) m) : qle (f x) (f y) := by
  have hd : qle qzero (qsub y x) := by unfold qsub; rat_linarith
  have h1 := hT x y hax hxb hay hyb
  have hg := hD x hax hxb
  -- (y − x)·g(x) ≥ (y − x)·m ≥ (y − x)·Q·(y − x)
  have h2 : qle (qmul (qsub y x) m) (qmul (qsub y x) (g x)) := scale_l hg hd
  have h3 : qle (qmul (qsub y x) (qmul Q (qsub y x))) (qmul (qsub y x) m) := scale_l hs hd
  have e1 : qEq (qmul (g x) (qsub y x)) (qmul (qsub y x) (g x)) := qmul_comm _ _
  have e2 : qEq (qmul Q (qmul (qsub y x) (qsub y x))) (qmul (qsub y x) (qmul Q (qsub y x))) := by q_ring
  unfold qsub at *
  rat_linarith

theorem chain_up (hT : TaylorLow f g Q a b) (hD : DerivFloor g m a b) (hQ : qle qzero Q) (h : QExpr)
    (hh : qle qzero h) (hQh : qle (qmul Q h) m) (hab : qle a b) :
    ∀ n, qle (qadd a (qmul (qnat n) h)) b → qle (f (qadd a (qmul (qnat 0) h))) (f (qadd a (qmul (qnat n) h)))
  | 0, _ => qle_refl _
  | n + 1, hb => by
      have hstep : qEq (qadd a (qmul (qnat (n + 1)) h)) (qadd (qadd a (qmul (qnat n) h)) h) := by
        refine qEq_trans (qadd_respects (qEq_refl _) (qmul_respects (qnat_succ n) (qEq_refl _))) ?_; q_ring
      have hnn : qle (qadd a (qmul (qnat n) h)) (qadd a (qmul (qnat (n + 1)) h)) := by
        refine qle_respects (qEq_refl _) (qEq_symm hstep) ?_
        rat_linarith
      have hb' : qle (qadd a (qmul (qnat n) h)) b := qle_trans hnn hb
      have ih := chain_up hT hD hQ h hh hQh hab n hb'
      have han : qle a (qadd a (qmul (qnat n) h)) := by
        have := qmul_nonneg (qnat_nonneg n) hh; rat_linarith
      have han1 : qle a (qadd a (qmul (qnat (n + 1)) h)) := qle_trans han hnn
      have hs : qle (qmul Q (qsub (qadd a (qmul (qnat (n + 1)) h)) (qadd a (qmul (qnat n) h)))) m := by
        have e : qEq (qsub (qadd a (qmul (qnat (n + 1)) h)) (qadd a (qmul (qnat n) h))) h := by
          refine qEq_trans (qadd_respects hstep (qEq_refl _)) ?_; q_ring
        exact qle_respects (qmul_respects (qEq_refl _) (qEq_symm e)) (qEq_refl _) hQh
      exact qle_trans ih (step_up f g Q m a b hT hD hQ han hb' han1 hb hnn hs)

/-- Archimedes: equal steps small enough. -/
theorem exists_step {x : QExpr} (hax : qle a x) (hQ : qle qzero Q) (hm : qlt qzero m) :
    ∃ n h, qEq (qmul (qnat n) h) (qsub x a) ∧ qle qzero h ∧ qle (qmul Q h) m := by
  obtain ⟨K, hK⟩ := exists_nat_bound (qmul (qmul (qsub x a) Q) (qinv' m))
  have hm0 : ¬ qEq m qzero := fun e => qlt_irrefl _ (qlt_respects (qEq_refl _) e hm)
  have hmi := qmul_inv'_cancel hm0                       -- m · m⁻¹ = 1
  have hn0 := qnat_ne_zero K
  have hni := qmul_inv'_cancel hn0                       -- n · n⁻¹ = 1
  have hinv_n : qle qzero (qinv' (qnat (K + 1))) := qinv'_nonneg_of_pos (qnat_succ_pos K)
  have hd : qle qzero (qsub x a) := by unfold qsub; rat_linarith
  refine ⟨K + 1, qmul (qsub x a) (qinv' (qnat (K + 1))), ?_, qmul_nonneg hd hinv_n, ?_⟩
  · refine qEq_trans (by q_ring : qEq (qmul (qnat (K + 1)) (qmul (qsub x a) (qinv' (qnat (K + 1)))))
        (qmul (qsub x a) (qmul (qnat (K + 1)) (qinv' (qnat (K + 1)))))) ?_
    refine qEq_trans (qmul_respects (qEq_refl _) hni) ?_; q_ring
  · -- (x − a)·Q ≤ K·m
    have hb : qle (qmul (qmul (qsub x a) Q) (qinv' m)) (qnat K) := by obtain ⟨u1, u2⟩ := hK; unfold qsub at u1 ⊢; rat_linarith
    have h1 : qle (qmul (qmul (qmul (qsub x a) Q) (qinv' m)) m) (qmul (qnat K) m) := scale hb (qle_of_qlt hm)
    have e1 : qEq (qmul (qmul (qmul (qsub x a) Q) (qinv' m)) m) (qmul (qsub x a) Q) := by
      refine qEq_trans (by q_ring : qEq (qmul (qmul (qmul (qsub x a) Q) (qinv' m)) m)
        (qmul (qmul (qsub x a) Q) (qmul m (qinv' m)))) ?_
      refine qEq_trans (qmul_respects (qEq_refl _) hmi) ?_; q_ring
    have h2 : qle (qmul (qsub x a) Q) (qmul (qnat K) m) := qle_respects e1 (qEq_refl _) h1
    -- ·n⁻¹
    have h3 := scale h2 hinv_n
    -- K·m·n⁻¹ ≤ m: K ≤ n, so K·n⁻¹ ≤ n·n⁻¹ = 1
    have hKn : qle (qmul (qnat K) (qinv' (qnat (K + 1)))) qone := by
      have := scale (qnat_mono (Nat.le_succ K)) hinv_n
      exact qle_respects (qEq_refl _) hni this
    have h4 : qle (qmul m (qmul (qnat K) (qinv' (qnat (K + 1))))) (qmul m qone) := scale_l hKn (qle_of_qlt hm)
    have e2 : qEq (qmul (qmul (qnat K) m) (qinv' (qnat (K + 1)))) (qmul m (qmul (qnat K) (qinv' (qnat (K + 1))))) := by q_ring
    have e3 : qEq (qmul (qmul (qsub x a) Q) (qinv' (qnat (K + 1)))) (qmul Q (qmul (qsub x a) (qinv' (qnat (K + 1))))) := by q_ring
    exact qle_respects e3 (qmul_one m) (qle_trans h3 (qle_respects (qEq_symm e2) (qEq_refl _) h4))

/-- **MONOTONE**: g ≥ m > 0 on [a, b] and f's Taylor bound there ⇒ f(a) ≤ f(x) for every x in [a, b]. -/
theorem mono_up (hf : ∀ u v, qEq u v → qEq (f u) (f v)) (hT : TaylorLow f g Q a b) (hD : DerivFloor g m a b)
    (hQ : qle qzero Q) (hm : qlt qzero m) {x : QExpr} (hax : qle a x) (hxb : qle x b) : qle (f a) (f x) := by
  obtain ⟨n, h, hnh, hh, hQh⟩ := exists_step Q m a hax hQ hm
  have hab : qle a b := qle_trans hax hxb
  have ex : qEq (qadd a (qmul (qnat n) h)) x := by
    refine qEq_trans (qadd_respects (qEq_refl _) hnh) ?_; unfold qsub; q_ring
  have e0 : qEq (qadd a (qmul (qnat 0) h)) a := by
    refine qEq_trans (qadd_respects (qEq_refl _) (qmul_respects qnat_zero (qEq_refl _))) ?_; q_ring
  have hc := chain_up f g Q m a b hT hD hQ h hh hQh hab n (qle_respects (qEq_symm ex) (qEq_refl _) hxb)
  exact qle_respects (hf _ _ e0) (hf _ _ ex) hc

/-- …and f(x) ≤ f(b): the same on [x, b] (the hypotheses restrict). Together: f([a, b]) ⊂ [f(a), f(b)]. -/
theorem mono_up_right (hf : ∀ u v, qEq u v → qEq (f u) (f v)) (hT : TaylorLow f g Q a b) (hD : DerivFloor g m a b)
    (hQ : qle qzero Q) (hm : qlt qzero m) {x : QExpr} (hax : qle a x) (hxb : qle x b) : qle (f x) (f b) := by
  have hT' : TaylorLow f g Q x b := fun u v hu hub hv hvb =>
    hT u v (qle_trans hax hu) hub (qle_trans hax hv) hvb
  have hD' : DerivFloor g m x b := fun u hu hub => hD u (qle_trans hax hu) hub
  exact mono_up f g Q m x b hf hT' hD' hQ hm hxb (qle_refl b)

end ZMonoTaylor

#print axioms ZMonoTaylor.step_up
#print axioms ZMonoTaylor.chain_up
#print axioms ZMonoTaylor.exists_step
#print axioms ZMonoTaylor.mono_up
#print axioms ZMonoTaylor.mono_up_right
