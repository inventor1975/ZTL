import ZTaylorN
import ZIntegralR

/-!
# ZMonoStep — the monotone leaf from the symbolic derivative's sign. Zero axioms.

`zintegral`'s monotone leaf reads the sign of `df/dx` over the piece. `ZIntegralR.monotone_leaf_up/down` take a slope
reading (`DRead`); the kernel reads its symbolic derivative fully (affine forms, ...), which no `DRead` mirrors. Here
the other road: a step reading of `f` (`StepRead`) and a box bound of the grammar's own derivative `D f` — read by the
naive `VRead` or the affine `AffR`, whichever the run proves — give the slope by `ZTaylorN.taylor_rem` at order 1
(no mean value theorem), and the slope gives the leaf.
-/

namespace ZMonoStep

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZIntegralR

/-- THE SLOPE FROM THE STEP: `f(t) − f(s)` is eventually in `(t − s)·[L, U]`, `[L, U]` a box bound of `D f`. -/
theorem slope_step {B : Box QExpr} {i : Nat} {e : G} {L U : QExpr} (hS : StepRead B i e) (hV : BoxEv B (D i e) L U)
    {p : Point QExpr} {s t : QExpr} (hs : InBox qOrd B (upd p i s)) (ht : InBox qOrd B (upd p i t)) (hst : qle s t) :
    Ev (fun n => qsub (evalN n (upd p i t) e) (evalN n (upd p i s) e)) (qmul L (qsub t s)) (qmul U (qsub t s)) := by
  intro k
  obtain ⟨N, hN⟩ := taylor_rem (B := B) (i := i) 1 e (fun t' ht' => by
      have : t' = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ ht'); subst this; exact hS)
    (fun t' ht' => by have : t' = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ ht'); subst this; exact ⟨L, U, hV⟩)
    hV (upd p i s) (upd p i t) hs ht (upd_fix p i s t) k
  refine ⟨N, fun n hn => ?_⟩
  have sd := hN n hn
  rw [upd_self, upd_self] at sd
  have c0 := cf_zero
  have c1 : qEq (cf 1) qone := by
    have := cf_succ 0
    have q1 : qEq (qnat (0 + 1)) qone := qEq_trans (qnat_succ 0) (qEq_trans (qadd_respects qnat_zero (qEq_refl _)) (by rat_ring))
    have e1 := qmul_respects q1 (qEq_refl (cf 1))
    exact qEq_trans (qEq_trans (by rat_ring) (qEq_symm e1)) (qEq_trans this c0)
  have hw : qle qzero (qmul (qpowN (qsub t s) 1) (cf 1)) := by
    have e : qEq (qmul (qpowN (qsub t s) 1) (cf 1)) (qmul (qmul qone (qsub t s)) (cf 1)) := qEq_refl _
    have e2 := qmul_respects (qEq_refl (qmul qone (qsub t s))) c1
    have d : qle qzero (qsub t s) := by unfold qsub; rat_linarith
    have e3 : qEq (qmul (qmul qone (qsub t s)) qone) (qsub t s) := by rat_ring
    rat_linarith
  obtain ⟨l1, l2⟩ := sd.1 hw
  have tp : qEq (tpoly i n (upd p i s) e (qsub t s) 1) (evalN n (upd p i s) e) := by
    show qEq (qadd qzero (qmul (evalN n (upd p i s) (Diter i 0 e)) (qmul qone (cf 0)))) _
    have := qmul_respects (qEq_refl (evalN n (upd p i s) e)) (qmul_respects (qEq_refl qone) c0)
    exact qEq_trans (qadd_respects (qEq_refl _) this) (by show qEq (qadd qzero (qmul (evalN n (upd p i s) e) (qmul qone qone))) _; rat_ring)
  have w1 : qEq (qmul (qpowN (qsub t s) 1) (cf 1)) (qsub t s) := by
    have e2 := qmul_respects (qEq_refl (qmul qone (qsub t s))) c1
    exact qEq_trans e2 (by rat_ring)
  have wL := qmul_respects w1 (qEq_refl L)
  have wU := qmul_respects w1 (qEq_refl U)
  show qle (qsub (qmul L (qsub t s)) (qeps k)) (qsub (evalN n (upd p i t) e) (evalN n (upd p i s) e)) ∧
    qle (qsub (evalN n (upd p i t) e) (evalN n (upd p i s) e)) (qadd (qmul U (qsub t s)) (qeps k))
  have cL : qEq (qmul (qsub t s) L) (qmul L (qsub t s)) := by rat_ring
  have cU : qEq (qmul (qsub t s) U) (qmul U (qsub t s)) := by rat_ring
  generalize tpoly i n (upd p i s) e (qsub t s) 1 = T at *
  generalize qmul (qpowN (qsub t s) 1) (cf 1) = W at *
  generalize qmul W L = WL at *
  generalize qmul W U = WU at *
  generalize qmul (qsub t s) L = TL at *
  generalize qmul (qsub t s) U = TU at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- A MONOTONE LEAF, RISING, from the step: `D f ≥ 0` over a box holding the piece. -/
theorem monotone_leaf_up_step {e : G} {p : Point QExpr} {i : Nat} {a b lo hi la hb' L U : QExpr} {B : Box QExpr}
    (hS : StepRead B i e) (hV : BoxEv B (D i e) L U) (hl : qle qzero L)
    (hB : ∀ t, qle a t → qle t b → InBox qOrd B (upd p i t))
    (hab : qle a b) (ea : Ev (fun n => evalN n (upd p i a) e) lo la) (eb : Ev (fun n => evalN n (upd p i b) e) hb' hi) :
    LeafEv e p i a b lo hi := by
  intro t hat htb k
  obtain ⟨N1, h1⟩ := slope_step hS hV (hB a (qle_refl a) hab) (hB t hat htb) hat (k + 1)
  obtain ⟨N2, h2⟩ := slope_step hS hV (hB t hat htb) (hB b hab (qle_refl b)) htb (k + 1)
  obtain ⟨N3, h3⟩ := ea (k + 1)
  obtain ⟨N4, h4⟩ := eb (k + 1)
  refine ⟨N1 + N2 + N3 + N4, fun n hn => ?_⟩
  have g1 : qle (qsub (qmul L (qsub t a)) (qeps (k + 1))) (qsub (evalN n (upd p i t) e) (evalN n (upd p i a) e)) :=
    (h1 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).1
  have g2 : qle (qsub (qmul L (qsub b t)) (qeps (k + 1))) (qsub (evalN n (upd p i b) e) (evalN n (upd p i t) e)) :=
    (h2 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).1
  have g3 : qle (qsub lo (qeps (k + 1))) (evalN n (upd p i a) e) :=
    (h3 n (Nat.le_trans (Nat.le_trans (Nat.le_add_left N3 (N1 + N2)) (Nat.le_add_right _ N4)) hn)).1
  have g4 : qle (evalN n (upd p i b) e) (qadd hi (qeps (k + 1))) :=
    (h4 n (Nat.le_trans (Nat.le_add_left N4 (N1 + N2 + N3)) hn)).2
  have f1 : qle qzero (qmul L (qsub t a)) := qmul_nonneg hl (by unfold qsub; rat_linarith)
  have f2 : qle qzero (qmul L (qsub b t)) := qmul_nonneg hl (by unfold qsub; rat_linarith)
  have ee := qeps_succ_add k
  show qle (qsub lo (qeps k)) (evalN n (upd p i t) e) ∧ qle (evalN n (upd p i t) e) (qadd hi (qeps k))
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- A MONOTONE LEAF, FALLING, from the step: `D f ≤ 0`. -/
theorem monotone_leaf_down_step {e : G} {p : Point QExpr} {i : Nat} {a b lo hi la hb' L U : QExpr} {B : Box QExpr}
    (hS : StepRead B i e) (hV : BoxEv B (D i e) L U) (hh : qle U qzero)
    (hB : ∀ t, qle a t → qle t b → InBox qOrd B (upd p i t))
    (hab : qle a b) (ea : Ev (fun n => evalN n (upd p i a) e) la hi) (eb : Ev (fun n => evalN n (upd p i b) e) lo hb') :
    LeafEv e p i a b lo hi := by
  intro t hat htb k
  obtain ⟨N1, h1⟩ := slope_step hS hV (hB a (qle_refl a) hab) (hB t hat htb) hat (k + 1)
  obtain ⟨N2, h2⟩ := slope_step hS hV (hB t hat htb) (hB b hab (qle_refl b)) htb (k + 1)
  obtain ⟨N3, h3⟩ := ea (k + 1)
  obtain ⟨N4, h4⟩ := eb (k + 1)
  refine ⟨N1 + N2 + N3 + N4, fun n hn => ?_⟩
  have g1 : qle (qsub (evalN n (upd p i t) e) (evalN n (upd p i a) e)) (qadd (qmul U (qsub t a)) (qeps (k + 1))) :=
    (h1 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).2
  have g2 : qle (qsub (evalN n (upd p i b) e) (evalN n (upd p i t) e)) (qadd (qmul U (qsub b t)) (qeps (k + 1))) :=
    (h2 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).2
  have g3 : qle (evalN n (upd p i a) e) (qadd hi (qeps (k + 1))) :=
    (h3 n (Nat.le_trans (Nat.le_trans (Nat.le_add_left N3 (N1 + N2)) (Nat.le_add_right _ N4)) hn)).2
  have g4 : qle (qsub lo (qeps (k + 1))) (evalN n (upd p i b) e) :=
    (h4 n (Nat.le_trans (Nat.le_add_left N4 (N1 + N2 + N3)) hn)).1
  have f1 : qle (qmul U (qsub t a)) qzero := by
    have := qmul_nonneg (show qle qzero (qneg U) by rat_linarith) (show qle qzero (qsub t a) by unfold qsub; rat_linarith)
    have e : qEq (qmul (qneg U) (qsub t a)) (qneg (qmul U (qsub t a))) := by rat_ring
    rat_linarith
  have f2 : qle (qmul U (qsub b t)) qzero := by
    have := qmul_nonneg (show qle qzero (qneg U) by rat_linarith) (show qle qzero (qsub b t) by unfold qsub; rat_linarith)
    have e : qEq (qmul (qneg U) (qsub b t)) (qneg (qmul U (qsub b t))) := by rat_ring
    rat_linarith
  have ee := qeps_succ_add k
  show qle (qsub lo (qeps k)) (evalN n (upd p i t) e) ∧ qle (evalN n (upd p i t) e) (qadd hi (qeps k))
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZMonoStep

#print axioms ZMonoStep.slope_step
#print axioms ZMonoStep.monotone_leaf_up_step
#print axioms ZMonoStep.monotone_leaf_down_step
