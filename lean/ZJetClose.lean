import ZJetRead
import ZTaylorLeaf

/-!
# ZJetClose — the kernel's Taylor reading carries everything the remainder needs. Zero axioms.

`ZTaylorN.taylor_rem` needs, for every derivative below the order, a step reading (`StepRead`) and a box bound; the
leaf needs the coefficients. `ZJetRead.cread_sound` gives the coefficients. Here the rest: from a `CRead` of `e`, every
iterate `D^t e` is bounded on the box and step-readable — for every `t`. The derivatives create no new transcendental
nodes (`D(e^u) = e^u·Du`, `D(sin u) = cos u·Du`, `D(tan u) = (1 + tan²u)·Du`); the new quotients have the old
denominators squared, clear of zero when the old ones are; nodes without `x_i` have derivative `0`.
-/

namespace ZJetClose

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZJet ZJetRead ZIntegralT ZIntegralR

variable {B : Box QExpr} {i : Nat}

/-- Bounded on the box. -/
def Bd (B : Box QExpr) (e : G) : Prop := ∃ l h, BoxEv B e l h
/-- Bounded on the box, clear of zero. -/
def Cl (B : Box QExpr) (e : G) : Prop := ∃ l h r1 r2, BoxEv B e l h ∧ RecipOK r1 r2 l h
/-- Every iterate bounded. -/
def BdAll (B : Box QExpr) (i : Nat) (e : G) : Prop := ∀ t, Bd B (Diter i t e)
/-- Every iterate step-readable. -/
def StAll (B : Box QExpr) (i : Nat) (e : G) : Prop := ∀ t, StepRead B i (Diter i t e)

theorem strongAll (P : Nat → Prop) (h0 : P 0) (hs : ∀ t, (∀ s, s ≤ t → P s) → P (t + 1)) : ∀ t, P t := by
  have : ∀ t, ∀ s, s ≤ t → P s := by
    intro t
    induction t with
    | zero => intro s hsl; have : s = 0 := Nat.le_zero.mp hsl; subst this; exact h0
    | succ t ih =>
        intro s hsl
        cases Nat.lt_or_eq_of_le hsl with
        | inl l => exact ih s (Nat.le_of_lt_succ l)
        | inr e => subst e; exact hs t ih
  exact fun t => this t t (Nat.le_refl t)

/-! ## Bounds -/

theorem corners_exist (a1 a2 b1 b2 : QExpr) : ∃ l h, Corners l h a1 a2 b1 b2 := by
  obtain ⟨M, _, hM0, _, ma, mb, mc, md⟩ := bound4 a1 a2 b1 b2
  have ab : ∀ x, qclose x qzero M → ZTrig.Ab x M := fun x ⟨c1, c2⟩ => by
    unfold qsub at c1 c2; exact ⟨by rat_linarith, by rat_linarith⟩
  have p11 := ZTrig.mul_abs (ab _ ma) (ab _ mc)
  have p12 := ZTrig.mul_abs (ab _ ma) (ab _ md)
  have p21 := ZTrig.mul_abs (ab _ mb) (ab _ mc)
  have p22 := ZTrig.mul_abs (ab _ mb) (ab _ md)
  exact ⟨_, _, ⟨p11.1, p12.1, p21.1, p22.1⟩, ⟨p11.2, p12.2, p21.2, p22.2⟩⟩

theorem bd_const (c : QExpr) : Bd B (.const c) := ⟨c, c, fun _ _ => Ev_const c⟩
theorem bd_var (j : Nat) : Bd B (.var j) := ⟨(B j).1, (B j).2, fun _ hp => Ev_of_exact 0 (fun _ _ => hp j)⟩
theorem bd_add {u v : G} : Bd B u → Bd B v → Bd B (.add u v)
  | ⟨_, _, a⟩, ⟨_, _, b⟩ => ⟨_, _, fun p hp => Ev_add (a p hp) (b p hp)⟩
theorem bd_sub {u v : G} : Bd B u → Bd B v → Bd B (.sub u v)
  | ⟨_, _, a⟩, ⟨_, _, b⟩ => ⟨_, _, fun p hp => Ev_sub (a p hp) (b p hp)⟩
theorem bd_mul {u v : G} : Bd B u → Bd B v → Bd B (.mul u v)
  | ⟨l1, h1, a⟩, ⟨l2, h2, b⟩ =>
    let ⟨_, _, c⟩ := corners_exist l1 h1 l2 h2
    ⟨_, _, fun p hp => Ev_mul (a p hp) (b p hp) c⟩
theorem bd_div {u v : G} : Bd B u → Cl B v → Bd B (.div u v)
  | ⟨l1, h1, a⟩, ⟨_, _, r1, r2, b, hR⟩ =>
    let ⟨_, _, c⟩ := corners_exist l1 h1 r1 r2
    ⟨_, _, fun p hp => Ev_mul (a p hp) (Ev_recip (b p hp) hR) c⟩
theorem bd_powN {u : G} (hu : Bd B u) : ∀ k, Bd B (.powN u k)
  | 0 => ⟨qone, qone, fun _ _ => Ev_const qone⟩
  | k + 1 =>
    let ⟨_, _, a⟩ := bd_powN hu k
    let ⟨_, _, b⟩ := hu
    let ⟨_, _, c⟩ := corners_exist _ _ _ _
    ⟨_, _, fun p hp => (Ev_mul (a p hp) (b p hp) c : Ev (fun n => evalN n p (.powN u (k + 1))) _ _)⟩

theorem sq_pos {x : QExpr} (hx : ¬ qEq x qzero) : qlt qzero (qmul x x) :=
  qlt_iff_le_not_le.mpr ⟨qmul_self_nonneg x, fun h => nz_sq hx (qle_antisymm h (qmul_self_nonneg x))⟩

/-- `x ≥ 1 ⇒ x² ≥ 1`. -/
theorem one_le_sq {x : QExpr} (h : qle qone x) : qle qone (qmul x x) := by
  have s := qmul_self_nonneg (qsub x qone)
  unfold qsub at s; rat_linarith

/-- A denominator clear of zero: its square too. -/
theorem cl_sq {v : G} : Cl B v → Cl B (.mul v v)
  | ⟨l, h, r1, r2, b, hlh, Or.inl ⟨lp, _, hb⟩⟩ => by
      have l0 := qle_of_qlt lp
      have p1 := qmul_nonneg l0 (show qle qzero (qsub h l) by unfold qsub; rat_linarith)
      have p2 := qmul_nonneg (show qle qzero h by rat_linarith) (show qle qzero (qsub h l) by unfold qsub; rat_linarith)
      unfold qsub at p1 p2
      have c : Corners (qmul l l) (qmul h h) l h l h :=
        ⟨⟨qle_refl _, by rat_linarith, by rat_linarith, by rat_linarith⟩,
         ⟨by rat_linarith, by rat_linarith, by rat_linarith, qle_refl _⟩⟩
      have s := one_le_sq hb
      refine ⟨_, _, qzero, qmul r2 r2, fun p hp => Ev_mul (b p hp) (b p hp) c, by rat_linarith,
        Or.inl ⟨qmul_pos lp lp, by rat_linarith, ?_⟩⟩
      have e : qEq (qmul (qmul r2 l) (qmul r2 l)) (qmul (qmul r2 r2) (qmul l l)) := by rat_ring
      exact qle_trans s (qle_of_qEq e)
  | ⟨l, h, r1, r2, b, hlh, Or.inr ⟨hn, ha, _⟩⟩ => by
      have h0 : qle h qzero := qle_of_qlt hn
      have p1 := qmul_nonneg (show qle qzero (qneg h) by rat_linarith) (show qle qzero (qsub h l) by unfold qsub; rat_linarith)
      have p2 := qmul_nonneg (show qle qzero (qneg l) by rat_linarith) (show qle qzero (qsub h l) by unfold qsub; rat_linarith)
      unfold qsub at p1 p2
      have c : Corners (qmul h h) (qmul l l) l h l h :=
        ⟨⟨by rat_linarith, by rat_linarith, by rat_linarith, qle_refl _⟩,
         ⟨qle_refl _, by rat_linarith, by rat_linarith, by rat_linarith⟩⟩
      have hz : ¬ qEq h qzero := fun e => qlt_irrefl _ (qlt_respects e (qEq_refl _) hn)
      have s := one_le_sq ha
      refine ⟨_, _, qzero, qmul r1 r1, fun p hp => Ev_mul (b p hp) (b p hp) c, by rat_linarith,
        Or.inl ⟨sq_pos hz, by rat_linarith, ?_⟩⟩
      have e : qEq (qmul (qmul r1 h) (qmul r1 h)) (qmul (qmul r1 r1) (qmul h h)) := by rat_ring
      exact qle_trans s (qle_of_qEq e)

theorem ev_le {x : Nat → QExpr} {l h : QExpr} (hx : Ev x l h) : qle l h := by
  cases qle.decidable l h with
  | isTrue t => exact t
  | isFalse f =>
    exfalso
    have hl : qle h l := (qle_total l h).resolve_left f
    have pos : qlt qzero (qsub l h) := qlt_iff_le_not_le.mpr ⟨by unfold qsub; rat_linarith,
      fun z => f (by unfold qsub at z; rat_linarith)⟩
    obtain ⟨Bq, hB⟩ := ZTrig.pos_floor pos
    obtain ⟨N, hN⟩ := hx (Bq + 1 + 1)
    obtain ⟨a, b⟩ := hN N (Nat.le_refl N)
    have e := qeps_succ_add Bq
    have e2 := qeps_succ_add (Bq + 1)
    have np := (qlt_iff_le_not_le.mp (qeps_pos (Bq + 1))).2
    apply np
    unfold qsub at *
    rat_linarith

/-- A box with no point: every bound holds there. -/
theorem boxEv_empty {e : G} {l h : QExpr} (r : BoxEv B e l h) (hn : ¬ qle l h) (e' : G) (l' h' : QExpr) :
    BoxEv B e' l' h' := fun p hp => absurd (ev_le (r p hp)) hn

/-- Two positive factors (`u ≥ lu > 0`, `v ≥ lv > 0`): their product is clear of zero. -/
theorem cl_mul_pos {u v : G} {lu hu lv hv : QExpr} (bu : BoxEv B u lu hu) (hlu : qlt qzero lu)
    (bv : BoxEv B v lv hv) (hlv : qlt qzero lv) : Cl B (.mul u v) := by
  cases qle.decidable lu hu with
  | isFalse f => exact ⟨qone, qone, qone, qone, boxEv_empty bu f _ _ _, qle_refl _, Or.inl ⟨qone_pos, by
      have := qle_of_qlt qone_pos; rat_linarith, by rat_linarith⟩⟩
  | isTrue h1 =>
  cases qle.decidable lv hv with
  | isFalse f => exact ⟨qone, qone, qone, qone, boxEv_empty bv f _ _ _, qle_refl _, Or.inl ⟨qone_pos, by
      have := qle_of_qlt qone_pos; rat_linarith, by rat_linarith⟩⟩
  | isTrue h2 =>
  have l0 := qle_of_qlt hlu
  have v0 := qle_of_qlt hlv
  have p1 := qmul_nonneg l0 (show qle qzero (qsub hv lv) by unfold qsub; rat_linarith)
  have p2 := qmul_nonneg (show qle qzero (qsub hu lu) by unfold qsub; rat_linarith) v0
  have p3 := qmul_nonneg (show qle qzero (qsub hu lu) by unfold qsub; rat_linarith) (show qle qzero (qsub hv lv) by unfold qsub; rat_linarith)
  have c : Corners (qmul lu lv) (qmul hu hv) lu hu lv hv := by
    unfold qsub at p1 p2 p3
    exact ⟨⟨qle_refl _, by rat_linarith, by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith, by rat_linarith, qle_refl _⟩⟩
  have pp := qmul_pos hlu hlv
  have cc := qmul_inv'_cancel (ne_zero_of_lt pp)
  have e : qEq (qmul (qinv' (qmul lu lv)) (qmul lu lv)) (qmul (qmul lu lv) (qinv' (qmul lu lv))) := by rat_ring
  unfold qsub at p1 p2 p3
  exact ⟨_, _, qzero, qinv' (qmul lu lv), fun p hp => Ev_mul (bu p hp) (bv p hp) c, by rat_linarith,
    Or.inl ⟨pp, by rat_linarith, by rat_linarith⟩⟩

theorem diter_uses {e : G} (hU : ¬ Uses e i) : ∀ t, ¬ Uses (Diter i t e) i := by
  intro t
  induction t generalizing e with
  | zero => exact hU
  | succ t ih => exact ih (D_free i 0 (fun _ => qzero) e hU).2

theorem bd_free {e : G} (hU : ¬ Uses e i) (h0 : Bd B e) : BdAll B i e
  | 0 => h0
  | t + 1 => ⟨qzero, qzero, fun p _ => Ev_congr_ev 0 (fun n _ => qEq_symm (Diter_free i n p t e hU)) (Ev_const qzero)⟩

theorem bd_constAll (c : QExpr) : BdAll B i (.const c) := bd_free (fun h => h) (bd_const c)

theorem bd_varAll (j : Nat) : BdAll B i (.var j)
  | 0 => bd_var j
  | t + 1 => bd_constAll (dvar i j) t

theorem bd_addAll {u v : G} (hu : BdAll B i u) (hv : BdAll B i v) : BdAll B i (.add u v) := fun t => by
  rw [Diter_add]; exact bd_add (hu t) (hv t)

theorem bd_subAll {u v : G} (hu : BdAll B i u) (hv : BdAll B i v) : BdAll B i (.sub u v) := fun t => by
  rw [Diter_sub]; exact bd_sub (hu t) (hv t)

theorem mulG : ∀ t (u v : G), (∀ s, s ≤ t → Bd B (Diter i s u)) → (∀ s, s ≤ t → Bd B (Diter i s v)) →
    Bd B (Diter i t (.mul u v))
  | 0, _, _, hu, hv => bd_mul (hu 0 (Nat.le_refl 0)) (hv 0 (Nat.le_refl 0))
  | t + 1, u, v, hu, hv => by
      show Bd B (Diter i t (.add (.mul (D i u) v) (.mul u (D i v))))
      rw [Diter_add]
      exact bd_add (mulG t (D i u) v (fun s hs => hu (s + 1) (Nat.succ_le_succ hs)) (fun s hs => hv s (Nat.le_trans hs (Nat.le_succ t))))
        (mulG t u (D i v) (fun s hs => hu s (Nat.le_trans hs (Nat.le_succ t))) (fun s hs => hv (s + 1) (Nat.succ_le_succ hs)))

theorem bd_mulAll {u v : G} (hu : BdAll B i u) (hv : BdAll B i v) : BdAll B i (.mul u v) :=
  fun t => mulG t u v (fun s _ => hu s) (fun s _ => hv s)

theorem bd_Dall {u : G} (hu : BdAll B i u) : BdAll B i (D i u) := fun t => hu (t + 1)

/-- The quotient, graded: its iterates to `t` need the parts' iterates to `t` only (the square root's denominator
holds the node itself). -/
theorem divGg : ∀ t (u v : G), (∀ s, s ≤ t → Bd B (Diter i s u)) → (∀ s, s ≤ t → Bd B (Diter i s v)) → Cl B v →
    Bd B (Diter i t (.div u v))
  | 0, _, _, hu, _, hc => bd_div (hu 0 (Nat.le_refl 0)) hc
  | t + 1, u, v, hu, hv, hc =>
      divGg t (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v)
        (fun s hs => by
          rw [Diter_sub]
          exact bd_sub (mulG s (D i u) v (fun s' hs' => hu (s' + 1) (Nat.succ_le_succ (Nat.le_trans hs' hs)))
              (fun s' hs' => hv s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t)))))
            (mulG s u (D i v) (fun s' hs' => hu s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t))))
              (fun s' hs' => hv (s' + 1) (Nat.succ_le_succ (Nat.le_trans hs' hs)))))
        (fun s hs => mulG s v v (fun s' hs' => hv s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t))))
          (fun s' hs' => hv s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t)))))
        (cl_sq hc)

theorem divG (t : Nat) (u v : G) (hu : BdAll B i u) (hv : BdAll B i v) (hc : Cl B v) : Bd B (Diter i t (.div u v)) :=
  divGg t u v (fun s _ => hu s) (fun s _ => hv s) hc

theorem bd_expAll {u : G} (hu : BdAll B i u) (he : Bd B (.exp u)) : BdAll B i (.exp u) :=
  strongAll _ he (fun t ih => mulG t (.exp u) (D i u) ih (fun s _ => hu (s + 1)))

theorem bd_scAll {u : G} (hu : BdAll B i u) (hs : Bd B (.sin u)) (hc : Bd B (.cos u)) :
    BdAll B i (.sin u) ∧ BdAll B i (.cos u) := by
  have := strongAll (fun t => Bd B (Diter i t (.sin u)) ∧ Bd B (Diter i t (.cos u))) ⟨hs, hc⟩ (fun t ih =>
    ⟨mulG t (.cos u) (D i u) (fun s hs => (ih s hs).2) (fun s _ => hu (s + 1)),
     mulG t (.sub (.const qzero) (.sin u)) (D i u)
       (fun s hs => by rw [Diter_sub]; exact bd_sub (bd_constAll qzero s) (ih s hs).1) (fun s _ => hu (s + 1))⟩)
  exact ⟨fun t => (this t).1, fun t => (this t).2⟩

theorem bd_tanAll {u : G} (hu : BdAll B i u) (ht : Bd B (.tan u)) : BdAll B i (.tan u) :=
  strongAll _ ht (fun t ih => mulG t (.add (.const qone) (.mul (.tan u) (.tan u))) (D i u)
    (fun s hs => by
      rw [Diter_add]
      exact bd_add (bd_constAll qone s) (mulG s (.tan u) (.tan u) (fun s' hs' => ih s' (Nat.le_trans hs' hs))
        (fun s' hs' => ih s' (Nat.le_trans hs' hs))))
    (fun s _ => hu (s + 1)))

theorem bd_powAll {u : G} (hu : BdAll B i u) : ∀ k, BdAll B i (.powN u k)
  | 0, 0 => bd_powN (hu 0) 0
  | 0, t + 1 => bd_constAll qzero t
  | k + 1, 0 => bd_powN (hu 0) (k + 1)
  | k + 1, t + 1 => bd_mulAll (bd_mulAll (bd_constAll _) (bd_powAll hu k)) (bd_Dall hu) t

/-! ## Steps -/

theorem st_free {e : G} (hU : ¬ Uses e i) : StAll B i e := fun t => StepRead.free (diter_uses hU t)

theorem st_constAll (c : QExpr) : StAll B i (.const c) := st_free (fun h => h)

theorem st_varAll (j : Nat) : StAll B i (.var j)
  | 0 => StepRead.var
  | t + 1 => st_constAll (dvar i j) t

theorem st_addAll {u v : G} (hu : StAll B i u) (hv : StAll B i v) : StAll B i (.add u v) := fun t => by
  rw [Diter_add]; exact StepRead.add (hu t) (hv t)

theorem st_subAll {u v : G} (hu : StAll B i u) (hv : StAll B i v) : StAll B i (.sub u v) := fun t => by
  rw [Diter_sub]; exact StepRead.sub (hu t) (hv t)

theorem mulS : ∀ t (u v : G), (∀ s, s ≤ t → StepRead B i (Diter i s u)) → (∀ s, s ≤ t → StepRead B i (Diter i s v)) →
    BdAll B i u → BdAll B i v → StepRead B i (Diter i t (.mul u v))
  | 0, _, _, su, sv, bu, bv =>
      let ⟨_, _, a⟩ := bu 0
      let ⟨_, _, b⟩ := bv 0
      let ⟨_, _, c⟩ := bu 1
      let ⟨_, _, d⟩ := bv 1
      StepRead.mul (su 0 (Nat.le_refl 0)) (sv 0 (Nat.le_refl 0)) a b c d
  | t + 1, u, v, su, sv, bu, bv => by
      show StepRead B i (Diter i t (.add (.mul (D i u) v) (.mul u (D i v))))
      rw [Diter_add]
      exact StepRead.add
        (mulS t (D i u) v (fun s hs => su (s + 1) (Nat.succ_le_succ hs)) (fun s hs => sv s (Nat.le_trans hs (Nat.le_succ t)))
          (bd_Dall bu) bv)
        (mulS t u (D i v) (fun s hs => su s (Nat.le_trans hs (Nat.le_succ t))) (fun s hs => sv (s + 1) (Nat.succ_le_succ hs))
          bu (bd_Dall bv))

theorem st_mulAll {u v : G} (su : StAll B i u) (sv : StAll B i v) (bu : BdAll B i u) (bv : BdAll B i v) :
    StAll B i (.mul u v) := fun t => mulS t u v (fun s _ => su s) (fun s _ => sv s) bu bv

theorem divSg : ∀ t (u v : G), (∀ s, s ≤ t → StepRead B i (Diter i s u)) → (∀ s, s ≤ t → StepRead B i (Diter i s v)) →
    BdAll B i u → BdAll B i v → Cl B v → StepRead B i (Diter i t (.div u v))
  | 0, _, _, su, sv, bu, bv, ⟨_, _, _, _, b, hR⟩ =>
      let ⟨_, _, a⟩ := bu 0
      let ⟨_, _, c⟩ := bu 1
      let ⟨_, _, d⟩ := bv 1
      StepRead.div (su 0 (Nat.le_refl 0)) (sv 0 (Nat.le_refl 0)) a b hR c d
  | t + 1, u, v, su, sv, bu, bv, hc =>
      divSg t (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v)
        (fun s hs => by
          rw [Diter_sub]
          exact StepRead.sub
            (mulS s (D i u) v (fun s' hs' => su (s' + 1) (Nat.succ_le_succ (Nat.le_trans hs' hs)))
              (fun s' hs' => sv s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t)))) (bd_Dall bu) bv)
            (mulS s u (D i v) (fun s' hs' => su s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t))))
              (fun s' hs' => sv (s' + 1) (Nat.succ_le_succ (Nat.le_trans hs' hs))) bu (bd_Dall bv)))
        (fun s hs => mulS s v v (fun s' hs' => sv s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t))))
          (fun s' hs' => sv s' (Nat.le_trans hs' (Nat.le_trans hs (Nat.le_succ t)))) bv bv)
        (bd_subAll (bd_mulAll (bd_Dall bu) bv) (bd_mulAll bu (bd_Dall bv))) (bd_mulAll bv bv) (cl_sq hc)

theorem divS (t : Nat) (u v : G) (su : StAll B i u) (sv : StAll B i v) (bu : BdAll B i u) (bv : BdAll B i v)
    (hc : Cl B v) : StepRead B i (Diter i t (.div u v)) :=
  divSg t u v (fun s _ => su s) (fun s _ => sv s) bu bv hc

theorem st_expAll {u : G} (su : StAll B i u) (bu : BdAll B i u) (he : Bd B (.exp u)) : StAll B i (.exp u) :=
  strongAll _
    (let ⟨_, _, a⟩ := bu 0
     let ⟨_, _, c⟩ := bu 1
     let ⟨_, _, e⟩ := he
     StepRead.exp (su 0) a c e)
    (fun t ih => mulS t (.exp u) (D i u) ih (fun s _ => su (s + 1)) (bd_expAll bu he) (bd_Dall bu))

theorem st_scAll {u : G} (su : StAll B i u) (bu : BdAll B i u) (hs : Bd B (.sin u)) (hc : Bd B (.cos u)) :
    StAll B i (.sin u) ∧ StAll B i (.cos u) := by
  obtain ⟨bs, bc⟩ := bd_scAll bu hs hc
  obtain ⟨_, _, a⟩ := bu 0
  obtain ⟨_, _, c⟩ := bu 1
  obtain ⟨_, _, es⟩ := hs
  obtain ⟨_, _, ec⟩ := hc
  have := strongAll (fun t => StepRead B i (Diter i t (.sin u)) ∧ StepRead B i (Diter i t (.cos u)))
    ⟨StepRead.sin (su 0) a c ec, StepRead.cos (su 0) a c es⟩ (fun t ih =>
    ⟨mulS t (.cos u) (D i u) (fun s hs => (ih s hs).2) (fun s _ => su (s + 1)) bc (bd_Dall bu),
     mulS t (.sub (.const qzero) (.sin u)) (D i u)
       (fun s hs => by rw [Diter_sub]; exact StepRead.sub (st_constAll qzero s) (ih s hs).1) (fun s _ => su (s + 1))
       (bd_subAll (bd_constAll qzero) bs) (bd_Dall bu)⟩)
  exact ⟨fun t => (this t).1, fun t => (this t).2⟩

theorem st_tanAll {u : G} (su : StAll B i u) (bu : BdAll B i u) (hs : Bd B (.sin u)) (hc : Cl B (.cos u))
    (ht : Bd B (.tan u)) : StAll B i (.tan u) := by
  obtain ⟨lc, hc', r1, r2, ec, hR⟩ := hc
  obtain ⟨ss, sc⟩ := st_scAll su bu hs ⟨lc, hc', ec⟩
  obtain ⟨bs, bc⟩ := bd_scAll bu hs ⟨lc, hc', ec⟩
  have bt := bd_tanAll bu ht
  exact strongAll _ (StepRead.tan (divS 0 (.sin u) (.cos u) ss sc bs bc ⟨lc, hc', r1, r2, ec, hR⟩) ec hR)
    (fun t ih => mulS t (.add (.const qone) (.mul (.tan u) (.tan u))) (D i u)
      (fun s hs => by
        rw [Diter_add]
        exact StepRead.add (st_constAll qone s) (mulS s (.tan u) (.tan u) (fun s' hs' => ih s' (Nat.le_trans hs' hs))
          (fun s' hs' => ih s' (Nat.le_trans hs' hs)) bt bt))
      (fun s _ => su (s + 1)) (bd_addAll (bd_constAll qone) (bd_mulAll bt bt)) (bd_Dall bu))

theorem st_powAll {u : G} (su : StAll B i u) (bu : BdAll B i u) : ∀ k, StAll B i (.powN u k)
  | 0, 0 => StepRead.powZ
  | 0, t + 1 => st_constAll qzero t
  | k + 1, 0 =>
      let ⟨_, _, a⟩ := bu 0
      let ⟨_, _, c⟩ := bu 1
      StepRead.powN (su 0) a c
  | k + 1, t + 1 =>
      st_mulAll (st_mulAll (st_constAll _) (st_powAll su bu k) (bd_constAll _) (bd_powAll bu k)) (fun s => su (s + 1))
        (bd_mulAll (bd_constAll _) (bd_powAll bu k)) (bd_Dall bu) t

/-- The square root: `D√u = Du / (2√u)` — its iterates by the graded quotient. -/
theorem sqrt_close {u : G} (su : StAll B i u) (bu : BdAll B i u) {lu hu SL SH dl dh r1 r2 : QExpr}
    (ru : BoxEv B u lu hu) (hlo : qle qzero lu) (hSL : qlt qzero SL) (hSL2 : qle (sq SL) lu) (hSH : qle qzero SH)
    (hSH2 : qle hu (sq SH)) (bs : BoxEv B (.sqrt u) SL SH) {cl ch : QExpr} (bs2 : BoxEv B (.sqrt u) cl ch)
    (hdv : Corners dl dh (qadd qone qone) (qadd qone qone) cl ch) (hR : RecipOK r1 r2 dl dh) :
    BdAll B i (.sqrt u) ∧ StAll B i (.sqrt u) := by
  have cl : Cl B (.mul (.const (qadd qone qone)) (.sqrt u)) :=
    ⟨dl, dh, r1, r2, fun p hp => Ev_mul (Ev_const _) (bs2 p hp) hdv, hR⟩
  have bd : BdAll B i (.sqrt u) := strongAll _ ⟨SL, SH, bs⟩ (fun t ih =>
    divGg t (D i u) (.mul (.const (qadd qone qone)) (.sqrt u)) (fun s _ => bu (s + 1))
      (fun s hs => mulG s (.const (qadd qone qone)) (.sqrt u) (fun s' _ => bd_constAll _ s')
        (fun s' hs' => ih s' (Nat.le_trans hs' hs))) cl)
  refine ⟨bd, strongAll _ ?_ (fun t ih =>
    divSg t (D i u) (.mul (.const (qadd qone qone)) (.sqrt u)) (fun s _ => su (s + 1))
      (fun s hs => mulS s (.const (qadd qone qone)) (.sqrt u) (fun s' _ => st_constAll _ s')
        (fun s' hs' => ih s' (Nat.le_trans hs' hs)) (bd_constAll _) bd)
      (bd_Dall bu) (bd_mulAll (bd_constAll _) bd) cl)⟩
  obtain ⟨_, _, d⟩ := bu 1
  exact StepRead.sqrt (su 0) ru hlo hSL hSL2 hSH hSH2 d

/-- A positive box bound is clear of zero. -/
theorem cl_pos {u : G} {l h : QExpr} (bu : BoxEv B u l h) (hl : qlt qzero l) : Cl B u := by
  cases qle.decidable l h with
  | isFalse f => exact ⟨qone, qone, qone, qone, boxEv_empty bu f _ _ _, qle_refl _, Or.inl ⟨qone_pos, by
      have := qle_of_qlt qone_pos; rat_linarith, by rat_linarith⟩⟩
  | isTrue h1 =>
    have cc := qmul_inv'_cancel (ne_zero_of_lt hl)
    have e : qEq (qmul (qinv' l) l) (qmul l (qinv' l)) := by rat_ring
    exact ⟨l, h, qzero, qinv' l, bu, h1, Or.inl ⟨hl, by rat_linarith, by rat_linarith⟩⟩

/-- `ln u`, `u` bounded below by a positive box bound: every iterate bounded and step-readable. -/
theorem ln_close {u : G} (su : StAll B i u) (bu : BdAll B i u) {l h : QExpr} (b0 : BoxEv B u l h) (hl : qlt qzero l)
    (hln : Bd B (.ln u)) : BdAll B i (.ln u) ∧ StAll B i (.ln u) := by
  have hc := cl_pos b0 hl
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => exact hln
    | succ t => exact divG t (D i u) u (bd_Dall bu) bu hc
  · cases t with
    | zero =>
        obtain ⟨_, _, d⟩ := bu 1
        exact StepRead.ln (su 0) b0 hl d
    | succ t => exact divS t (D i u) u (fun s => su (s + 1)) su (bd_Dall bu) bu hc

/-- `1 + u·u` is at least `1` on the box, and bounded. -/
theorem one_sq_box {u : G} {l h : QExpr} (bu : BoxEv B u l h) :
    ∃ H, BoxEv B (.add (.const qone) (.mul u u)) qone H := by
  obtain ⟨M, _, hM⟩ := read_bound bu
  refine ⟨qadd qone (qmul M M), fun p hp => ?_⟩
  obtain ⟨N, hN⟩ := hM p hp
  refine Ev_of_exact N (fun n hn => ?_)
  have s := ZAtan.sq_le (hN n hn)
  have z := qmul_self_nonneg (evalN n p u)
  show qle qone (qadd qone (qmul (evalN n p u) (evalN n p u))) ∧ qle (qadd qone (qmul (evalN n p u) (evalN n p u))) _
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## From the kernel's reading -/

/-- A coefficient reading bounds the value: `BoxEv` from `k = 0`. -/
theorem boxEv_of_cread {K : Nat} {e : G} {c : Nat → QExpr × QExpr} (r : CRead B i K e c) : BoxEv B e (c 0).1 (c 0).2 :=
  fun p hp => Ev_congr_ev 0 (fun n _ => J_zero i n p e) (cread_sound hp r 0 (Nat.zero_le K))

/-- THE KERNEL'S TAYLOR READING CARRIES THE REMAINDER'S HYPOTHESES: every iterate `D^t e` bounded on the box and
step-readable, for every `t`. -/
theorem cread_good {K : Nat} : ∀ {e : G} {c : Nat → QExpr × QExpr}, CRead B i K e c → BdAll B i e ∧ StAll B i e := by
  intro e c r
  induction r with
  | @free e c l h hU hV _ _ => exact ⟨bd_free hU ⟨l, h, boxEv_of_read hV⟩, st_free hU⟩
  | var _ _ _ => exact ⟨bd_varAll i, st_varAll i⟩
  | add _ _ _ ihu ihv => exact ⟨bd_addAll ihu.1 ihv.1, st_addAll ihu.2 ihv.2⟩
  | sub _ _ _ ihu ihv => exact ⟨bd_subAll ihu.1 ihv.1, st_subAll ihu.2 ihv.2⟩
  | mul _ _ _ ihu ihv => exact ⟨bd_mulAll ihu.1 ihv.1, st_mulAll ihu.2 ihv.2 ihu.1 ihv.1⟩
  | @div u v a b c l0 h0 r1 r2 _ rv _ _ hR _ ihu ihv =>
      have hc : Cl B v := ⟨_, _, r1, r2, boxEv_of_cread rv, hR⟩
      exact ⟨fun t => divG t u v ihu.1 ihv.1 hc, fun t => divS t u v ihu.2 ihv.2 ihu.1 ihv.1 hc⟩
  | @exp u a c D l0 h0 _ hV _ _ _ ihu =>
      exact ⟨bd_expAll ihu.1 ⟨l0, h0, boxEv_of_read hV⟩, st_expAll ihu.2 ihu.1 ⟨l0, h0, boxEv_of_read hV⟩⟩
  | @sin u a s c D _ hSC ihu =>
      obtain ⟨⟨ls, hs, rs, _⟩, ⟨lc, hc, rc, _⟩, _⟩ := hSC
      exact ⟨(bd_scAll ihu.1 ⟨ls, hs, boxEv_of_read rs⟩ ⟨lc, hc, boxEv_of_read rc⟩).1,
        (st_scAll ihu.2 ihu.1 ⟨ls, hs, boxEv_of_read rs⟩ ⟨lc, hc, boxEv_of_read rc⟩).1⟩
  | @cos u a s c D _ hSC ihu =>
      obtain ⟨⟨ls, hs, rs, _⟩, ⟨lc, hc, rc, _⟩, _⟩ := hSC
      exact ⟨(bd_scAll ihu.1 ⟨ls, hs, boxEv_of_read rs⟩ ⟨lc, hc, boxEv_of_read rc⟩).2,
        (st_scAll ihu.2 ihu.1 ⟨ls, hs, boxEv_of_read rs⟩ ⟨lc, hc, boxEv_of_read rc⟩).2⟩
  | @tan u a s c D t l0 h0 r1 r2 _ hSC hV _ hR _ ihu =>
      obtain ⟨⟨ls, hs, rs, _⟩, ⟨lc, hc, rc, hcc⟩, _⟩ := hSC
      have ht : Bd B (.tan u) := ⟨l0, h0, fun p hp => (boxEv_of_read hV p hp : Ev (fun n => evalN n p (.tan u)) l0 h0)⟩
      have cl : Cl B (.cos u) := ⟨_, _, r1, r2, fun p hp => Ev_widen (boxEv_of_read rc p hp) hcc.1 hcc.2, hR⟩
      exact ⟨bd_tanAll ihu.1 ht, st_tanAll ihu.2 ihu.1 ⟨ls, hs, boxEv_of_read rs⟩ cl ht⟩
  | @powN u m a p l0 h0 W dv R _ _ _ _ ihu => exact ⟨bd_powAll ihu.1 m, st_powAll ihu.2 ihu.1 m⟩
  | @powR u c a p l0 h0 W dv R ru hpos hV _ _ ihu =>
      have bu := boxEv_of_cread ru
      have lnB : Bd B (.ln u) := by
        cases hV with
        | exp rw _ _ =>
          cases rw with
          | mul _ rl _ => exact ⟨_, _, boxEv_of_read rl⟩
      obtain ⟨bl, sl⟩ := ln_close ihu.2 ihu.1 bu hpos lnB
      have bw := bd_mulAll (bd_constAll c) bl
      have sw := st_mulAll (st_constAll c) sl (bd_constAll c) bl
      have be : Bd B (.exp (.mul (.const c) (.ln u))) := ⟨_, _, boxEv_of_read hV⟩
      exact ⟨bd_expAll bw be, st_expAll sw bw be⟩
  | @log10 u a l c l0 h0 L1 L2 r1 r2 s1 s2 ru rl hpos hRu hV _ hL hL1 hR _ ihu ihl =>
      have bu := boxEv_of_cread ru
      have bL : BoxEv B (.ln (.const (qnat 10))) L1 L2 := boxEv_of_read hL
      have clm : Cl B (.mul u (.ln (.const (qnat 10)))) := cl_mul_pos bu hpos bL hL1
      have bfree : BdAll B i (.ln (.const (qnat 10))) := bd_free (fun h => h) ⟨_, _, bL⟩
      refine ⟨fun t => ?_, fun t => ?_⟩
      · cases t with
        | zero => exact ⟨_, _, boxEv_of_read hV⟩
        | succ t => exact divG t (D i u) (.mul u (.ln (.const (qnat 10)))) (bd_Dall ihu.1) (bd_mulAll ihu.1 bfree) clm
      · cases t with
        | zero => exact StepRead.log10 (ihl.2 0) bu hpos bL hL1
        | succ t =>
            exact divS t (D i u) (.mul u (.ln (.const (qnat 10)))) (fun s => ihu.2 (s + 1))
              (st_mulAll ihu.2 (st_free (fun h => h)) ihu.1 bfree) (bd_Dall ihu.1) (bd_mulAll ihu.1 bfree) clm
  | @ln u a c Dl l0 h0 r1 r2 ru _ _ hpos hR _ _ _ ihu =>
      have bu := boxEv_of_cread ru
      have hc : Cl B u := ⟨_, _, r1, r2, bu, hR⟩
      refine ⟨fun t => ?_, fun t => ?_⟩
      · cases t with
        | zero => exact ⟨_, _, fun p hp => (boxEv_of_cread (CRead.ln ru ‹_› ‹_› hpos hR ‹_› ‹_› ‹_›) p hp)⟩
        | succ t => exact divG t (D i u) u (bd_Dall ihu.1) ihu.1 hc
      · cases t with
        | zero =>
            obtain ⟨_, _, d⟩ := ihu.1 1
            exact StepRead.ln (ihu.2 0) bu hpos d
        | succ t => exact divS t (D i u) u (fun s => ihu.2 (s + 1)) ihu.2 (bd_Dall ihu.1) ihu.1 hc
  | @atan u a c U w Dd l0 h0 r1 r2 ru hV _ _ _ _ _ _ _ ihu =>
      have bu := boxEv_of_cread ru
      obtain ⟨H, bv⟩ := one_sq_box bu
      have hc : Cl B (.add (.const qone) (.mul u u)) := cl_pos bv qone_pos
      have bvA : BdAll B i (.add (.const qone) (.mul u u)) := bd_addAll (bd_constAll qone) (bd_mulAll ihu.1 ihu.1)
      have svA : StAll B i (.add (.const qone) (.mul u u)) :=
        st_addAll (st_constAll qone) (st_mulAll ihu.2 ihu.2 ihu.1 ihu.1)
      refine ⟨fun t => ?_, fun t => ?_⟩
      · cases t with
        | zero => exact ⟨l0, h0, boxEv_of_read hV⟩
        | succ t => exact divG t (D i u) _ (bd_Dall ihu.1) bvA hc
      · cases t with
        | zero =>
            obtain ⟨_, _, d⟩ := ihu.1 1
            exact StepRead.atan (ihu.2 0) bu d
        | succ t => exact divS t (D i u) _ (fun s => ihu.2 (s + 1)) svA (bd_Dall ihu.1) bvA hc
  | @sqrt u a c l0 h0 dl dh r1 r2 _ hV hc0 hpos hdv hR _ _ ihu =>
      have bs : BoxEv B (.sqrt u) l0 h0 := boxEv_of_read hV
      cases hV with
      | sqrt ru hlo _ hSL2 hSH hSH2 =>
          exact sqrt_close ihu.2 ihu.1 (boxEv_of_read ru) hlo hpos hSL2 hSH hSH2 bs
            (fun p hp => Ev_widen (bs p hp) hc0.1 hc0.2) hdv hR

/-! ## The leaf from the kernel's readings -/

/-- Eventually in `[l, h]` to every precision: `l ≤ h`. -/
theorem ev_order {x : Nat → QExpr} {l h : QExpr} (hx : Ev x l h) : qle l h := by
  cases qle.decidable l h with
  | isTrue t => exact t
  | isFalse f =>
    exfalso
    have hl : qle h l := (qle_total l h).resolve_left f
    have pos : qlt qzero (qsub l h) := qlt_iff_le_not_le.mpr ⟨by unfold qsub; rat_linarith,
      fun z => f (by unfold qsub at z; rat_linarith)⟩
    obtain ⟨Bq, hB⟩ := ZTrig.pos_floor pos
    obtain ⟨N, hN⟩ := hx (Bq + 1 + 1)
    obtain ⟨a, b⟩ := hN N (Nat.le_refl N)
    have e := qeps_succ_add Bq
    have e2 := qeps_succ_add (Bq + 1)
    have np := (qlt_iff_le_not_le.mp (qeps_pos (Bq + 1))).2
    apply np
    unfold qsub at *
    rat_linarith

/-- `D^M e` from its coefficient: `[lo·M!, hi·M!]`. -/
theorem boxEv_top {B : Box QExpr} {i K : Nat} {e : G} {c : Nat → QExpr × QExpr} (r : CRead B i K e c) (M : Nat)
    (hM : M ≤ K) (ho : qle (c M).1 (c M).2) :
    BoxEv B (Diter i M e) (qmul (c M).1 (qnat (fact M))) (qmul (c M).2 (qnat (fact M))) := by
  have f0 := qle_of_qlt (fact_pos M)
  have d := qmul_nonneg (show qle qzero (qsub (c M).2 (c M).1) by unfold qsub; rat_linarith) f0
  unfold qsub at d
  have co : Corners (qmul (c M).1 (qnat (fact M))) (qmul (c M).2 (qnat (fact M))) (c M).1 (c M).2
      (qnat (fact M)) (qnat (fact M)) :=
    ⟨⟨qle_refl _, qle_refl _, by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith, qle_refl _, qle_refl _⟩⟩
  intro q hq
  refine Ev_congr_ev 0 (fun n _ => ?_) (Ev_mul (cread_sound hq r M hM) (Ev_const (qnat (fact M))) co)
  show qEq (qmul (qmul (evalN n q (Diter i M e)) (cf M)) (qnat (fact M))) (evalN n q (Diter i M e))
  have c1 := qmul_inv'_cancel (ne_zero_of_lt (fact_pos M))
  have : qEq (qmul (qmul (evalN n q (Diter i M e)) (cf M)) (qnat (fact M)))
      (qmul (evalN n q (Diter i M e)) (qmul (qnat (fact M)) (qinv' (qnat (fact M))))) := by unfold cf; rat_ring
  exact qEq_trans this (qEq_trans (qmul_respects (qEq_refl _) c1) (by rat_ring))

theorem cf_fact (M : Nat) (x : QExpr) : qEq (qmul (cf M) (qmul x (qnat (fact M)))) x := by
  have c1 := qmul_inv'_cancel (ne_zero_of_lt (fact_pos M))
  have : qEq (qmul (cf M) (qmul x (qnat (fact M)))) (qmul x (qmul (qnat (fact M)) (qinv' (qnat (fact M))))) := by
    unfold cf; rat_ring
  exact qEq_trans this (qEq_trans (qmul_respects (qEq_refl _) c1) (by rat_ring))

theorem ab_congr {x y M : QExpr} (e : qEq x y) (h : ZTrig.Ab y M) : ZTrig.Ab x M := by
  obtain ⟨a, b⟩ := h; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE KERNEL'S TAYLOR LEAF OF ORDER `2(r+1)`, FROM ITS OWN READINGS: `cP` — the kernel's coefficients over the piece
(the remainder uses `cP_{2(r+1)}`), `cM` — at the midpoint (the even coefficients). Every symmetric tagged sum of mesh
`μ` lies in the leaf's interval, widened by `μ`-terms and `ε`. No hypothesis on the derivatives: they all follow from
the readings (`cread_good`, `cread_sound`). -/
theorem taylorN_kernel {B Bm : Box QExpr} {i r : Nat} {e : G} {p : Point QExpr} {m h μ K KR : QExpr} {cs : List Cell}
    {cP cM : Nat → QExpr × QExpr} (hp : Nat → QExpr)
    (rP : CRead B i (2 * (r + 1)) e cP) (rM : CRead Bm i (2 * r) e cM) (hm : InBox qOrd Bm (upd p i m))
    (hab : ∀ j, j < r + 1 → ZTrig.Ab (cM (2 * j)).1 K ∧ ZTrig.Ab (cM (2 * j)).2 K)
    (hRL : ZTrig.Ab (cP (2 * (r + 1))).1 KR) (hRU : ZTrig.Ab (cP (2 * (r + 1))).2 KR)
    (hhp : ∀ j, j ≤ r + 1 → qEq (qmul (qnat (2 * j + 1)) (hp j)) (qpowN h (2 * j + 1)))
    (hB : ∀ t, qle (qsub m h) t → qle t (qadd m h) → InBox qOrd B (upd p i t))
    (hch : Chain qzero h cs) (hok : ∀ c, List.Mem c cs → CellOK μ c) (hμ : qle qzero μ) (hh : qle qzero h) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qadd (ZTrig.bs (fun j => qmul (qadd (cM (2 * j)).1 (cM (2 * j)).1) (hp j)) (r + 1))
            (qmul (qadd (cP (2 * (r + 1))).1 (cP (2 * (r + 1))).1) (hp (r + 1))))
          (qadd (ZTrig.bs (fun j => qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
              (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))) (r + 1))
            (qadd (qmul (qadd KR KR) (qmul μ (qpowN h (2 * (r + 1))))) (qmul (qadd (qeps k) (qeps k)) h))))
        (ssum n e p i m cs) ∧
      qle (ssum n e p i m cs)
        (qadd (qadd (ZTrig.bs (fun j => qmul (qadd (cM (2 * j)).2 (cM (2 * j)).2) (hp j)) (r + 1))
            (qmul (qadd (cP (2 * (r + 1))).2 (cP (2 * (r + 1))).2) (hp (r + 1))))
          (qadd (ZTrig.bs (fun j => qadd (qmul (qadd K K) (qmul μ (qpowN h (2 * j))))
              (qmul (qadd (qeps k) (qeps k)) (qadd (hp j) (qmul μ (qpowN h (2 * j)))))) (r + 1))
            (qadd (qmul (qadd KR KR) (qmul μ (qpowN h (2 * (r + 1))))) (qmul (qadd (qeps k) (qeps k)) h)))) := by
  have g := cread_good rP
  have mid : InBox qOrd B (upd p i m) := hB m (by unfold qsub; have := hh; rat_linarith) (by rat_linarith)
  have ho := ev_order (cread_sound mid rP (2 * (r + 1)) (Nat.le_refl _))
  have eL := cf_fact (2 * (r + 1)) (cP (2 * (r + 1))).1
  have eU := cf_fact (2 * (r + 1)) (cP (2 * (r + 1))).2
  have leaf := ZTaylorLeaf.taylorN_leaf (B := B) (i := i) (r := r) (e := e) (p := p) (m := m) (h := h) (μ := μ) (K := K)
    (KR := KR) (cs := cs) (fun j => (cM (2 * j)).1) (fun j => (cM (2 * j)).2) hp
    (fun t _ => g.2 t) (fun t _ => g.1 (t + 1)) (boxEv_top rP (2 * (r + 1)) (Nat.le_refl _) ho)
    (fun j hj => cread_sound hm rM (2 * j) (by
      have := Nat.le_of_lt_succ hj
      show 2 * j ≤ 2 * r
      exact Nat.mul_le_mul_left 2 this))
    hab (ab_congr eL hRL) (ab_congr eU hRU) hhp hB hch hok hμ
  intro k
  obtain ⟨N, hN⟩ := leaf k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨lo, hi⟩ := hN n hn
  have m1 := qmul_respects (qadd_respects eL eL) (qEq_refl (hp (r + 1)))
  have m2 := qmul_respects (qadd_respects eU eU) (qEq_refl (hp (r + 1)))
  unfold qsub at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) (qmul (cP (2 * (r + 1))).1 (qnat (fact (2 * (r + 1))))))
    (qmul (cf (2 * (r + 1))) (qmul (cP (2 * (r + 1))).1 (qnat (fact (2 * (r + 1))))))) (hp (r + 1)) = X at *
  generalize qmul (qadd (qmul (cf (2 * (r + 1))) (qmul (cP (2 * (r + 1))).2 (qnat (fact (2 * (r + 1))))))
    (qmul (cf (2 * (r + 1))) (qmul (cP (2 * (r + 1))).2 (qnat (fact (2 * (r + 1))))))) (hp (r + 1)) = Y at *
  generalize qmul (qadd (cP (2 * (r + 1))).1 (cP (2 * (r + 1))).1) (hp (r + 1)) = X' at *
  generalize qmul (qadd (cP (2 * (r + 1))).2 (cP (2 * (r + 1))).2) (hp (r + 1)) = Y' at *
  generalize ssum n e p i m cs = S at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZJetClose

#print axioms ZJetClose.cl_sq
#print axioms ZJetClose.divS
#print axioms ZJetClose.st_tanAll
#print axioms ZJetClose.sqrt_close
#print axioms ZJetClose.one_sq_box
#print axioms ZJetClose.cread_good
#print axioms ZJetClose.ev_order
#print axioms ZJetClose.taylorN_kernel
