import ZExpAdd2

/-!
# ZPowTaylor — Taylor's bound for a monomial, exactly. Zero axioms.

The interval path of `zseries` reads f on [m − r, m + r] as f(m) ± |f'(m)|·r + D2·r²/2, D2 = Σ |c_k| e_k (e_k − 1)
R^(e_k − 2). Its core is one inequality per term, proved here with no calculus, for x, m with |x|, |m| ≤ R:

    T_e(x, m) = x^e − m^e − e·m^(e−1)·(x − m)        |T_e| ≤ Bd_e · (x − m)²,   Bd_0 = 0, Bd_{e+1} = R·Bd_e + e·R^(e−1)

(`taylor_mono`), from the recursion `T_{e+1} = x·T_e + e·m^(e−1)·(x − m)²` (`T_succ`). Bd_e is e(e−1)/2·R^(e−2), the
code's term over 2 (checked in the stand). `taylor_sum`: for a partial sum P_N = Σ c_k x^{e_k} with |c_k| ≤ a_k,
|P_N(x) − P_N(m) − P'_N(m)(x − m)| ≤ (Σ a_k Bd_{e_k}(R))·(x − m)² — for every N, so for the limit wherever it exists.
-/

namespace ZPowTaylor
open VR VR.Numbers ZExp ZExpAdd2

def pw (x : QExpr) : Nat → QExpr
  | 0 => qone
  | n + 1 => qmul x (pw x n)

/-- e·m^(e−1), written without subtraction. -/
def Dm (m : QExpr) : Nat → QExpr
  | 0 => qzero
  | e + 1 => qmul (qnat (e + 1)) (pw m e)

def T (x m : QExpr) (e : Nat) : QExpr := qsub (qsub (pw x e) (pw m e)) (qmul (Dm m e) (qsub x m))

theorem m_Dm (m : QExpr) : ∀ e, qEq (qmul m (Dm m e)) (qmul (qnat e) (pw m e))
  | 0 => by show qEq (qmul m qzero) (qmul (qnat 0) qone); refine qEq_trans ?_ (qmul_respects (qEq_symm qnat_zero) (qEq_refl _)); q_ring
  | e + 1 => by show qEq (qmul m (qmul (qnat (e + 1)) (pw m e))) (qmul (qnat (e + 1)) (qmul m (pw m e))); q_ring

/-- THE RECURSION. -/
theorem T_succ (x m : QExpr) (e : Nat) :
    qEq (T x m (e + 1)) (qadd (qmul x (T x m e)) (qmul (Dm m e) (qmul (qsub x m) (qsub x m)))) := by
  have s1 : qEq (T x m (e + 1)) (qsub (qsub (qmul x (pw x e)) (qmul m (pw m e)))
      (qmul (qmul (qadd (qnat e) qone) (pw m e)) (qsub x m))) := by
    show qEq (qsub (qsub (qmul x (pw x e)) (qmul m (pw m e))) (qmul (qmul (qnat (e + 1)) (pw m e)) (qsub x m))) _
    exact qadd_respects (qEq_refl _) (qneg_respects (qmul_respects (qmul_respects (qnat_succ e) (qEq_refl _)) (qEq_refl _)))
  have s2 : qEq (qsub (qsub (qmul x (pw x e)) (qmul m (pw m e))) (qmul (qmul (qadd (qnat e) qone) (pw m e)) (qsub x m)))
      (qsub (qsub (qmul x (pw x e)) (qmul x (pw m e))) (qmul (qmul (qnat e) (pw m e)) (qsub x m))) := by
    unfold qsub; q_ring
  have s3 : qEq (qsub (qsub (qmul x (pw x e)) (qmul x (pw m e))) (qmul (qmul (qnat e) (pw m e)) (qsub x m)))
      (qsub (qsub (qmul x (pw x e)) (qmul x (pw m e))) (qmul (qmul m (Dm m e)) (qsub x m))) :=
    qadd_respects (qEq_refl _) (qneg_respects (qmul_respects (qEq_symm (m_Dm m e)) (qEq_refl _)))
  have s4 : qEq (qsub (qsub (qmul x (pw x e)) (qmul x (pw m e))) (qmul (qmul m (Dm m e)) (qsub x m)))
      (qadd (qmul x (T x m e)) (qmul (Dm m e) (qmul (qsub x m) (qsub x m)))) := by
    unfold T qsub; q_ring
  exact qEq_trans s1 (qEq_trans s2 (qEq_trans s3 s4))

/-! ## The bounds -/

def DR (R : QExpr) : Nat → QExpr
  | 0 => qzero
  | e + 1 => qmul (qnat (e + 1)) (pw R e)

def Bd (R : QExpr) : Nat → QExpr
  | 0 => qzero
  | e + 1 => qadd (qmul R (Bd R e)) (DR R e)

theorem close_zero_self {a : QExpr} (h : qle qzero a) : qclose a qzero a := by
  constructor <;> (unfold qsub; rat_linarith)

theorem pw_bound {m R : QExpr} (hm : qclose m qzero R) : ∀ e, qclose (pw m e) qzero (pw R e)
  | 0 => by
      show qclose qone qzero qone
      exact close_zero_self (qle_of_qlt (by
        have := qnat_succ_pos 0
        exact qlt_respects (qnat_zero |> fun h => qEq_refl _) (by
          refine qEq_trans (qnat_succ 0) ?_; refine qEq_trans (qadd_respects qnat_zero (qEq_refl _)) ?_; q_ring) this))
  | e + 1 => qmul_abs_bound hm (pw_bound hm e)

theorem Dm_bound {m R : QExpr} (hm : qclose m qzero R) : ∀ e, qclose (Dm m e) qzero (DR R e)
  | 0 => qclose_refl _ _ (qle_refl _)
  | e + 1 => qmul_abs_bound (close_zero_self (qnat_nonneg (e + 1))) (pw_bound hm e)

/-- **TAYLOR FOR A MONOMIAL**: |x^e − m^e − e·m^(e−1)(x − m)| ≤ Bd_e·(x − m)², |x|, |m| ≤ R. -/
theorem taylor_mono {x m R : QExpr} (hx : qclose x qzero R) (hm : qclose m qzero R) :
    ∀ e, qclose (T x m e) qzero (qmul (Bd R e) (qmul (qsub x m) (qsub x m)))
  | 0 => by
      have e0 : qEq (T x m 0) qzero := by show qEq (qsub (qsub qone qone) (qmul qzero (qsub x m))) qzero; unfold qsub; q_ring
      have e1 : qEq (qmul (Bd R 0) (qmul (qsub x m) (qsub x m))) qzero := by
        show qEq (qmul qzero (qmul (qsub x m) (qsub x m))) qzero; q_ring
      exact qclose_respects (qEq_symm e0) (qEq_refl _) (qEq_symm e1) (qclose_refl _ _ (qle_refl _))
  | e + 1 => by
      have ih := taylor_mono hx hm e
      have p1 := qmul_abs_bound hx ih
      have hsq : qclose (qmul (qsub x m) (qsub x m)) qzero (qmul (qsub x m) (qsub x m)) :=
        close_zero_self (qmul_self_nonneg _)
      have p2 := qmul_abs_bound (Dm_bound hm e) hsq
      have hs := T_succ x m e
      obtain ⟨a1, a2⟩ := p1
      obtain ⟨b1, b2⟩ := p2
      have eB : qEq (qmul (Bd R (e + 1)) (qmul (qsub x m) (qsub x m)))
          (qadd (qmul R (qmul (Bd R e) (qmul (qsub x m) (qsub x m)))) (qmul (DR R e) (qmul (qsub x m) (qsub x m)))) := by
        show qEq (qmul (qadd (qmul R (Bd R e)) (DR R e)) (qmul (qsub x m) (qsub x m))) _
        q_ring
      constructor <;> (unfold qsub at *; rat_linarith)

/-! ## A power series' partial sum: P_N(x) − P_N(m) − P'_N(m)(x − m) = Σ c_k T_{e_k}, bounded termwise -/

/-- Σ_{k<N} c_k·x^{e_k}, and its termwise derivative at m. -/
def P (c : Nat → QExpr) (e : Nat → Nat) (x : QExpr) (N : Nat) : QExpr := sumTo (fun k => qmul (c k) (pw x (e k))) N
def P' (c : Nat → QExpr) (e : Nat → Nat) (m : QExpr) (N : Nat) : QExpr := sumTo (fun k => qmul (c k) (Dm m (e k))) N
/-- The bound's coefficient: Σ_{k<N} |c_k|·Bd_{e_k}(R). -/
def Q (a : Nat → QExpr) (e : Nat → Nat) (R : QExpr) (N : Nat) : QExpr := sumTo (fun k => qmul (a k) (Bd R (e k))) N

theorem taylor_sum (c a : Nat → QExpr) (e : Nat → Nat) {x m R : QExpr} (hx : qclose x qzero R) (hm : qclose m qzero R)
    (hca : ∀ k, qclose (c k) qzero (a k)) : ∀ N,
    qclose (qsub (qsub (P c e x N) (P c e m N)) (qmul (P' c e m N) (qsub x m))) qzero
      (qmul (Q a e R N) (qmul (qsub x m) (qsub x m)))
  | 0 => by
      have e0 : qEq (qsub (qsub (P c e x 0) (P c e m 0)) (qmul (P' c e m 0) (qsub x m))) qzero := by
        show qEq (qsub (qsub qzero qzero) (qmul qzero (qsub x m))) qzero; unfold qsub; q_ring
      have e1 : qEq (qmul (Q a e R 0) (qmul (qsub x m) (qsub x m))) qzero := by
        show qEq (qmul qzero (qmul (qsub x m) (qsub x m))) qzero; q_ring
      exact qclose_respects (qEq_symm e0) (qEq_refl _) (qEq_symm e1) (qclose_refl _ _ (qle_refl _))
  | N + 1 => by
      have ih := taylor_sum c a e hx hm hca N
      have hT := qmul_abs_bound (hca N) (taylor_mono hx hm (e N))
      have hs : qEq (qsub (qsub (P c e x (N + 1)) (P c e m (N + 1))) (qmul (P' c e m (N + 1)) (qsub x m)))
          (qadd (qsub (qsub (P c e x N) (P c e m N)) (qmul (P' c e m N) (qsub x m))) (qmul (c N) (T x m (e N)))) := by
        show qEq (qsub (qsub (qadd (P c e x N) (qmul (c N) (pw x (e N)))) (qadd (P c e m N) (qmul (c N) (pw m (e N)))))
          (qmul (qadd (P' c e m N) (qmul (c N) (Dm m (e N)))) (qsub x m))) _
        unfold T qsub; q_ring
      have hb : qEq (qmul (Q a e R (N + 1)) (qmul (qsub x m) (qsub x m)))
          (qadd (qmul (Q a e R N) (qmul (qsub x m) (qsub x m))) (qmul (a N) (qmul (Bd R (e N)) (qmul (qsub x m) (qsub x m))))) := by
        show qEq (qmul (qadd (Q a e R N) (qmul (a N) (Bd R (e N)))) (qmul (qsub x m) (qsub x m))) _
        q_ring
      obtain ⟨a1, a2⟩ := ih
      obtain ⟨b1, b2⟩ := hT
      constructor <;> (unfold qsub at *; rat_linarith)

/-! ## The positive series' tail (`zseries._abs_series_bound`) -/

/-- Positive terms halving from k on: every partial tail Σ_{k<j≤k+d} a_j stays below a_k
(the code adds a_k once more for the whole tail). -/
theorem tail_halving (a : Nat → QExpr) (k : Nat) (ha : ∀ j, qle qzero (a j))
    (hh : ∀ j, k ≤ j → qle (qadd (a (j + 1)) (a (j + 1))) (a j)) :
    ∀ d, qle (sumTo (fun i => a (k + 1 + i)) d) (a k) := by
  -- stronger: the partial tail plus twice the last-but-one term... by induction with the bound a_k − a_{k+d}
  have key : ∀ d, qle (qadd (sumTo (fun i => a (k + 1 + i)) d) (a (k + d))) (a k) := by
    intro d
    induction d with
    | zero => show qle (qadd qzero (a (k + 0))) (a k); exact qle_of_qEq (by rw [Nat.add_zero]; q_ring)
    | succ d ih =>
        have h1 := hh (k + d) (Nat.le_add_right k d)
        show qle (qadd (qadd (sumTo (fun i => a (k + 1 + i)) d) (a (k + 1 + d))) (a (k + (d + 1)))) (a k)
        have e1 : k + 1 + d = k + d + 1 := by rw [Nat.add_right_comm]
        have e2 : k + (d + 1) = k + d + 1 := by rw [Nat.add_succ]
        rw [e1, e2]
        rat_linarith
  intro d
  have := key d
  have := ha (k + d)
  rat_linarith

end ZPowTaylor

#print axioms ZPowTaylor.m_Dm
#print axioms ZPowTaylor.T_succ
#print axioms ZPowTaylor.close_zero_self
#print axioms ZPowTaylor.pw_bound
#print axioms ZPowTaylor.Dm_bound
#print axioms ZPowTaylor.taylor_mono
#print axioms ZPowTaylor.taylor_sum
#print axioms ZPowTaylor.tail_halving
