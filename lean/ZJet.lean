import ZTaylorLeaf

/-!
# ZJet — the jets of the symbolic derivative; the kernel's Taylor recurrences, exactly. Zero axioms.

Layer 3 of the higher Taylor orders. `J e k = (D^k e)(p)/k!` at the index `n` — the `k`-th Taylor coefficient as the
grammar's own derivative computes it. `zcertify.taylor_coeffs` computes the same coefficients by recurrences along
the graph; here, node by node, the jets satisfy those recurrences exactly:

  * `J_D` — `Dsh (J e) = J (D e)` (`(k+1)·J_{k+1}(e) = J_k(De)`);
  * `J_const`, `J_var`, `J_free` — a constant series, `(x, 1, 0, …)`, a node without `x` is a constant;
  * `J_add`, `J_sub` — termwise; `J_mul` — the convolution (Leibniz);
  * `J_exp` — `Dsh E = E ∗ Dsh A` (`k·e_k = Σ i·a_i·e_{k−i}`); `J_sin`, `J_cos` — the coupled pair;
  * `J_div` — `Q ∗ V = U` (`q_k = (a_k − Σ_{i≥1} b_i q_{k−i})/b₀`), `v(p) ≠ 0`, by multiplying by `V` and cancelling;
  * `J_tan` — `T ∗ C = S` (the kernel reads tan as sin/cos), `cos u(p) ≠ 0`, by uniqueness of a linear jet
    equation (`ode_zero`);
  * `J_sqrt` — `(S ∗ S)_{k+1} = U_{k+1}` (`√u(p) ≠ 0`; the value itself is a reading — the grid root squares to `u`
    only up to its gap);
  * `J_pow_succ` — `J(u^{m+1}) = J(u) ∗ J(u^m)`; `J_miller` — `A ∗ Dsh P = m·P ∗ Dsh A`, Miller's
    `k·a₀·p_k = Σ_{i<k} (m(k−i) − i)·a_{k−i}·p_i`.

The convolution's algebra on the way: commutative, associative (through `Dsh`), the unit `(1, 0, …)`, cancellation
by a series with a nonzero head. Not covered: ln, log10, atan, a non-natural exponent.
-/

namespace ZJet

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN

/-- The jet: `J e k = (D^k e)(p)/k!` at the index `n`. -/
def J (i n : Nat) (p : Point QExpr) (e : G) (k : Nat) : QExpr := qmul (evalN n p (Diter i k e)) (cf k)

theorem J_D (i n : Nat) (p : Point QExpr) (e : G) (k : Nat) : qEq (ZTrig.Dsh (J i n p e) k) (J i n p (D i e) k) := by
  have c := cf_succ k
  show qEq (qmul (qnat (k + 1)) (qmul (evalN n p (Diter i k (D i e))) (cf (k + 1)))) (qmul (evalN n p (Diter i k (D i e))) (cf k))
  have r : qEq (qmul (qnat (k + 1)) (qmul (evalN n p (Diter i k (D i e))) (cf (k + 1))))
      (qmul (evalN n p (Diter i k (D i e))) (qmul (qnat (k + 1)) (cf (k + 1)))) := by rat_ring
  exact qEq_trans r (qmul_respects (qEq_refl _) c)

theorem Diter_add (i : Nat) : ∀ k (u v : G), Diter i k (.add u v) = .add (Diter i k u) (Diter i k v)
  | 0, _, _ => rfl
  | k + 1, u, v => Diter_add i k (D i u) (D i v)

theorem Diter_sub (i : Nat) : ∀ k (u v : G), Diter i k (.sub u v) = .sub (Diter i k u) (Diter i k v)
  | 0, _, _ => rfl
  | k + 1, u, v => Diter_sub i k (D i u) (D i v)

theorem J_add (i n : Nat) (p : Point QExpr) (u v : G) (k : Nat) :
    qEq (J i n p (.add u v) k) (qadd (J i n p u k) (J i n p v k)) := by
  unfold J; rw [Diter_add]
  show qEq (qmul (qadd (evalN n p (Diter i k u)) (evalN n p (Diter i k v))) (cf k)) _; rat_ring

theorem J_sub (i n : Nat) (p : Point QExpr) (u v : G) (k : Nat) :
    qEq (J i n p (.sub u v) k) (qsub (J i n p u k) (J i n p v k)) := by
  unfold J; rw [Diter_sub]
  show qEq (qmul (qsub (evalN n p (Diter i k u)) (evalN n p (Diter i k v))) (cf k)) _; unfold qsub; rat_ring

/-- Cancelling a positive natural factor from an equation. -/
theorem cancel_succ {X Y : QExpr} (k : Nat) (h : qEq (qmul (qnat (k + 1)) X) (qmul (qnat (k + 1)) Y)) : qEq X Y := by
  have c := qmul_inv'_cancel (qnat_ne_zero k)
  have e1 := qmul_respects (qEq_refl (qinv' (qnat (k + 1)))) h
  have r1 : qEq (qmul (qinv' (qnat (k + 1))) (qmul (qnat (k + 1)) X)) (qmul X (qmul (qnat (k + 1)) (qinv' (qnat (k + 1))))) := by rat_ring
  have r2 : qEq (qmul (qinv' (qnat (k + 1))) (qmul (qnat (k + 1)) Y)) (qmul Y (qmul (qnat (k + 1)) (qinv' (qnat (k + 1))))) := by rat_ring
  have s1 := qmul_respects (qEq_refl X) c
  have s2 := qmul_respects (qEq_refl Y) c
  have o1 : qEq (qmul X qone) X := by rat_ring
  have o2 : qEq (qmul Y qone) Y := by rat_ring
  exact qEq_trans (qEq_symm o1) (qEq_trans (qEq_symm s1) (qEq_trans (qEq_symm r1) (qEq_trans e1 (qEq_trans r2 (qEq_trans s2 o2)))))

/-- THE PRODUCT'S JET IS THE CONVOLUTION (Leibniz, from the symbolic derivative). -/
theorem J_mul (i n : Nat) (p : Point QExpr) : ∀ k (u v : G), qEq (J i n p (.mul u v) k) (ZTrig.cv (J i n p u) (J i n p v) k)
  | 0, u, v => by
      have c0 := cf_zero
      show qEq (qmul (qmul (evalN n p u) (evalN n p v)) (cf 0)) (qmul (qmul (evalN n p u) (cf 0)) (qmul (evalN n p v) (cf 0)))
      have r := qmul_respects (qEq_refl (qmul (evalN n p u) (evalN n p v))) c0
      have r' := qmul_respects (qmul_respects (qEq_refl (evalN n p u)) c0) (qmul_respects (qEq_refl (evalN n p v)) c0)
      exact qEq_trans r (qEq_trans (by rat_ring) (qEq_symm r'))
  | k + 1, u, v => by
      apply cancel_succ k
      -- (k+1)·J(uv)_{k+1} = J(D(uv))_k = J(Du·v)_k + J(u·Dv)_k
      have d := J_D i n p (.mul u v) k
      have a := J_add i n p (.mul (D i u) v) (.mul u (D i v)) k
      have m1 := J_mul i n p k (D i u) v
      have m2 := J_mul i n p k u (D i v)
      have c1 := ZTrig.cv_congr k (ZTrig.Dsh (J i n p u)) (J i n p (D i u)) (J i n p v) (J i n p v) (J_D i n p u) (fun _ => qEq_refl _)
      have c2 := ZTrig.cv_congr k (J i n p u) (J i n p u) (ZTrig.Dsh (J i n p v)) (J i n p (D i v)) (fun _ => qEq_refl _) (J_D i n p v)
      have lb := ZTrig.leibniz (J i n p v) k (J i n p u)
      show qEq (qmul (qnat (k + 1)) (J i n p (.mul u v) (k + 1))) _
      have dd : qEq (ZTrig.Dsh (J i n p (.mul u v)) k) (qmul (qnat (k + 1)) (J i n p (.mul u v) (k + 1))) := qEq_refl _
      have e : qEq (J i n p (D i (.mul u v)) k) (J i n p (.add (.mul (D i u) v) (.mul u (D i v))) k) := qEq_refl _
      generalize ZTrig.Dsh (J i n p (.mul u v)) k = A at *
      generalize qmul (qnat (k + 1)) (J i n p (.mul u v) (k + 1)) = A' at *
      generalize J i n p (D i (.mul u v)) k = B at *
      generalize J i n p (.add (.mul (D i u) v) (.mul u (D i v))) k = B' at *
      generalize J i n p (.mul (D i u) v) k = C1 at *
      generalize J i n p (.mul u (D i v)) k = C2 at *
      generalize ZTrig.cv (J i n p (D i u)) (J i n p v) k = E1 at *
      generalize ZTrig.cv (J i n p u) (J i n p (D i v)) k = E2 at *
      generalize ZTrig.cv (ZTrig.Dsh (J i n p u)) (J i n p v) k = F1 at *
      generalize ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p v)) k = F2 at *
      generalize qmul (qnat (k + 1)) (ZTrig.cv (J i n p u) (J i n p v) (k + 1)) = W at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem Diter_free (i n : Nat) (p : Point QExpr) : ∀ k (e : G), ¬ Uses e i → qEq (evalN n p (Diter i k (D i e))) qzero
  | 0, e, h => (D_free i n p e h).1
  | k + 1, e, h => Diter_free i n p k (D i e) (D_free i n p e h).2

/-- THE KERNEL'S CONSTANT: a node without `x_i` has the jet `(value, 0, 0, …)`. -/
theorem J_free (i n : Nat) (p : Point QExpr) (e : G) (h : ¬ Uses e i) :
    qEq (J i n p e 0) (evalN n p e) ∧ ∀ k, qEq (J i n p e (k + 1)) qzero := by
  refine ⟨?_, fun k => ?_⟩
  · show qEq (qmul (evalN n p e) (cf 0)) (evalN n p e)
    exact qEq_trans (qmul_respects (qEq_refl _) cf_zero) (by rat_ring)
  show qEq (qmul (evalN n p (Diter i k (D i e))) (cf (k + 1))) qzero
  exact z_mul_l (Diter_free i n p k e h)

/-- The variable `x_i`: the jet `(x, 1, 0, 0, …)`. -/
theorem J_var (i n : Nat) (p : Point QExpr) :
    qEq (J i n p (.var i) 0) (p i) ∧ qEq (J i n p (.var i) 1) qone ∧ ∀ k, qEq (J i n p (.var i) (k + 2)) qzero := by
  refine ⟨?_, ?_, fun k => ?_⟩
  · show qEq (qmul (p i) (cf 0)) (p i)
    exact qEq_trans (qmul_respects (qEq_refl _) cf_zero) (by rat_ring)
  · show qEq (qmul (dvar i i) (cf 1)) qone
    rw [dvar_eq]
    have c := cf_succ 0
    have n1 : qEq (qnat (0 + 1)) qone := qEq_trans (qnat_succ 0) (by have := qnat_zero; exact qle_antisymm (by rat_linarith) (by rat_linarith))
    have r := qmul_respects n1 (qEq_refl (cf 1))
    have o : qEq (qmul qone (cf 1)) (cf 1) := by rat_ring
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm o) (qEq_trans (qEq_symm r) (qEq_trans c cf_zero)))
  · show qEq (qmul (evalN n p (Diter i k (D i (D i (.var i))))) (cf (k + 2))) qzero
    exact z_mul_l (Diter_free i n p k (D i (.var i)) (fun h => h))

/-- EXP: `Dsh J(e^u) = J(e^u) ∗ Dsh J(u)` — the kernel's `k·e_k = Σ i·a_i·e_{k−i}`. -/
theorem J_exp (i n : Nat) (p : Point QExpr) (u : G) (k : Nat) :
    qEq (ZTrig.Dsh (J i n p (.exp u)) k) (ZTrig.cv (J i n p (.exp u)) (ZTrig.Dsh (J i n p u)) k) :=
  qEq_trans (J_D i n p (.exp u) k) (qEq_trans (J_mul i n p k (.exp u) (D i u))
    (ZTrig.cv_congr k _ _ _ _ (fun _ => qEq_refl _) (fun j => qEq_symm (J_D i n p u j))))

/-- SIN: `Dsh J(sin u) = J(cos u) ∗ Dsh J(u)`. -/
theorem J_sin (i n : Nat) (p : Point QExpr) (u : G) (k : Nat) :
    qEq (ZTrig.Dsh (J i n p (.sin u)) k) (ZTrig.cv (J i n p (.cos u)) (ZTrig.Dsh (J i n p u)) k) :=
  qEq_trans (J_D i n p (.sin u) k) (qEq_trans (J_mul i n p k (.cos u) (D i u))
    (ZTrig.cv_congr k _ _ _ _ (fun _ => qEq_refl _) (fun j => qEq_symm (J_D i n p u j))))

/-- COS: `Dsh J(cos u) = (−J(sin u)) ∗ Dsh J(u)`. -/
theorem J_cos (i n : Nat) (p : Point QExpr) (u : G) (k : Nat) :
    qEq (ZTrig.Dsh (J i n p (.cos u)) k) (ZTrig.cv (fun j => qneg (J i n p (.sin u) j)) (ZTrig.Dsh (J i n p u)) k) := by
  have a := qEq_trans (J_D i n p (.cos u) k) (J_mul i n p k (.sub (.const qzero) (.sin u)) (D i u))
  refine qEq_trans a (ZTrig.cv_congr k _ _ _ _ (fun j => ?_) (fun j => qEq_symm (J_D i n p u j)))
  have s := J_sub i n p (.const qzero) (.sin u) j
  have z : qEq (J i n p (.const qzero) j) qzero := by
    cases j with
    | zero => exact (J_free i n p (.const qzero) (fun h => h)).1
    | succ j => exact (J_free i n p (.const qzero) (fun h => h)).2 j
  refine qEq_trans s ?_
  unfold qsub; exact qEq_trans (qadd_respects z (qEq_refl _)) (by rat_ring)

/-! ## The convolution's algebra -/

theorem cv_comm : ∀ (m : Nat) (F G : Nat → QExpr), qEq (ZTrig.cv F G m) (ZTrig.cv G F m)
  | 0, F, G => by show qEq (qmul (F 0) (G 0)) (qmul (G 0) (F 0)); rat_ring
  | m + 1, F, G => by
      have ih := cv_comm m (fun i => F (i + 1)) G
      have sh := ZTrig.cv_shiftG m G F
      show qEq (qadd (qmul (F 0) (G (m + 1))) (ZTrig.cv (fun i => F (i + 1)) G m)) _
      generalize ZTrig.cv (fun i => F (i + 1)) G m = A at *
      generalize ZTrig.cv G (fun i => F (i + 1)) m = A' at *
      generalize ZTrig.cv G F (m + 1) = B at *
      have c : qEq (qmul (F 0) (G (m + 1))) (qmul (G (m + 1)) (F 0)) := by rat_ring
      generalize qmul (F 0) (G (m + 1)) = P at *; generalize qmul (G (m + 1)) (F 0) = P' at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem cv_addG (m : Nat) (F G G' : Nat → QExpr) :
    qEq (ZTrig.cv F (fun i => qadd (G i) (G' i)) m) (qadd (ZTrig.cv F G m) (ZTrig.cv F G' m)) :=
  qEq_trans (cv_comm m _ _) (qEq_trans (ZTrig.cv_addF m G G' F) (qadd_respects (cv_comm m _ _) (cv_comm m _ _)))

/-- Only the terms up to `m` matter. -/
theorem cv_congr_upto : ∀ (m : Nat) (F F' G : Nat → QExpr), (∀ j, j ≤ m → qEq (F j) (F' j)) →
    qEq (ZTrig.cv F G m) (ZTrig.cv F' G m)
  | 0, F, F', G, h => qmul_respects (h 0 (Nat.le_refl 0)) (qEq_refl _)
  | m + 1, F, F', G, h =>
      qadd_respects (qmul_respects (h 0 (Nat.zero_le _)) (qEq_refl _))
        (cv_congr_upto m (fun i => F (i + 1)) (fun i => F' (i + 1)) G (fun j hj => h (j + 1) (Nat.succ_le_succ hj)))

theorem cv_congr_uptoG (m : Nat) (F G G' : Nat → QExpr) (h : ∀ j, j ≤ m → qEq (G j) (G' j)) :
    qEq (ZTrig.cv F G m) (ZTrig.cv F G' m) :=
  qEq_trans (cv_comm m _ _) (qEq_trans (cv_congr_upto m G G' F h) (cv_comm m _ _))

/-- `Dsh` of a convolution, pointwise: `Dsh (F ∗ G) = Dsh F ∗ G + F ∗ Dsh G`. -/
theorem Dsh_cv (F G : Nat → QExpr) (m : Nat) :
    qEq (ZTrig.Dsh (ZTrig.cv F G) m) (qadd (ZTrig.cv (ZTrig.Dsh F) G m) (ZTrig.cv F (ZTrig.Dsh G) m)) :=
  qEq_symm (ZTrig.leibniz G m F)

/-- ASSOCIATIVITY, through `Dsh` (Leibniz twice). -/
theorem cv_assoc : ∀ (m : Nat) (F G H : Nat → QExpr),
    qEq (ZTrig.cv (ZTrig.cv F G) H m) (ZTrig.cv F (ZTrig.cv G H) m)
  | 0, F, G, H => by
      show qEq (qmul (qmul (F 0) (G 0)) (H 0)) (qmul (F 0) (qmul (G 0) (H 0))); rat_ring
  | m + 1, F, G, H => by
      apply cancel_succ m
      -- (m+1)·LHS(m+1) = Dsh(cv F G) ∗ H + cv F G ∗ Dsh H
      have l1 := ZTrig.leibniz H m (ZTrig.cv F G)
      have l2 := ZTrig.leibniz (ZTrig.cv G H) m F
      have d1 := ZTrig.cv_congr m (ZTrig.Dsh (ZTrig.cv F G)) (fun j => qadd (ZTrig.cv (ZTrig.Dsh F) G j) (ZTrig.cv F (ZTrig.Dsh G) j))
        H H (fun j => Dsh_cv F G j) (fun _ => qEq_refl _)
      have d2 := ZTrig.cv_addF m (ZTrig.cv (ZTrig.Dsh F) G) (ZTrig.cv F (ZTrig.Dsh G)) H
      have a1 := cv_assoc m (ZTrig.Dsh F) G H
      have a2 := cv_assoc m F (ZTrig.Dsh G) H
      have a3 := cv_assoc m F G (ZTrig.Dsh H)
      have d3 := ZTrig.cv_congr m F F (ZTrig.Dsh (ZTrig.cv G H)) (fun j => qadd (ZTrig.cv (ZTrig.Dsh G) H j) (ZTrig.cv G (ZTrig.Dsh H) j))
        (fun _ => qEq_refl _) (fun j => Dsh_cv G H j)
      have d4 := cv_addG m F (ZTrig.cv (ZTrig.Dsh G) H) (ZTrig.cv G (ZTrig.Dsh H))
      generalize ZTrig.cv (ZTrig.Dsh (ZTrig.cv F G)) H m = X1 at *
      generalize ZTrig.cv (ZTrig.cv F G) (ZTrig.Dsh H) m = X2 at *
      generalize qmul (qnat (m + 1)) (ZTrig.cv (ZTrig.cv F G) H (m + 1)) = L at *
      generalize ZTrig.cv (ZTrig.Dsh F) (ZTrig.cv G H) m = Y1 at *
      generalize ZTrig.cv F (ZTrig.Dsh (ZTrig.cv G H)) m = Y2 at *
      generalize qmul (qnat (m + 1)) (ZTrig.cv F (ZTrig.cv G H) (m + 1)) = R at *
      generalize ZTrig.cv (fun j => qadd (ZTrig.cv (ZTrig.Dsh F) G j) (ZTrig.cv F (ZTrig.Dsh G) j)) H m = Z1 at *
      generalize ZTrig.cv (ZTrig.cv (ZTrig.Dsh F) G) H m = Z2 at *
      generalize ZTrig.cv (ZTrig.cv F (ZTrig.Dsh G)) H m = Z3 at *
      generalize ZTrig.cv (ZTrig.Dsh F) (ZTrig.cv G H) m = Z4 at *
      generalize ZTrig.cv F (ZTrig.cv (ZTrig.Dsh G) H) m = Z5 at *
      generalize ZTrig.cv F (ZTrig.cv G (ZTrig.Dsh H)) m = Z6 at *
      generalize ZTrig.cv F (fun j => qadd (ZTrig.cv (ZTrig.Dsh G) H j) (ZTrig.cv G (ZTrig.Dsh H) j)) m = Z7 at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The unit `(1, 0, 0, …)`. -/
def unitS (k : Nat) : QExpr := match k with
  | 0 => qone
  | _ + 1 => qzero

theorem cv_unit : ∀ (m : Nat) (F : Nat → QExpr), qEq (ZTrig.cv unitS F m) (F m)
  | 0, F => by show qEq (qmul qone (F 0)) (F 0); rat_ring
  | m + 1, F => by
      show qEq (qadd (qmul qone (F (m + 1))) (ZTrig.cv (fun i => unitS (i + 1)) F m)) (F (m + 1))
      have z : ∀ j, qEq (unitS (j + 1)) (qmul qzero (unitS j)) := fun j => by show qEq qzero _; rat_ring
      have c := ZTrig.cv_congr m (fun i => unitS (i + 1)) (fun i => qmul qzero (unitS i)) F F z (fun _ => qEq_refl _)
      have s := ZTrig.cv_scaleF qzero m unitS F
      have o : qEq (qmul qzero (ZTrig.cv unitS F m)) qzero := by rat_ring
      have o2 : qEq (qmul qone (F (m + 1))) (F (m + 1)) := by rat_ring
      generalize ZTrig.cv (fun i => unitS (i + 1)) F m = A at *
      generalize ZTrig.cv (fun i => qmul qzero (unitS i)) F m = A' at *
      generalize qmul qzero (ZTrig.cv unitS F m) = B at *
      generalize qmul qone (F (m + 1)) = C at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- CANCELLATION: `Z ∗ G = 0` up to `k`, `G₀ ≠ 0` ⇒ `Z = 0` up to `k`. -/
theorem cv_cancel {Z G : Nat → QExpr} (hG : ¬ qEq (G 0) qzero) :
    ∀ k, (∀ j, j ≤ k → qEq (ZTrig.cv Z G j) qzero) → ∀ j, j ≤ k → qEq (Z j) qzero
  | 0, h, j, hj => by
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      have e : qEq (qmul (Z 0) (G 0)) qzero := h 0 (Nat.le_refl 0)
      have c := qmul_inv'_cancel hG
      have r : qEq (Z 0) (qmul (qmul (Z 0) (G 0)) (qinv' (G 0))) := by
        have := qmul_respects (qEq_refl (Z 0)) c
        exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
      exact qEq_trans r (qEq_trans (qmul_respects e (qEq_refl _)) (by rat_ring))
  | k + 1, h, j, hj => by
      have ih := cv_cancel hG k (fun j' hj' => h j' (Nat.le_trans hj' (Nat.le_succ k)))
      cases Nat.lt_or_eq_of_le hj with
      | inl l => exact ih j (Nat.le_of_lt_succ l)
      | inr e =>
        subst e
        have sh := ZTrig.cv_shiftG k Z G
        have z1 : qEq (ZTrig.cv Z (fun j => G (j + 1)) k) (ZTrig.cv (fun _ => qzero) (fun j => G (j + 1)) k) :=
          cv_congr_upto k Z (fun _ => qzero) _ ih
        have z2 : qEq (ZTrig.cv (fun _ => qzero) (fun j => G (j + 1)) k) qzero := by
          have := ZTrig.cv_scaleF qzero k (fun _ => qzero) (fun j => G (j + 1))
          have c := ZTrig.cv_congr k (fun _ => qzero) (fun i => qmul qzero ((fun _ => qzero) i)) (fun j => G (j + 1)) (fun j => G (j + 1))
            (fun _ => by show qEq qzero (qmul qzero qzero); rat_ring) (fun _ => qEq_refl _)
          exact qEq_trans c (qEq_trans this (by rat_ring))
        have hk := h (k + 1) (Nat.le_refl _)
        have e2 : qEq (qmul (Z (k + 1)) (G 0)) qzero := by
          generalize ZTrig.cv Z (fun j => G (j + 1)) k = A at *
          generalize ZTrig.cv (fun _ => qzero) (fun j => G (j + 1)) k = A' at *
          generalize ZTrig.cv Z G (k + 1) = B at *
          generalize qmul (Z (k + 1)) (G 0) = P at *
          exact qle_antisymm (by rat_linarith) (by rat_linarith)
        have c := qmul_inv'_cancel hG
        have r : qEq (Z (k + 1)) (qmul (qmul (Z (k + 1)) (G 0)) (qinv' (G 0))) := by
          have := qmul_respects (qEq_refl (Z (k + 1))) c
          exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
        exact qEq_trans r (qEq_trans (qmul_respects e2 (qEq_refl _)) (by rat_ring))

/-! ## The quotient -/

theorem J_zero (i n : Nat) (p : Point QExpr) (e : G) : qEq (J i n p e 0) (evalN n p e) := by
  show qEq (qmul (evalN n p e) (cf 0)) _
  exact qEq_trans (qmul_respects (qEq_refl _) cf_zero) (by rat_ring)

theorem nz_sq {a : QExpr} (h : ¬ qEq a qzero) : ¬ qEq (qmul a a) qzero := by
  intro z
  apply h
  have c := qmul_inv'_cancel h
  have r : qEq a (qmul (qmul a a) (qinv' a)) := by
    have := qmul_respects (qEq_refl a) c
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
  exact qEq_trans r (qEq_trans (qmul_respects z (qEq_refl _)) (by rat_ring))

theorem nz_J0 (i n : Nat) (p : Point QExpr) {v : G} (h : ¬ qEq (evalN n p v) qzero) : ¬ qEq (J i n p v 0) qzero :=
  fun z => h (qEq_trans (qEq_symm (J_zero i n p v)) z)

/-- THE QUOTIENT: `J(u/v) ∗ J(v) = J(u)` — the kernel's `q_k = (a_k − Σ_{i≥1} b_i q_{k−i})/b₀`. Strong induction:
the step multiplies by `J v` and cancels it (`v(p) ≠ 0`). -/
theorem J_div (i n : Nat) (p : Point QExpr) : ∀ k (u v : G), ¬ qEq (evalN n p v) qzero →
    ∀ j, j ≤ k → qEq (ZTrig.cv (J i n p (.div u v)) (J i n p v) j) (J i n p u j)
  | 0, u, v, hv, j, hj => by
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      show qEq (qmul (J i n p (.div u v) 0) (J i n p v 0)) _
      have a := qmul_respects (J_zero i n p (.div u v)) (J_zero i n p v)
      refine qEq_trans a (qEq_trans ?_ (qEq_symm (J_zero i n p u)))
      show qEq (qmul (qmul (evalN n p u) (qinv' (evalN n p v))) (evalN n p v)) (evalN n p u)
      have c := qmul_inv'_cancel hv
      have := qmul_respects (qEq_refl (evalN n p u)) c
      exact qEq_trans (by rat_ring) (qEq_trans this (by rat_ring))
  | k + 1, u, v, hv, j, hj => by
      cases Nat.lt_or_eq_of_le hj with
      | inl l => exact J_div i n p k u v hv j (Nat.le_of_lt_succ l)
      | inr e =>
        subst e
        have hvv : ¬ qEq (evalN n p (.mul v v)) qzero := nz_sq hv
        have IA := J_div i n p k (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v) hvv
        have IB := J_div i n p k u v hv
        -- T = J(D(u/v)) ∗ V + Q ∗ J(Dv);  T ∗ V = J(Du) ∗ V up to k
        have st : ∀ j, j ≤ k → qEq (ZTrig.cv (fun t => qsub (qadd
              (ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v) t)
              (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v)) t)) (J i n p (D i u) t)) (J i n p v) j) qzero := by
          intro j hj
          have s0 := ZTrig.cv_subF j (fun t => qadd
              (ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v) t)
              (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v)) t)) (J i n p (D i u)) (J i n p v)
          have s1 := ZTrig.cv_addF j
              (ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v))
              (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v))) (J i n p v)
          have a1 := cv_assoc j (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v) (J i n p v)
          have a2 := ZTrig.cv_congr j (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v)))
              (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v)))
              (ZTrig.cv (J i n p v) (J i n p v)) (J i n p (.mul v v)) (fun _ => qEq_refl _) (fun t => qEq_symm (J_mul i n p t v v))
          have a3 := IA j hj
          have a4 := J_sub i n p (.mul (D i u) v) (.mul u (D i v)) j
          have a5 := J_mul i n p j (D i u) v
          have a6 := J_mul i n p j u (D i v)
          have b1 := cv_comm j (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v))) (J i n p v)
          have b2 := cv_assoc j (J i n p v) (J i n p (.div u v)) (J i n p (D i v))
          have b3 := ZTrig.cv_congr j (ZTrig.cv (J i n p v) (J i n p (.div u v))) (ZTrig.cv (J i n p (.div u v)) (J i n p v))
              (J i n p (D i v)) (J i n p (D i v)) (fun t => cv_comm t _ _) (fun _ => qEq_refl _)
          have b4 := cv_congr_upto j (ZTrig.cv (J i n p (.div u v)) (J i n p v)) (J i n p u) (J i n p (D i v))
              (fun t ht => IB t (Nat.le_trans ht hj))
          unfold qsub at a4
          generalize ZTrig.cv (fun t => qsub (qadd
              (ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v) t)
              (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v)) t)) (J i n p (D i u) t)) (J i n p v) j = X at *
          generalize ZTrig.cv (fun t => qadd
              (ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v) t)
              (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v)) t)) (J i n p v) j = Tv at *
          generalize ZTrig.cv (ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v)) (J i n p v) j = P1 at *
          generalize ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (ZTrig.cv (J i n p v) (J i n p v)) j = P2 at *
          generalize ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p (.mul v v)) j = P3 at *
          generalize J i n p (.sub (.mul (D i u) v) (.mul u (D i v))) j = P4 at *
          generalize J i n p (.mul (D i u) v) j = P5 at *
          generalize J i n p (.mul u (D i v)) j = P6 at *
          generalize ZTrig.cv (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v))) (J i n p v) j = R1 at *
          generalize ZTrig.cv (J i n p v) (ZTrig.cv (J i n p (.div u v)) (J i n p (D i v))) j = R2 at *
          generalize ZTrig.cv (ZTrig.cv (J i n p v) (J i n p (.div u v))) (J i n p (D i v)) j = R3 at *
          generalize ZTrig.cv (ZTrig.cv (J i n p (.div u v)) (J i n p v)) (J i n p (D i v)) j = R4 at *
          generalize ZTrig.cv (J i n p u) (J i n p (D i v)) j = R5 at *
          generalize ZTrig.cv (J i n p (D i u)) (J i n p v) j = W at *
          unfold qsub at s0
          exact qle_antisymm (by rat_linarith) (by rat_linarith)
        have zk := cv_cancel (nz_J0 i n p hv) k st k (Nat.le_refl k)
        apply cancel_succ k
        have lb := ZTrig.leibniz (J i n p v) k (J i n p (.div u v))
        have c1 := ZTrig.cv_congr k (ZTrig.Dsh (J i n p (.div u v)))
            (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v) (J i n p v)
            (fun t => J_D i n p (.div u v) t) (fun _ => qEq_refl _)
        have c2 := ZTrig.cv_congr k (J i n p (.div u v)) (J i n p (.div u v)) (ZTrig.Dsh (J i n p v)) (J i n p (D i v))
            (fun _ => qEq_refl _) (fun t => J_D i n p v t)
        have d := J_D i n p u k
        have dd : qEq (ZTrig.Dsh (J i n p u) k) (qmul (qnat (k + 1)) (J i n p u (k + 1))) := qEq_refl _
        unfold qsub at zk
        generalize ZTrig.cv (ZTrig.Dsh (J i n p (.div u v))) (J i n p v) k = A1 at *
        generalize ZTrig.cv (J i n p (.div u v)) (ZTrig.Dsh (J i n p v)) k = A2 at *
        generalize qmul (qnat (k + 1)) (ZTrig.cv (J i n p (.div u v)) (J i n p v) (k + 1)) = L at *
        generalize ZTrig.cv (J i n p (.div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v))) (J i n p v) k = B1 at *
        generalize ZTrig.cv (J i n p (.div u v)) (J i n p (D i v)) k = B2 at *
        generalize ZTrig.Dsh (J i n p u) k = E at *
        generalize qmul (qnat (k + 1)) (J i n p u (k + 1)) = R at *
        generalize J i n p (D i u) k = Du at *
        exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## tan — by uniqueness: `Z = T∗C − S` solves `Dsh Z = (T∗DU)∗Z`, `Z₀ = 0`, so `Z = 0` -/

theorem cv_zeroG (F : Nat → QExpr) (m : Nat) : qEq (ZTrig.cv F (fun _ => qzero) m) qzero := by
  have c := ZTrig.cv_congr m F F (fun _ => qzero) (fun j => qmul qzero ((fun _ => qzero) j))
    (fun _ => qEq_refl _) (fun _ => by show qEq qzero (qmul qzero qzero); rat_ring)
  exact qEq_trans c (qEq_trans (ZTrig.cv_scaleG qzero m F (fun _ => qzero)) (by rat_ring))

theorem cv_negG (F G : Nat → QExpr) (m : Nat) :
    qEq (ZTrig.cv F (fun t => qneg (G t)) m) (qneg (ZTrig.cv F G m)) := by
  have c := ZTrig.cv_congr m F F (fun t => qneg (G t)) (fun t => qmul (qneg qone) (G t))
    (fun _ => qEq_refl _) (fun j => by show qEq (qneg (G j)) (qmul (qneg qone) (G j)); rat_ring)
  exact qEq_trans c (qEq_trans (ZTrig.cv_scaleG (qneg qone) m F G) (by rat_ring))

theorem cv_subG (F G G' : Nat → QExpr) (m : Nat) :
    qEq (ZTrig.cv F (fun t => qsub (G t) (G' t)) m) (qsub (ZTrig.cv F G m) (ZTrig.cv F G' m)) := by
  have a := cv_comm m F (fun t => qsub (G t) (G' t))
  have b := ZTrig.cv_subF m G G' F
  have c1 := cv_comm m G F
  have c2 := cv_comm m G' F
  unfold qsub at *
  generalize ZTrig.cv F (fun t => qadd (G t) (qneg (G' t))) m = X at *
  generalize ZTrig.cv (fun t => qadd (G t) (qneg (G' t))) F m = X' at *
  generalize ZTrig.cv G F m = A at *; generalize ZTrig.cv G' F m = B at *
  generalize ZTrig.cv F G m = A' at *; generalize ZTrig.cv F G' m = B' at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `A ∗ (B ∗ C) = B ∗ (A ∗ C)`. -/
theorem cv_swap (A B C : Nat → QExpr) (m : Nat) :
    qEq (ZTrig.cv A (ZTrig.cv B C) m) (ZTrig.cv B (ZTrig.cv A C) m) :=
  qEq_trans (qEq_symm (cv_assoc m A B C))
    (qEq_trans (ZTrig.cv_congr m _ _ C C (fun t => cv_comm t A B) (fun _ => qEq_refl _)) (cv_assoc m B A C))

/-- A linear jet equation with zero start has only the zero solution. -/
theorem ode_zero (A Z : Nat → QExpr) (h0 : qEq (Z 0) qzero) (h : ∀ k, qEq (ZTrig.Dsh Z k) (ZTrig.cv A Z k)) :
    ∀ k, ∀ j, j ≤ k → qEq (Z j) qzero
  | 0, j, hj => by
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0; exact h0
  | k + 1, j, hj => by
      have ih := ode_zero A Z h0 h k
      cases Nat.lt_or_eq_of_le hj with
      | inl l => exact ih j (Nat.le_of_lt_succ l)
      | inr e =>
        subst e
        apply qEq_trans _ (qEq_refl qzero)
        apply cancel_succ k
        have c := cv_congr_uptoG k A Z (fun _ => qzero) ih
        have z := cv_zeroG A k
        have d : qEq (ZTrig.Dsh Z k) (qmul (qnat (k + 1)) (Z (k + 1))) := qEq_refl _
        have hk := h k
        have o : qEq (qmul (qnat (k + 1)) qzero) qzero := by rat_ring
        generalize ZTrig.Dsh Z k = X at *
        generalize qmul (qnat (k + 1)) (Z (k + 1)) = Y at *
        generalize qmul (qnat (k + 1)) qzero = O at *
        generalize ZTrig.cv A Z k = P at *
        generalize ZTrig.cv A (fun _ => qzero) k = P' at *
        exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The algebra of tan: from the jet equations of tan, sin, cos and `T₀C₀ = S₀`, `T ∗ C = S`. -/
theorem tan_ode (T C S DU : Nat → QExpr)
    (hT : ∀ t, qEq (ZTrig.Dsh T t) (ZTrig.cv (fun s => qadd (unitS s) (ZTrig.cv T T s)) DU t))
    (hS : ∀ t, qEq (ZTrig.Dsh S t) (ZTrig.cv C DU t))
    (hC : ∀ t, qEq (ZTrig.Dsh C t) (ZTrig.cv (fun s => qneg (S s)) DU t))
    (h0 : qEq (qmul (T 0) (C 0)) (S 0)) : ∀ k, qEq (ZTrig.cv T C k) (S k) := by
  have key : ∀ k, qEq (ZTrig.Dsh (fun t => qsub (ZTrig.cv T C t) (S t)) k)
      (ZTrig.cv (ZTrig.cv T DU) (fun t => qsub (ZTrig.cv T C t) (S t)) k) := by
    intro k
    have e0 : qEq (ZTrig.Dsh (fun t => qsub (ZTrig.cv T C t) (S t)) k)
        (qsub (ZTrig.Dsh (ZTrig.cv T C) k) (ZTrig.Dsh S k)) := by
      show qEq (qmul (qnat (k + 1)) (qsub (ZTrig.cv T C (k + 1)) (S (k + 1))))
        (qsub (qmul (qnat (k + 1)) (ZTrig.cv T C (k + 1))) (qmul (qnat (k + 1)) (S (k + 1))))
      generalize qnat (k + 1) = c; generalize ZTrig.cv T C (k + 1) = a; generalize S (k + 1) = b
      unfold qsub
      rat_ring
    have e1 := Dsh_cv T C k
    -- Dsh T ∗ C = C∗DU + T∗(DU∗(T∗C))
    have L1 : qEq (ZTrig.cv (ZTrig.Dsh T) C k)
        (qadd (ZTrig.cv C DU k) (ZTrig.cv T (ZTrig.cv DU (ZTrig.cv T C)) k)) := by
      refine qEq_trans (ZTrig.cv_congr k _ _ C C hT (fun _ => qEq_refl _)) ?_
      refine qEq_trans (cv_assoc k _ DU C) ?_
      refine qEq_trans (ZTrig.cv_addF k unitS (ZTrig.cv T T) (ZTrig.cv DU C)) ?_
      refine qadd_respects (qEq_trans (cv_unit k _) (cv_comm k DU C)) ?_
      refine qEq_trans (cv_assoc k T T _) ?_
      exact ZTrig.cv_congr k T T _ _ (fun _ => qEq_refl _) (fun t => cv_swap T DU C t)
    -- T ∗ Dsh C = −T∗(S∗DU)
    have L2 : qEq (ZTrig.cv T (ZTrig.Dsh C) k) (qneg (ZTrig.cv T (ZTrig.cv S DU) k)) := by
      refine qEq_trans (ZTrig.cv_congr k T T _ _ (fun _ => qEq_refl _) hC) ?_
      refine qEq_trans (ZTrig.cv_congr k T T _ (fun t => qneg (ZTrig.cv S DU t)) (fun _ => qEq_refl _)
        (fun t => qEq_trans (ZTrig.cv_congr t _ (fun s => qmul (qneg qone) (S s)) DU DU (fun s => by show qEq (qneg (S s)) (qmul (qneg qone) (S s)); rat_ring) (fun _ => qEq_refl _))
          (qEq_trans (ZTrig.cv_scaleF (qneg qone) t S DU) (by show qEq _ (qneg (ZTrig.cv S DU t)); rat_ring)))) ?_
      exact cv_negG T _ k
    have R : qEq (ZTrig.cv (ZTrig.cv T DU) (fun t => qsub (ZTrig.cv T C t) (S t)) k)
        (qsub (ZTrig.cv T (ZTrig.cv DU (ZTrig.cv T C)) k) (ZTrig.cv T (ZTrig.cv S DU) k)) := by
      refine qEq_trans (cv_subG _ _ _ k) ?_
      have r1 := cv_assoc k T DU (ZTrig.cv T C)
      have r2 := qEq_trans (cv_assoc k T DU S) (ZTrig.cv_congr k T T _ _ (fun _ => qEq_refl _) (fun t => cv_comm t DU S))
      unfold qsub
      exact qadd_respects r1 (qneg_respects r2)
    have e7 := hS k
    unfold qsub at *
    generalize ZTrig.Dsh (fun t => qadd (ZTrig.cv T C t) (qneg (S t))) k = X at *
    generalize ZTrig.cv (ZTrig.cv T DU) (fun t => qadd (ZTrig.cv T C t) (qneg (S t))) k = Y at *
    generalize ZTrig.Dsh (ZTrig.cv T C) k = A at *
    generalize ZTrig.Dsh S k = B at *
    generalize ZTrig.cv (ZTrig.Dsh T) C k = A1 at *
    generalize ZTrig.cv T (ZTrig.Dsh C) k = A2 at *
    generalize ZTrig.cv C DU k = CD at *
    generalize ZTrig.cv T (ZTrig.cv DU (ZTrig.cv T C)) k = P at *
    generalize ZTrig.cv T (ZTrig.cv S DU) k = Q at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have z0 : qEq ((fun t => qsub (ZTrig.cv T C t) (S t)) 0) qzero := by
    show qEq (qsub (qmul (T 0) (C 0)) (S 0)) qzero
    unfold qsub at *
    generalize qmul (T 0) (C 0) = a at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  intro k
  have z := ode_zero _ _ z0 key k k (Nat.le_refl k)
  show qEq _ _
  have z' : qEq (qsub (ZTrig.cv T C k) (S k)) qzero := z
  unfold qsub at z'
  generalize ZTrig.cv T C k = a at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- TAN: `J(tan u) ∗ J(cos u) = J(sin u)` — the kernel's `tan = sin/cos` recurrence. `cos u(p) ≠ 0`. -/
theorem J_tan (i n : Nat) (p : Point QExpr) (u : G) (hc : ¬ qEq (evalN n p (.cos u)) qzero) (k : Nat) :
    qEq (ZTrig.cv (J i n p (.tan u)) (J i n p (.cos u)) k) (J i n p (.sin u) k) := by
  refine tan_ode _ _ _ (ZTrig.Dsh (J i n p u)) (fun t => ?_) (J_sin i n p u) (J_cos i n p u) ?_ k
  · refine qEq_trans (J_D i n p (.tan u) t) ?_
    refine qEq_trans (J_mul i n p t (.add (.const qone) (.mul (.tan u) (.tan u))) (D i u)) ?_
    refine ZTrig.cv_congr t _ _ _ _ (fun s => ?_) (fun s => qEq_symm (J_D i n p u s))
    refine qEq_trans (J_add i n p (.const qone) (.mul (.tan u) (.tan u)) s) (qadd_respects ?_ (J_mul i n p s _ _))
    cases s with
    | zero => exact (J_free i n p (.const qone) (fun h => h)).1
    | succ s => exact (J_free i n p (.const qone) (fun h => h)).2 s
  · have a := qmul_respects (J_zero i n p (.tan u)) (J_zero i n p (.cos u))
    refine qEq_trans a (qEq_trans ?_ (qEq_symm (J_zero i n p (.sin u))))
    show qEq (qmul (qmul (ZTrig.Sn (evalN n p u) n) (qinv' (ZTrig.Cn (evalN n p u) n))) (ZTrig.Cn (evalN n p u) n))
      (ZTrig.Sn (evalN n p u) n)
    have hc' : ¬ qEq (ZTrig.Cn (evalN n p u) n) qzero := hc
    have c := qmul_inv'_cancel hc'
    have := qmul_respects (qEq_refl (ZTrig.Sn (evalN n p u) n)) c
    exact qEq_trans (by rat_ring) (qEq_trans this (by rat_ring))

/-! ## Powers `u^m` — the m-fold convolution, and Miller's recurrence -/

theorem J_const (i n : Nat) (p : Point QExpr) (c : QExpr) (t : Nat) : qEq (J i n p (.const c) t) (qmul c (unitS t)) := by
  cases t with
  | zero => exact qEq_trans (J_free i n p (.const c) (fun h => h)).1 (by show qEq c (qmul c qone); rat_ring)
  | succ t => exact qEq_trans ((J_free i n p (.const c) (fun h => h)).2 t) (by show qEq qzero (qmul c qzero); rat_ring)

theorem J_cmul (i n : Nat) (p : Point QExpr) (c : QExpr) (e : G) (s : Nat) :
    qEq (J i n p (.mul (.const c) e) s) (qmul c (J i n p e s)) :=
  qEq_trans (J_mul i n p s (.const c) e)
    (qEq_trans (ZTrig.cv_congr s _ (fun t => qmul c (unitS t)) _ _ (J_const i n p c) (fun _ => qEq_refl _))
      (qEq_trans (ZTrig.cv_scaleF c s unitS _) (qmul_respects (qEq_refl c) (cv_unit s _))))

theorem J_pow0 (i n : Nat) (p : Point QExpr) (u : G) (t : Nat) : qEq (J i n p (.powN u 0) t) (unitS t) := by
  cases t with
  | zero => exact J_zero i n p (.powN u 0)
  | succ t =>
      show qEq (qmul (evalN n p (Diter i t (D i (.const qzero)))) (cf (t + 1))) qzero
      exact z_mul_l (Diter_free i n p t (.const qzero) (fun h => h))

theorem Dsh_pow0 (i n : Nat) (p : Point QExpr) (u : G) (t : Nat) : qEq (ZTrig.Dsh (J i n p (.powN u 0)) t) qzero := by
  show qEq (qmul (qnat (t + 1)) (J i n p (.powN u 0) (t + 1))) qzero
  exact z_mul_r (J_pow0 i n p u (t + 1))

/-- `Dsh J(u^{m+1}) = (m+1)·J(u^m) ∗ Dsh J(u)`. -/
theorem J_powD (i n : Nat) (p : Point QExpr) (u : G) (m t : Nat) :
    qEq (ZTrig.Dsh (J i n p (.powN u (m + 1))) t)
      (qmul (qnat (m + 1)) (ZTrig.cv (J i n p (.powN u m)) (ZTrig.Dsh (J i n p u)) t)) :=
  qEq_trans (J_D i n p (.powN u (m + 1)) t)
    (qEq_trans (J_mul i n p t (.mul (.const (qnat (m + 1))) (.powN u m)) (D i u))
      (qEq_trans (ZTrig.cv_congr t _ (fun s => qmul (qnat (m + 1)) (J i n p (.powN u m) s)) _ (ZTrig.Dsh (J i n p u))
          (J_cmul i n p (qnat (m + 1)) (.powN u m)) (fun s => qEq_symm (J_D i n p u s)))
        (ZTrig.cv_scaleF (qnat (m + 1)) t _ _)))

/-- `J(u^{m+1}) = J(u) ∗ J(u^m)`: the power's jet is the m-fold convolution. -/
theorem J_pow_succ (i n : Nat) (p : Point QExpr) (u : G) : ∀ (m t : Nat),
    qEq (J i n p (.powN u (m + 1)) t) (ZTrig.cv (J i n p u) (J i n p (.powN u m)) t)
  | m, 0 => by
      have a := qmul_respects (J_zero i n p u) (J_zero i n p (.powN u m))
      refine qEq_trans (J_zero i n p (.powN u (m + 1))) (qEq_trans ?_ (qEq_symm a))
      show qEq (qmul (qpowN (evalN n p u) m) (evalN n p u)) (qmul (evalN n p u) (qpowN (evalN n p u) m))
      rat_ring
  | 0, t + 1 => by
      apply cancel_succ t
      have d : qEq (ZTrig.Dsh (J i n p (.powN u 1)) t)
          (qmul (qnat 1) (ZTrig.cv (J i n p (.powN u 0)) (ZTrig.Dsh (J i n p u)) t)) := J_powD i n p u 0 t
      have dd : qEq (ZTrig.Dsh (J i n p (.powN u 1)) t) (qmul (qnat (t + 1)) (J i n p (.powN u 1) (t + 1))) := qEq_refl _
      have lb := ZTrig.leibniz (J i n p (.powN u 0)) t (J i n p u)
      have c1 := qEq_trans (ZTrig.cv_congr t _ _ _ _ (fun _ => qEq_refl _) (J_pow0 i n p u))
        (qEq_trans (cv_comm t _ unitS) (cv_unit t (ZTrig.Dsh (J i n p u))))
      have c2 := qEq_trans (ZTrig.cv_congr t (J i n p u) (J i n p u) _ (fun _ => qzero) (fun _ => qEq_refl _) (Dsh_pow0 i n p u)) (cv_zeroG _ t)
      have c3 := qEq_trans (ZTrig.cv_congr t _ _ _ _ (J_pow0 i n p u) (fun _ => qEq_refl _)) (cv_unit t (ZTrig.Dsh (J i n p u)))
      have o : qEq (qnat 1) qone := qEq_trans (qnat_succ 0) (qEq_trans (qadd_respects qnat_zero (qEq_refl _)) (by rat_ring))
      generalize ZTrig.Dsh (J i n p (.powN u 1)) t = A at *
      generalize qmul (qnat (t + 1)) (J i n p (.powN u 1) (t + 1)) = L at *
      generalize qmul (qnat (t + 1)) (ZTrig.cv (J i n p u) (J i n p (.powN u 0)) (t + 1)) = R at *
      generalize ZTrig.cv (ZTrig.Dsh (J i n p u)) (J i n p (.powN u 0)) t = X1 at *
      generalize ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p (.powN u 0))) t = X2 at *
      generalize ZTrig.cv (J i n p (.powN u 0)) (ZTrig.Dsh (J i n p u)) t = X3 at *
      generalize ZTrig.Dsh (J i n p u) t = W at *
      generalize qnat 1 = one at *
      have d' : qEq A X3 := qEq_trans d (qEq_trans (qmul_respects o (qEq_refl _)) (by rat_ring))
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | m + 1, t + 1 => by
      apply cancel_succ t
      have d := J_powD i n p u (m + 1) t
      have dd : qEq (ZTrig.Dsh (J i n p (.powN u (m + 1 + 1))) t) (qmul (qnat (t + 1)) (J i n p (.powN u (m + 1 + 1)) (t + 1))) := qEq_refl _
      have lb := ZTrig.leibniz (J i n p (.powN u (m + 1))) t (J i n p u)
      have c1 := cv_comm t (ZTrig.Dsh (J i n p u)) (J i n p (.powN u (m + 1)))
      have c2 : qEq (ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p (.powN u (m + 1)))) t)
          (qmul (qnat (m + 1)) (ZTrig.cv (J i n p (.powN u (m + 1))) (ZTrig.Dsh (J i n p u)) t)) := by
        refine qEq_trans (ZTrig.cv_congr t _ _ _ _ (fun _ => qEq_refl _) (J_powD i n p u m)) ?_
        refine qEq_trans (ZTrig.cv_scaleG (qnat (m + 1)) t _ _) (qmul_respects (qEq_refl _) ?_)
        refine qEq_trans (qEq_symm (cv_assoc t _ _ _)) ?_
        exact ZTrig.cv_congr t _ _ _ _ (fun s => qEq_symm (J_pow_succ i n p u m s)) (fun _ => qEq_refl _)
      have q := qnat_succ (m + 1)
      generalize ZTrig.Dsh (J i n p (.powN u (m + 1 + 1))) t = A at *
      generalize qmul (qnat (t + 1)) (J i n p (.powN u (m + 1 + 1)) (t + 1)) = L at *
      generalize qmul (qnat (t + 1)) (ZTrig.cv (J i n p u) (J i n p (.powN u (m + 1))) (t + 1)) = R at *
      generalize ZTrig.cv (ZTrig.Dsh (J i n p u)) (J i n p (.powN u (m + 1))) t = X1 at *
      generalize ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p (.powN u (m + 1)))) t = X2 at *
      generalize ZTrig.cv (J i n p (.powN u (m + 1))) (ZTrig.Dsh (J i n p u)) t = X3 at *
      generalize qnat (m + 1 + 1) = N2 at *
      generalize qnat (m + 1) = N1 at *
      have d' : qEq A (qadd (qmul N1 X3) X3) := qEq_trans d (qEq_trans (qmul_respects q (qEq_refl _)) (by rat_ring))
      have c2' : qEq X2 (qmul N1 X3) := c2
      clear d q c2
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- MILLER: `J(u) ∗ Dsh J(u^m) = m·J(u^m) ∗ Dsh J(u)` — the kernel's `k·a₀·p_k = Σ_{i<k} (m(k−i) − i)·a_{k−i}·p_i`. -/
theorem J_miller (i n : Nat) (p : Point QExpr) (u : G) : ∀ (m t : Nat),
    qEq (ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p (.powN u m))) t)
      (qmul (qnat m) (ZTrig.cv (J i n p (.powN u m)) (ZTrig.Dsh (J i n p u)) t))
  | 0, t => by
      refine qEq_trans (ZTrig.cv_congr t (J i n p u) (J i n p u) _ (fun _ => qzero) (fun _ => qEq_refl _) (Dsh_pow0 i n p u)) ?_
      refine qEq_trans (cv_zeroG _ t) ?_
      exact qEq_symm (z_mul_l qnat_zero)
  | m + 1, t => by
      refine qEq_trans (ZTrig.cv_congr t _ _ _ _ (fun _ => qEq_refl _) (J_powD i n p u m)) ?_
      refine qEq_trans (ZTrig.cv_scaleG (qnat (m + 1)) t _ _) (qmul_respects (qEq_refl _) ?_)
      refine qEq_trans (qEq_symm (cv_assoc t _ _ _)) ?_
      exact ZTrig.cv_congr t _ _ _ _ (fun s => qEq_symm (J_pow_succ i n p u m s)) (fun _ => qEq_refl _)

/-! ## The square root — `S ∗ S = U` from the first coefficient on, exactly at every index -/

theorem two_ne : ¬ qEq (qadd qone qone) qzero := fun e => by
  have := qle_of_qlt qone_pos
  exact (qlt_iff_le_not_le.mp qone_pos).2 (by rat_linarith)

theorem two_mul_nz {s : QExpr} (h : ¬ qEq s qzero) : ¬ qEq (qmul (qadd qone qone) s) qzero := fun z => by
  apply h
  have c := qmul_inv'_cancel two_ne
  have r : qEq s (qmul (qmul (qadd qone qone) s) (qinv' (qadd qone qone))) := by
    have := qmul_respects (qEq_refl s) c
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
  exact qEq_trans r (qEq_trans (qmul_respects z (qEq_refl _)) (by rat_ring))

/-- SQRT: `(S ∗ S)_{k+1} = U_{k+1}` — the kernel's `sq_k = (a_k − Σ_{1≤i<k} sq_i sq_{k−i})/(2 s₀)`; `√u(p) ≠ 0` at `n`
(the grid root squares to `u` only up to its gap, so the value `k = 0` is a reading, not an identity). -/
theorem J_sqrt (i n : Nat) (p : Point QExpr) (u : G) (hs : ¬ qEq (evalN n p (.sqrt u)) qzero) (k : Nat) :
    qEq (ZTrig.cv (J i n p (.sqrt u)) (J i n p (.sqrt u)) (k + 1)) (J i n p u (k + 1)) := by
  have hv : ¬ qEq (evalN n p (.mul (.const (qadd qone qone)) (.sqrt u))) qzero := two_mul_nz hs
  have jd := J_div i n p k (D i u) (.mul (.const (qadd qone qone)) (.sqrt u)) hv k (Nat.le_refl k)
  -- J(D √u) = Dsh S, J(2√u) = 2·S, J(D u) = Dsh U
  have c1 := ZTrig.cv_congr k (J i n p (.div (D i u) (.mul (.const (qadd qone qone)) (.sqrt u))))
    (ZTrig.Dsh (J i n p (.sqrt u))) (J i n p (.mul (.const (qadd qone qone)) (.sqrt u)))
    (fun t => qmul (qadd qone qone) (J i n p (.sqrt u) t))
    (fun t => qEq_symm (J_D i n p (.sqrt u) t)) (J_cmul i n p (qadd qone qone) (.sqrt u))
  have c2 := ZTrig.cv_scaleG (qadd qone qone) k (ZTrig.Dsh (J i n p (.sqrt u))) (J i n p (.sqrt u))
  have du := qEq_symm (J_D i n p u k)
  have lb := ZTrig.leibniz (J i n p (.sqrt u)) k (J i n p (.sqrt u))
  have co := cv_comm k (J i n p (.sqrt u)) (ZTrig.Dsh (J i n p (.sqrt u)))
  have dd : qEq (ZTrig.Dsh (J i n p u) k) (qmul (qnat (k + 1)) (J i n p u (k + 1))) := qEq_refl _
  apply cancel_succ k
  generalize ZTrig.cv (J i n p (.div (D i u) (.mul (.const (qadd qone qone)) (.sqrt u))))
    (J i n p (.mul (.const (qadd qone qone)) (.sqrt u))) k = A at *
  generalize ZTrig.cv (ZTrig.Dsh (J i n p (.sqrt u))) (fun t => qmul (qadd qone qone) (J i n p (.sqrt u) t)) k = A' at *
  generalize ZTrig.cv (ZTrig.Dsh (J i n p (.sqrt u))) (J i n p (.sqrt u)) k = X at *
  generalize ZTrig.cv (J i n p (.sqrt u)) (ZTrig.Dsh (J i n p (.sqrt u))) k = X' at *
  generalize J i n p (D i u) k = W at *
  generalize ZTrig.Dsh (J i n p u) k = W' at *
  generalize qmul (qnat (k + 1)) (ZTrig.cv (J i n p (.sqrt u)) (J i n p (.sqrt u)) (k + 1)) = L at *
  generalize qmul (qnat (k + 1)) (J i n p u (k + 1)) = R at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## The logarithm — `Dsh L ∗ U = Dsh U` -/

/-- LN: `(Dsh J(ln u)) ∗ J(u) = Dsh J(u)` — the kernel's `l_k = (a_k − (1/k)Σ_{1≤i<k} i·l_i·a_{k−i})/a₀`; `u(p) ≠ 0`. -/
theorem J_ln (i n : Nat) (p : Point QExpr) (u : G) (hu : ¬ qEq (evalN n p u) qzero) (k : Nat) :
    qEq (ZTrig.cv (ZTrig.Dsh (J i n p (.ln u))) (J i n p u) k) (ZTrig.Dsh (J i n p u) k) := by
  have jd := J_div i n p k (D i u) u hu k (Nat.le_refl k)
  have c1 := ZTrig.cv_congr k (ZTrig.Dsh (J i n p (.ln u))) (J i n p (.div (D i u) u)) (J i n p u) (J i n p u)
    (fun t => J_D i n p (.ln u) t) (fun _ => qEq_refl _)
  exact qEq_trans c1 (qEq_trans jd (qEq_symm (J_D i n p u k)))

/-! ## log10 — `L·J(log10 u)_{k+1} = J(ln u)_{k+1}`, `L = ln 10` -/

theorem nz_mul {x y : QExpr} (hx : ¬ qEq x qzero) (hy : ¬ qEq y qzero) : ¬ qEq (qmul x y) qzero := fun z => by
  apply hx
  have c := qmul_inv'_cancel hy
  have r : qEq x (qmul (qmul x y) (qinv' y)) := by
    have := qmul_respects (qEq_refl x) c
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
  exact qEq_trans r (qEq_trans (qmul_respects z (qEq_refl _)) (by rat_ring))

/-- LOG10: the kernel's `log10` series is `ln`'s divided by `ln 10` (from the first coefficient on). -/
theorem J_log10 (i n : Nat) (p : Point QExpr) (u : G) (hu : ¬ qEq (evalN n p u) qzero)
    (hL : ¬ qEq (evalN n p (.ln (.const (qnat 10)))) qzero) (t : Nat) :
    qEq (qmul (evalN n p (.ln (.const (qnat 10)))) (J i n p (.log10 u) (t + 1))) (J i n p (.ln u) (t + 1)) := by
  generalize hLv : evalN n p (.ln (.const (qnat 10))) = L at hL
  have Jl : ∀ s, qEq (J i n p (.ln (.const (qnat 10))) s) (qmul L (unitS s)) := fun s => by
    cases s with
    | zero => rw [← hLv]; exact qEq_trans (J_free i n p (.ln (.const (qnat 10))) (fun h => h)).1 (by show qEq _ (qmul _ qone); rat_ring)
    | succ s => exact qEq_trans ((J_free i n p (.ln (.const (qnat 10))) (fun h => h)).2 s) (by show qEq qzero (qmul L qzero); rat_ring)
  -- J(u·ℓ) = L·J(u)
  have Jm : ∀ s, qEq (J i n p (.mul u (.ln (.const (qnat 10)))) s) (qmul L (J i n p u s)) := fun s =>
    qEq_trans (J_mul i n p s u _) (qEq_trans (cv_congr_uptoG s _ _ _ (fun s' _ => Jl s'))
      (qEq_trans (ZTrig.cv_scaleG L s _ unitS) (qmul_respects (qEq_refl L)
        (qEq_trans (cv_comm s _ _) (cv_unit s _)))))
  have huL : ¬ qEq (evalN n p (.mul u (.ln (.const (qnat 10))))) qzero := by
    show ¬ qEq (qmul (evalN n p u) (evalN n p (.ln (.const (qnat 10))))) qzero
    rw [hLv]; exact nz_mul hu hL
  -- L·cv(Dsh Log, U) = Dsh U = cv(Dsh Ln, U), for every index
  have zero : ∀ k, qEq (ZTrig.cv (fun s => qsub (qmul L (ZTrig.Dsh (J i n p (.log10 u)) s)) (ZTrig.Dsh (J i n p (.ln u)) s))
      (J i n p u) k) qzero := fun k => by
    have jd := J_div i n p k (D i u) (.mul u (.ln (.const (qnat 10)))) huL k (Nat.le_refl k)
    have c1 := ZTrig.cv_congr k (J i n p (.div (D i u) (.mul u (.ln (.const (qnat 10))))))
      (ZTrig.Dsh (J i n p (.log10 u))) _ (fun s => qmul L (J i n p u s))
      (fun s => qEq_symm (J_D i n p (.log10 u) s)) Jm
    have c2 := ZTrig.cv_scaleG L k (ZTrig.Dsh (J i n p (.log10 u))) (J i n p u)
    have jl := J_ln i n p u hu k
    have sf := ZTrig.cv_subF k (fun s => qmul L (ZTrig.Dsh (J i n p (.log10 u)) s)) (ZTrig.Dsh (J i n p (.ln u))) (J i n p u)
    have s1 := ZTrig.cv_scaleF L k (ZTrig.Dsh (J i n p (.log10 u))) (J i n p u)
    have du := qEq_symm (J_D i n p u k)
    have c3 := cv_comm k (ZTrig.Dsh (J i n p (.log10 u))) (fun s => qmul L (J i n p u s))
    clear Jm Jl
    unfold qsub at *
    generalize ZTrig.cv (fun s => qadd (qmul L (ZTrig.Dsh (J i n p (.log10 u)) s)) (qneg (ZTrig.Dsh (J i n p (.ln u)) s))) (J i n p u) k = X at *
    generalize ZTrig.cv (fun s => qmul L (ZTrig.Dsh (J i n p (.log10 u)) s)) (J i n p u) k = Y at *
    generalize ZTrig.cv (ZTrig.Dsh (J i n p (.ln u))) (J i n p u) k = Z at *
    generalize ZTrig.cv (J i n p (.div (D i u) (.mul u (.ln (.const (qnat 10)))))) (J i n p (.mul u (.ln (.const (qnat 10))))) k = W1 at *
    generalize ZTrig.cv (ZTrig.Dsh (J i n p (.log10 u))) (fun s => qmul L (J i n p u s)) k = W2 at *
    generalize ZTrig.cv (ZTrig.Dsh (J i n p (.log10 u))) (J i n p u) k = W3 at *
    generalize ZTrig.cv (fun s => qmul L (J i n p u s)) (ZTrig.Dsh (J i n p (.log10 u))) k = W4 at *
    generalize J i n p (D i u) k = V1 at *
    generalize ZTrig.Dsh (J i n p u) k = V2 at *
    generalize qmul L W3 = LW at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have hu0 : ¬ qEq (J i n p u 0) qzero := nz_J0 i n p hu
  have z := cv_cancel hu0 t (fun j _ => zero j) t (Nat.le_refl t)
  apply cancel_succ t
  have d1 : qEq (ZTrig.Dsh (J i n p (.log10 u)) t) (qmul (qnat (t + 1)) (J i n p (.log10 u) (t + 1))) := qEq_refl _
  have d2 : qEq (ZTrig.Dsh (J i n p (.ln u)) t) (qmul (qnat (t + 1)) (J i n p (.ln u) (t + 1))) := qEq_refl _
  have z' : qEq (qsub (qmul L (ZTrig.Dsh (J i n p (.log10 u)) t)) (ZTrig.Dsh (J i n p (.ln u)) t)) qzero := z
  have e : qEq (qmul (qnat (t + 1)) (qmul L (J i n p (.log10 u) (t + 1)))) (qmul L (qmul (qnat (t + 1)) (J i n p (.log10 u) (t + 1)))) := by
    rat_ring
  have m := qmul_respects (qEq_refl L) d1
  unfold qsub at z'
  generalize ZTrig.Dsh (J i n p (.log10 u)) t = A at *
  generalize ZTrig.Dsh (J i n p (.ln u)) t = A' at *
  generalize qmul (qnat (t + 1)) (J i n p (.ln u) (t + 1)) = R at *
  generalize qmul (qnat (t + 1)) (qmul L (J i n p (.log10 u) (t + 1))) = R' at *
  generalize qmul (qnat (t + 1)) (J i n p (.log10 u) (t + 1)) = R'' at *
  generalize qmul L A = LA at *
  generalize qmul L R'' = LR at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## A real exponent — `u^c = exp(c·ln u)`, Miller's recurrence with `c` -/

/-- MILLER, ANY EXPONENT: `J(u) ∗ Dsh J(exp(c·ln u)) = c·J(exp(c·ln u)) ∗ Dsh J(u)`; `u(p) ≠ 0`. -/
theorem J_millerR (i n : Nat) (p : Point QExpr) (u : G) (c : QExpr) (hu : ¬ qEq (evalN n p u) qzero) (j : Nat) :
    qEq (ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p (.exp (.mul (.const c) (.ln u))))) j)
      (qmul c (ZTrig.cv (J i n p (.exp (.mul (.const c) (.ln u)))) (ZTrig.Dsh (J i n p u)) j)) := by
  -- Dsh P = c·(P ∗ Dsh L)
  have dw : ∀ t, qEq (ZTrig.Dsh (J i n p (.mul (.const c) (.ln u))) t) (qmul c (ZTrig.Dsh (J i n p (.ln u)) t)) := fun t => by
    show qEq (qmul (qnat (t + 1)) (J i n p (.mul (.const c) (.ln u)) (t + 1))) (qmul c (qmul (qnat (t + 1)) (J i n p (.ln u) (t + 1))))
    have := J_cmul i n p c (.ln u) (t + 1)
    exact qEq_trans (qmul_respects (qEq_refl _) this) (by rat_ring)
  have dP : ∀ t, qEq (ZTrig.Dsh (J i n p (.exp (.mul (.const c) (.ln u)))) t)
      (qmul c (ZTrig.cv (J i n p (.exp (.mul (.const c) (.ln u)))) (ZTrig.Dsh (J i n p (.ln u))) t)) := fun t =>
    qEq_trans (J_exp i n p _ t) (qEq_trans (ZTrig.cv_congr t _ _ _ _ (fun _ => qEq_refl _) dw)
      (ZTrig.cv_scaleG c t _ _))
  -- U ∗ (c·(P ∗ DshL)) = c·(P ∗ (U ∗ DshL)) = c·(P ∗ DshU)
  have s1 := ZTrig.cv_congr j (J i n p u) (J i n p u) _ _ (fun _ => qEq_refl _) dP
  have s2 := ZTrig.cv_scaleG c j (J i n p u) (ZTrig.cv (J i n p (.exp (.mul (.const c) (.ln u)))) (ZTrig.Dsh (J i n p (.ln u))))
  have s3 := cv_swap (J i n p u) (J i n p (.exp (.mul (.const c) (.ln u)))) (ZTrig.Dsh (J i n p (.ln u))) j
  have s4 := ZTrig.cv_congr j (J i n p (.exp (.mul (.const c) (.ln u)))) (J i n p (.exp (.mul (.const c) (.ln u))))
    (ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p (.ln u)))) (ZTrig.Dsh (J i n p u)) (fun _ => qEq_refl _)
    (fun t => qEq_trans (cv_comm t _ _) (J_ln i n p u hu t))
  exact qEq_trans s1 (qEq_trans s2 (qmul_respects (qEq_refl c) (qEq_trans s3 s4)))

/-! ## atan — `Dsh J(atan u) ∗ J(1 + u·u) = Dsh J(u)`, and `J(1 + u·u) = unit + J(u) ∗ J(u)` -/

theorem one_sq_nz (x : QExpr) : ¬ qEq (qadd qone (qmul x x)) qzero := fun z => by
  have := qmul_self_nonneg x; have o := qone_pos
  have o' := qlt_iff_le_not_le.mp o
  exact o'.2 (by rat_linarith)

theorem J_atan (i n : Nat) (p : Point QExpr) (u : G) (k : Nat) :
    qEq (ZTrig.cv (ZTrig.Dsh (J i n p (.atan u))) (J i n p (.add (.const qone) (.mul u u))) k) (ZTrig.Dsh (J i n p u) k) := by
  have jd := J_div i n p k (D i u) (.add (.const qone) (.mul u u)) (one_sq_nz (evalN n p u)) k (Nat.le_refl k)
  have c1 := ZTrig.cv_congr k (ZTrig.Dsh (J i n p (.atan u))) (J i n p (.div (D i u) (.add (.const qone) (.mul u u))))
    (J i n p (.add (.const qone) (.mul u u))) (J i n p (.add (.const qone) (.mul u u)))
    (fun t => J_D i n p (.atan u) t) (fun _ => qEq_refl _)
  exact qEq_trans c1 (qEq_trans jd (qEq_symm (J_D i n p u k)))

theorem J_one_sq (i n : Nat) (p : Point QExpr) (u : G) (s : Nat) :
    qEq (J i n p (.add (.const qone) (.mul u u)) s) (qadd (unitS s) (ZTrig.cv (J i n p u) (J i n p u) s)) :=
  qEq_trans (J_add i n p _ _ s) (qadd_respects (qEq_trans (J_const i n p qone s) (qone_mul _)) (J_mul i n p s u u))

end ZJet

#print axioms ZJet.J_D
#print axioms ZJet.J_add
#print axioms ZJet.J_mul
#print axioms ZDeriv.D_free
#print axioms ZJet.J_free
#print axioms ZJet.J_var
#print axioms ZJet.J_exp
#print axioms ZJet.J_sin
#print axioms ZJet.J_cos
#print axioms ZJet.cv_comm
#print axioms ZJet.cv_assoc
#print axioms ZJet.cv_unit
#print axioms ZJet.cv_cancel
#print axioms ZJet.J_div
#print axioms ZJet.ode_zero
#print axioms ZJet.J_tan
#print axioms ZJet.J_pow_succ
#print axioms ZJet.J_miller
#print axioms ZJet.J_sqrt
#print axioms ZJet.J_ln
#print axioms ZJet.J_log10
#print axioms ZJet.J_atan
#print axioms ZJet.J_one_sq
#print axioms ZJet.J_millerR
