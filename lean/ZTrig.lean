import ZPow

/-!
# ZTrig — `cos` and `sin` on VR's operational reals, and their addition formulas. Zero axioms.

The curator, 2026-10-17: the full sine. The kernel has `sin`/`cos` since 2026-10-13 (`zfunc.py`, proved brackets
for any argument); this is the proof that its rules are sound, in the VR discipline (no mean value theorem, no
choice). The key is the ADDITION FORMULA, and it comes from the series by algebra:

  * the terms of `e^(ix)` without complex numbers: `cr`, `ci`, with `(m+1)·cr_{m+1} = −x·ci_m`,
    `(m+1)·ci_{m+1} = x·cr_m` — the imaginary unit lives in the recursion, no `m mod 4` (`Nat.mod` lemmas carry
    `propext`);
  * the convolution `cv F G m = Σ_{i≤m} F_i·G_{m−i}`, defined by SHIFTING `F` (no `Nat` subtraction), and its
    Leibniz rule (`leibniz`): `cv(DF, G, m) + cv(F, DG, m) = (m+1)·cv(F, G, m+1)`, `DF_i = (i+1)·F_{i+1}`;
  * the binomial theorem for the terms (`binom`, `binom_c`): `tm(x+y)_m = cv(tm x, tm y, m)` and its complex twin.

This file: stage 1, the algebra.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn

/-- `Σ_{i<n} F i`. -/
def bs (F : Nat → QExpr) : Nat → QExpr
  | 0 => qzero
  | n + 1 => qadd (bs F n) (F n)

/-- `Σ_{i≤m} F_i·G_{m−i}`, by shifting `F`. -/
def cv : (Nat → QExpr) → (Nat → QExpr) → Nat → QExpr
  | F, G, 0 => qmul (F 0) (G 0)
  | F, G, m + 1 => qadd (qmul (F 0) (G (m + 1))) (cv (fun i => F (i + 1)) G m)

/-- `(DF)_i = (i+1)·F_{i+1}` — the derivative of a power series, coefficientwise. -/
def Dsh (F : Nat → QExpr) (i : Nat) : QExpr := qmul (qnat (i + 1)) (F (i + 1))

/-! ## The convolution: congruence, linearity -/

theorem cv_congr : ∀ (m : Nat) (F F' G G' : Nat → QExpr), (∀ i, qEq (F i) (F' i)) → (∀ i, qEq (G i) (G' i)) →
    qEq (cv F G m) (cv F' G' m)
  | 0, F, F', G, G', hF, hG => qmul_respects (hF 0) (hG 0)
  | m + 1, F, F', G, G', hF, hG =>
      qadd_respects (qmul_respects (hF 0) (hG (m + 1)))
        (cv_congr m (fun i => F (i + 1)) (fun i => F' (i + 1)) G G' (fun i => hF (i + 1)) hG)

theorem cv_addF : ∀ (m : Nat) (F F' G : Nat → QExpr),
    qEq (cv (fun i => qadd (F i) (F' i)) G m) (qadd (cv F G m) (cv F' G m))
  | 0, F, F', G => by show qEq (qmul (qadd (F 0) (F' 0)) (G 0)) (qadd (qmul (F 0) (G 0)) (qmul (F' 0) (G 0))); rat_ring
  | m + 1, F, F', G => by
      have ih := cv_addF m (fun i => F (i + 1)) (fun i => F' (i + 1)) G
      show qEq (qadd (qmul (qadd (F 0) (F' 0)) (G (m + 1))) (cv (fun i => qadd (F (i + 1)) (F' (i + 1))) G m))
        (qadd (qadd (qmul (F 0) (G (m + 1))) (cv (fun i => F (i + 1)) G m))
          (qadd (qmul (F' 0) (G (m + 1))) (cv (fun i => F' (i + 1)) G m)))
      generalize cv (fun i => qadd (F (i + 1)) (F' (i + 1))) G m = X at *
      generalize cv (fun i => F (i + 1)) G m = Y at *
      generalize cv (fun i => F' (i + 1)) G m = Z at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem cv_scaleF (c : QExpr) : ∀ (m : Nat) (F G : Nat → QExpr),
    qEq (cv (fun i => qmul c (F i)) G m) (qmul c (cv F G m))
  | 0, F, G => by show qEq (qmul (qmul c (F 0)) (G 0)) (qmul c (qmul (F 0) (G 0))); rat_ring
  | m + 1, F, G => by
      have ih := cv_scaleF c m (fun i => F (i + 1)) G
      show qEq (qadd (qmul (qmul c (F 0)) (G (m + 1))) (cv (fun i => qmul c (F (i + 1))) G m))
        (qmul c (qadd (qmul (F 0) (G (m + 1))) (cv (fun i => F (i + 1)) G m)))
      have e := qmul_add c (qmul (F 0) (G (m + 1))) (cv (fun i => F (i + 1)) G m)
      generalize cv (fun i => qmul c (F (i + 1))) G m = X at *
      generalize cv (fun i => F (i + 1)) G m = Y at *
      have e2 : qEq (qmul (qmul c (F 0)) (G (m + 1))) (qmul c (qmul (F 0) (G (m + 1)))) := by rat_ring
      have e3 := qmul_respects (qEq_refl c) (qEq_refl Y)
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem cv_scaleG (c : QExpr) : ∀ (m : Nat) (F G : Nat → QExpr),
    qEq (cv F (fun j => qmul c (G j)) m) (qmul c (cv F G m))
  | 0, F, G => by show qEq (qmul (F 0) (qmul c (G 0))) (qmul c (qmul (F 0) (G 0))); rat_ring
  | m + 1, F, G => by
      have ih := cv_scaleG c m (fun i => F (i + 1)) G
      show qEq (qadd (qmul (F 0) (qmul c (G (m + 1)))) (cv (fun i => F (i + 1)) (fun j => qmul c (G j)) m))
        (qmul c (qadd (qmul (F 0) (G (m + 1))) (cv (fun i => F (i + 1)) G m)))
      have e := qmul_add c (qmul (F 0) (G (m + 1))) (cv (fun i => F (i + 1)) G m)
      generalize cv (fun i => F (i + 1)) (fun j => qmul c (G j)) m = X at *
      generalize cv (fun i => F (i + 1)) G m = Y at *
      have e2 : qEq (qmul (F 0) (qmul c (G (m + 1)))) (qmul c (qmul (F 0) (G (m + 1)))) := by rat_ring
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## The Leibniz rule -/

/-- `cv(DF, G, m) + cv(F, DG, m) = (m+1)·cv(F, G, m+1)`. -/
theorem leibniz (G : Nat → QExpr) : ∀ (m : Nat) (F : Nat → QExpr),
    qEq (qadd (cv (Dsh F) G m) (cv F (Dsh G) m)) (qmul (qnat (m + 1)) (cv F G (m + 1)))
  | 0, F => by
      show qEq (qadd (qmul (qmul (qnat 1) (F 1)) (G 0)) (qmul (F 0) (qmul (qnat 1) (G 1))))
        (qmul (qnat 1) (qadd (qmul (F 0) (G 1)) (qmul (F 1) (G 0))))
      rat_ring
  | m + 1, F => by
      have ih := leibniz G m (fun i => F (i + 1))
      -- (DF)∘succ = D(F∘succ) + F∘succ∘succ
      have sh : qEq (cv (fun i => Dsh F (i + 1)) G m)
          (qadd (cv (Dsh (fun i => F (i + 1))) G m) (cv (fun i => F (i + 1 + 1)) G m)) := by
        refine qEq_trans (cv_congr m _ (fun i => qadd (Dsh (fun i => F (i + 1)) i) (F (i + 1 + 1))) G G (fun i => ?_)
          (fun _ => qEq_refl _)) (cv_addF m _ _ G)
        show qEq (qmul (qnat (i + 1 + 1)) (F (i + 1 + 1))) (qadd (qmul (qnat (i + 1)) (F (i + 1 + 1))) (F (i + 1 + 1)))
        have e := qmul_respects (qnat_succ (i + 1)) (qEq_refl (F (i + 1 + 1)))
        exact qEq_trans e (by rat_ring)
      have u1 := qnat_succ (m + 1)
      show qEq (qadd (qadd (qmul (qmul (qnat (0 + 1)) (F (0 + 1))) (G (m + 1))) (cv (fun i => Dsh F (i + 1)) G m))
          (qadd (qmul (F 0) (qmul (qnat (m + 1 + 1)) (G (m + 1 + 1)))) (cv (fun i => F (i + 1)) (Dsh G) m)))
        (qmul (qnat (m + 1 + 1)) (qadd (qmul (F 0) (G (m + 1 + 1)))
          (qadd (qmul (F (0 + 1)) (G (m + 1))) (cv (fun i => F (i + 1 + 1)) G m))))
      have n1 : qEq (qnat (0 + 1)) qone := by have := qnat_succ 0; have := qnat_zero; exact qle_antisymm (by rat_linarith) (by rat_linarith)
      have e1 := qmul_respects (qmul_respects n1 (qEq_refl (F 1))) (qEq_refl (G (m + 1)))
      have e2 : qEq (qmul (qnat (m + 1 + 1)) (qadd (qmul (F 0) (G (m + 1 + 1)))
          (qadd (qmul (F 1) (G (m + 1))) (cv (fun i => F (i + 1 + 1)) G m))))
          (qmul (qadd (qnat (m + 1)) qone) (qadd (qmul (F 0) (G (m + 1 + 1)))
            (qadd (qmul (F 1) (G (m + 1))) (cv (fun i => F (i + 1 + 1)) G m)))) := qmul_respects u1 (qEq_refl _)
      have e3 : qEq (qmul (F 0) (qmul (qnat (m + 1 + 1)) (G (m + 1 + 1))))
          (qmul (F 0) (qmul (qadd (qnat (m + 1)) qone) (G (m + 1 + 1)))) :=
        qmul_respects (qEq_refl _) (qmul_respects u1 (qEq_refl _))
      -- ih: cv(D Fs, G, m) + cv(Fs, DG, m) = (m+1)·cv(Fs, G, m+1), and cv(Fs, G, m+1) unfolds
      have ih' : qEq (qadd (cv (Dsh (fun i => F (i + 1))) G m) (cv (fun i => F (i + 1)) (Dsh G) m))
          (qmul (qnat (m + 1)) (qadd (qmul (F 1) (G (m + 1))) (cv (fun i => F (i + 1 + 1)) G m))) := ih
      generalize cv (fun i => Dsh F (i + 1)) G m = A at *
      generalize cv (Dsh (fun i => F (i + 1))) G m = B at *
      generalize cv (fun i => F (i + 1 + 1)) G m = C at *
      generalize cv (fun i => F (i + 1)) (Dsh G) m = D at *
      generalize qnat (m + 1) = c at *
      generalize qnat (m + 1 + 1) = c' at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## The binomial theorem for the terms -/

/-- Divide by `k + 1`. -/
theorem cancel_nat {k : Nat} {y z : QExpr} (h : qEq (qmul (qnat (k + 1)) y) (qmul (qnat (k + 1)) z)) : qEq y z :=
  qle_antisymm (le_of_nat_mul (qle_of_qEq h)) (le_of_nat_mul (qle_of_qEq (qEq_symm h)))

/-- `x·tm x i = D(tm x)_i`. -/
theorem tm_D (x : QExpr) (i : Nat) : qEq (qmul x (tm x i)) (Dsh (tm x) i) :=
  qEq_trans (qmul_comm x (tm x i)) (qEq_symm (tm_succ x i))

/-- THE BINOMIAL THEOREM: `(x+y)^m/m! = Σ_{i≤m} x^i/i!·y^(m−i)/(m−i)!`. -/
theorem binom (x y : QExpr) : ∀ m, qEq (tm (qadd x y) m) (cv (tm x) (tm y) m)
  | 0 => by show qEq qone (qmul qone qone); rat_ring
  | m + 1 => by
      have ih := binom x y m
      have L := leibniz (tm y) m (tm x)
      have a1 := cv_scaleF x m (tm x) (tm y)
      have a2 := cv_scaleG y m (tm x) (tm y)
      have c1 := cv_congr m (fun i => qmul x (tm x i)) (Dsh (tm x)) (tm y) (tm y) (tm_D x) (fun _ => qEq_refl _)
      have c2 := cv_congr m (tm x) (tm x) (fun j => qmul y (tm y j)) (Dsh (tm y)) (fun _ => qEq_refl _) (tm_D y)
      have s := tm_succ (qadd x y) m
      have e := qmul_respects ih (qEq_refl (qadd x y))
      refine cancel_nat (k := m) ?_
      generalize cv (fun i => qmul x (tm x i)) (tm y) m = A at *
      generalize cv (Dsh (tm x)) (tm y) m = A' at *
      generalize cv (tm x) (fun j => qmul y (tm y j)) m = B at *
      generalize cv (tm x) (Dsh (tm y)) m = B' at *
      generalize cv (tm x) (tm y) m = C at *
      generalize cv (tm x) (tm y) (m + 1) = C' at *
      generalize tm (qadd x y) m = T at *
      generalize tm (qadd x y) (m + 1) = T' at *
      generalize qnat (m + 1) = c at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## The terms of `e^(ix)`, without complex numbers -/

/-- Real and imaginary parts of `(ix)^m/m!`: `cr_{m+1} = −ci_m·x/(m+1)`, `ci_{m+1} = cr_m·x/(m+1)`. -/
def crci (x : QExpr) : Nat → QExpr × QExpr
  | 0 => (qone, qzero)
  | m + 1 => (qmul (qmul (qneg (crci x m).2) x) (qinv' (qnat (m + 1))),
              qmul (qmul (crci x m).1 x) (qinv' (qnat (m + 1))))

def cr (x : QExpr) (m : Nat) : QExpr := (crci x m).1
def ci (x : QExpr) (m : Nat) : QExpr := (crci x m).2

theorem cr_D (x : QExpr) (i : Nat) : qEq (qmul (qneg x) (ci x i)) (Dsh (cr x) i) := by
  have hc := qmul_inv'_cancel (qnat_ne_zero i)
  show qEq (qmul (qneg x) (ci x i)) (qmul (qnat (i + 1)) (qmul (qmul (qneg (ci x i)) x) (qinv' (qnat (i + 1)))))
  have e : qEq (qmul (qnat (i + 1)) (qmul (qmul (qneg (ci x i)) x) (qinv' (qnat (i + 1)))))
      (qmul (qmul (qneg (ci x i)) x) (qmul (qnat (i + 1)) (qinv' (qnat (i + 1))))) := by rat_ring
  exact qEq_symm (qEq_trans e (qEq_trans (qmul_respects (qEq_refl _) hc) (by rat_ring)))

theorem ci_D (x : QExpr) (i : Nat) : qEq (qmul x (cr x i)) (Dsh (ci x) i) := by
  have hc := qmul_inv'_cancel (qnat_ne_zero i)
  show qEq (qmul x (cr x i)) (qmul (qnat (i + 1)) (qmul (qmul (cr x i) x) (qinv' (qnat (i + 1)))))
  have e : qEq (qmul (qnat (i + 1)) (qmul (qmul (cr x i) x) (qinv' (qnat (i + 1)))))
      (qmul (qmul (cr x i) x) (qmul (qnat (i + 1)) (qinv' (qnat (i + 1))))) := by rat_ring
  exact qEq_symm (qEq_trans e (qEq_trans (qmul_respects (qEq_refl _) hc) (by rat_ring)))

theorem cv_subF : ∀ (m : Nat) (F F' G : Nat → QExpr),
    qEq (cv (fun i => qsub (F i) (F' i)) G m) (qsub (cv F G m) (cv F' G m)) := by
  intro m F F' G
  have a := cv_addF m F (fun i => qmul (qneg qone) (F' i)) G
  have b := cv_scaleF (qneg qone) m F' G
  have c := cv_congr m (fun i => qsub (F i) (F' i)) (fun i => qadd (F i) (qmul (qneg qone) (F' i))) G G
    (fun i => by show qEq (qsub (F i) (F' i)) (qadd (F i) (qmul (qneg qone) (F' i))); unfold qsub; rat_ring)
    (fun _ => qEq_refl _)
  generalize cv (fun i => qsub (F i) (F' i)) G m = X at *
  generalize cv (fun i => qadd (F i) (qmul (qneg qone) (F' i))) G m = Y at *
  generalize cv (fun i => qmul (qneg qone) (F' i)) G m = Z at *
  generalize cv F G m = U at *; generalize cv F' G m = V at *
  unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE BINOMIAL THEOREM FOR `e^(i(x+y))`: `cr(x+y) = cv(cr x, cr y) − cv(ci x, ci y)`,
`ci(x+y) = cv(cr x, ci y) + cv(ci x, cr y)`. -/
theorem binom_c (x y : QExpr) : ∀ m,
    qEq (cr (qadd x y) m) (qsub (cv (cr x) (cr y) m) (cv (ci x) (ci y) m)) ∧
    qEq (ci (qadd x y) m) (qadd (cv (cr x) (ci y) m) (cv (ci x) (cr y) m))
  | 0 => ⟨by show qEq qone (qsub (qmul qone qone) (qmul qzero qzero)); unfold qsub; rat_ring,
          by show qEq qzero (qadd (qmul qone qzero) (qmul qzero qone)); rat_ring⟩
  | m + 1 => by
      obtain ⟨ihr, ihi⟩ := binom_c x y m
      -- Leibniz for the four products
      have Lrr := leibniz (cr y) m (cr x)
      have Lii := leibniz (ci y) m (ci x)
      have Lri := leibniz (ci y) m (cr x)
      have Lir := leibniz (cr y) m (ci x)
      -- D(cr) = −x·ci, D(ci) = x·cr, under cv
      have d1 := cv_congr m (Dsh (cr x)) (fun i => qmul (qneg x) (ci x i)) (cr y) (cr y) (fun i => qEq_symm (cr_D x i)) (fun _ => qEq_refl _)
      have d2 := cv_congr m (cr x) (cr x) (Dsh (cr y)) (fun j => qmul (qneg y) (ci y j)) (fun _ => qEq_refl _) (fun j => qEq_symm (cr_D y j))
      have d3 := cv_congr m (Dsh (ci x)) (fun i => qmul x (cr x i)) (ci y) (ci y) (fun i => qEq_symm (ci_D x i)) (fun _ => qEq_refl _)
      have d4 := cv_congr m (ci x) (ci x) (Dsh (ci y)) (fun j => qmul y (cr y j)) (fun _ => qEq_refl _) (fun j => qEq_symm (ci_D y j))
      have d5 := cv_congr m (Dsh (cr x)) (fun i => qmul (qneg x) (ci x i)) (ci y) (ci y) (fun i => qEq_symm (cr_D x i)) (fun _ => qEq_refl _)
      have d6 := cv_congr m (cr x) (cr x) (Dsh (ci y)) (fun j => qmul y (cr y j)) (fun _ => qEq_refl _) (fun j => qEq_symm (ci_D y j))
      have d7 := cv_congr m (Dsh (ci x)) (fun i => qmul x (cr x i)) (cr y) (cr y) (fun i => qEq_symm (ci_D x i)) (fun _ => qEq_refl _)
      have d8 := cv_congr m (ci x) (ci x) (Dsh (cr y)) (fun j => qmul (qneg y) (ci y j)) (fun _ => qEq_refl _) (fun j => qEq_symm (cr_D y j))
      have s1 := cv_scaleF (qneg x) m (ci x) (cr y)
      have s2 := cv_scaleG (qneg y) m (cr x) (ci y)
      have s3 := cv_scaleF x m (cr x) (ci y)
      have s4 := cv_scaleG y m (ci x) (cr y)
      have s5 := cv_scaleF (qneg x) m (ci x) (ci y)
      have s6 := cv_scaleG y m (cr x) (cr y)
      have s7 := cv_scaleF x m (cr x) (cr y)
      have s8 := cv_scaleG (qneg y) m (ci x) (ci y)
      -- the recursion of cr, ci at x + y
      have r1 := cr_D (qadd x y) m
      have r2 := ci_D (qadd x y) m
      have er := qmul_respects (qEq_refl (qneg (qadd x y))) ihi
      have ei := qmul_respects (qEq_refl (qadd x y)) ihr
      constructor
      · refine cancel_nat (k := m) ?_
        show qEq (qmul (qnat (m + 1)) (cr (qadd x y) (m + 1))) _
        have r1' : qEq (qmul (qneg (qadd x y)) (ci (qadd x y) m)) (qmul (qnat (m + 1)) (cr (qadd x y) (m + 1))) := r1
        generalize cv (Dsh (cr x)) (cr y) m = a1 at *; generalize cv (cr x) (Dsh (cr y)) m = a2 at *
        generalize cv (Dsh (ci x)) (ci y) m = a3 at *; generalize cv (ci x) (Dsh (ci y)) m = a4 at *
        generalize cv (Dsh (cr x)) (ci y) m = a5 at *; generalize cv (cr x) (Dsh (ci y)) m = a6 at *
        generalize cv (Dsh (ci x)) (cr y) m = a7 at *; generalize cv (ci x) (Dsh (cr y)) m = a8 at *
        generalize cv (fun i => qmul (qneg x) (ci x i)) (cr y) m = b1 at *
        generalize cv (cr x) (fun j => qmul (qneg y) (ci y j)) m = b2 at *
        generalize cv (fun i => qmul x (cr x i)) (ci y) m = b3 at *
        generalize cv (ci x) (fun j => qmul y (cr y j)) m = b4 at *
        generalize cv (fun i => qmul (qneg x) (ci x i)) (ci y) m = b5 at *
        generalize cv (cr x) (fun j => qmul y (cr y j)) m = b6 at *
        generalize cv (fun i => qmul x (cr x i)) (cr y) m = b7 at *
        generalize cv (ci x) (fun j => qmul (qneg y) (ci y j)) m = b8 at *
        generalize cv (cr x) (cr y) m = c1 at *; generalize cv (ci x) (ci y) m = c2 at *
        generalize cv (cr x) (ci y) m = c3 at *; generalize cv (ci x) (cr y) m = c4 at *
        generalize cv (cr x) (cr y) (m + 1) = e1 at *; generalize cv (ci x) (ci y) (m + 1) = e2 at *
        generalize cv (cr x) (ci y) (m + 1) = e3 at *; generalize cv (ci x) (cr y) (m + 1) = e4 at *
        generalize cr (qadd x y) m = R0 at *; generalize ci (qadd x y) m = I0 at *
        generalize cr (qadd x y) (m + 1) = R1 at *; generalize ci (qadd x y) (m + 1) = I1 at *
        generalize qnat (m + 1) = k at *
        unfold qsub at *
        exact qle_antisymm (by rat_linarith) (by rat_linarith)
      · refine cancel_nat (k := m) ?_
        show qEq (qmul (qnat (m + 1)) (ci (qadd x y) (m + 1))) _
        have r2' : qEq (qmul (qadd x y) (cr (qadd x y) m)) (qmul (qnat (m + 1)) (ci (qadd x y) (m + 1))) := r2
        generalize cv (Dsh (cr x)) (cr y) m = a1 at *; generalize cv (cr x) (Dsh (cr y)) m = a2 at *
        generalize cv (Dsh (ci x)) (ci y) m = a3 at *; generalize cv (ci x) (Dsh (ci y)) m = a4 at *
        generalize cv (Dsh (cr x)) (ci y) m = a5 at *; generalize cv (cr x) (Dsh (ci y)) m = a6 at *
        generalize cv (Dsh (ci x)) (cr y) m = a7 at *; generalize cv (ci x) (Dsh (cr y)) m = a8 at *
        generalize cv (fun i => qmul (qneg x) (ci x i)) (cr y) m = b1 at *
        generalize cv (cr x) (fun j => qmul (qneg y) (ci y j)) m = b2 at *
        generalize cv (fun i => qmul x (cr x i)) (ci y) m = b3 at *
        generalize cv (ci x) (fun j => qmul y (cr y j)) m = b4 at *
        generalize cv (fun i => qmul (qneg x) (ci x i)) (ci y) m = b5 at *
        generalize cv (cr x) (fun j => qmul y (cr y j)) m = b6 at *
        generalize cv (fun i => qmul x (cr x i)) (cr y) m = b7 at *
        generalize cv (ci x) (fun j => qmul (qneg y) (ci y j)) m = b8 at *
        generalize cv (cr x) (cr y) m = c1 at *; generalize cv (ci x) (ci y) m = c2 at *
        generalize cv (cr x) (ci y) m = c3 at *; generalize cv (ci x) (cr y) m = c4 at *
        generalize cv (cr x) (cr y) (m + 1) = e1 at *; generalize cv (ci x) (ci y) (m + 1) = e2 at *
        generalize cv (cr x) (ci y) (m + 1) = e3 at *; generalize cv (ci x) (cr y) (m + 1) = e4 at *
        generalize cr (qadd x y) m = R0 at *; generalize ci (qadd x y) m = I0 at *
        generalize cr (qadd x y) (m + 1) = R1 at *; generalize ci (qadd x y) (m + 1) = I1 at *
        generalize qnat (m + 1) = k at *
        unfold qsub at *
        exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## Squares and triangles of partial sums -/

/-- `Σ_{m<N} cv(F, G, m)` — the triangle `i + j < N`. -/
def tri (F G : Nat → QExpr) (N : Nat) : QExpr := bs (cv F G) N

/-- The square `i, j < N` minus the triangle: the corner `i, j < N ≤ i + j`. -/
def corner (F G : Nat → QExpr) (N : Nat) : QExpr := qsub (qmul (bs F N) (bs G N)) (tri F G N)

theorem bs_shift (F : Nat → QExpr) : ∀ N, qEq (bs F (N + 1)) (qadd (F 0) (bs (fun i => F (i + 1)) N))
  | 0 => by show qEq (qadd qzero (F 0)) (qadd (F 0) qzero); rat_ring
  | N + 1 => by
      have ih := bs_shift F N
      show qEq (qadd (bs F (N + 1)) (F (N + 1))) (qadd (F 0) (qadd (bs (fun i => F (i + 1)) N) (F (N + 1))))
      generalize bs F (N + 1) = X at *; generalize bs (fun i => F (i + 1)) N = Y at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The convolution, shifting `G` instead: `cv(F, G, m+1) = cv(F, G∘succ, m) + F_{m+1}·G_0`. -/
theorem cv_shiftG : ∀ (m : Nat) (F G : Nat → QExpr),
    qEq (cv F G (m + 1)) (qadd (cv F (fun j => G (j + 1)) m) (qmul (F (m + 1)) (G 0)))
  | 0, F, G => by
      show qEq (qadd (qmul (F 0) (G 1)) (qmul (F 1) (G 0))) (qadd (qmul (F 0) (G 1)) (qmul (F 1) (G 0)))
      exact qEq_refl _
  | m + 1, F, G => by
      have ih := cv_shiftG m (fun i => F (i + 1)) G
      show qEq (qadd (qmul (F 0) (G (m + 1 + 1))) (cv (fun i => F (i + 1)) G (m + 1)))
        (qadd (qadd (qmul (F 0) (G (m + 1 + 1))) (cv (fun i => F (i + 1)) (fun j => G (j + 1)) m)) (qmul (F (m + 1 + 1)) (G 0)))
      generalize cv (fun i => F (i + 1)) G (m + 1) = X at *
      generalize cv (fun i => F (i + 1)) (fun j => G (j + 1)) m = Y at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem tri_recF (F G : Nat → QExpr) : ∀ N,
    qEq (tri F G (N + 1)) (qadd (qmul (F 0) (bs G (N + 1))) (tri (fun i => F (i + 1)) G N))
  | 0 => by show qEq (qadd qzero (qmul (F 0) (G 0))) (qadd (qmul (F 0) (qadd qzero (G 0))) qzero); rat_ring
  | N + 1 => by
      have ih := tri_recF F G N
      show qEq (qadd (tri F G (N + 1)) (qadd (qmul (F 0) (G (N + 1))) (cv (fun i => F (i + 1)) G N)))
        (qadd (qmul (F 0) (qadd (bs G (N + 1)) (G (N + 1)))) (qadd (tri (fun i => F (i + 1)) G N) (cv (fun i => F (i + 1)) G N)))
      generalize tri F G (N + 1) = X at *; generalize tri (fun i => F (i + 1)) G N = Y at *
      generalize cv (fun i => F (i + 1)) G N = Z at *; generalize bs G (N + 1) = W at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem tri_recG (F G : Nat → QExpr) : ∀ N,
    qEq (tri F G (N + 1)) (qadd (qmul (bs F (N + 1)) (G 0)) (tri F (fun j => G (j + 1)) N))
  | 0 => by show qEq (qadd qzero (qmul (F 0) (G 0))) (qadd (qmul (qadd qzero (F 0)) (G 0)) qzero); rat_ring
  | N + 1 => by
      have ih := tri_recG F G N
      have c := cv_shiftG N F G
      show qEq (qadd (tri F G (N + 1)) (cv F G (N + 1)))
        (qadd (qmul (qadd (bs F (N + 1)) (F (N + 1))) (G 0)) (qadd (tri F (fun j => G (j + 1)) N) (cv F (fun j => G (j + 1)) N)))
      generalize tri F G (N + 1) = X at *; generalize tri F (fun j => G (j + 1)) N = Y at *
      generalize cv F G (N + 1) = Z at *; generalize cv F (fun j => G (j + 1)) N = Z' at *
      generalize bs F (N + 1) = W at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE CORNER'S RECURSION: `corner(F, G, N+1) = corner(F∘succ, G, N) + S_{F∘succ}(N)·G_N`. -/
theorem corner_rec (F G : Nat → QExpr) (N : Nat) :
    qEq (corner F G (N + 1)) (qadd (corner (fun i => F (i + 1)) G N) (qmul (bs (fun i => F (i + 1)) N) (G N))) := by
  have a := bs_shift F N
  have b : qEq (tri F G (N + 1)) (qadd (qmul (F 0) (qadd (bs G N) (G N))) (tri (fun i => F (i + 1)) G N)) :=
    tri_recF F G N
  unfold corner
  show qEq (qsub (qmul (bs F (N + 1)) (qadd (bs G N) (G N))) (tri F G (N + 1))) _
  have e := qmul_respects a (qEq_refl (qadd (bs G N) (G N)))
  generalize bs F (N + 1) = X at *; generalize tri F G (N + 1) = T at *
  generalize bs (fun i => F (i + 1)) N = Y at *; generalize tri (fun i => F (i + 1)) G N = T' at *
  generalize bs G N = W at *
  unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## Bounds -/

/-- `|x| ≤ a`, as two inequalities. -/
def Ab (x a : QExpr) : Prop := qle (qneg a) x ∧ qle x a

theorem bs_abs {F A : Nat → QExpr} (h : ∀ i, Ab (F i) (A i)) : ∀ N, Ab (bs F N) (bs A N)
  | 0 => ⟨by show qle (qneg qzero) qzero; rat_linarith, qle_refl _⟩
  | N + 1 => by
      obtain ⟨a1, a2⟩ := bs_abs h N
      obtain ⟨b1, b2⟩ := h N
      exact ⟨by show qle (qneg (qadd (bs A N) (A N))) (qadd (bs F N) (F N)); rat_linarith,
             by show qle (qadd (bs F N) (F N)) (qadd (bs A N) (A N)); rat_linarith⟩

theorem mul_abs {u v U V : QExpr} (hu : Ab u U) (hv : Ab v V) : Ab (qmul u v) (qmul U V) := by
  obtain ⟨u1, u2⟩ := hu; obtain ⟨v1, v2⟩ := hv
  have U0 : qle qzero U := by rat_linarith
  have V0 : qle qzero V := by rat_linarith
  have p := qmul_nonneg U0 V0
  have e1 : qEq (qmul (qneg U) (qneg V)) (qmul U V) := by rat_ring
  have e2 : qEq (qmul (qneg U) V) (qneg (qmul U V)) := by rat_ring
  have e3 : qEq (qmul U (qneg V)) (qneg (qmul U V)) := by rat_ring
  refine ⟨mul_lo u1 u2 v1 v2 (by rat_linarith) (by rat_linarith) (by rat_linarith) (by rat_linarith),
          mul_hi u1 u2 v1 v2 (by rat_linarith) (by rat_linarith) (by rat_linarith) (by rat_linarith)⟩

/-- THE CORNER IS BOUNDED BY ITS MAJORANTS' CORNER. -/
theorem corner_abs {G B : Nat → QExpr} (hG : ∀ j, Ab (G j) (B j)) : ∀ (N : Nat) (F A : Nat → QExpr),
    (∀ i, Ab (F i) (A i)) → Ab (corner F G N) (corner A B N)
  | 0, F, A, _ => by
      unfold corner
      show Ab (qsub (qmul qzero qzero) qzero) (qsub (qmul qzero qzero) qzero)
      have e : qEq (qsub (qmul qzero qzero) qzero) qzero := by unfold qsub; rat_ring
      exact ⟨by rat_linarith, by rat_linarith⟩
  | N + 1, F, A, hF => by
      have ih := corner_abs hG N (fun i => F (i + 1)) (fun i => A (i + 1)) (fun i => hF (i + 1))
      have rF := corner_rec F G N
      have rA := corner_rec A B N
      have m := mul_abs (bs_abs (fun i => hF (i + 1)) N) (hG N)
      obtain ⟨i1, i2⟩ := ih; obtain ⟨m1, m2⟩ := m
      generalize corner F G (N + 1) = X at *; generalize corner A B (N + 1) = Y at *
      generalize corner (fun i => F (i + 1)) G N = X' at *; generalize corner (fun i => A (i + 1)) B N = Y' at *
      generalize qmul (bs (fun i => F (i + 1)) N) (G N) = P at *
      generalize qmul (bs (fun i => A (i + 1)) N) (B N) = Q at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## Non-negative majorants: the square of side `M` lies in the triangle of side `2M` -/

def NN (A : Nat → QExpr) : Prop := ∀ i, qle qzero (A i)

theorem cv_nonneg {B : Nat → QExpr} (hB : NN B) : ∀ (m : Nat) (A : Nat → QExpr), NN A → qle qzero (cv A B m)
  | 0, A, hA => qmul_nonneg (hA 0) (hB 0)
  | m + 1, A, hA => by
      have a := qmul_nonneg (hA 0) (hB (m + 1))
      have b := cv_nonneg hB m (fun i => A (i + 1)) (fun i => hA (i + 1))
      show qle qzero (qadd (qmul (A 0) (B (m + 1))) (cv (fun i => A (i + 1)) B m)); rat_linarith

theorem bs_nonneg {A : Nat → QExpr} (hA : NN A) : ∀ N, qle qzero (bs A N)
  | 0 => qle_refl _
  | N + 1 => by have := bs_nonneg hA N; have := hA N; show qle qzero (qadd (bs A N) (A N)); rat_linarith

theorem bs_mono {A : Nat → QExpr} (hA : NN A) {N N' : Nat} (h : N ≤ N') : qle (bs A N) (bs A N') := by
  obtain ⟨j, rfl⟩ := le_ex h
  induction j with
  | zero => exact qle_refl _
  | succ j ih =>
      have := hA (N + j)
      show qle (bs A N) (qadd (bs A (N + j)) (A (N + j)))
      have := ih (Nat.le_add_right N j); rat_linarith

theorem idx2 (M k : Nat) : M + 1 + (M + 1) + k = M + M + k + 1 + 1 := by
  rw [Nat.add_succ, Nat.succ_add, Nat.succ_add, Nat.succ_add]

/-- THE SQUARE IN THE TRIANGLE: for non-negative terms, `S_A(M)·S_B(M) ≤ tri(A, B, 2M + k)`. -/
theorem sq_le_tri : ∀ (M k : Nat) (A B : Nat → QExpr), NN A → NN B →
    qle (qmul (bs A M) (bs B M)) (tri A B (M + M + k))
  | 0, k, A, B, hA, hB => by
      have t := bs_nonneg (A := cv A B) (fun m => cv_nonneg hB m A hA) (0 + 0 + k)
      show qle (qmul qzero qzero) (bs (cv A B) (0 + 0 + k))
      have e : qEq (qmul qzero qzero) qzero := by rat_ring
      rat_linarith
  | M + 1, k, A, B, hA, hB => by
      rw [idx2 M k]
      have ih := sq_le_tri M k (fun i => A (i + 1)) (fun j => B (j + 1)) (fun i => hA (i + 1)) (fun j => hB (j + 1))
      have r1 := tri_recF A B (M + M + k + 1)
      have r2 := tri_recG (fun i => A (i + 1)) B (M + M + k)
      have sA := bs_shift A M
      have sB := bs_shift B M
      have m1 := bs_mono hB (show M + 1 ≤ M + M + k + 1 + 1 from
        Nat.succ_le_succ (Nat.le_trans (Nat.le_add_right M (M + k)) (Nat.le_trans (Nat.le_of_eq (Nat.add_assoc M M k).symm) (Nat.le_succ _))))
      have m2 := bs_mono (A := fun i => A (i + 1)) (fun i => hA (i + 1)) (show M ≤ M + M + k + 1 from
        Nat.le_trans (Nat.le_add_right M (M + k)) (Nat.le_trans (Nat.le_of_eq (Nat.add_assoc M M k).symm) (Nat.le_succ _)))
      have f1 := scale_l m1 (hA 0)
      have f2 := ZExp.scale m2 (hB 0)
      have e := qmul_respects sA sB
      have e2 := qmul_respects (qEq_refl (A 0)) sB
      generalize tri A B (M + M + k + 1 + 1) = T at *
      generalize tri (fun i => A (i + 1)) B (M + M + k + 1) = T1 at *
      generalize tri (fun i => A (i + 1)) (fun j => B (j + 1)) (M + M + k) = T2 at *
      generalize bs A (M + 1) = a1 at *; generalize bs B (M + 1) = b1 at *
      generalize bs (fun i => A (i + 1)) M = a2 at *; generalize bs (fun j => B (j + 1)) M = b2 at *
      generalize bs B (M + M + k + 1 + 1) = b3 at *; generalize bs (fun i => A (i + 1)) (M + M + k + 1) = a3 at *
      exact (by rat_linarith : qle (qmul a1 b1) T)

/-! ## The corner of `exp`'s series is small -/

theorem S_bs (x : QExpr) : ∀ N, S x N = bs (tm x) N
  | 0 => rfl
  | N + 1 => by show qadd (S x N) (tm x N) = qadd (bs (tm x) N) (tm x N); rw [S_bs x N]

/-- `corner(tm a, tm b, 2M + k) ≤ 2·t_a(M)·Hb + Ha·2·t_b(M)` once `M` is good for both. -/
theorem corner_exp {a b Ha Hb : QExpr} (ha : qle qzero a) (hb : qle qzero b)
    (hHa : ∀ n, qle (S a n) Ha) (hHb : ∀ n, qle (S b n) Hb) {M : Nat} (ga : Good a M) (gb : Good b M) (k : Nat) :
    qle (corner (tm a) (tm b) (M + M + k))
      (qadd (qmul (qadd (tm a M) (tm a M)) Hb) (qmul Ha (qadd (tm b M) (tm b M)))) := by
  have nA : NN (tm a) := tm_nonneg ha
  have nB : NN (tm b) := tm_nonneg hb
  have sq := sq_le_tri M k (tm a) (tm b) nA nB
  obtain ⟨_, ua⟩ := S_between ha ga (M + M + k) (Nat.le_trans (Nat.le_add_right M M) (Nat.le_add_right _ k))
  obtain ⟨_, ub⟩ := S_between hb gb (M + M + k) (Nat.le_trans (Nat.le_add_right M M) (Nat.le_add_right _ k))
  rw [S_bs, S_bs] at ua ub
  have pa := bs_nonneg nA M
  have pb := bs_nonneg nB (M + M + k)
  have ma := bs_mono nB (show M ≤ M + M + k from Nat.le_trans (Nat.le_add_right M M) (Nat.le_add_right _ k))
  have hb2 := hHb (M + M + k); rw [S_bs] at hb2
  have ha2 := hHa M; rw [S_bs] at ha2
  have t0 := tm_nonneg ha M
  have u0 := tm_nonneg hb M
  -- S_a(N)·S_b(N) − S_a(M)·S_b(M) = (S_a(N) − S_a(M))·S_b(N) + S_a(M)·(S_b(N) − S_b(M))
  have f1 := ZExp.scale (show qle (qsub (bs (tm a) (M + M + k)) (bs (tm a) M)) (qadd (tm a M) (tm a M)) by
    unfold qsub; rat_linarith) pb
  have f2 := scale_l hb2 (show qle qzero (qadd (tm a M) (tm a M)) by rat_linarith)
  have f3 := ZExp.scale ha2 (show qle qzero (qsub (bs (tm b) (M + M + k)) (bs (tm b) M)) by unfold qsub; rat_linarith)
  have f4 := scale_l (show qle (qsub (bs (tm b) (M + M + k)) (bs (tm b) M)) (qadd (tm b M) (tm b M)) by
    unfold qsub; rat_linarith) (qle_trans (bs_nonneg nA M) ha2)
  unfold corner
  generalize bs (tm a) (M + M + k) = SA at *; generalize bs (tm b) (M + M + k) = SB at *
  generalize bs (tm a) M = sa at *; generalize bs (tm b) M = sb at *
  generalize tri (tm a) (tm b) (M + M + k) = T at *
  generalize tm a M = ta at *; generalize tm b M = tb at *
  unfold qsub at *
  rat_linarith

/-! ## The addition formulas, for the partial sums -/

/-- The partial sums of `cos` and `sin`. -/
def Cn (x : QExpr) (N : Nat) : QExpr := bs (cr x) N
def Sn (x : QExpr) (N : Nat) : QExpr := bs (ci x) N

theorem bs_congr {F G : Nat → QExpr} (h : ∀ i, qEq (F i) (G i)) : ∀ N, qEq (bs F N) (bs G N)
  | 0 => qEq_refl _
  | N + 1 => qadd_respects (bs_congr h N) (h N)

theorem bs_add (F G : Nat → QExpr) : ∀ N, qEq (bs (fun i => qadd (F i) (G i)) N) (qadd (bs F N) (bs G N))
  | 0 => by show qEq qzero (qadd qzero qzero); rat_ring
  | N + 1 => by
      have ih := bs_add F G N
      show qEq (qadd (bs (fun i => qadd (F i) (G i)) N) (qadd (F N) (G N))) (qadd (qadd (bs F N) (F N)) (qadd (bs G N) (G N)))
      generalize bs (fun i => qadd (F i) (G i)) N = X at *; generalize bs F N = Y at *; generalize bs G N = Z at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem bs_sub (F G : Nat → QExpr) : ∀ N, qEq (bs (fun i => qsub (F i) (G i)) N) (qsub (bs F N) (bs G N))
  | 0 => by show qEq qzero (qsub qzero qzero); unfold qsub; rat_ring
  | N + 1 => by
      have ih := bs_sub F G N
      show qEq (qadd (bs (fun i => qsub (F i) (G i)) N) (qsub (F N) (G N))) (qsub (qadd (bs F N) (F N)) (qadd (bs G N) (G N)))
      generalize bs (fun i => qsub (F i) (G i)) N = X at *; generalize bs F N = Y at *; generalize bs G N = Z at *
      unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `|cr x m|, |ci x m| ≤ |x|^m/m!`. -/
theorem crci_abs {x a : QExpr} (hx : Ab x a) : ∀ m, Ab (cr x m) (tm a m) ∧ Ab (ci x m) (tm a m)
  | 0 => by
      show Ab qone qone ∧ Ab qzero qone
      have := qle_of_qlt qone_pos
      exact ⟨⟨by rat_linarith, qle_refl _⟩, ⟨by rat_linarith, by rat_linarith⟩⟩
  | m + 1 => by
      obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := crci_abs hx m
      have p : qle qzero (qinv' (qnat (m + 1))) := qinv'_nonneg_of_pos (qnat_succ_pos m)
      have mr := mul_abs (u := qneg (ci x m)) (U := tm a m) ⟨by rat_linarith, by rat_linarith⟩ hx
      have mi := mul_abs (u := cr x m) (U := tm a m) ⟨r1, r2⟩ hx
      obtain ⟨mr1, mr2⟩ := mr; obtain ⟨mi1, mi2⟩ := mi
      have s1 := ZExp.scale mr1 p; have s2 := ZExp.scale mr2 p
      have s3 := ZExp.scale mi1 p; have s4 := ZExp.scale mi2 p
      have e1 : qEq (qmul (qneg (qmul (tm a m) a)) (qinv' (qnat (m + 1)))) (qneg (qmul (qmul (tm a m) a) (qinv' (qnat (m + 1))))) := by
        rat_ring
      show Ab (qmul (qmul (qneg (ci x m)) x) (qinv' (qnat (m + 1)))) (qmul (qmul (tm a m) a) (qinv' (qnat (m + 1)))) ∧
        Ab (qmul (qmul (cr x m) x) (qinv' (qnat (m + 1)))) (qmul (qmul (tm a m) a) (qinv' (qnat (m + 1))))
      exact ⟨⟨by rat_linarith, s2⟩, ⟨by rat_linarith, s4⟩⟩

/-- THE ADDITION FORMULA FOR `cos`, AT INDEX `N`: `C(x+y) − (C(x)C(y) − S(x)S(y))` is the difference of two corners. -/
theorem add_C_exact (x y : QExpr) (N : Nat) :
    qEq (qsub (Cn (qadd x y) N) (qsub (qmul (Cn x N) (Cn y N)) (qmul (Sn x N) (Sn y N))))
      (qsub (corner (ci x) (ci y) N) (corner (cr x) (cr y) N)) := by
  have b := bs_congr (fun m => (binom_c x y m).1) N
  have d := bs_sub (cv (cr x) (cr y)) (cv (ci x) (ci y)) N
  unfold Cn Sn corner tri
  generalize bs (cr (qadd x y)) N = A at *
  generalize bs (fun m => qsub (cv (cr x) (cr y) m) (cv (ci x) (ci y) m)) N = B at *
  generalize bs (cv (cr x) (cr y)) N = T1 at *; generalize bs (cv (ci x) (ci y)) N = T2 at *
  generalize qmul (bs (cr x) N) (bs (cr y) N) = P1 at *; generalize qmul (bs (ci x) N) (bs (ci y) N) = P2 at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE ADDITION FORMULA FOR `sin`, AT INDEX `N`. -/
theorem add_S_exact (x y : QExpr) (N : Nat) :
    qEq (qsub (Sn (qadd x y) N) (qadd (qmul (Cn x N) (Sn y N)) (qmul (Sn x N) (Cn y N))))
      (qneg (qadd (corner (cr x) (ci y) N) (corner (ci x) (cr y) N))) := by
  have b := bs_congr (fun m => (binom_c x y m).2) N
  have d := bs_add (cv (cr x) (ci y)) (cv (ci x) (cr y)) N
  unfold Cn Sn corner tri
  generalize bs (ci (qadd x y)) N = A at *
  generalize bs (fun m => qadd (cv (cr x) (ci y) m) (cv (ci x) (cr y) m)) N = B at *
  generalize bs (cv (cr x) (ci y)) N = T1 at *; generalize bs (cv (ci x) (cr y)) N = T2 at *
  generalize qmul (bs (cr x) N) (bs (ci y) N) = P1 at *; generalize qmul (bs (ci x) N) (bs (cr y) N) = P2 at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- With `|x| ≤ a`, `|y| ≤ b`: both errors are at most twice the corner of `exp`'s series. -/
theorem add_bounds {x y a b : QExpr} (hx : Ab x a) (hy : Ab y b) (N : Nat) :
    Ab (qsub (Cn (qadd x y) N) (qsub (qmul (Cn x N) (Cn y N)) (qmul (Sn x N) (Sn y N))))
       (qadd (corner (tm a) (tm b) N) (corner (tm a) (tm b) N)) ∧
    Ab (qsub (Sn (qadd x y) N) (qadd (qmul (Cn x N) (Sn y N)) (qmul (Sn x N) (Cn y N))))
       (qadd (corner (tm a) (tm b) N) (corner (tm a) (tm b) N)) := by
  have hr : ∀ m, Ab (cr x m) (tm a m) := fun m => (crci_abs hx m).1
  have hi : ∀ m, Ab (ci x m) (tm a m) := fun m => (crci_abs hx m).2
  have gr : ∀ m, Ab (cr y m) (tm b m) := fun m => (crci_abs hy m).1
  have gi : ∀ m, Ab (ci y m) (tm b m) := fun m => (crci_abs hy m).2
  obtain ⟨k1, k2⟩ := corner_abs gr N (cr x) (tm a) hr
  obtain ⟨k3, k4⟩ := corner_abs gi N (ci x) (tm a) hi
  obtain ⟨k5, k6⟩ := corner_abs gi N (cr x) (tm a) hr
  obtain ⟨k7, k8⟩ := corner_abs gr N (ci x) (tm a) hi
  have eC := add_C_exact x y N
  have eS := add_S_exact x y N
  generalize corner (tm a) (tm b) N = K at *
  generalize corner (cr x) (cr y) N = c1 at *; generalize corner (ci x) (ci y) N = c2 at *
  generalize corner (cr x) (ci y) N = c3 at *; generalize corner (ci x) (cr y) N = c4 at *
  generalize qsub (Cn (qadd x y) N) (qsub (qmul (Cn x N) (Cn y N)) (qmul (Sn x N) (Sn y N))) = DC at *
  generalize qsub (Sn (qadd x y) N) (qadd (qmul (Cn x N) (Sn y N)) (qmul (Sn x N) (Cn y N))) = DS at *
  unfold qsub at *
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩

end ZTrig

#print axioms ZTrig.cv_congr
#print axioms ZTrig.cv_addF
#print axioms ZTrig.cv_scaleF
#print axioms ZTrig.cv_scaleG
#print axioms ZTrig.leibniz
#print axioms ZTrig.binom
#print axioms ZTrig.binom_c
#print axioms ZTrig.tri_recF
#print axioms ZTrig.tri_recG
#print axioms ZTrig.corner_rec
#print axioms ZTrig.corner_abs
#print axioms ZTrig.sq_le_tri
#print axioms ZTrig.corner_exp
#print axioms ZTrig.crci_abs
#print axioms ZTrig.add_C_exact
#print axioms ZTrig.add_S_exact
#print axioms ZTrig.add_bounds
