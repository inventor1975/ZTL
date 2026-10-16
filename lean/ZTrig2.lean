import ZTrig

/-!
# ZTrig2 — `cos` and `sin` as operational reals: Lipschitz, Cauchy, parity, the Pythagorean identity. Zero axioms.

Stage 2 of the full sine (the curator, 2026-10-17). From `ZTrig`'s partial sums `Cn`, `Sn`:

  * `crci_lip` — at a fixed index the partial sums move by at most `|x − y|·S(a, N)` (`|x|, |y| ≤ a`): the terms'
    differences follow the terms' recursion, `|Δcr_{m+1}|, |Δci_{m+1}| ≤ |x − y|·a^m/m!`;
  * `Cn_tail` — past a good index the partial sums move by at most `2·a^M/M!`;
  * `crci_neg`, `crci_zero` — `cos` is even, `sin` odd, `cos 0 = 1`, `sin 0 = 0`, exactly at every index;
  * `pyth` — `cos² + sin² = 1`, at every index up to the corner of `exp`'s series (the addition formula at `y = −x`).
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn

/-! ## Respect, parity, zero -/

theorem crci_respects {x x' : QExpr} (h : qEq x x') : ∀ m, qEq (cr x m) (cr x' m) ∧ qEq (ci x m) (ci x' m)
  | 0 => ⟨qEq_refl _, qEq_refl _⟩
  | m + 1 => by
      obtain ⟨r, i⟩ := crci_respects h m
      exact ⟨qmul_respects (qmul_respects (qneg_respects i) h) (qEq_refl _),
             qmul_respects (qmul_respects r h) (qEq_refl _)⟩

/-- `cos` is even, `sin` odd, term by term. -/
theorem crci_neg (x : QExpr) : ∀ m, qEq (cr (qneg x) m) (cr x m) ∧ qEq (ci (qneg x) m) (qneg (ci x m))
  | 0 => ⟨qEq_refl _, by show qEq qzero (qneg qzero); rat_ring⟩
  | m + 1 => by
      obtain ⟨r, i⟩ := crci_neg x m
      constructor
      · show qEq (qmul (qmul (qneg (ci (qneg x) m)) (qneg x)) (qinv' (qnat (m + 1))))
          (qmul (qmul (qneg (ci x m)) x) (qinv' (qnat (m + 1))))
        have e := qmul_respects (qmul_respects (qneg_respects i) (qEq_refl (qneg x))) (qEq_refl (qinv' (qnat (m + 1))))
        exact qEq_trans e (by rat_ring)
      · show qEq (qmul (qmul (cr (qneg x) m) (qneg x)) (qinv' (qnat (m + 1))))
          (qneg (qmul (qmul (cr x m) x) (qinv' (qnat (m + 1)))))
        have e := qmul_respects (qmul_respects r (qEq_refl (qneg x))) (qEq_refl (qinv' (qnat (m + 1))))
        exact qEq_trans e (by rat_ring)

/-- At `0`: `cr = 1, 0, 0, …`, `ci = 0, 0, …`. -/
theorem crci_zero : ∀ m, qEq (cr qzero (m + 1)) qzero ∧ qEq (ci qzero m) qzero
  | 0 => ⟨by show qEq (qmul (qmul (qneg qzero) qzero) (qinv' (qnat 1))) qzero; rat_ring, qEq_refl _⟩
  | m + 1 => by
      obtain ⟨r, i⟩ := crci_zero m
      exact ⟨by show qEq (qmul (qmul (qneg (ci qzero (m + 1))) qzero) (qinv' (qnat (m + 1 + 1)))) qzero; rat_ring,
             by show qEq (qmul (qmul (cr qzero m) qzero) (qinv' (qnat (m + 1)))) qzero; rat_ring⟩

theorem Cn_zero : ∀ N, qEq (Cn qzero (N + 1)) qone
  | 0 => by show qEq (qadd qzero qone) qone; rat_ring
  | N + 1 => by
      have ih := Cn_zero N
      have z := (crci_zero N).1
      show qEq (qadd (Cn qzero (N + 1)) (cr qzero (N + 1))) qone
      generalize Cn qzero (N + 1) = X at *; generalize cr qzero (N + 1) = Y at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem Sn_zero : ∀ N, qEq (Sn qzero N) qzero
  | 0 => qEq_refl _
  | N + 1 => by
      have ih := Sn_zero N
      have z := (crci_zero N).2
      show qEq (qadd (Sn qzero N) (ci qzero N)) qzero
      generalize Sn qzero N = X at *; generalize ci qzero N = Y at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem Cn_respects {x x' : QExpr} (h : qEq x x') (N : Nat) : qEq (Cn x N) (Cn x' N) :=
  bs_congr (fun m => (crci_respects h m).1) N
theorem Sn_respects {x x' : QExpr} (h : qEq x x') (N : Nat) : qEq (Sn x N) (Sn x' N) :=
  bs_congr (fun m => (crci_respects h m).2) N

theorem Cn_neg (x : QExpr) (N : Nat) : qEq (Cn (qneg x) N) (Cn x N) := bs_congr (fun m => (crci_neg x m).1) N

theorem bs_neg (F : Nat → QExpr) : ∀ N, qEq (bs (fun i => qneg (F i)) N) (qneg (bs F N))
  | 0 => by show qEq qzero (qneg qzero); rat_ring
  | N + 1 => by
      have ih := bs_neg F N
      show qEq (qadd (bs (fun i => qneg (F i)) N) (qneg (F N))) (qneg (qadd (bs F N) (F N)))
      generalize bs (fun i => qneg (F i)) N = X at *; generalize bs F N = Y at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem Sn_neg (x : QExpr) (N : Nat) : qEq (Sn (qneg x) N) (qneg (Sn x N)) :=
  qEq_trans (bs_congr (fun m => (crci_neg x m).2) N) (bs_neg (ci x) N)

/-! ## Lipschitz in the argument, at a fixed index -/

/-- `|x − y| ≤ e`, `|x|, |y| ≤ a`: `|Δcr_m|, |Δci_m| ≤ e·L_m`, `L_0 = 0`, `L_{m+1} = a^m/m!`. -/
def Lb (a : QExpr) : Nat → QExpr
  | 0 => qzero
  | m + 1 => tm a m

theorem crci_lip {x y a e : QExpr} (hx : Ab x a) (hy : Ab y a) (he : Ab (qsub x y) e) :
    ∀ m, Ab (qsub (cr x m) (cr y m)) (qmul e (Lb a m)) ∧ Ab (qsub (ci x m) (ci y m)) (qmul e (Lb a m))
  | 0 => by
      show Ab (qsub qone qone) (qmul e qzero) ∧ Ab (qsub qzero qzero) (qmul e qzero)
      have z : qEq (qmul e qzero) qzero := qmul_zero e
      unfold qsub; exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩
  | m + 1 => by
      obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := crci_lip hx hy he m
      obtain ⟨⟨ry1, ry2⟩, ⟨iy1, iy2⟩⟩ := crci_abs hy m
      have p : qle qzero (qinv' (qnat (m + 1))) := qinv'_nonneg_of_pos (qnat_succ_pos m)
      -- Δ(u·x) = Δu·x + u_y·(x − y)
      have m1 := mul_abs (u := qsub (ci x m) (ci y m)) (U := qmul e (Lb a m)) ⟨i1, i2⟩ hx
      have m2 := mul_abs (u := ci y m) (U := tm a m) ⟨iy1, iy2⟩ he
      have m3 := mul_abs (u := qsub (cr x m) (cr y m)) (U := qmul e (Lb a m)) ⟨r1, r2⟩ hx
      have m4 := mul_abs (u := cr y m) (U := tm a m) ⟨ry1, ry2⟩ he
      -- e·L_m·a + a^m/m!·e = e·(m+1)·a^m/m!·… : a·L_m = m·tm a m
      have key : qEq (qadd (qmul (qmul e (Lb a m)) a) (qmul (tm a m) e)) (qmul e (qmul (qnat (m + 1)) (tm a m))) := by
        cases m with
        | zero =>
            show qEq (qadd (qmul (qmul e qzero) a) (qmul (tm a 0) e)) (qmul e (qmul (qnat 1) (tm a 0)))
            have n1 : qEq (qnat 1) qone := by have := qnat_succ 0; have := qnat_zero; exact qle_antisymm (by rat_linarith) (by rat_linarith)
            have := qmul_respects (qEq_refl e) (qmul_respects n1 (qEq_refl (tm a 0)))
            exact qEq_trans (show qEq (qadd (qmul (qmul e qzero) a) (qmul (tm a 0) e)) (qmul e (qmul qone (tm a 0))) by rat_ring)
              (qEq_symm this)
        | succ k =>
            show qEq (qadd (qmul (qmul e (tm a k)) a) (qmul (tm a (k + 1)) e)) (qmul e (qmul (qnat (k + 1 + 1)) (tm a (k + 1))))
            have t := tm_succ a k
            have s := qmul_respects (qnat_succ (k + 1)) (qEq_refl (tm a (k + 1)))
            have e1 := qmul_respects (qEq_refl e) s
            have e2 := qmul_respects (qEq_refl e) t
            generalize tm a k = T0 at *; generalize tm a (k + 1) = T1 at *; generalize qnat (k + 1) = c at *
            generalize qnat (k + 1 + 1) = c' at *
            exact qle_antisymm (by rat_linarith) (by rat_linarith)
      have hc := qmul_inv'_cancel (qnat_ne_zero m)
      obtain ⟨a1, a2⟩ := m1; obtain ⟨b1, b2⟩ := m2; obtain ⟨c1, c2⟩ := m3; obtain ⟨d1, d2⟩ := m4
      have bound : ∀ X, qle (qneg (qadd (qmul (qmul e (Lb a m)) a) (qmul (tm a m) e))) X →
          qle X (qadd (qmul (qmul e (Lb a m)) a) (qmul (tm a m) e)) →
          Ab (qmul X (qinv' (qnat (m + 1)))) (qmul e (Lb a (m + 1))) := fun X h1 h2 => by
        have s1 := ZExp.scale h1 p; have s2 := ZExp.scale h2 p
        have k1 := qmul_respects key (qEq_refl (qinv' (qnat (m + 1))))
        have k2 : qEq (qmul (qmul e (qmul (qnat (m + 1)) (tm a m))) (qinv' (qnat (m + 1))))
            (qmul e (qmul (tm a m) (qmul (qnat (m + 1)) (qinv' (qnat (m + 1)))))) := by rat_ring
        have k3 := qmul_respects (qEq_refl e) (qmul_respects (qEq_refl (tm a m)) hc)
        have k4 : qEq (qmul e (qmul (tm a m) qone)) (qmul e (tm a m)) := by rat_ring
        have k5 : qEq (qmul (qneg (qadd (qmul (qmul e (Lb a m)) a) (qmul (tm a m) e))) (qinv' (qnat (m + 1))))
            (qneg (qmul (qadd (qmul (qmul e (Lb a m)) a) (qmul (tm a m) e)) (qinv' (qnat (m + 1))))) := by rat_ring
        show Ab (qmul X (qinv' (qnat (m + 1)))) (qmul e (tm a m))
        generalize qmul (qadd (qmul (qmul e (Lb a m)) a) (qmul (tm a m) e)) (qinv' (qnat (m + 1))) = W at *
        generalize qmul (qmul e (qmul (qnat (m + 1)) (tm a m))) (qinv' (qnat (m + 1))) = W' at *
        generalize qmul e (qmul (tm a m) (qmul (qnat (m + 1)) (qinv' (qnat (m + 1))))) = W'' at *
        generalize qmul e (qmul (tm a m) qone) = W3 at *
        exact ⟨by rat_linarith, by rat_linarith⟩
      constructor
      · show Ab (qsub (qmul (qmul (qneg (ci x m)) x) (qinv' (qnat (m + 1)))) (qmul (qmul (qneg (ci y m)) y) (qinv' (qnat (m + 1)))))
          (qmul e (Lb a (m + 1)))
        have eq : qEq (qsub (qmul (qmul (qneg (ci x m)) x) (qinv' (qnat (m + 1)))) (qmul (qmul (qneg (ci y m)) y) (qinv' (qnat (m + 1)))))
            (qmul (qneg (qadd (qmul (qsub (ci x m) (ci y m)) x) (qmul (ci y m) (qsub x y)))) (qinv' (qnat (m + 1)))) := by
          unfold qsub; rat_ring
        obtain ⟨u1, u2⟩ := bound (qneg (qadd (qmul (qsub (ci x m) (ci y m)) x) (qmul (ci y m) (qsub x y))))
          (by rat_linarith) (by rat_linarith)
        exact ⟨qle_trans u1 (qle_of_qEq (qEq_symm eq)), qle_trans (qle_of_qEq eq) u2⟩
      · show Ab (qsub (qmul (qmul (cr x m) x) (qinv' (qnat (m + 1)))) (qmul (qmul (cr y m) y) (qinv' (qnat (m + 1)))))
          (qmul e (Lb a (m + 1)))
        have eq : qEq (qsub (qmul (qmul (cr x m) x) (qinv' (qnat (m + 1)))) (qmul (qmul (cr y m) y) (qinv' (qnat (m + 1)))))
            (qmul (qadd (qmul (qsub (cr x m) (cr y m)) x) (qmul (cr y m) (qsub x y))) (qinv' (qnat (m + 1)))) := by
          unfold qsub; rat_ring
        obtain ⟨u1, u2⟩ := bound (qadd (qmul (qsub (cr x m) (cr y m)) x) (qmul (cr y m) (qsub x y)))
          (by rat_linarith) (by rat_linarith)
        exact ⟨qle_trans u1 (qle_of_qEq (qEq_symm eq)), qle_trans (qle_of_qEq eq) u2⟩

theorem bs_Lb (a : QExpr) : ∀ N, qEq (bs (Lb a) (N + 1)) (S a N)
  | 0 => by show qEq (qadd qzero qzero) qzero; rat_ring
  | N + 1 => by
      have ih := bs_Lb a N
      show qEq (qadd (bs (Lb a) (N + 1)) (tm a N)) (qadd (S a N) (tm a N))
      exact qadd_respects ih (qEq_refl _)

theorem bs_Lb_le {a : QExpr} (ha : qle qzero a) : ∀ N, qle (bs (Lb a) N) (S a N)
  | 0 => qle_refl _
  | N + 1 => by
      have e := bs_Lb a N
      have t := tm_nonneg ha N
      show qle (bs (Lb a) (N + 1)) (qadd (S a N) (tm a N))
      rat_linarith

theorem bs_scale (c : QExpr) (F : Nat → QExpr) : ∀ N, qEq (bs (fun i => qmul c (F i)) N) (qmul c (bs F N))
  | 0 => by show qEq qzero (qmul c qzero); rat_ring
  | N + 1 => by
      have ih := bs_scale c F N
      show qEq (qadd (bs (fun i => qmul c (F i)) N) (qmul c (F N))) (qmul c (qadd (bs F N) (F N)))
      exact qEq_trans (qadd_respects ih (qEq_refl _)) (by rat_ring)

/-- LIPSCHITZ: `|C_N(x) − C_N(y)|, |S_N(x) − S_N(y)| ≤ e·S(a, N)`, `|x|, |y| ≤ a`, `|x − y| ≤ e`. -/
theorem CS_lip {x y a e : QExpr} (hx : Ab x a) (hy : Ab y a) (he : Ab (qsub x y) e) (N : Nat) :
    Ab (qsub (Cn x N) (Cn y N)) (qmul e (S a N)) ∧ Ab (qsub (Sn x N) (Sn y N)) (qmul e (S a N)) := by
  have ha : qle qzero a := by obtain ⟨h1, h2⟩ := hx; rat_linarith
  have he0 : qle qzero e := by obtain ⟨h1, h2⟩ := he; rat_linarith
  have L := scale_l (bs_Lb_le ha N) he0
  have sc := bs_scale e (Lb a) N
  obtain ⟨c1, c2⟩ := bs_abs (fun m => (crci_lip hx hy he m).1) N
  obtain ⟨d1, d2⟩ := bs_abs (fun m => (crci_lip hx hy he m).2) N
  have s1 := bs_sub (cr x) (cr y) N
  have s2 := bs_sub (ci x) (ci y) N
  unfold Cn Sn
  generalize bs (fun i => qmul e (Lb a i)) N = W at *
  generalize bs (fun i => qsub (cr x i) (cr y i)) N = D1 at *
  generalize bs (fun i => qsub (ci x i) (ci y i)) N = D2 at *
  generalize qsub (bs (cr x) N) (bs (cr y) N) = E1 at *
  generalize qsub (bs (ci x) N) (bs (ci y) N) = E2 at *
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩

/-- THE TAIL: past a good index `M ≤ N`, `|C_N(x) − C_M(x)|, |S_N(x) − S_M(x)| ≤ 2·a^M/M!`. -/
theorem CS_tail {x a : QExpr} (hx : Ab x a) {M : Nat} (g : Good a M) (N : Nat) (hMN : M ≤ N) :
    Ab (qsub (Cn x N) (Cn x M)) (qadd (tm a M) (tm a M)) ∧ Ab (qsub (Sn x N) (Sn x M)) (qadd (tm a M) (tm a M)) := by
  have ha : qle qzero a := by obtain ⟨h1, h2⟩ := hx; rat_linarith
  obtain ⟨j, rfl⟩ := le_ex hMN
  obtain ⟨_, ub⟩ := S_between ha g (M + j) (Nat.le_add_right M j)
  -- Σ_{M ≤ m < M+j} |term| ≤ S(a, M+j) − S(a, M)
  have key : ∀ j, Ab (qsub (Cn x (M + j)) (Cn x M)) (qsub (S a (M + j)) (S a M)) ∧
      Ab (qsub (Sn x (M + j)) (Sn x M)) (qsub (S a (M + j)) (S a M)) := by
    intro j
    induction j with
    | zero =>
        show Ab (qsub (Cn x M) (Cn x M)) (qsub (S a M) (S a M)) ∧ Ab (qsub (Sn x M) (Sn x M)) (qsub (S a M) (S a M))
        unfold qsub; exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩
    | succ j ih =>
        obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := ih
        obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := crci_abs hx (M + j)
        show Ab (qsub (qadd (Cn x (M + j)) (cr x (M + j))) (Cn x M)) (qsub (qadd (S a (M + j)) (tm a (M + j))) (S a M)) ∧
          Ab (qsub (qadd (Sn x (M + j)) (ci x (M + j))) (Sn x M)) (qsub (qadd (S a (M + j)) (tm a (M + j))) (S a M))
        unfold qsub at *; exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩
  obtain ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ := key j
  unfold qsub at *
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩

/-- THE PYTHAGOREAN IDENTITY, AT EVERY INDEX: `|1 − (C_N(x)² + S_N(x)²)| ≤ 2·corner(tm a, tm a, N+1)`. -/
theorem pyth {x a : QExpr} (hx : Ab x a) (N : Nat) :
    Ab (qsub qone (qadd (qmul (Cn x (N + 1)) (Cn x (N + 1))) (qmul (Sn x (N + 1)) (Sn x (N + 1)))))
       (qadd (corner (tm a) (tm a) (N + 1)) (corner (tm a) (tm a) (N + 1))) := by
  have hnx : Ab (qneg x) a := by obtain ⟨h1, h2⟩ := hx; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨⟨k1, k2⟩, _⟩ := add_bounds hx hnx (N + 1)
  have z : qEq (qadd x (qneg x)) qzero := by rat_ring
  have c0 := qEq_trans (Cn_respects z (N + 1)) (Cn_zero N)
  have cn := Cn_neg x (N + 1)
  have sn := Sn_neg x (N + 1)
  have p1 := qmul_respects (qEq_refl (Cn x (N + 1))) cn
  have p2 := qmul_respects (qEq_refl (Sn x (N + 1))) sn
  generalize corner (tm a) (tm a) (N + 1) = K at *
  generalize Cn (qadd x (qneg x)) (N + 1) = C0 at *
  generalize Cn (qneg x) (N + 1) = Cm at *; generalize Sn (qneg x) (N + 1) = Sm at *
  generalize Cn x (N + 1) = C at *; generalize Sn x (N + 1) = Sx at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZTrig

#print axioms ZTrig.crci_respects
#print axioms ZTrig.crci_neg
#print axioms ZTrig.Cn_zero
#print axioms ZTrig.Sn_neg
#print axioms ZTrig.crci_lip
#print axioms ZTrig.CS_lip
#print axioms ZTrig.CS_tail
#print axioms ZTrig.pyth
