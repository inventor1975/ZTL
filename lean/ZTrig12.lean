import ZTrig11

/-!
# ZTrig12 — chords of `sin` and `cos` on a grid: the kernel's first-order rule. Zero axioms.

Stage 12 of the full sine. The kernel reads `(sin u)' = cos(U)·Du` and `(cos u)' = −sin(U)·Du`. A slope reading is
pairwise (`Δf ∈ Δx·[l, h]` for any two points), so what is needed is the CHORD: `sin b − sin a = (b − a)·χ` with `χ`
inside the kernel's reading of `cos` over `[lu, hu]` — classically the mean value theorem. Here without it:

  * `near_S`, `near_C` — `|S_{N+2}(d) − d| ≤ a²·S_a(N)`, `|C_{N+2}(d) − 1| ≤ a²·S_a(N)` (`|d| ≤ a`);
  * `step_S`, `step_C` — one grid step from the addition formulas: `S(x + δ) − S(x) − δ·C(x)` is `O(δ²)` plus the
    formulas' own corner;
  * `chord_gen` — `2^K` steps of `δ = (b − a)/2^K`: the steps telescope, `χ` is the grid's average of the
    derivative's values, each eventually in its reading; the error `O((b − a)²/2^K)` plus `2^K` corners → 0;
  * `chord_sin`, `chord_cos` — the chords inside `cos`'s and `−sin`'s readings.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

theorem tm_succ_le {a : QExpr} (ha : qle qzero a) (m : Nat) : qle (tm a (m + 1)) (qmul (tm a m) a) := by
  have t0 := qmul_nonneg (tm_nonneg ha m) ha
  have i1 : qle (qinv' (qnat (m + 1))) qone := by
    have c := qmul_inv'_cancel (qnat_ne_zero m)
    have p := qinv'_nonneg_of_pos (qnat_succ_pos m)
    have o : qle qone (qnat (m + 1)) := by have := qnat_succ m; have := qnat_nonneg m; rat_linarith
    have s := scale_l o p
    have c' := qmul_comm (qnat (m + 1)) (qinv' (qnat (m + 1)))
    generalize qmul (qnat (m + 1)) (qinv' (qnat (m + 1))) = P at *
    generalize qmul (qinv' (qnat (m + 1))) (qnat (m + 1)) = P' at *
    have e : qEq (qmul (qinv' (qnat (m + 1))) qone) (qinv' (qnat (m + 1))) := by rat_ring
    rat_linarith
  have s := scale_l i1 t0
  have e : qEq (qmul (qmul (tm a m) a) qone) (qmul (tm a m) a) := by rat_ring
  have c := qmul_comm (qmul (tm a m) a) (qinv' (qnat (m + 1)))
  show qle (qmul (qmul (tm a m) a) (qinv' (qnat (m + 1)))) _
  generalize qmul (qmul (tm a m) a) qone = U at *
  generalize qmul (qmul (tm a m) a) (qinv' (qnat (m + 1))) = V at *
  generalize qmul (qinv' (qnat (m + 1))) (qmul (tm a m) a) = V' at *
  rat_linarith

theorem tm_two {a : QExpr} (ha : qle qzero a) (m : Nat) : qle (tm a (m + 2)) (qmul (qmul a a) (tm a m)) := by
  have s1 := tm_succ_le ha (m + 1)
  have s2 := scale_l (tm_succ_le ha m) ha
  have e1 : qEq (qmul a (tm a (m + 1))) (qmul (tm a (m + 1)) a) := qmul_comm _ _
  have e2 : qEq (qmul a (qmul (tm a m) a)) (qmul (qmul a a) (tm a m)) := by rat_ring
  generalize qmul a (tm a (m + 1)) = X at *; generalize qmul (tm a (m + 1)) a = X' at *
  generalize qmul a (qmul (tm a m) a) = Y at *; generalize qmul (qmul a a) (tm a m) = Y' at *
  rat_linarith

/-- The tail past the first two terms, against `a²·S_a`. -/
theorem tail2 {F : Nat → QExpr} {a : QExpr} (ha : qle qzero a) (hF : ∀ m, Ab (F m) (tm a m)) (N : Nat) :
    Ab (bs (fun i => F (i + 2)) N) (qmul (qmul a a) (S a N)) := by
  have h : ∀ i, Ab (F (i + 2)) (qmul (qmul a a) (tm a i)) := fun i => by
    obtain ⟨f1, f2⟩ := hF (i + 2); have t := tm_two ha i; exact ⟨by rat_linarith, by rat_linarith⟩
  have b := bs_abs h N
  have sc := bs_scale (qmul a a) (tm a) N
  rw [S_bs]
  obtain ⟨b1, b2⟩ := b
  generalize bs (fun i => qmul (qmul a a) (tm a i)) N = P at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem bs_two (F : Nat → QExpr) (N : Nat) : qEq (bs F (N + 2)) (qadd (qadd (F 0) (F 1)) (bs (fun i => F (i + 2)) N)) := by
  have s1 : qEq (bs F (N + 2)) (qadd (F 0) (bs (fun i => F (i + 1)) (N + 1))) := bs_shift F (N + 1)
  have s2 : qEq (bs (fun i => F (i + 1)) (N + 1)) (qadd (F 1) (bs (fun i => F (i + 2)) N)) :=
    bs_shift (fun i => F (i + 1)) N
  generalize bs F (N + 2) = A at *
  generalize bs (fun i => F (i + 1)) (N + 1) = B at *
  generalize bs (fun i => F (i + 2)) N = C at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem ci_one (d : QExpr) : qEq (ci d 1) d := by
  show qEq (qmul (qmul qone d) (qinv' (qnat 1))) d
  have := tm_one d
  exact this

theorem cr_one (d : QExpr) : qEq (cr d 1) qzero := by
  show qEq (qmul (qmul (qneg qzero) d) (qinv' (qnat 1))) qzero; rat_ring

/-- `sin d ≈ d` to second order. -/
theorem near_S {d a : QExpr} (hd : Ab d a) (N : Nat) : Ab (qsub (Sn d (N + 2)) d) (qmul (qmul a a) (S a N)) := by
  have ha : qle qzero a := by obtain ⟨h1, h2⟩ := hd; rat_linarith
  have t := tail2 ha (fun m => (crci_abs hd m).2) N
  have e := bs_two (ci d) N
  have c1 := ci_one d
  have c0 : qEq (ci d 0) qzero := qEq_refl _
  obtain ⟨t1, t2⟩ := t
  unfold Sn
  generalize bs (ci d) (N + 2) = A at *; generalize bs (fun i => ci d (i + 2)) N = T at *
  generalize ci d 1 = c at *; generalize ci d 0 = c' at *
  unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `cos d ≈ 1` to second order. -/
theorem near_C {d a : QExpr} (hd : Ab d a) (N : Nat) : Ab (qsub (Cn d (N + 2)) qone) (qmul (qmul a a) (S a N)) := by
  have ha : qle qzero a := by obtain ⟨h1, h2⟩ := hd; rat_linarith
  have t := tail2 ha (fun m => (crci_abs hd m).1) N
  have e := bs_two (cr d) N
  have c1 := cr_one d
  have c0 : qEq (cr d 0) qone := qEq_refl _
  obtain ⟨t1, t2⟩ := t
  unfold Cn
  generalize bs (cr d) (N + 2) = A at *; generalize bs (fun i => cr d (i + 2)) N = T at *
  generalize cr d 1 = c at *; generalize cr d 0 = c' at *
  unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩

theorem tm_mono_x {a b : QExpr} (ha : qle qzero a) (hab : qle a b) : ∀ m, qle (tm a m) (tm b m)
  | 0 => qle_refl _
  | m + 1 => by
      have ih := tm_mono_x ha hab m
      have b0 : qle qzero b := qle_trans ha hab
      have t0 := tm_nonneg ha m
      have s1 := ZExp.scale ih ha
      have s2 := scale_l hab (tm_nonneg b0 m)
      have i0 := qinv'_nonneg_of_pos (qnat_succ_pos m)
      have s3 := ZExp.scale (show qle (qmul (tm a m) a) (qmul (tm b m) b) by
        have c := qmul_comm (tm b m) a; have c' := qmul_comm (tm b m) b
        generalize qmul (tm a m) a = P at *; generalize qmul (tm b m) a = Q at *; generalize qmul a (tm b m) = Q' at *
        generalize qmul (tm b m) b = R at *; generalize qmul b (tm b m) = R' at *
        rat_linarith) i0
      exact s3

theorem S_mono_x {a b : QExpr} (ha : qle qzero a) (hab : qle a b) : ∀ N, qle (S a N) (S b N)
  | 0 => qle_refl _
  | N + 1 => by
      have ih := S_mono_x ha hab N
      have t := tm_mono_x ha hab N
      show qle (qadd (S a N) (tm a N)) (qadd (S b N) (tm b N)); rat_linarith

/-- ONE GRID STEP OF `sin`: `S(x + δ) − S(x) − δ·C(x)` is the addition formula's corner plus `O(a²)`. -/
theorem step_S {x δ A a : QExpr} (hx : Ab x A) (h1 : Ab δ qone) (hδ : Ab δ a) (N : Nat) :
    Ab (qsub (qsub (Sn (qadd x δ) (N + 2)) (Sn x (N + 2))) (qmul δ (Cn x (N + 2))))
      (qadd (qadd (corner (tm A) (tm qone) (N + 2)) (corner (tm A) (tm qone) (N + 2)))
        (qadd (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))) (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))))) := by
  obtain ⟨_, ⟨f1, f2⟩⟩ := add_bounds hx h1 (N + 2)
  obtain ⟨cA, sA⟩ := CS_abs hx (N + 2)
  obtain ⟨m1, m2⟩ := mul_abs cA (near_S hδ N)
  obtain ⟨n1, n2⟩ := mul_abs sA (near_C hδ N)
  have e : qEq (qsub (qsub (Sn (qadd x δ) (N + 2)) (Sn x (N + 2))) (qmul δ (Cn x (N + 2))))
      (qadd (qsub (Sn (qadd x δ) (N + 2)) (qadd (qmul (Cn x (N + 2)) (Sn δ (N + 2))) (qmul (Sn x (N + 2)) (Cn δ (N + 2)))))
        (qadd (qmul (Cn x (N + 2)) (qsub (Sn δ (N + 2)) δ)) (qmul (Sn x (N + 2)) (qsub (Cn δ (N + 2)) qone)))) := by
    unfold qsub; rat_ring
  generalize qsub (Sn (qadd x δ) (N + 2)) (qadd (qmul (Cn x (N + 2)) (Sn δ (N + 2))) (qmul (Sn x (N + 2)) (Cn δ (N + 2)))) = P at *
  generalize qmul (Cn x (N + 2)) (qsub (Sn δ (N + 2)) δ) = Q at *
  generalize qmul (Sn x (N + 2)) (qsub (Cn δ (N + 2)) qone) = R at *
  generalize qsub (qsub (Sn (qadd x δ) (N + 2)) (Sn x (N + 2))) (qmul δ (Cn x (N + 2))) = L at *
  generalize corner (tm A) (tm qone) (N + 2) = K at *
  generalize qmul (S A (N + 2)) (qmul (qmul a a) (S a N)) = T at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- ONE GRID STEP OF `cos`: `C(x + δ) − C(x) + δ·S(x)` likewise. -/
theorem step_C {x δ A a : QExpr} (hx : Ab x A) (h1 : Ab δ qone) (hδ : Ab δ a) (N : Nat) :
    Ab (qsub (qsub (Cn (qadd x δ) (N + 2)) (Cn x (N + 2))) (qmul δ (qneg (Sn x (N + 2)))))
      (qadd (qadd (corner (tm A) (tm qone) (N + 2)) (corner (tm A) (tm qone) (N + 2)))
        (qadd (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))) (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))))) := by
  obtain ⟨⟨f1, f2⟩, _⟩ := add_bounds hx h1 (N + 2)
  obtain ⟨cA, sA⟩ := CS_abs hx (N + 2)
  obtain ⟨m1, m2⟩ := mul_abs cA (near_C hδ N)
  obtain ⟨n1, n2⟩ := mul_abs sA (near_S hδ N)
  have e : qEq (qsub (qsub (Cn (qadd x δ) (N + 2)) (Cn x (N + 2))) (qmul δ (qneg (Sn x (N + 2)))))
      (qadd (qsub (Cn (qadd x δ) (N + 2)) (qsub (qmul (Cn x (N + 2)) (Cn δ (N + 2))) (qmul (Sn x (N + 2)) (Sn δ (N + 2)))))
        (qsub (qmul (Cn x (N + 2)) (qsub (Cn δ (N + 2)) qone)) (qmul (Sn x (N + 2)) (qsub (Sn δ (N + 2)) δ)))) := by
    unfold qsub; rat_ring
  generalize qsub (Cn (qadd x δ) (N + 2)) (qsub (qmul (Cn x (N + 2)) (Cn δ (N + 2))) (qmul (Sn x (N + 2)) (Sn δ (N + 2)))) = P at *
  generalize qmul (Cn x (N + 2)) (qsub (Cn δ (N + 2)) qone) = Q at *
  generalize qmul (Sn x (N + 2)) (qsub (Sn δ (N + 2)) δ) = R at *
  generalize qsub (qsub (Cn (qadd x δ) (N + 2)) (Cn x (N + 2))) (qmul δ (qneg (Sn x (N + 2)))) = L at *
  generalize corner (tm A) (tm qone) (N + 2) = K at *
  generalize qmul (S A (N + 2)) (qmul (qmul a a) (S a N)) = T at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The grid `x_j = a + j·(b − a)·2^−K` -/

def xg (a b : QExpr) (K j : Nat) : QExpr := qadd a (qmul (qnat j) (qmul (qsub b a) (qeps K)))

theorem g_one (K : Nat) : qEq (qmul (qnat (2 ^ K)) (qeps K)) qone := by
  have h1 := qnat_pow2 K
  have h2 : qEq (qmul (qofInt (pow2 K)) (qeps (0 + K))) (qeps 0) := qpow2_mul_eps K 0
  rw [Nat.zero_add] at h2
  exact qEq_trans (qmul_respects h1 (qEq_refl _)) (qEq_trans h2 qeps_zero)

theorem xg_zero (a b : QExpr) (K : Nat) : qEq (xg a b K 0) a := by
  have e := qmul_respects (qnat_zero) (qEq_refl (qmul (qsub b a) (qeps K)))
  unfold xg; generalize qmul (qnat 0) (qmul (qsub b a) (qeps K)) = P at *
  have : qEq (qmul qzero (qmul (qsub b a) (qeps K))) qzero := by rat_ring
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem xg_top (a b : QExpr) (K : Nat) : qEq (xg a b K (2 ^ K)) b := by
  have g := g_one K
  have e : qEq (qmul (qnat (2 ^ K)) (qmul (qsub b a) (qeps K))) (qmul (qsub b a) (qmul (qnat (2 ^ K)) (qeps K))) := by
    rat_ring
  have f := qmul_respects (qEq_refl (qsub b a)) g
  unfold xg
  generalize qmul (qnat (2 ^ K)) (qmul (qsub b a) (qeps K)) = P at *
  generalize qmul (qnat (2 ^ K)) (qeps K) = Q at *
  have o : qEq (qmul (qsub b a) qone) (qsub b a) := by rat_ring
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem xg_succ (a b : QExpr) (K j : Nat) : qEq (xg a b K (j + 1)) (qadd (xg a b K j) (qmul (qsub b a) (qeps K))) := by
  have e := qmul_respects (qnat_succ j) (qEq_refl (qmul (qsub b a) (qeps K)))
  unfold xg
  generalize qmul (qnat (j + 1)) (qmul (qsub b a) (qeps K)) = P at *
  have d : qEq (qmul (qadd (qnat j) qone) (qmul (qsub b a) (qeps K)))
      (qadd (qmul (qnat j) (qmul (qsub b a) (qeps K))) (qmul (qsub b a) (qeps K))) := by rat_ring
  generalize qmul (qadd (qnat j) qone) (qmul (qsub b a) (qeps K)) = P' at *
  generalize qmul (qnat j) (qmul (qsub b a) (qeps K)) = P'' at *
  generalize qmul (qsub b a) (qeps K) = D at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- A grid point is a convex combination: `x_j = a + T·(b − a)`, `T = j·2^−K ∈ [0, 1]` for `j ≤ 2^K`. -/
theorem xg_T (a b : QExpr) (K j : Nat) : qEq (xg a b K j) (qadd a (qmul (qmul (qnat j) (qeps K)) (qsub b a))) := by
  unfold xg; rat_ring

theorem T_unit {K j : Nat} (hj : j ≤ 2 ^ K) : qle qzero (qmul (qnat j) (qeps K)) ∧ qle (qmul (qnat j) (qeps K)) qone := by
  have m := ZExp.scale (qnat_mono hj) (qeps_nonneg K)
  have g := g_one K
  exact ⟨qmul_nonneg (qnat_nonneg j) (qeps_nonneg K), by rat_linarith⟩

theorem conv {a b L U T : QExpr} (t0 : qle qzero T) (t1 : qle T qone) (a1 : qle L a) (a2 : qle a U)
    (b1 : qle L b) (b2 : qle b U) : qle L (qadd a (qmul T (qsub b a))) ∧ qle (qadd a (qmul T (qsub b a))) U := by
  have p1 := qmul_nonneg (show qle qzero (qsub qone T) by unfold qsub; rat_linarith) (show qle qzero (qsub a L) by unfold qsub; rat_linarith)
  have p2 := qmul_nonneg t0 (show qle qzero (qsub b L) by unfold qsub; rat_linarith)
  have p3 := qmul_nonneg (show qle qzero (qsub qone T) by unfold qsub; rat_linarith) (show qle qzero (qsub U a) by unfold qsub; rat_linarith)
  have p4 := qmul_nonneg t0 (show qle qzero (qsub U b) by unfold qsub; rat_linarith)
  have e1 : qEq (qadd (qmul (qsub qone T) (qsub a L)) (qmul T (qsub b L))) (qsub (qadd a (qmul T (qsub b a))) L) := by
    unfold qsub; rat_ring
  have e2 : qEq (qadd (qmul (qsub qone T) (qsub U a)) (qmul T (qsub U b))) (qsub U (qadd a (qmul T (qsub b a)))) := by
    unfold qsub; rat_ring
  generalize qmul (qsub qone T) (qsub a L) = P1 at *; generalize qmul T (qsub b L) = P2 at *
  generalize qmul (qsub qone T) (qsub U a) = P3 at *; generalize qmul T (qsub U b) = P4 at *
  generalize qmul T (qsub b a) = W at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## Finite sums -/

theorem bs_tele (f : Nat → QExpr) : ∀ G, qEq (bs (fun j => qsub (f (j + 1)) (f j)) G) (qsub (f G) (f 0))
  | 0 => by show qEq qzero (qsub (f 0) (f 0)); unfold qsub; rat_ring
  | G + 1 => by
      have ih := bs_tele f G
      show qEq (qadd (bs (fun j => qsub (f (j + 1)) (f j)) G) (qsub (f (G + 1)) (f G))) _
      generalize bs (fun j => qsub (f (j + 1)) (f j)) G = P at *
      unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem bs_abs_c {g : Nat → QExpr} {c : QExpr} : ∀ G, (∀ j, j < G → Ab (g j) c) → Ab (bs g G) (qmul (qnat G) c)
  | 0, _ => by
      show Ab qzero (qmul (qnat 0) c)
      have e := qmul_respects qnat_zero (qEq_refl c)
      have z : qEq (qmul qzero c) qzero := by rat_ring
      generalize qmul (qnat 0) c = P at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | G + 1, h => by
      obtain ⟨i1, i2⟩ := bs_abs_c G (fun j hj => h j (Nat.lt_succ_of_lt hj))
      obtain ⟨t1, t2⟩ := h G (Nat.lt_succ_self G)
      have e := qmul_respects (qnat_succ G) (qEq_refl c)
      have d : qEq (qmul (qadd (qnat G) qone) c) (qadd (qmul (qnat G) c) c) := by rat_ring
      show Ab (qadd (bs g G) (g G)) _
      generalize qmul (qnat (G + 1)) c = P at *; generalize qmul (qadd (qnat G) qone) c = P' at *
      generalize qmul (qnat G) c = Q at *
      exact ⟨by rat_linarith, by rat_linarith⟩

theorem bs_in_c {g : Nat → QExpr} {l h : QExpr} : ∀ G, (∀ j, j < G → qle l (g j) ∧ qle (g j) h) →
    qle (qmul (qnat G) l) (bs g G) ∧ qle (bs g G) (qmul (qnat G) h)
  | 0, _ => by
      show qle (qmul (qnat 0) l) qzero ∧ qle qzero (qmul (qnat 0) h)
      have e1 := qmul_respects qnat_zero (qEq_refl l); have e2 := qmul_respects qnat_zero (qEq_refl h)
      have z1 : qEq (qmul qzero l) qzero := by rat_ring
      have z2 : qEq (qmul qzero h) qzero := by rat_ring
      generalize qmul (qnat 0) l = P at *; generalize qmul (qnat 0) h = Q at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | G + 1, hg => by
      obtain ⟨i1, i2⟩ := bs_in_c G (fun j hj => hg j (Nat.lt_succ_of_lt hj))
      obtain ⟨t1, t2⟩ := hg G (Nat.lt_succ_self G)
      have e1 := qmul_respects (qnat_succ G) (qEq_refl l); have e2 := qmul_respects (qnat_succ G) (qEq_refl h)
      have d1 : qEq (qmul (qadd (qnat G) qone) l) (qadd (qmul (qnat G) l) l) := by rat_ring
      have d2 : qEq (qmul (qadd (qnat G) qone) h) (qadd (qmul (qnat G) h) h) := by rat_ring
      show qle _ (qadd (bs g G) (g G)) ∧ qle (qadd (bs g G) (g G)) _
      generalize qmul (qnat (G + 1)) l = P at *; generalize qmul (qadd (qnat G) qone) l = P' at *
      generalize qmul (qnat G) l = Q at *
      generalize qmul (qnat (G + 1)) h = R at *; generalize qmul (qadd (qnat G) qone) h = R' at *
      generalize qmul (qnat G) h = T at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- Finitely many "eventually"s are one "eventually" — by induction, no choice. -/
theorem fin_N {P : Nat → Nat → Prop} (h : ∀ j, ∃ N, ∀ n, N ≤ n → P j n) :
    ∀ G, ∃ N, ∀ n, N ≤ n → ∀ j, j < G → P j n
  | 0 => ⟨0, fun _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | G + 1 => by
      obtain ⟨N1, h1⟩ := fin_N h G
      obtain ⟨N2, h2⟩ := h G
      refine ⟨N1 + N2, fun n hn j hj => ?_⟩
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
      | inl l => exact h1 n (le_l' hn) j l
      | inr e => rw [e]; exact h2 n (le_r' hn)

/-! ## The chord -/

theorem Ev_xg {a b : Nat → QExpr} {lu hu : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu) {K j : Nat} (hj : j ≤ 2 ^ K) :
    Ev (fun n => xg (a n) (b n) K j) lu hu := fun k => by
  obtain ⟨N1, h1⟩ := ha k; obtain ⟨N2, h2⟩ := hb k
  obtain ⟨t0, t1⟩ := T_unit hj
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := h1 n (le_l' hn); obtain ⟨b1, b2⟩ := h2 n (le_r' hn)
  obtain ⟨c1, c2⟩ := conv t0 t1 a1 a2 b1 b2
  have e := xg_T (a n) (b n) K j
  show qle _ (xg (a n) (b n) K j) ∧ qle (xg (a n) (b n) K j) _
  generalize xg (a n) (b n) K j = X at *
  generalize qadd (a n) (qmul (qmul (qnat j) (qeps K)) (qsub (b n) (a n))) = Y at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- The average of `2^K` values times `2^−K`. -/
theorem avg_in {Sg l h : QExpr} {K : Nat} (hs : qle (qmul (qnat (2 ^ K)) l) Sg ∧ qle Sg (qmul (qnat (2 ^ K)) h)) :
    qle l (qmul (qeps K) Sg) ∧ qle (qmul (qeps K) Sg) h := by
  have g := g_one K
  have s1 := scale_l hs.1 (qeps_nonneg K)
  have s2 := scale_l hs.2 (qeps_nonneg K)
  have e1 : qEq (qmul (qeps K) (qmul (qnat (2 ^ K)) l)) (qmul (qmul (qnat (2 ^ K)) (qeps K)) l) := by rat_ring
  have e2 : qEq (qmul (qeps K) (qmul (qnat (2 ^ K)) h)) (qmul (qmul (qnat (2 ^ K)) (qeps K)) h) := by rat_ring
  have f1 := qmul_respects g (qEq_refl l); have f2 := qmul_respects g (qEq_refl h)
  have o1 : qEq (qmul qone l) l := by rat_ring
  have o2 : qEq (qmul qone h) h := by rat_ring
  generalize qmul (qeps K) (qmul (qnat (2 ^ K)) l) = P at *; generalize qmul (qeps K) (qmul (qnat (2 ^ K)) h) = Q at *
  generalize qmul (qmul (qnat (2 ^ K)) (qeps K)) l = P' at *; generalize qmul (qmul (qnat (2 ^ K)) (qeps K)) h = Q' at *
  generalize qmul (qeps K) Sg = X at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- The total error: `2^K·(ε' + (D·2^−K)²·H) = 2^K·ε' + D²H·2^−K`. -/
theorem err_total (e' Dm H : QExpr) (K : Nat) :
    qEq (qmul (qnat (2 ^ K)) (qadd e' (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)))
      (qadd (qmul (qnat (2 ^ K)) e') (qmul (qmul (qmul Dm Dm) H) (qeps K))) := by
  have g := g_one K
  have e : qEq (qmul (qnat (2 ^ K)) (qadd e' (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)))
      (qadd (qmul (qnat (2 ^ K)) e') (qmul (qmul (qmul (qmul Dm Dm) H) (qeps K)) (qmul (qnat (2 ^ K)) (qeps K)))) := by
    rat_ring
  have f := qmul_respects (qEq_refl (qmul (qmul (qmul Dm Dm) H) (qeps K))) g
  have o : qEq (qmul (qmul (qmul (qmul Dm Dm) H) (qeps K)) qone) (qmul (qmul (qmul Dm Dm) H) (qeps K)) := by rat_ring
  generalize qmul (qmul (qmul (qmul Dm Dm) H) (qeps K)) (qmul (qnat (2 ^ K)) (qeps K)) = P at *
  generalize qmul (qmul (qmul (qmul Dm Dm) H) (qeps K)) qone = P' at *
  generalize qmul (qnat (2 ^ K)) (qadd e' (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)) = L at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE CHORD, GENERICALLY: a value function `F` whose grid steps are `δ·D + O(δ²)` (plus a vanishing part), `D`
read in `[dl, dh]` over `[lu, hu]`: from some index on, `F(b) − F(a) = (b − a)·χ` up to `ε_k`, `χ ∈ [dl, dh] ± ε_k`. -/
theorem chord_gen (F D : QExpr → Nat → QExpr) (hF : ∀ x y n, qEq x y → qEq (F x n) (F y n))
    (step : ∀ {A : QExpr}, qle qzero A → ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x δ a, Ab x A → Ab δ qone →
      Ab δ a → qle a qone → Ab (qsub (qsub (F (qadd x δ) n) (F x n)) (qmul δ (D x n))) (qadd (qeps k) (qmul (qmul a a) H)))
    {a b : Nat → QExpr} {lu hu dl dh : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu)
    (hD : ∀ x : Nat → QExpr, Ev x lu hu → Ev (fun n => D (x n) n) dl dh) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub dl (qeps k)) χ ∧ qle χ (qadd dh (qeps k)) ∧
      Ab (qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) χ)) (qeps k) := by
  intro k
  obtain ⟨M, _, hM0, _, ml, mh, _, _⟩ := bound4 lu hu lu hu
  have o := qle_of_qlt qone_pos
  have hA0 : qle qzero (qadd M qone) := by rat_linarith
  obtain ⟨H, hH0, hH⟩ := step hA0
  have hD0 : qle qzero (qadd (qadd M qone) (qadd M qone)) := by rat_linarith
  generalize hAd : qadd M qone = A at hA0 hD0 hH
  generalize hDd : qadd A A = Dm at hD0
  obtain ⟨Bc, hB1, _⟩ := qexpr_bound (qadd (qmul (qmul Dm Dm) H) Dm)
  have hX0 : qle qzero (qmul (qmul Dm Dm) H) := qmul_nonneg (qmul_nonneg hD0 hD0) hH0
  have hC : qle (qadd (qmul (qmul Dm Dm) H) Dm) (qofInt (pow2 Bc)) := by unfold qsub at hB1; rat_linarith
  -- K: the grid's depth
  have pe := qpow2_mul_eps Bc (k + 1)
  have sK := ZExp.scale hC (qeps_nonneg ((k + 1) + Bc))
  have c1 := qmul_comm (qofInt (pow2 Bc)) (qeps ((k + 1) + Bc))
  have d1 : qEq (qmul (qadd (qmul (qmul Dm Dm) H) Dm) (qeps ((k + 1) + Bc)))
      (qadd (qmul (qmul (qmul Dm Dm) H) (qeps ((k + 1) + Bc))) (qmul Dm (qeps ((k + 1) + Bc)))) := by rat_ring
  have p1 := qmul_nonneg hX0 (qeps_nonneg ((k + 1) + Bc))
  have p2 := qmul_nonneg hD0 (qeps_nonneg ((k + 1) + Bc))
  have ek := qeps_succ_add k
  have e1 := qeps_le_one (k + 1)
  have bK1 : qle (qmul (qmul (qmul Dm Dm) H) (qeps ((k + 1) + Bc))) (qeps (k + 1)) := by
    generalize qmul (qadd (qmul (qmul Dm Dm) H) Dm) (qeps ((k + 1) + Bc)) = P at *
    generalize qmul (qofInt (pow2 Bc)) (qeps ((k + 1) + Bc)) = Q at *
    generalize qmul (qeps ((k + 1) + Bc)) (qofInt (pow2 Bc)) = Q' at *
    rat_linarith
  have bK2 : qle (qmul Dm (qeps ((k + 1) + Bc))) qone := by
    generalize qmul (qadd (qmul (qmul Dm Dm) H) Dm) (qeps ((k + 1) + Bc)) = P at *
    generalize qmul (qofInt (pow2 Bc)) (qeps ((k + 1) + Bc)) = Q at *
    generalize qmul (qeps ((k + 1) + Bc)) (qofInt (pow2 Bc)) = Q' at *
    rat_linarith
  generalize hK : (k + 1) + Bc = K at bK1 bK2 p2
  -- the step's precision: 2^K·ε' = ε_{k+1}
  have pS := qpow2_mul_eps K (k + 1)
  have qn := qnat_pow2 K
  have eS : qEq (qmul (qnat (2 ^ K)) (qeps ((k + 1) + K))) (qeps (k + 1)) :=
    qEq_trans (qmul_respects qn (qEq_refl _)) pS
  obtain ⟨Ns, hNs⟩ := hH ((k + 1) + K)
  -- the derivative at every grid point
  obtain ⟨Nd, hNd⟩ := fin_N (P := fun j n => j < 2 ^ K →
      qle (qsub dl (qeps k)) (D (xg (a n) (b n) K j) n) ∧ qle (D (xg (a n) (b n) K j) n) (qadd dh (qeps k)))
    (fun j => by
      cases Nat.lt_or_ge j (2 ^ K) with
      | inl hj =>
        obtain ⟨N, hN⟩ := hD _ (Ev_xg ha hb (Nat.le_of_lt hj)) k
        exact ⟨N, fun n hn _ => hN n hn⟩
      | inr hj => exact ⟨0, fun _ _ h => absurd h (Nat.not_lt_of_ge hj)⟩) (2 ^ K)
  obtain ⟨Na, hNa⟩ := ha 0
  obtain ⟨Nb, hNb⟩ := hb 0
  refine ⟨Ns + (Nd + (Na + Nb)), fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := hNa n (le_l' (le_r' (le_r' hn)))
  obtain ⟨b1, b2⟩ := hNb n (le_r' (le_r' (le_r' hn)))
  have z := qeps_zero
  obtain ⟨m1, m2⟩ := ml; obtain ⟨m3, m4⟩ := mh
  unfold qsub at m1 m2 m3 m4 a1 b1
  -- the grid's points within `A`, the step within `Dm·ε_K ≤ 1`
  have lo1 : qle (qneg A) (qsub lu qone) := by rw [← hAd]; unfold qsub; rat_linarith
  have hi1 : qle (qadd hu qone) A := by rw [← hAd]; rat_linarith
  have aL : qle (qsub lu qone) (a n) := by unfold qsub; rat_linarith
  have aU : qle (a n) (qadd hu qone) := by rat_linarith
  have bL : qle (qsub lu qone) (b n) := by unfold qsub; rat_linarith
  have bU : qle (b n) (qadd hu qone) := by rat_linarith
  have gA : ∀ j, j ≤ 2 ^ K → Ab (xg (a n) (b n) K j) A := fun j hj => by
    obtain ⟨t0, t1⟩ := T_unit hj
    obtain ⟨c1, c2⟩ := conv t0 t1 aL aU bL bU
    have e := xg_T (a n) (b n) K j
    generalize xg (a n) (b n) K j = X at *
    generalize qadd (a n) (qmul (qmul (qnat j) (qeps K)) (qsub (b n) (a n))) = Y at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  have hΔ : Ab (qsub (b n) (a n)) Dm := by
    rw [← hDd]; obtain ⟨x1, x2⟩ := gA 0 (Nat.zero_le _)
    have e0 := xg_zero (a n) (b n) K
    generalize xg (a n) (b n) K 0 = X at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have hδ : Ab (qmul (qsub (b n) (a n)) (qeps K)) (qmul Dm (qeps K)) :=
    mul_abs hΔ ⟨by have := qeps_nonneg K; rat_linarith, qle_refl _⟩
  have hδ1 : Ab (qmul (qsub (b n) (a n)) (qeps K)) qone := by
    obtain ⟨d1, d2⟩ := hδ; exact ⟨by rat_linarith, by rat_linarith⟩
  -- each step
  have st : ∀ j, j < 2 ^ K → Ab (qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)))
      (qadd (qeps ((k + 1) + K)) (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)) := fun j hj => by
    have s := hNs n (le_l' hn) _ _ _ (gA j (Nat.le_of_lt hj)) hδ1 hδ bK2
    have r := hF _ _ n (qEq_symm (xg_succ (a n) (b n) K j))
    obtain ⟨s1, s2⟩ := s
    generalize F (qadd (xg (a n) (b n) K j) (qmul (qsub (b n) (a n)) (qeps K))) n = P at *
    generalize F (xg (a n) (b n) K (j + 1)) n = P' at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨S1, S2⟩ := bs_abs_c (2 ^ K) st
  -- the sum, rearranged
  have tl := bs_tele (fun j => F (xg (a n) (b n) K j) n) (2 ^ K)
  have sb := bs_sub (fun j => qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
    (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)) (2 ^ K)
  have sc := bs_scale (qmul (qsub (b n) (a n)) (qeps K)) (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)
  have fT := hF _ _ n (xg_top (a n) (b n) K)
  have f0 := hF _ _ n (xg_zero (a n) (b n) K)
  have et := err_total (qeps ((k + 1) + K)) Dm H K
  have bd := hNd n (le_l' (le_r' hn))
  obtain ⟨χ1, χ2⟩ := avg_in (K := K) (bs_in_c (2 ^ K) (fun j hj => bd j hj hj))
  refine ⟨qmul (qeps K) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)), χ1, χ2, ?_⟩
  have re : qEq (qmul (qmul (qsub (b n) (a n)) (qeps K)) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)))
      (qmul (qsub (b n) (a n)) (qmul (qeps K) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)))) := by rat_ring
  generalize bs (fun j => qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n))) (2 ^ K) = Tot at *
  generalize bs (fun j => qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n)) (2 ^ K) = Tl at *
  generalize bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)) (2 ^ K) = Sd at *
  generalize qmul (qmul (qsub (b n) (a n)) (qeps K)) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)) = Sd' at *
  generalize qmul (qsub (b n) (a n)) (qmul (qeps K) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K))) = W at *
  generalize F (xg (a n) (b n) K (2 ^ K)) n = Fb' at *; generalize F (xg (a n) (b n) K 0) n = Fa' at *
  generalize F (b n) n = Fb at *; generalize F (a n) n = Fa at *
  generalize qmul (qnat (2 ^ K)) (qadd (qeps ((k + 1) + K)) (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)) = E at *
  generalize qmul (qnat (2 ^ K)) (qeps ((k + 1) + K)) = E1 at *
  generalize qmul (qmul (qmul Dm Dm) H) (qeps K) = E2 at *
  clear hNs hNd hNa hNb hH hD st gA bd χ1 χ2
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The step's bound made uniform: the corner below `ε_k`, `S_A ≤ H_A`, `S_a ≤ S_1 ≤ H_1` (`a ≤ 1`). -/
theorem step_unif_core {A : QExpr} (hA : qle qzero A) : ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ m, N ≤ m + 2 → ∀ a,
    qle qzero a → qle a qone →
    qle (qadd (qadd (corner (tm A) (tm qone) (m + 2)) (corner (tm A) (tm qone) (m + 2)))
      (qadd (qmul (S A (m + 2)) (qmul (qmul a a) (S a m))) (qmul (S A (m + 2)) (qmul (qmul a a) (S a m)))))
      (qadd (qeps k) (qmul (qmul a a) H)) := by
  have o := qle_of_qlt qone_pos
  obtain ⟨HA, hHA⟩ := S_bounded hA
  obtain ⟨H1, hH1⟩ := S_bounded o
  have HA0 : qle qzero HA := qle_trans (S_nonneg hA 0) (hHA 0)
  have H10 : qle qzero H1 := qle_trans (S_nonneg o 0) (hH1 0)
  refine ⟨qadd (qmul HA H1) (qmul HA H1), by have := qmul_nonneg HA0 H10; rat_linarith, fun k => ?_⟩
  obtain ⟨Nc, hNc⟩ := corner_small hA o (k + 1)
  refine ⟨Nc, fun m hm a a0 a1 => ?_⟩
  have c := hNc (m + 2) hm
  have e := qeps_succ_add k
  have aa := qmul_nonneg a0 a0
  have sa : qle (S a m) H1 := qle_trans (S_mono_x a0 a1 m) (hH1 m)
  have sa0 := S_nonneg a0 m
  have sA := hHA (m + 2)
  have sA0 := S_nonneg hA (m + 2)
  -- S_A·(a²·S_a) ≤ H_A·(a²·H_1)
  have f1 := scale_l sa aa
  have f2 := ZExp.scale sA (qmul_nonneg aa sa0)
  have f3 := scale_l f1 HA0
  have r : qEq (qmul HA (qmul (qmul a a) H1)) (qmul (qmul a a) (qmul HA H1)) := by rat_ring
  have d : qEq (qmul (qmul a a) (qadd (qmul HA H1) (qmul HA H1))) (qadd (qmul (qmul a a) (qmul HA H1)) (qmul (qmul a a) (qmul HA H1))) := by
    rat_ring
  have cm := qmul_comm (S A (m + 2)) (qmul (qmul a a) (S a m))
  have cm' := qmul_comm HA (qmul (qmul a a) (S a m))
  generalize corner (tm A) (tm qone) (m + 2) = K at *
  generalize qmul (S A (m + 2)) (qmul (qmul a a) (S a m)) = P at *
  generalize qmul (qmul (qmul a a) (S a m)) (S A (m + 2)) = P' at *
  generalize qmul HA (qmul (qmul a a) (S a m)) = Q at *
  generalize qmul (qmul (qmul a a) (S a m)) HA = Q' at *
  generalize qmul HA (qmul (qmul a a) H1) = R at *
  generalize qmul (qmul a a) (qadd (qmul HA H1) (qmul HA H1)) = T at *
  generalize qmul (qmul a a) (qmul HA H1) = U at *
  rat_linarith

theorem step_unif_S {A : QExpr} (hA : qle qzero A) : ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x δ a, Ab x A →
    Ab δ qone → Ab δ a → qle a qone →
    Ab (qsub (qsub (Sn (qadd x δ) n) (Sn x n)) (qmul δ (Cn x n))) (qadd (qeps k) (qmul (qmul a a) H)) := by
  obtain ⟨H, H0, hH⟩ := step_unif_core hA
  refine ⟨H, H0, fun k => ?_⟩
  obtain ⟨N, hN⟩ := hH k
  refine ⟨N + 2, fun n hn x δ a hx h1 hδ a1 => ?_⟩
  have a0 : qle qzero a := by obtain ⟨d1, d2⟩ := hδ; rat_linarith
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero (N + 1))
  | succ n' => cases n' with
    | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero N)
    | succ m =>
      have b := hN m (le_l' hn) a a0 a1
      obtain ⟨s1, s2⟩ := step_S hx h1 hδ m
      exact ⟨qle_trans (by rat_linarith) s1, qle_trans s2 b⟩

theorem step_unif_C {A : QExpr} (hA : qle qzero A) : ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x δ a, Ab x A →
    Ab δ qone → Ab δ a → qle a qone →
    Ab (qsub (qsub (Cn (qadd x δ) n) (Cn x n)) (qmul δ (qneg (Sn x n)))) (qadd (qeps k) (qmul (qmul a a) H)) := by
  obtain ⟨H, H0, hH⟩ := step_unif_core hA
  refine ⟨H, H0, fun k => ?_⟩
  obtain ⟨N, hN⟩ := hH k
  refine ⟨N + 2, fun n hn x δ a hx h1 hδ a1 => ?_⟩
  have a0 : qle qzero a := by obtain ⟨d1, d2⟩ := hδ; rat_linarith
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero (N + 1))
  | succ n' => cases n' with
    | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero N)
    | succ m =>
      have b := hN m (le_l' hn) a a0 a1
      obtain ⟨s1, s2⟩ := step_C hx h1 hδ m
      exact ⟨qle_trans (by rat_linarith) s1, qle_trans s2 b⟩

theorem Ev_negate {x : Nat → QExpr} {l h : QExpr} (hx : Ev x l h) : Ev (fun n => qneg (x n)) (qneg h) (qneg l) :=
  fun k => by
    obtain ⟨N, hN⟩ := hx k
    exact ⟨N, fun n hn => by
      obtain ⟨a, b⟩ := hN n hn; show qle _ (qneg (x n)) ∧ qle (qneg (x n)) _
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩

/-- THE CHORD OF `sin` lies in the kernel's reading of `cos` over `[lu, hu]`. -/
theorem chord_sin {a b : Nat → QExpr} {lu hu cl ch : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu) (hlh : qle lu hu)
    (hi : CosHi lu hu ch) (lo : CosLo lu hu cl) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub cl (qeps k)) χ ∧ qle χ (qadd ch (qeps k)) ∧
      Ab (qsub (qsub (Sn (b n) n) (Sn (a n) n)) (qmul (qsub (b n) (a n)) χ)) (qeps k) :=
  chord_gen (fun x n => Sn x n) (fun x n => Cn x n) (fun _ _ n e => Sn_respects e n) (fun hA => step_unif_S hA)
    ha hb (fun _ hx => Ev_cos hx hlh hi lo)

/-- THE CHORD OF `cos` lies in the kernel's reading of `−sin` over `[lu, hu]`. -/
theorem chord_cos {a b : Nat → QExpr} {lu hu sl sh : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu) (hlh : qle lu hu)
    (hi : SinHi lu hu sh) (lo : SinLo lu hu sl) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub (qneg sh) (qeps k)) χ ∧ qle χ (qadd (qneg sl) (qeps k)) ∧
      Ab (qsub (qsub (Cn (b n) n) (Cn (a n) n)) (qmul (qsub (b n) (a n)) χ)) (qeps k) :=
  chord_gen (fun x n => Cn x n) (fun x n => qneg (Sn x n)) (fun _ _ n e => Cn_respects e n) (fun hA => step_unif_C hA)
    ha hb (fun _ hx => Ev_negate (Ev_sin hx hlh hi lo))

/-- A chord times a step: `F(b) − F(a) ≈ Δ·χ`, `χ` and `Δ` eventually in their intervals, the corners bracketed. -/
theorem Ev_chord_mul {Fa Fb a b : Nat → QExpr} {c1 c2 t1 t2 m M : QExpr}
    (ch : ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub c1 (qeps k)) χ ∧ qle χ (qadd c2 (qeps k)) ∧
      Ab (qsub (qsub (Fb n) (Fa n)) (qmul (qsub (b n) (a n)) χ)) (qeps k))
    (hΔ : Ev (fun n => qsub (b n) (a n)) t1 t2) (hc : Corners m M c1 c2 t1 t2) :
    Ev (fun n => qsub (Fb n) (Fa n)) m M := fun k => by
  obtain ⟨M0, B, hM0, hMB, m1, m2, m3, m4⟩ := bound4 c1 c2 t1 t2
  obtain ⟨N1, h1⟩ := ch ((k + 1) + (B + 2))
  obtain ⟨N2, h2⟩ := hΔ ((k + 1) + (B + 2))
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨χ, x1, x2, ⟨d1, d2⟩⟩ := h1 n (le_l' hn)
  obtain ⟨y1, y2⟩ := h2 n (le_r' hn)
  have he := qeps_nonneg ((k + 1) + (B + 2))
  have he1 := eps_le_one ((k + 1) + (B + 2))
  obtain ⟨p1, p2⟩ := approx_corner hc m1 m2 m3 m4 he he1 x1 x2 y1 y2
  have es := eps_scale hM0 hMB (k + 1)
  have cm := qmul_comm (qsub (b n) (a n)) χ
  have ee := qeps_succ_add k
  have el : qle (qeps ((k + 1) + (B + 2))) (qeps (k + 1)) := eps_anti (Nat.le_add_right _ _)
  show qle _ (qsub (Fb n) (Fa n)) ∧ qle (qsub (Fb n) (Fa n)) _
  generalize qmul (qsub (b n) (a n)) χ = P at *; generalize qmul χ (qsub (b n) (a n)) = P' at *
  generalize qmul (qeps ((k + 1) + (B + 2))) (qadd (qadd M0 M0) qone) = E at *
  generalize qsub (Fb n) (Fa n) = D at *
  clear h1 h2; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE KERNEL'S `(sin u)' = cos(U)·Du` IS SOUND for slopes: `Δ sin u ∈ corners(cos U, Δu)`. -/
theorem Ev_sin_slope {a b : Nat → QExpr} {lu hu cl ch t1 t2 m M : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu)
    (hlh : qle lu hu) (hi : CosHi lu hu ch) (lo : CosLo lu hu cl)
    (hΔ : Ev (fun n => qsub (b n) (a n)) t1 t2) (hc : Corners m M cl ch t1 t2) :
    Ev (fun n => qsub (Sn (b n) n) (Sn (a n) n)) m M :=
  Ev_chord_mul (chord_sin ha hb hlh hi lo) hΔ hc

/-- THE KERNEL'S `(cos u)' = −sin(U)·Du` IS SOUND for slopes. -/
theorem Ev_cos_slope {a b : Nat → QExpr} {lu hu sl sh t1 t2 m M : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu)
    (hlh : qle lu hu) (hi : SinHi lu hu sh) (lo : SinLo lu hu sl)
    (hΔ : Ev (fun n => qsub (b n) (a n)) t1 t2) (hc : Corners m M (qneg sh) (qneg sl) t1 t2) :
    Ev (fun n => qsub (Cn (b n) n) (Cn (a n) n)) m M :=
  Ev_chord_mul (chord_cos ha hb hlh hi lo) hΔ hc

end ZTrig

#print axioms ZTrig.tm_two
#print axioms ZTrig.near_S
#print axioms ZTrig.near_C
#print axioms ZTrig.S_mono_x
#print axioms ZTrig.step_S
#print axioms ZTrig.step_C
#print axioms ZTrig.xg_top
#print axioms ZTrig.xg_succ
#print axioms ZTrig.conv
#print axioms ZTrig.bs_tele
#print axioms ZTrig.bs_abs_c
#print axioms ZTrig.bs_in_c
#print axioms ZTrig.fin_N
#print axioms ZTrig.Ev_xg
#print axioms ZTrig.avg_in
#print axioms ZTrig.err_total
#print axioms ZTrig.chord_gen
#print axioms ZTrig.step_unif_S
#print axioms ZTrig.step_unif_C
#print axioms ZTrig.chord_sin
#print axioms ZTrig.chord_cos
#print axioms ZTrig.Ev_chord_mul
#print axioms ZTrig.Ev_sin_slope
#print axioms ZTrig.Ev_cos_slope
