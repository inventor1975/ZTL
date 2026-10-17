import ZJet

/-!
# ZJetRead — the kernel's interval Taylor coefficients, sound. Zero axioms.

`zcertify.taylor_coeffs` reads `f^(k)/k!` over a piece as intervals, by recurrences along the graph. `ZJet` showed
the exact jets satisfy those recurrences. Here the interval side: `CRead` mirrors the kernel's recurrences node by node
(the same sums in the same form — Miller's weights combined as the kernel combines them, since a combined weight
gives a tighter interval than two sums), and `cread_sound` shows every coefficient of every point of the box
eventually lies in its interval.

Part 1: the interval convolution `CvB` and its soundness; the exact form of Miller's sum.
-/

namespace ZJetRead

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZJet

/-- `[l, h]` bounds the convolution `Σ_{j≤m} A_j B_{m−j}` of interval families, along `cv`'s own recursion. -/
def CvB : Nat → (Nat → QExpr × QExpr) → (Nat → QExpr × QExpr) → QExpr → QExpr → Prop
  | 0, A, B, l, h => Corners l h (A 0).1 (A 0).2 (B 0).1 (B 0).2
  | m + 1, A, B, l, h => ∃ l1 h1 l2 h2, Corners l1 h1 (A 0).1 (A 0).2 (B (m + 1)).1 (B (m + 1)).2 ∧
      CvB m (fun j => A (j + 1)) B l2 h2 ∧ qle l (qadd l1 l2) ∧ qle (qadd h1 h2) h

/-- THE INTERVAL CONVOLUTION IS SOUND. -/
theorem Ev_cv : ∀ (m : Nat) (F G : Nat → Nat → QExpr) (A B : Nat → QExpr × QExpr) {l h : QExpr},
    (∀ j, j ≤ m → Ev (fun n => F n j) (A j).1 (A j).2) → (∀ j, j ≤ m → Ev (fun n => G n j) (B j).1 (B j).2) →
    CvB m A B l h → Ev (fun n => ZTrig.cv (F n) (G n) m) l h
  | 0, F, G, A, B, l, h, hF, hG, hc => Ev_mul (hF 0 (Nat.le_refl 0)) (hG 0 (Nat.le_refl 0)) hc
  | m + 1, F, G, A, B, l, h, hF, hG, hc => by
      obtain ⟨l1, h1, l2, h2, c, r, hl, hh⟩ := hc
      have e1 := Ev_mul (hF 0 (Nat.zero_le _)) (hG (m + 1) (Nat.le_refl _)) c
      have e2 := Ev_cv m (fun n j => F n (j + 1)) G (fun j => A (j + 1)) B
        (fun j hj => hF (j + 1) (Nat.succ_le_succ hj)) (fun j hj => hG j (Nat.le_trans hj (Nat.le_succ m))) r
      exact Ev_widen (Ev_add e1 e2) hl hh

/-- `c ⊇ [l, h]`. -/
def Hull (c : QExpr × QExpr) (l h : QExpr) : Prop := qle c.1 l ∧ qle h c.2

theorem Ev_hull {x : Nat → QExpr} {l h : QExpr} {c : QExpr × QExpr} (hx : Ev x l h) (hc : Hull c l h) : Ev x c.1 c.2 :=
  Ev_widen hx hc.1 hc.2

theorem Ev_const (c : QExpr) : Ev (fun _ => c) c c := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)

/-- A value eventually in an interval clear of zero is eventually nonzero. -/
theorem ev_nz {x : Nat → QExpr} {li hi lv hv : QExpr} (hx : Ev x lv hv) (h : RecipOK li hi lv hv) :
    ∃ N, ∀ n, N ≤ n → ¬ qEq (x n) qzero := by
  obtain ⟨J, hJ⟩ := recip_near h 0
  obtain ⟨N, hN⟩ := hx J
  exact ⟨N, fun n hn => by obtain ⟨a, b⟩ := hN n hn; exact (hJ (x n) a b).1⟩

/-! ## Miller's sum in the kernel's form -/

/-- `F ∗ ((s+1)·G) + (i·F) ∗ G = (j+1)·(F ∗ G)`. -/
theorem cv_weight : ∀ (j : Nat) (F G : Nat → QExpr),
    qEq (qadd (ZTrig.cv F (fun s => qmul (qnat (s + 1)) (G s)) j) (ZTrig.cv (fun i => qmul (qnat i) (F i)) G j))
      (qmul (qnat (j + 1)) (ZTrig.cv F G j))
  | 0, F, G => by
      show qEq (qadd (qmul (F 0) (qmul (qnat (0 + 1)) (G 0))) (qmul (qmul (qnat 0) (F 0)) (G 0)))
        (qmul (qnat (0 + 1)) (qmul (F 0) (G 0)))
      have z := qnat_zero
      generalize qnat (0 + 1) = c at *
      generalize qnat 0 = c0 at *
      have : qEq (qmul (qmul c0 (F 0)) (G 0)) qzero := by
        have := qmul_respects (qmul_respects z (qEq_refl (F 0))) (qEq_refl (G 0))
        exact qEq_trans this (by rat_ring)
      generalize qmul (qmul c0 (F 0)) (G 0) = Z at *
      have r : qEq (qmul (F 0) (qmul c (G 0))) (qmul c (qmul (F 0) (G 0))) := by rat_ring
      generalize qmul (F 0) (qmul c (G 0)) = X at *
      generalize qmul c (qmul (F 0) (G 0)) = Y at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | j + 1, F, G => by
      -- unfold one step of each `cv`
      show qEq (qadd (qadd (qmul (F 0) (qmul (qnat (j + 1 + 1)) (G (j + 1))))
            (ZTrig.cv (fun i => F (i + 1)) (fun s => qmul (qnat (s + 1)) (G s)) j))
          (qadd (qmul (qmul (qnat 0) (F 0)) (G (j + 1)))
            (ZTrig.cv (fun i => qmul (qnat (i + 1)) (F (i + 1))) G j)))
        (qmul (qnat (j + 1 + 1)) (qadd (qmul (F 0) (G (j + 1))) (ZTrig.cv (fun i => F (i + 1)) G j)))
      have ih := cv_weight j (fun i => F (i + 1)) G
      -- (i+1)·F(i+1) = i·F(i+1) + F(i+1)
      have sp := ZTrig.cv_congr j (fun i => qmul (qnat (i + 1)) (F (i + 1)))
        (fun i => qadd (qmul (qnat i) (F (i + 1))) (F (i + 1))) G G
        (fun i => by
          show qEq (qmul (qnat (i + 1)) (F (i + 1))) (qadd (qmul (qnat i) (F (i + 1))) (F (i + 1)))
          have q := qnat_succ i
          have := qmul_respects q (qEq_refl (F (i + 1)))
          exact qEq_trans this (by rat_ring)) (fun _ => qEq_refl _)
      have ad := ZTrig.cv_addF j (fun i => qmul (qnat i) (F (i + 1))) (fun i => F (i + 1)) G
      have q2 := qnat_succ (j + 1)
      have q1 := qnat_succ j
      have z := qnat_zero
      have z0 : qEq (qmul (qmul (qnat 0) (F 0)) (G (j + 1))) qzero := by
        have := qmul_respects (qmul_respects z (qEq_refl (F 0))) (qEq_refl (G (j + 1)))
        exact qEq_trans this (by rat_ring)
      generalize ZTrig.cv (fun i => F (i + 1)) (fun s => qmul (qnat (s + 1)) (G s)) j = X1 at *
      generalize ZTrig.cv (fun i => qmul (qnat (i + 1)) (F (i + 1))) G j = X2 at *
      generalize ZTrig.cv (fun i => qadd (qmul (qnat i) (F (i + 1))) (F (i + 1))) G j = X3 at *
      generalize ZTrig.cv (fun i => qmul (qnat i) (F (i + 1))) G j = X4 at *
      generalize ZTrig.cv (fun i => F (i + 1)) G j = X5 at *
      generalize qmul (qmul (qnat 0) (F 0)) (G (j + 1)) = Z at *
      generalize qnat (j + 1 + 1) = N2 at *
      generalize qnat (j + 1) = N1 at *
      -- N2·(F0·G + X5) = F0·N2·G + N1·X5 + X5
      have e1 : qEq (qmul (F 0) (qmul N2 (G (j + 1)))) (qmul N2 (qmul (F 0) (G (j + 1)))) := by rat_ring
      have e2 : qEq (qmul N2 (qadd (qmul (F 0) (G (j + 1))) X5)) (qadd (qmul N2 (qmul (F 0) (G (j + 1)))) (qmul N2 X5)) := by rat_ring
      have e3 : qEq (qmul N2 X5) (qadd (qmul N1 X5) X5) := by
        have := qmul_respects q2 (qEq_refl X5); exact qEq_trans this (by rat_ring)
      generalize qmul (F 0) (qmul N2 (G (j + 1))) = P1 at *
      generalize qmul N2 (qmul (F 0) (G (j + 1))) = P2 at *
      generalize qmul N2 (qadd (qmul (F 0) (G (j + 1))) X5) = P3 at *
      generalize qmul N2 X5 = P4 at *
      generalize qmul N1 X5 = P5 at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `Dsh P ∗ A = (i·P) ∗ A' + (j+1)·P_{j+1}·A₀`, `A' = A ∘ succ`. -/
theorem cvD_shift (P A : Nat → QExpr) (j : Nat) :
    qEq (ZTrig.cv (ZTrig.Dsh P) A j)
      (qadd (ZTrig.cv (fun i => qmul (qnat i) (P i)) (fun t => A (t + 1)) j) (qmul (qmul (qnat (j + 1)) (P (j + 1))) (A 0))) := by
  have sh := ZTrig.cv_shiftG j (fun i => qmul (qnat i) (P i)) A
  have u : qEq (ZTrig.cv (fun i => qmul (qnat i) (P i)) A (j + 1))
      (qadd (qmul (qmul (qnat 0) (P 0)) (A (j + 1))) (ZTrig.cv (ZTrig.Dsh P) A j)) := qEq_refl _
  have z : qEq (qmul (qmul (qnat 0) (P 0)) (A (j + 1))) qzero := by
    have := qmul_respects (qmul_respects qnat_zero (qEq_refl (P 0))) (qEq_refl (A (j + 1)))
    exact qEq_trans this (by rat_ring)
  generalize ZTrig.cv (fun i => qmul (qnat i) (P i)) A (j + 1) = X at *
  generalize qmul (qmul (qnat 0) (P 0)) (A (j + 1)) = Z at *
  generalize ZTrig.cv (ZTrig.Dsh P) A j = Y at *
  generalize ZTrig.cv (fun i => qmul (qnat i) (P i)) (fun t => A (t + 1)) j = W at *
  generalize qmul (qmul (qnat (j + 1)) (P (j + 1))) (A 0) = V at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- MILLER IN THE KERNEL'S FORM: `(j+1)·A₀·P_{j+1} = Σ_{s≤j} (m(j+1) − (m+1)s)·P_s·A_{j+1−s}`. -/
theorem pow_form (i n : Nat) (p : Point QExpr) (u : G) (m j : Nat) :
    qEq (qmul (qmul (qnat (j + 1)) (J i n p u 0)) (J i n p (.powN u m) (j + 1)))
      (ZTrig.cv (fun s => qmul (qsub (qmul (qnat m) (qnat (j + 1))) (qmul (qnat (m + 1)) (qnat s))) (J i n p (.powN u m) s))
        (fun t => J i n p u (t + 1)) j) := by
  have mi := J_miller i n p u m j
  have co := cv_comm j (J i n p u) (ZTrig.Dsh (J i n p (.powN u m)))
  have ds := cvD_shift (J i n p (.powN u m)) (J i n p u) j
  have wt := cv_weight j (J i n p (.powN u m)) (fun t => J i n p u (t + 1))
  have dA : qEq (ZTrig.cv (J i n p (.powN u m)) (ZTrig.Dsh (J i n p u)) j)
      (ZTrig.cv (J i n p (.powN u m)) (fun s => qmul (qnat (s + 1)) ((fun t => J i n p u (t + 1)) s)) j) := qEq_refl _
  -- the target, by linearity
  have lin := ZTrig.cv_congr j
    (fun s => qmul (qsub (qmul (qnat m) (qnat (j + 1))) (qmul (qnat (m + 1)) (qnat s))) (J i n p (.powN u m) s))
    (fun s => qsub (qmul (qmul (qnat m) (qnat (j + 1))) (J i n p (.powN u m) s))
      (qmul (qnat (m + 1)) (qmul (qnat s) (J i n p (.powN u m) s))))
    (fun t => J i n p u (t + 1)) (fun t => J i n p u (t + 1))
    (fun s => by
      show qEq (qmul (qsub (qmul (qnat m) (qnat (j + 1))) (qmul (qnat (m + 1)) (qnat s))) (J i n p (.powN u m) s))
        (qsub (qmul (qmul (qnat m) (qnat (j + 1))) (J i n p (.powN u m) s))
          (qmul (qnat (m + 1)) (qmul (qnat s) (J i n p (.powN u m) s))))
      unfold qsub; rat_ring) (fun _ => qEq_refl _)
  have sb := ZTrig.cv_subF j (fun s => qmul (qmul (qnat m) (qnat (j + 1))) (J i n p (.powN u m) s))
    (fun s => qmul (qnat (m + 1)) (qmul (qnat s) (J i n p (.powN u m) s))) (fun t => J i n p u (t + 1))
  have s1 := ZTrig.cv_scaleF (qmul (qnat m) (qnat (j + 1))) j (J i n p (.powN u m)) (fun t => J i n p u (t + 1))
  have s2 := ZTrig.cv_scaleF (qnat (m + 1)) j (fun s => qmul (qnat s) (J i n p (.powN u m) s)) (fun t => J i n p u (t + 1))
  have q := qnat_succ m
  unfold qsub at *
  generalize ZTrig.cv (fun s => qmul (qadd (qmul (qnat m) (qnat (j + 1))) (qneg (qmul (qnat (m + 1)) (qnat s)))) (J i n p (.powN u m) s))
    (fun t => J i n p u (t + 1)) j = T at *
  generalize ZTrig.cv (fun s => qadd (qmul (qmul (qnat m) (qnat (j + 1))) (J i n p (.powN u m) s))
      (qneg (qmul (qnat (m + 1)) (qmul (qnat s) (J i n p (.powN u m) s))))) (fun t => J i n p u (t + 1)) j = T' at *
  generalize ZTrig.cv (fun s => qmul (qmul (qnat m) (qnat (j + 1))) (J i n p (.powN u m) s)) (fun t => J i n p u (t + 1)) j = T1 at *
  generalize ZTrig.cv (fun s => qmul (qnat (m + 1)) (qmul (qnat s) (J i n p (.powN u m) s))) (fun t => J i n p u (t + 1)) j = T2 at *
  generalize ZTrig.cv (fun s => qmul (qnat s) (J i n p (.powN u m) s)) (fun t => J i n p u (t + 1)) j = IP at *
  generalize ZTrig.cv (J i n p (.powN u m)) (fun t => J i n p u (t + 1)) j = PA at *
  generalize ZTrig.cv (J i n p (.powN u m)) (fun s => qmul (qnat (s + 1)) ((fun t => J i n p u (t + 1)) s)) j = PD at *
  generalize ZTrig.cv (J i n p (.powN u m)) (ZTrig.Dsh (J i n p u)) j = PD' at *
  generalize ZTrig.cv (J i n p u) (ZTrig.Dsh (J i n p (.powN u m))) j = AP at *
  generalize ZTrig.cv (ZTrig.Dsh (J i n p (.powN u m))) (J i n p u) j = AP' at *
  generalize J i n p (.powN u m) (j + 1) = Pk at *
  generalize J i n p u 0 = A0 at *
  generalize qnat (m + 1) = M1 at *
  generalize qnat m = M at *
  generalize qnat (j + 1) = K at *
  -- the two nonlinear steps by hand, the rest is linear in the monomials
  have hPD : qEq PD' (qadd (qmul K PA) (qneg IP)) := by
    clear mi co ds lin sb s1 s2 q
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have hM := qmul_respects (qEq_refl M) hPD
  have hM1 := qmul_respects q (qEq_refl IP)
  clear wt dA hPD q
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## The reading -/

/-- `1/(m+1)`. -/
def inv1 (m : Nat) : QExpr := qinv' (qnat (m + 1))

/-- The coupled sin/cos series of `u` (the kernel computes them together): values read, then
`s_{m+1} = (c ∗ D)_m/(m+1)`, `c_{m+1} = −(s ∗ D)_m/(m+1)`, `D_t ⊇ (t+1)·a_{t+1}`. -/
def SC (B : Box QExpr) (K : Nat) (u : G) (a s c D : Nat → QExpr × QExpr) : Prop :=
  (∃ l h, VRead B (.sin u) l h ∧ Hull (s 0) l h) ∧ (∃ l h, VRead B (.cos u) l h ∧ Hull (c 0) l h) ∧
  (∀ t, t < K → Corners (D t).1 (D t).2 (qnat (t + 1)) (qnat (t + 1)) (a (t + 1)).1 (a (t + 1)).2) ∧
  (∀ m, m < K → ∃ l h l' h', CvB m c D l h ∧ Corners l' h' l h (inv1 m) (inv1 m) ∧ Hull (s (m + 1)) l' h') ∧
  (∀ m, m < K → ∃ l h l' h', CvB m s D l h ∧ Corners l' h' l h (qneg (inv1 m)) (qneg (inv1 m)) ∧ Hull (c (m + 1)) l' h')

/-- THE KERNEL'S TAYLOR COEFFICIENTS (`zcertify.taylor_coeffs`), node by node, up to order `K`, in `x_i`, over the
box `B`. Values (`k = 0`) are the kernel's value readings (`VRead`); the rest are its recurrences. -/
inductive CRead (B : Box QExpr) (i K : Nat) : G → (Nat → QExpr × QExpr) → Prop where
  | free {e : G} {c : Nat → QExpr × QExpr} {l h : QExpr} : ¬ Uses e i → VRead B e l h → Hull (c 0) l h →
      (∀ k, k < K → Hull (c (k + 1)) qzero qzero) → CRead B i K e c
  | var {c : Nat → QExpr × QExpr} : Hull (c 0) (B i).1 (B i).2 → (0 < K → Hull (c 1) qone qone) →
      (∀ k, k + 1 < K → Hull (c (k + 2)) qzero qzero) → CRead B i K (.var i) c
  | add {u v : G} {a b c : Nat → QExpr × QExpr} : CRead B i K u a → CRead B i K v b →
      (∀ k, k ≤ K → Hull (c k) (qadd (a k).1 (b k).1) (qadd (a k).2 (b k).2)) → CRead B i K (.add u v) c
  | sub {u v : G} {a b c : Nat → QExpr × QExpr} : CRead B i K u a → CRead B i K v b →
      (∀ k, k ≤ K → Hull (c k) (qsub (a k).1 (b k).2) (qsub (a k).2 (b k).1)) → CRead B i K (.sub u v) c
  | mul {u v : G} {a b c : Nat → QExpr × QExpr} : CRead B i K u a → CRead B i K v b →
      (∀ k, k ≤ K → ∃ l h, CvB k a b l h ∧ Hull (c k) l h) → CRead B i K (.mul u v) c
  | div {u v : G} {a b c : Nat → QExpr × QExpr} {l0 h0 r1 r2 : QExpr} : CRead B i K u a → CRead B i K v b →
      VRead B (.div u v) l0 h0 → Hull (c 0) l0 h0 → RecipOK r1 r2 (b 0).1 (b 0).2 →
      (∀ m, m < K → ∃ l h l' h', CvB m c (fun j => b (j + 1)) l h ∧
        Corners l' h' (qsub (a (m + 1)).1 h) (qsub (a (m + 1)).2 l) r1 r2 ∧ Hull (c (m + 1)) l' h') →
      CRead B i K (.div u v) c
  | exp {u : G} {a c D : Nat → QExpr × QExpr} {l0 h0 : QExpr} : CRead B i K u a →
      VRead B (.exp u) l0 h0 → Hull (c 0) l0 h0 →
      (∀ t, t < K → Corners (D t).1 (D t).2 (qnat (t + 1)) (qnat (t + 1)) (a (t + 1)).1 (a (t + 1)).2) →
      (∀ m, m < K → ∃ l h l' h', CvB m c D l h ∧ Corners l' h' l h (inv1 m) (inv1 m) ∧ Hull (c (m + 1)) l' h') →
      CRead B i K (.exp u) c
  | sin {u : G} {a s c D : Nat → QExpr × QExpr} : CRead B i K u a → SC B K u a s c D → CRead B i K (.sin u) s
  | cos {u : G} {a s c D : Nat → QExpr × QExpr} : CRead B i K u a → SC B K u a s c D → CRead B i K (.cos u) c
  | tan {u : G} {a s c D t : Nat → QExpr × QExpr} {l0 h0 r1 r2 : QExpr} : CRead B i K u a → SC B K u a s c D →
      VRead B (.div (.sin u) (.cos u)) l0 h0 → Hull (t 0) l0 h0 → RecipOK r1 r2 (c 0).1 (c 0).2 →
      (∀ m, m < K → ∃ l h l' h', CvB m t (fun j => c (j + 1)) l h ∧
        Corners l' h' (qsub (s (m + 1)).1 h) (qsub (s (m + 1)).2 l) r1 r2 ∧ Hull (t (m + 1)) l' h') →
      CRead B i K (.tan u) t
  | powN {u : G} {m : Nat} {a p : Nat → QExpr × QExpr} {l0 h0 : QExpr} (W : Nat → Nat → QExpr × QExpr)
      (dv R : Nat → QExpr × QExpr) : CRead B i K u a → VRead B (.powN u m) l0 h0 → Hull (p 0) l0 h0 →
      (∀ j, j < K →
        (∀ s, s ≤ j → Corners (W j s).1 (W j s).2
          (qsub (qmul (qnat m) (qnat (j + 1))) (qmul (qnat (m + 1)) (qnat s)))
          (qsub (qmul (qnat m) (qnat (j + 1))) (qmul (qnat (m + 1)) (qnat s))) (p s).1 (p s).2) ∧
        Corners (dv j).1 (dv j).2 (qnat (j + 1)) (qnat (j + 1)) (a 0).1 (a 0).2 ∧
        RecipOK (R j).1 (R j).2 (dv j).1 (dv j).2 ∧
        ∃ l h l' h', CvB j (W j) (fun t => a (t + 1)) l h ∧ Corners l' h' l h (R j).1 (R j).2 ∧
          Hull (p (j + 1)) l' h') →
      CRead B i K (.powN u m) p

/-! ## Soundness -/

theorem strong_upto {K : Nat} (P : Nat → Prop) (h0 : P 0) (hs : ∀ m, m < K → (∀ j, j ≤ m → P j) → P (m + 1)) :
    ∀ k, k ≤ K → ∀ j, j ≤ k → P j
  | 0, _, j, hj => by have : j = 0 := Nat.le_zero.mp hj; subst this; exact h0
  | k + 1, hk, j, hj => by
      have ih := strong_upto P h0 hs k (Nat.le_trans (Nat.le_succ k) hk)
      cases Nat.lt_or_eq_of_le hj with
      | inl l => exact ih j (Nat.le_of_lt_succ l)
      | inr e => subst e; exact hs k (Nat.lt_of_succ_le hk) ih

theorem div_solve {x y z w : QExpr} (hz : ¬ qEq z qzero) (h : qEq (qadd y (qmul x z)) w) :
    qEq x (qmul (qsub w y) (qinv' z)) := by
  have c := qmul_inv'_cancel hz
  have a : qEq (qmul (qsub w y) (qinv' z)) (qmul (qmul x z) (qinv' z)) := by
    refine qmul_respects ?_ (qEq_refl _)
    unfold qsub; generalize qmul x z = X at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have b : qEq (qmul (qmul x z) (qinv' z)) (qmul x (qmul z (qinv' z))) := by rat_ring
  have d := qmul_respects (qEq_refl x) c
  exact qEq_symm (qEq_trans a (qEq_trans b (qEq_trans d (by rat_ring))))

theorem mul_solve {x y z : QExpr} (hz : ¬ qEq z qzero) (h : qEq (qmul z x) y) : qEq x (qmul y (qinv' z)) := by
  have h' : qEq (qadd qzero (qmul x z)) y := qEq_trans (by rat_ring) h
  have := div_solve hz h'
  exact qEq_trans this (qmul_respects (by unfold qsub; rat_ring) (qEq_refl _))

theorem nat_solve {x y : QExpr} (m : Nat) (h : qEq (qmul (qnat (m + 1)) x) y) : qEq x (qmul y (inv1 m)) :=
  mul_solve (ne_zero_of_lt (qnat_succ_pos m)) h

theorem cv_negF (F G : Nat → QExpr) (m : Nat) :
    qEq (ZTrig.cv (fun t => qneg (F t)) G m) (qneg (ZTrig.cv F G m)) := by
  have c := ZTrig.cv_congr m (fun t => qneg (F t)) (fun t => qmul (qneg qone) (F t)) G G
    (fun j => by show qEq (qneg (F j)) (qmul (qneg qone) (F j)); rat_ring) (fun _ => qEq_refl _)
  exact qEq_trans c (qEq_trans (ZTrig.cv_scaleF (qneg qone) m F G) (by rat_ring))

/-- The value of a reading, at `k = 0`. -/
theorem ev0 {B : Box QExpr} {q : Point QExpr} (hq : InBox qOrd B q) (i : Nat) {e : G} {l h : QExpr}
    {c : QExpr × QExpr} (r : VRead B e l h) (hc : Hull c l h) : Ev (fun n => J i n q e 0) c.1 c.2 :=
  Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (J_zero i n q e)) (value_sound hq r)) hc

/-- `D_t ⊇ (t+1)·a_{t+1}` bounds `Dsh J(u)`. -/
theorem ev_D {i n0 K : Nat} {q : Point QExpr} {u : G} {a D : Nat → QExpr × QExpr}
    (hu : ∀ k, k ≤ K → Ev (fun n => J i n q u k) (a k).1 (a k).2)
    (hD : ∀ t, t < K → Corners (D t).1 (D t).2 (qnat (t + 1)) (qnat (t + 1)) (a (t + 1)).1 (a (t + 1)).2)
    (m : Nat) (hm : m < K) : ∀ t, t ≤ m → Ev (fun n => ZTrig.Dsh (J i n q u) t) (D t).1 (D t).2 :=
  have _ := n0
  fun t ht => Ev_mul (Ev_const _) (hu (t + 1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ht hm)))
    (hD t (Nat.lt_of_le_of_lt ht hm))

/-- The coupled pair is sound. -/
theorem sc_sound {B : Box QExpr} {q : Point QExpr} (hq : InBox qOrd B q) {i K : Nat} {u : G} {a s c D : Nat → QExpr × QExpr}
    (hu : ∀ k, k ≤ K → Ev (fun n => J i n q u k) (a k).1 (a k).2) (h : SC B K u a s c D) :
    ∀ k, k ≤ K → ∀ j, j ≤ k →
      Ev (fun n => J i n q (.sin u) j) (s j).1 (s j).2 ∧ Ev (fun n => J i n q (.cos u) j) (c j).1 (c j).2 := by
  obtain ⟨⟨ls, hs, rs, cs⟩, ⟨lc, hc, rc, cc⟩, hD, hS, hC⟩ := h
  refine strong_upto (K := K) _ ⟨ev0 hq i rs cs, ev0 hq i rc cc⟩ (fun m hm ih => ?_)
  have eD := ev_D (n0 := 0) hu hD m hm
  obtain ⟨l, h, l', h', cb, co, hh⟩ := hS m hm
  obtain ⟨l2, h2, l2', h2', cb2, co2, hh2⟩ := hC m hm
  refine ⟨?_, ?_⟩
  · have e := Ev_mul (Ev_cv m (fun n => J i n q (.cos u)) (fun n => ZTrig.Dsh (J i n q u)) c D
      (fun j hj => (ih j hj).2) eD cb) (Ev_const (inv1 m)) co
    refine Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (nat_solve m ?_)) e) hh
    exact qEq_trans (qEq_refl _) (J_sin i n q u m)
  · have e := Ev_mul (Ev_cv m (fun n => J i n q (.sin u)) (fun n => ZTrig.Dsh (J i n q u)) s D
      (fun j hj => (ih j hj).1) eD cb2) (Ev_const (qneg (inv1 m))) co2
    refine Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm ?_) e) hh2
    have k := qEq_trans (J_cos i n q u m) (cv_negF (J i n q (.sin u)) (ZTrig.Dsh (J i n q u)) m)
    have := nat_solve m k
    exact qEq_trans this (by rat_ring)

/-- THE KERNEL'S TAYLOR COEFFICIENTS ARE SOUND: at every point of the box, every coefficient up to `K` eventually lies in
its interval. -/
theorem cread_sound {B : Box QExpr} {q : Point QExpr} (hq : InBox qOrd B q) {i K : Nat} :
    ∀ {e : G} {c : Nat → QExpr × QExpr}, CRead B i K e c → ∀ k, k ≤ K → Ev (fun n => J i n q e k) (c k).1 (c k).2 := by
  intro e c r
  induction r with
  | @free e c l h hU hV hc hz =>
      intro k hk
      cases k with
      | zero => exact ev0 hq i hV hc
      | succ k =>
          exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm ((J_free i n q e hU).2 k)) (Ev_const qzero))
            (hz k (Nat.lt_of_succ_le hk))
  | @var c h0 h1 h2 =>
      intro k hk
      match k, hk with
      | 0, _ =>
          exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (J_var i n q).1)
            (Ev_of_exact 0 (fun _ _ => hq i))) h0
      | 1, hk =>
          exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (J_var i n q).2.1) (Ev_const qone))
            (h1 (Nat.lt_of_succ_le hk))
      | k + 2, hk =>
          exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm ((J_var i n q).2.2 k)) (Ev_const qzero))
            (h2 k (Nat.lt_of_succ_le hk))
  | @add u v a b c _ _ hc ihu ihv =>
      intro k hk
      exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (J_add i n q u v k)) (Ev_add (ihu k hk) (ihv k hk))) (hc k hk)
  | @sub u v a b c _ _ hc ihu ihv =>
      intro k hk
      exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (J_sub i n q u v k)) (Ev_sub (ihu k hk) (ihv k hk))) (hc k hk)
  | @mul u v a b c _ _ hc ihu ihv =>
      intro k hk
      obtain ⟨l, h, cb, hh⟩ := hc k hk
      exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (J_mul i n q k u v))
        (Ev_cv k (fun n => J i n q u) (fun n => J i n q v) a b (fun j hj => ihu j (Nat.le_trans hj hk))
          (fun j hj => ihv j (Nat.le_trans hj hk)) cb)) hh
  | @div u v a b c l0 h0 r1 r2 _ _ hV hc0 hR hs ihu ihv =>
      intro k hk
      refine strong_upto (K := K) (fun j => Ev (fun n => J i n q (.div u v) j) (c j).1 (c j).2)
        (ev0 hq i hV hc0) (fun m hm ih => ?_) k hk k (Nat.le_refl k)
      obtain ⟨N0, hN0⟩ := ev_nz (ihv 0 (Nat.zero_le _)) hR
      obtain ⟨l, h, l', h', cb, co, hh⟩ := hs m hm
      have e := Ev_mul (Ev_sub (ihu (m + 1) (Nat.succ_le_of_lt hm))
        (Ev_cv m (fun n => J i n q (.div u v)) (fun n j => J i n q v (j + 1)) c (fun j => b (j + 1)) ih
          (fun j hj => ihv (j + 1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hj hm))) cb))
        (Ev_recip (ihv 0 (Nat.zero_le _)) hR) co
      refine Ev_hull (Ev_congr_ev N0 (fun n hn => qEq_symm ?_) e) hh
      have nz := hN0 n hn
      have hv : ¬ qEq (evalN n q v) qzero := fun z => nz (qEq_trans (J_zero i n q v) z)
      have jd := J_div i n q (m + 1) u v hv (m + 1) (Nat.le_refl _)
      have sh := ZTrig.cv_shiftG m (J i n q (.div u v)) (J i n q v)
      exact div_solve nz (qEq_trans (qEq_symm sh) jd)
  | @exp u a c D l0 h0 _ hV hc0 hD hs ihu =>
      intro k hk
      refine strong_upto (K := K) (fun j => Ev (fun n => J i n q (.exp u) j) (c j).1 (c j).2)
        (ev0 hq i hV hc0) (fun m hm ih => ?_) k hk k (Nat.le_refl k)
      obtain ⟨l, h, l', h', cb, co, hh⟩ := hs m hm
      have e := Ev_mul (Ev_cv m (fun n => J i n q (.exp u)) (fun n => ZTrig.Dsh (J i n q u)) c D ih
        (ev_D (n0 := 0) ihu hD m hm) cb) (Ev_const (inv1 m)) co
      exact Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (nat_solve m (J_exp i n q u m))) e) hh
  | @sin u a s c D _ hSC ihu =>
      intro k hk
      exact (sc_sound hq ihu hSC k hk k (Nat.le_refl k)).1
  | @cos u a s c D _ hSC ihu =>
      intro k hk
      exact (sc_sound hq ihu hSC k hk k (Nat.le_refl k)).2
  | @tan u a s c D t l0 h0 r1 r2 _ hSC hV ht0 hR hs ihu =>
      intro k hk
      have sc := sc_sound hq ihu hSC
      have v : Ev (fun n => evalN n q (.div (.sin u) (.cos u))) l0 h0 := value_sound hq hV
      have e0 : Ev (fun n => J i n q (.tan u) 0) (t 0).1 (t 0).2 :=
        Ev_hull (Ev_congr_ev (x := fun n => evalN n q (.div (.sin u) (.cos u))) 0 (fun n _ => qEq_trans
          (qEq_refl (evalN n q (.tan u)) : qEq (evalN n q (.div (.sin u) (.cos u))) (evalN n q (.tan u)))
          (qEq_symm (J_zero i n q (.tan u)))) v) ht0
      refine strong_upto (K := K) (fun j => Ev (fun n => J i n q (.tan u) j) (t j).1 (t j).2)
        e0 (fun m hm ih => ?_) k hk k (Nat.le_refl k)
      obtain ⟨N0, hN0⟩ := ev_nz (sc 0 (Nat.zero_le _) 0 (Nat.le_refl 0)).2 hR
      obtain ⟨l, h, l', h', cb, co, hh⟩ := hs m hm
      have e := Ev_mul (Ev_sub (sc (m + 1) (Nat.succ_le_of_lt hm) (m + 1) (Nat.le_refl _)).1
        (Ev_cv m (fun n => J i n q (.tan u)) (fun n j => J i n q (.cos u) (j + 1)) t (fun j => c (j + 1)) ih
          (fun j hj => (sc (j + 1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hj hm)) (j + 1) (Nat.le_refl _)).2) cb))
        (Ev_recip (sc 0 (Nat.zero_le _) 0 (Nat.le_refl 0)).2 hR) co
      refine Ev_hull (Ev_congr_ev N0 (fun n hn => qEq_symm ?_) e) hh
      have nz := hN0 n hn
      have hc : ¬ qEq (evalN n q (.cos u)) qzero := fun z => nz (qEq_trans (J_zero i n q (.cos u)) z)
      have jt := J_tan i n q u hc (m + 1)
      have sh := ZTrig.cv_shiftG m (J i n q (.tan u)) (J i n q (.cos u))
      exact div_solve nz (qEq_trans (qEq_symm sh) jt)
  | @powN u m a p l0 h0 W dv R _ hV hp0 hs ihu =>
      intro k hk
      refine strong_upto (K := K) (fun j => Ev (fun n => J i n q (.powN u m) j) (p j).1 (p j).2)
        (ev0 hq i hV hp0) (fun j hj ih => ?_) k hk k (Nat.le_refl k)
      obtain ⟨hW, hdv, hR, l, h, l', h', cb, co, hh⟩ := hs j hj
      have edv : Ev (fun n => qmul (qnat (j + 1)) (J i n q u 0)) (dv j).1 (dv j).2 :=
        Ev_mul (Ev_const _) (ihu 0 (Nat.zero_le _)) hdv
      obtain ⟨N0, hN0⟩ := ev_nz edv hR
      have e := Ev_mul (Ev_cv j
        (fun n s => qmul (qsub (qmul (qnat m) (qnat (j + 1))) (qmul (qnat (m + 1)) (qnat s))) (J i n q (.powN u m) s))
        (fun n t => J i n q u (t + 1)) (W j) (fun t => a (t + 1))
        (fun s hs' => Ev_mul (Ev_const _) (ih s hs') (hW s hs'))
        (fun s hs' => ihu (s + 1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hs' hj))) cb)
        (Ev_recip edv hR) co
      exact Ev_hull (Ev_congr_ev N0 (fun n hn => qEq_symm (mul_solve (hN0 n hn) (pow_form i n q u m j))) e) hh

end ZJetRead

#print axioms ZJetRead.Ev_cv
#print axioms ZJetRead.cv_weight
#print axioms ZJetRead.pow_form
#print axioms ZJetRead.sc_sound
#print axioms ZJetRead.cread_sound
