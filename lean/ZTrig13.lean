import ZTrig12

/-!
# ZTrig13 — the second-order step of `sin` and `cos`, on a grid. Zero axioms.

Stage 13 of the full sine. The Taylor leaf of order 2 needs `R(a, b) = F(b) − F(a) − (b − a)·F'(a)`; classically
`F''(ξ)·(b − a)²/2`. Here from chords alone, as `ZExp2` did for `exp`:

  * along `2^K` steps `F(b) − F(a) = Σ δ·D(x_j) + O(δ)` (`ZTrig12`), so `R ≈ Σ δ·(D(x_j) − D(a))`;
  * each `D(x_j) − D(a) = j·δ·χ_j` up to `ε`, `χ_j` a chord of `D` — inside the reading of `D'` (`ZTrig12`); the
    factor `j·δ² ≥ 0` whatever the sign of `δ`, so `χ_j` is eliminated term by term (no choice of a function);
  * `2·Σ_{j<G} j = G² − G`, `δ²G² = Δ²`: `2R ∈ Δ²·[D'_lo, D'_hi]`, up to `ε_k` from some index on (`chord2_gen`);
  * `Ev_sin2`: `2R_sin ∈ Δ²·[−sh, −sl]`; `Ev_cos2`: `2R_cos ∈ Δ²·[−ch, −cl]`.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-- `2·Σ_{j<G} j = G² − G`. -/
theorem bs_nat : ∀ G, qEq (qadd (bs (fun j => qnat j) G) (bs (fun j => qnat j) G))
    (qsub (qmul (qnat G) (qnat G)) (qnat G))
  | 0 => by
      show qEq (qadd qzero qzero) (qsub (qmul (qnat 0) (qnat 0)) (qnat 0))
      have z := qnat_zero
      have m := qmul_respects z z
      have e : qEq (qmul qzero qzero) qzero := by rat_ring
      generalize qmul (qnat 0) (qnat 0) = P at *; generalize qnat 0 = Z at *
      unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | G + 1 => by
      have ih := bs_nat G
      have s := qnat_succ G
      have m := qmul_respects s s
      have e : qEq (qmul (qadd (qnat G) qone) (qadd (qnat G) qone))
          (qadd (qadd (qmul (qnat G) (qnat G)) (qadd (qnat G) (qnat G))) qone) := by rat_ring
      show qEq (qadd (qadd (bs (fun j => qnat j) G) (qnat G)) (qadd (bs (fun j => qnat j) G) (qnat G))) _
      generalize bs (fun j => qnat j) G = P at *
      generalize qmul (qnat (G + 1)) (qnat (G + 1)) = Q at *
      generalize qmul (qadd (qnat G) qone) (qadd (qnat G) qone) = Q' at *
      generalize qmul (qnat G) (qnat G) = Q'' at *
      unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- One term, the chord eliminated: `δ·(D(x_j) − D(a)) ∈ j·δ²·[el − ε, eh + ε] ± |δ|·ε`. -/
theorem term_bound {δ dj da xj xa χ el eh e aK : QExpr} {j : Nat}
    (hx : qEq (qsub xj xa) (qmul (qnat j) δ)) (c1 : qle (qsub el e) χ) (c2 : qle χ (qadd eh e))
    (hc : Ab (qsub (qsub dj da) (qmul (qsub xj xa) χ)) e) (hδ : Ab δ aK) :
    qle (qsub (qmul (qmul (qnat j) (qmul δ δ)) (qsub el e)) (qmul aK e)) (qmul δ (qsub dj da)) ∧
    qle (qmul δ (qsub dj da)) (qadd (qmul (qmul (qnat j) (qmul δ δ)) (qadd eh e)) (qmul aK e)) := by
  have w0 : qle qzero (qmul (qnat j) (qmul δ δ)) := qmul_nonneg (qnat_nonneg j) (qmul_self_nonneg δ)
  have s1 := scale_l c1 w0
  have s2 := scale_l c2 w0
  obtain ⟨m1, m2⟩ := mul_abs hδ hc
  have e1 : qEq (qmul δ (qsub dj da))
      (qadd (qmul (qmul (qnat j) (qmul δ δ)) χ) (qmul δ (qsub (qsub dj da) (qmul (qsub xj xa) χ)))) := by
    have r := qmul_respects (qEq_refl δ) (qmul_respects hx (qEq_refl χ))
    have r2 : qEq (qmul δ (qmul (qmul (qnat j) δ) χ)) (qmul (qmul (qnat j) (qmul δ δ)) χ) := by rat_ring
    have r3 : qEq (qmul δ (qsub dj da)) (qadd (qmul δ (qmul (qsub xj xa) χ)) (qmul δ (qsub (qsub dj da) (qmul (qsub xj xa) χ)))) := by
      unfold qsub; rat_ring
    generalize qmul δ (qmul (qsub xj xa) χ) = P at *; generalize qmul δ (qmul (qmul (qnat j) δ) χ) = P' at *
    generalize qmul (qmul (qnat j) (qmul δ δ)) χ = P'' at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  generalize qmul δ (qsub dj da) = T at *
  generalize qmul δ (qsub (qsub dj da) (qmul (qsub xj xa) χ)) = U at *
  generalize qmul (qmul (qnat j) (qmul δ δ)) χ = V at *
  generalize qmul aK e = W at *
  exact ⟨by unfold qsub at *; rat_linarith, by rat_linarith⟩

theorem bs_const (c : QExpr) : ∀ G, qEq (bs (fun _ => c) G) (qmul (qnat G) c)
  | 0 => by
      show qEq qzero (qmul (qnat 0) c)
      have e := qmul_respects qnat_zero (qEq_refl c)
      have z : qEq (qmul qzero c) qzero := by rat_ring
      generalize qmul (qnat 0) c = P at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | G + 1 => by
      have ih := bs_const c G
      have e := qmul_respects (qnat_succ G) (qEq_refl c)
      have d : qEq (qmul (qadd (qnat G) qone) c) (qadd (qmul (qnat G) c) c) := by rat_ring
      show qEq (qadd (bs (fun _ => c) G) c) _
      generalize bs (fun _ => c) G = P at *
      generalize qmul (qnat (G + 1)) c = Q at *; generalize qmul (qadd (qnat G) qone) c = Q' at *
      generalize qmul (qnat G) c = Q'' at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem bs_lohi {g lo hi : Nat → QExpr} : ∀ G, (∀ j, j < G → qle (lo j) (g j) ∧ qle (g j) (hi j)) →
    qle (bs lo G) (bs g G) ∧ qle (bs g G) (bs hi G)
  | 0, _ => ⟨qle_refl _, qle_refl _⟩
  | G + 1, h => by
      obtain ⟨i1, i2⟩ := bs_lohi G (fun j hj => h j (Nat.lt_succ_of_lt hj))
      obtain ⟨t1, t2⟩ := h G (Nat.lt_succ_self G)
      show qle (qadd (bs lo G) (lo G)) (qadd (bs g G) (g G)) ∧ qle (qadd (bs g G) (g G)) (qadd (bs hi G) (hi G))
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- `Σ_j (j·w·c − v) = w·c·Σ j − G·v`. -/
theorem bs_jw (w c v : QExpr) (G : Nat) :
    qEq (bs (fun j => qsub (qmul (qmul (qnat j) w) c) v) G)
      (qsub (qmul (qmul w c) (bs (fun j => qnat j) G)) (qmul (qnat G) v)) := by
  have s := bs_sub (fun j => qmul (qmul (qnat j) w) c) (fun _ => v) G
  have c1 := bs_congr (F := fun j => qmul (qmul (qnat j) w) c) (G := fun j => qmul (qmul w c) (qnat j))
    (fun j => show qEq (qmul (qmul (qnat j) w) c) (qmul (qmul w c) (qnat j)) by rat_ring) G
  have c2 := bs_scale (qmul w c) (fun j => qnat j) G
  have c3 := bs_const v G
  generalize bs (fun j => qsub (qmul (qmul (qnat j) w) c) v) G = A at *
  generalize bs (fun j => qmul (qmul (qnat j) w) c) G = B at *
  generalize bs (fun j => qmul (qmul w c) (qnat j)) G = C at *
  generalize bs (fun _ => v) G = D at *
  generalize qmul (qmul w c) (bs (fun j => qnat j) G) = E at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem bs_jw' (w c v : QExpr) (G : Nat) :
    qEq (bs (fun j => qadd (qmul (qmul (qnat j) w) c) v) G)
      (qadd (qmul (qmul w c) (bs (fun j => qnat j) G)) (qmul (qnat G) v)) := by
  have s := bs_add (fun j => qmul (qmul (qnat j) w) c) (fun _ => v) G
  have c1 := bs_congr (F := fun j => qmul (qmul (qnat j) w) c) (G := fun j => qmul (qmul w c) (qnat j))
    (fun j => show qEq (qmul (qmul (qnat j) w) c) (qmul (qmul w c) (qnat j)) by rat_ring) G
  have c2 := bs_scale (qmul w c) (fun j => qnat j) G
  have c3 := bs_const v G
  generalize bs (fun j => qadd (qmul (qmul (qnat j) w) c) v) G = A at *
  generalize bs (fun j => qmul (qmul (qnat j) w) c) G = B at *
  generalize bs (fun j => qmul (qmul w c) (qnat j)) G = C at *
  generalize bs (fun _ => v) G = D at *
  generalize qmul (qmul w c) (bs (fun j => qnat j) G) = E at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `δ²·c·(G² − G)` with `δ = Δ·e`, `G·e = 1`: `Δ²·c − Δ²·e·c`. -/
theorem sq_grid {Δ e G c : QExpr} (g : qEq (qmul G e) qone) :
    qEq (qmul (qmul (qmul (qmul Δ e) (qmul Δ e)) c) (qsub (qmul G G) G))
      (qsub (qmul (qmul Δ Δ) c) (qmul (qmul (qmul Δ Δ) e) c)) := by
  have h1 : qEq (qmul (qmul (qmul (qmul Δ e) (qmul Δ e)) c) (qsub (qmul G G) G))
      (qsub (qmul (qmul (qmul Δ Δ) c) (qmul (qmul G e) (qmul G e))) (qmul (qmul (qmul (qmul Δ Δ) e) c) (qmul G e))) := by
    unfold qsub; rat_ring
  have h2 := qmul_respects (qEq_refl (qmul (qmul Δ Δ) c)) (qmul_respects g g)
  have h3 := qmul_respects (qEq_refl (qmul (qmul (qmul Δ Δ) e) c)) g
  have o1 : qEq (qmul (qmul (qmul Δ Δ) c) (qmul qone qone)) (qmul (qmul Δ Δ) c) := by rat_ring
  have o2 : qEq (qmul (qmul (qmul (qmul Δ Δ) e) c) qone) (qmul (qmul (qmul Δ Δ) e) c) := by rat_ring
  generalize qmul (qmul (qmul (qmul Δ e) (qmul Δ e)) c) (qsub (qmul G G) G) = L at *
  generalize qmul (qmul (qmul Δ Δ) c) (qmul (qmul G e) (qmul G e)) = P at *
  generalize qmul (qmul (qmul (qmul Δ Δ) e) c) (qmul G e) = Q at *
  generalize qmul (qmul (qmul Δ Δ) c) (qmul qone qone) = P' at *
  generalize qmul (qmul (qmul (qmul Δ Δ) e) c) qone = Q' at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gq_scale (Δ X : QExpr) (K : Nat) : qEq (qmul (qnat (2 ^ K)) (qmul (qmul Δ (qeps K)) X)) (qmul Δ X) := by
  have g := g_one K
  have e : qEq (qmul (qnat (2 ^ K)) (qmul (qmul Δ (qeps K)) X)) (qmul (qmul Δ X) (qmul (qnat (2 ^ K)) (qeps K))) := by rat_ring
  have f := qmul_respects (qEq_refl (qmul Δ X)) g
  have o : qEq (qmul (qmul Δ X) qone) (qmul Δ X) := by rat_ring
  generalize qmul (qnat (2 ^ K)) (qmul (qmul Δ (qeps K)) X) = L at *
  generalize qmul (qmul Δ X) (qmul (qnat (2 ^ K)) (qeps K)) = P at *
  generalize qmul (qmul Δ X) qone = P' at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE SECOND-ORDER STEP, GENERICALLY: `F`'s grid steps are `δ·D + O(δ²)`, `D`'s chords from `a` lie in
`[el, eh]`: from some index on, `2·(F(b) − F(a) − (b − a)·D(a)) ∈ (b − a)²·[el, eh] ± ε_k`. -/
theorem chord2_gen (F D : QExpr → Nat → QExpr) (hF : ∀ x y n, qEq x y → qEq (F x n) (F y n))
    (step : ∀ {A : QExpr}, qle qzero A → ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x δ a, Ab x A → Ab δ qone →
      Ab δ a → qle a qone → Ab (qsub (qsub (F (qadd x δ) n) (F x n)) (qmul δ (D x n))) (qadd (qeps k) (qmul (qmul a a) H)))
    {a b : Nat → QExpr} {lu hu el eh : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu)
    (hDc : ∀ c : Nat → QExpr, Ev c lu hu → ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub el (qeps k)) χ ∧
      qle χ (qadd eh (qeps k)) ∧ Ab (qsub (qsub (D (c n) n) (D (a n) n)) (qmul (qsub (c n) (a n)) χ)) (qeps k)) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) el) (qeps k))
        (qadd (qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) (D (a n) n)))
              (qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) (D (a n) n)))) ∧
      qle (qadd (qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) (D (a n) n)))
              (qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) (D (a n) n))))
        (qadd (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) eh) (qeps k)) := by
  intro k
  obtain ⟨M, _, hM0, _, ml, mh, mel, meh⟩ := bound4 lu hu el eh
  have o := qle_of_qlt qone_pos
  have hA0 : qle qzero (qadd M qone) := by rat_linarith
  obtain ⟨H, hH0, hH⟩ := step hA0
  have hD0 : qle qzero (qadd (qadd M qone) (qadd M qone)) := by rat_linarith
  obtain ⟨e1', e2'⟩ := mel; obtain ⟨e3', e4'⟩ := meh
  have elA : Ab el (qadd M qone) := by unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have ehA : Ab eh (qadd M qone) := by unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  generalize hAd : qadd M qone = A at hA0 hD0 hH elA ehA
  generalize hDd : qadd A A = Dm at hD0
  -- the budget X·ε_K ≤ ε_{k+3}
  have q1 := qmul_nonneg (qmul_nonneg hD0 hD0) hH0
  have q2 := qmul_nonneg (qmul_nonneg hD0 hD0) hA0
  have q3 := qmul_nonneg hD0 hD0
  have hX0 : qle qzero (qadd (qadd (qadd (qmul (qmul Dm Dm) H) (qmul (qmul Dm Dm) H)) (qmul (qmul Dm Dm) A))
      (qadd (qadd Dm Dm) (qadd (qmul Dm Dm) (qmul Dm Dm)))) := by rat_linarith
  generalize hXd : qadd (qadd (qadd (qmul (qmul Dm Dm) H) (qmul (qmul Dm Dm) H)) (qmul (qmul Dm Dm) A))
      (qadd (qadd Dm Dm) (qadd (qmul Dm Dm) (qmul Dm Dm))) = X at hX0
  obtain ⟨Bc, hB1, _⟩ := qexpr_bound (qadd X Dm)
  have hC : qle (qadd X Dm) (qofInt (pow2 Bc)) := by unfold qsub at hB1; rat_linarith
  have pe := qpow2_mul_eps Bc (k + 3)
  have sK := ZExp.scale hC (qeps_nonneg ((k + 3) + Bc))
  have c1 := qmul_comm (qofInt (pow2 Bc)) (qeps ((k + 3) + Bc))
  have d1 : qEq (qmul (qadd X Dm) (qeps ((k + 3) + Bc))) (qadd (qmul X (qeps ((k + 3) + Bc))) (qmul Dm (qeps ((k + 3) + Bc)))) := by
    rat_ring
  have p1 := qmul_nonneg hX0 (qeps_nonneg ((k + 3) + Bc))
  have p2 := qmul_nonneg hD0 (qeps_nonneg ((k + 3) + Bc))
  have e3 := qeps_le_one (k + 3)
  have bX : qle (qmul X (qeps ((k + 3) + Bc))) (qeps (k + 3)) := by
    generalize qmul (qadd X Dm) (qeps ((k + 3) + Bc)) = P at *
    generalize qmul (qofInt (pow2 Bc)) (qeps ((k + 3) + Bc)) = Q at *
    generalize qmul (qeps ((k + 3) + Bc)) (qofInt (pow2 Bc)) = Q' at *
    rat_linarith
  have bD : qle (qmul Dm (qeps ((k + 3) + Bc))) qone := by
    generalize qmul (qadd X Dm) (qeps ((k + 3) + Bc)) = P at *
    generalize qmul (qofInt (pow2 Bc)) (qeps ((k + 3) + Bc)) = Q at *
    generalize qmul (qeps ((k + 3) + Bc)) (qofInt (pow2 Bc)) = Q' at *
    rat_linarith
  generalize hK : (k + 3) + Bc = K at bX bD p1 p2
  have eK1 := qeps_le_one K
  have eK0 := qeps_nonneg K
  -- the step's precision: 2^K·ε_s = ε_{k+3}
  have eS : qEq (qmul (qnat (2 ^ K)) (qeps ((k + 3) + K))) (qeps (k + 3)) :=
    qEq_trans (qmul_respects (qnat_pow2 K) (qEq_refl _)) (qpow2_mul_eps K (k + 3))
  obtain ⟨Ns, hNs⟩ := hH ((k + 3) + K)
  -- the chords of `D` from `a` to every grid point
  obtain ⟨Nd, hNd⟩ := fin_N (P := fun j n => j < 2 ^ K → ∃ χ, qle (qsub el (qeps K)) χ ∧ qle χ (qadd eh (qeps K)) ∧
      Ab (qsub (qsub (D (xg (a n) (b n) K j) n) (D (a n) n)) (qmul (qsub (xg (a n) (b n) K j) (a n)) χ)) (qeps K))
    (fun j => by
      cases Nat.lt_or_ge j (2 ^ K) with
      | inl hj =>
        obtain ⟨N, hN⟩ := hDc _ (Ev_xg ha hb (Nat.le_of_lt hj)) K
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
  have aL : qle (qsub lu qone) (a n) := by unfold qsub; rat_linarith
  have aU : qle (a n) (qadd hu qone) := by rat_linarith
  have bL : qle (qsub lu qone) (b n) := by unfold qsub; rat_linarith
  have bU : qle (b n) (qadd hu qone) := by rat_linarith
  have gA : ∀ j, j ≤ 2 ^ K → Ab (xg (a n) (b n) K j) A := fun j hj => by
    obtain ⟨t0, t1⟩ := T_unit hj
    obtain ⟨c1, c2⟩ := conv t0 t1 aL aU bL bU
    have e := xg_T (a n) (b n) K j
    rw [← hAd]
    generalize xg (a n) (b n) K j = X' at *
    generalize qadd (a n) (qmul (qmul (qnat j) (qeps K)) (qsub (b n) (a n))) = Y at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have hΔ : Ab (qsub (b n) (a n)) Dm := by
    rw [← hDd]; obtain ⟨x1, x2⟩ := gA 0 (Nat.zero_le _)
    have e0 := xg_zero (a n) (b n) K
    generalize xg (a n) (b n) K 0 = X' at *
    rw [← hAd] at *; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have hδ : Ab (qmul (qsub (b n) (a n)) (qeps K)) (qmul Dm (qeps K)) := mul_abs hΔ ⟨by rat_linarith, qle_refl _⟩
  have hδ1 : Ab (qmul (qsub (b n) (a n)) (qeps K)) qone := by
    obtain ⟨d1, d2⟩ := hδ; exact ⟨by rat_linarith, by rat_linarith⟩
  -- the steps
  have st : ∀ j, j < 2 ^ K → Ab (qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)))
      (qadd (qeps ((k + 3) + K)) (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)) := fun j hj => by
    have s := hNs n (le_l' hn) _ _ _ (gA j (Nat.le_of_lt hj)) hδ1 hδ bD
    have r := hF _ _ n (qEq_symm (xg_succ (a n) (b n) K j))
    obtain ⟨s1, s2⟩ := s
    generalize F (qadd (xg (a n) (b n) K j) (qmul (qsub (b n) (a n)) (qeps K))) n = P at *
    generalize F (xg (a n) (b n) K (j + 1)) n = P' at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨S1, S2⟩ := bs_abs_c (2 ^ K) st
  -- the terms
  have tb : ∀ j, j < 2 ^ K →
      qle (qsub (qmul (qmul (qnat j) (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))))
          (qsub el (qeps K))) (qmul (qmul Dm (qeps K)) (qeps K)))
        (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) ∧
      qle (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n)))
        (qadd (qmul (qmul (qnat j) (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))))
          (qadd eh (qeps K))) (qmul (qmul Dm (qeps K)) (qeps K))) := fun j hj => by
    obtain ⟨χ, c1, c2, hc⟩ := hNd n (le_l' (le_r' hn)) j hj hj
    have hx : qEq (qsub (xg (a n) (b n) K j) (a n)) (qmul (qnat j) (qmul (qsub (b n) (a n)) (qeps K))) := by
      unfold xg qsub; rat_ring
    exact term_bound hx c1 c2 hc hδ
  obtain ⟨T1, T2⟩ := bs_lohi (2 ^ K) tb
  have j1 := bs_jw (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K))
    (qmul (qmul Dm (qeps K)) (qeps K)) (2 ^ K)
  have j2 := bs_jw' (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K))
    (qmul (qmul Dm (qeps K)) (qeps K)) (2 ^ K)
  have bn := bs_nat (2 ^ K)
  have g1 := g_one K
  have sgl := sq_grid (Δ := qsub (b n) (a n)) (c := qsub el (qeps K)) g1
  have sgh := sq_grid (Δ := qsub (b n) (a n)) (c := qadd eh (qeps K)) g1
  have dl := qmul_respects (qEq_refl (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K)))) bn
  have dh := qmul_respects (qEq_refl (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K)))) bn
  have gw := gq_scale Dm (qeps K) K
  -- R = Σ steps + Σ terms
  have tl := bs_tele (fun j => F (xg (a n) (b n) K j) n) (2 ^ K)
  have split : ∀ j, qEq (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qadd (qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)))
        (qadd (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n)))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n)))) := fun j => by unfold qsub; rat_ring
  have cg := bs_congr split (2 ^ K)
  have ad1 := bs_add (fun j => qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)))
    (fun j => qadd (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n)))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n))) (2 ^ K)
  have ad2 := bs_add (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n)))
    (fun _ => qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n)) (2 ^ K)
  have bc := bs_const (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n)) (2 ^ K)
  have gd := gq_scale (qsub (b n) (a n)) (D (a n) n) K
  have fT := hF _ _ n (xg_top (a n) (b n) K)
  have f0 := hF _ _ n (xg_zero (a n) (b n) K)
  have et := err_total (qeps ((k + 3) + K)) Dm H K
  -- the small products
  have ΔΔ := mul_abs hΔ hΔ
  have ΔΔe := mul_abs ΔΔ (show Ab (qeps K) (qeps K) from ⟨by rat_linarith, qle_refl _⟩)
  have cL : Ab (qsub el (qeps K)) (qadd A qone) := by obtain ⟨x1, x2⟩ := elA; unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  have cH : Ab (qadd eh (qeps K)) (qadd A qone) := by obtain ⟨x1, x2⟩ := ehA; exact ⟨by rat_linarith, by rat_linarith⟩
  have xe : qEq (qmul X (qeps K)) (qadd (qadd (qadd (qmul (qmul (qmul Dm Dm) H) (qeps K)) (qmul (qmul (qmul Dm Dm) H) (qeps K)))
      (qmul (qmul (qmul Dm Dm) A) (qeps K))) (qadd (qadd (qmul Dm (qeps K)) (qmul Dm (qeps K)))
      (qadd (qmul (qmul Dm Dm) (qeps K)) (qmul (qmul Dm Dm) (qeps K))))) := by rw [← hXd]; rat_ring
  have pr : qEq (qmul (qmul (qmul Dm Dm) (qeps K)) (qadd A qone))
      (qadd (qmul (qmul (qmul Dm Dm) A) (qeps K)) (qmul (qmul Dm Dm) (qeps K))) := by rat_ring
  obtain ⟨k1, k2⟩ := mul_abs ΔΔe cL
  obtain ⟨k3, k4⟩ := mul_abs ΔΔe cH
  obtain ⟨_, k5⟩ := ΔΔe
  have i1 : qEq (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qsub el (qeps K)))
      (qsub (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) el) (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qeps K))) := by
    unfold qsub; rat_ring
  have i2 : qEq (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qadd eh (qeps K)))
      (qadd (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) eh) (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qeps K))) := by
    rat_ring
  have tw1 : qEq (qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K)))
        (qadd (bs (fun j => qnat j) (2 ^ K)) (bs (fun j => qnat j) (2 ^ K))))
      (qadd (qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K)))
          (bs (fun j => qnat j) (2 ^ K)))
        (qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K)))
          (bs (fun j => qnat j) (2 ^ K)))) := by rat_ring
  have tw2 : qEq (qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K)))
        (qadd (bs (fun j => qnat j) (2 ^ K)) (bs (fun j => qnat j) (2 ^ K))))
      (qadd (qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K)))
          (bs (fun j => qnat j) (2 ^ K)))
        (qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K)))
          (bs (fun j => qnat j) (2 ^ K)))) := by rat_ring
  -- the sum of terms, both sides
  have STl : qle (qsub (qsub (qsub (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) el)
        (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qeps K)))
        (qmul (qmul (qmul (qmul Dm Dm) A) (qeps K)) qone)) (qadd (qmul (qmul Dm Dm) (qeps K)) (qadd (qmul Dm (qeps K)) (qmul Dm (qeps K)))))
      (qadd (bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K))
        (bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K))) := by
    generalize bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K) = Str at *
    generalize bs (fun j => qsub (qmul (qmul (qnat j) (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))))
        (qsub el (qeps K))) (qmul (qmul Dm (qeps K)) (qeps K))) (2 ^ K) = Lo at *
    generalize bs (fun j => qnat j) (2 ^ K) = Sj at *
    generalize qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K))) Sj = WS at *
    generalize qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K))) (qadd Sj Sj) = WS2 at *
    generalize qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qsub el (qeps K)))
      (qsub (qmul (qnat (2 ^ K)) (qnat (2 ^ K))) (qnat (2 ^ K))) = WG at *
    generalize qmul (qnat (2 ^ K)) (qmul (qmul Dm (qeps K)) (qeps K)) = GV at *
    generalize qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qsub el (qeps K)) = DC at *
    generalize qmul (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qeps K)) (qsub el (qeps K)) = DEC at *
    generalize qmul (qmul (qmul Dm Dm) (qeps K)) (qadd A qone) = PB at *
    clear tb st hNd hNs hNa hNb split cg ad1 ad2 S1 S2 T2 j2 dh sgh tw2 k3 k4
    unfold qsub at *; rat_linarith
  have STh : qle (qadd (bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K))
        (bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K)))
      (qadd (qadd (qadd (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) eh)
        (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qeps K)))
        (qmul (qmul (qmul Dm Dm) A) (qeps K))) (qadd (qmul (qmul Dm Dm) (qeps K)) (qadd (qmul Dm (qeps K)) (qmul Dm (qeps K))))) := by
    generalize bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K) = Str at *
    generalize bs (fun j => qadd (qmul (qmul (qnat j) (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))))
        (qadd eh (qeps K))) (qmul (qmul Dm (qeps K)) (qeps K))) (2 ^ K) = Hi at *
    generalize bs (fun j => qnat j) (2 ^ K) = Sj at *
    generalize qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K))) Sj = WS at *
    generalize qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K))) (qadd Sj Sj) = WS2 at *
    generalize qmul (qmul (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qmul (qsub (b n) (a n)) (qeps K))) (qadd eh (qeps K)))
      (qsub (qmul (qnat (2 ^ K)) (qnat (2 ^ K))) (qnat (2 ^ K))) = WG at *
    generalize qmul (qnat (2 ^ K)) (qmul (qmul Dm (qeps K)) (qeps K)) = GV at *
    generalize qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qadd eh (qeps K)) = DC at *
    generalize qmul (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qeps K)) (qadd eh (qeps K)) = DEC at *
    generalize qmul (qmul (qmul Dm Dm) (qeps K)) (qadd A qone) = PB at *
    clear tb st hNd hNs hNa hNb split cg ad1 ad2 S1 S2 T1 j1 dl sgl tw1 k1 k2 STl
    unfold qsub at *; rat_linarith
  -- R = Σ steps + Σ terms
  have RS : qEq (qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) (D (a n) n)))
      (qadd (bs (fun j => qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n))) (2 ^ K))
        (bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K))) := by
    generalize bs (fun j => qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n)) (2 ^ K) = Tl at *
    generalize bs (fun j => qadd (qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)))
        (qadd (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n)))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n)))) (2 ^ K) = Cg at *
    generalize bs (fun j => qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n))) (2 ^ K) = Sst at *
    generalize bs (fun j => qadd (qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n)))
          (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n))) (2 ^ K) = Bt at *
    generalize bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K) = Str at *
    generalize bs (fun _ => qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n)) (2 ^ K) = Bc' at *
    generalize qmul (qnat (2 ^ K)) (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (a n) n)) = GD at *
    generalize qmul (qsub (b n) (a n)) (D (a n) n) = ΔD at *
    generalize F (xg (a n) (b n) K (2 ^ K)) n = Fb' at *; generalize F (xg (a n) (b n) K 0) n = Fa' at *
    generalize F (b n) n = Fb at *; generalize F (a n) n = Fa at *
    clear tb st hNd hNs hNa hNb split S1 S2 T1 T2 STl STh
    unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  -- the budget
  have ek := qeps_succ_add k; have ek1 := qeps_succ_add (k + 1); have ek2 := qeps_succ_add (k + 2)
  have e3n := qeps_nonneg (k + 3)
  generalize qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) (D (a n) n)) = R at *
  generalize bs (fun j => qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n))) (2 ^ K) = Sst at *
  generalize bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (qsub (D (xg (a n) (b n) K j) n) (D (a n) n))) (2 ^ K) = Str at *
  generalize qmul (qnat (2 ^ K)) (qadd (qeps ((k + 3) + K)) (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)) = E at *
  generalize qmul (qnat (2 ^ K)) (qeps ((k + 3) + K)) = E1 at *
  generalize qmul X (qeps K) = XE at *
  generalize qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) el = DL at *
  generalize qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) eh = DH at *
  generalize qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qeps K) = DE at *
  generalize qmul (qmul (qmul Dm Dm) H) (qeps K) = Q1 at *
  generalize qmul (qmul (qmul Dm Dm) A) (qeps K) = Q2 at *
  generalize qmul Dm (qeps K) = Q3 at *
  generalize qmul (qmul Dm Dm) (qeps K) = Q4 at *
  have z1 : qEq (qmul Q2 qone) Q2 := by rat_ring
  clear tb st hNd hNs hNa hNb split cg ad1 ad2 T1 T2 j1 j2 dl dh sgl sgh tw1 tw2 k1 k2 k3 k4 bc gd fT f0 tl gw pr i1 i2
  obtain ⟨S1', S2'⟩ := And.intro S1 S2
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE SECOND-ORDER STEP OF `sin`: `2·(S(b) − S(a) − (b − a)·C(a)) ∈ (b − a)²·[−sh, −sl]`, eventually, to every
precision (`[sl, sh]` the kernel's reading of `sin` over `[lu, hu]`). -/
theorem Ev_sin2 {a b : Nat → QExpr} {lu hu sl sh : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu) (hlh : qle lu hu)
    (hi : SinHi lu hu sh) (lo : SinLo lu hu sl) : ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qneg sh)) (qeps k))
        (qadd (qsub (qsub (Sn (b n) n) (Sn (a n) n)) (qmul (qsub (b n) (a n)) (Cn (a n) n)))
              (qsub (qsub (Sn (b n) n) (Sn (a n) n)) (qmul (qsub (b n) (a n)) (Cn (a n) n)))) ∧
      qle (qadd (qsub (qsub (Sn (b n) n) (Sn (a n) n)) (qmul (qsub (b n) (a n)) (Cn (a n) n)))
              (qsub (qsub (Sn (b n) n) (Sn (a n) n)) (qmul (qsub (b n) (a n)) (Cn (a n) n))))
        (qadd (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qneg sl)) (qeps k)) :=
  chord2_gen (fun x n => Sn x n) (fun x n => Cn x n) (fun _ _ n e => Sn_respects e n) (fun hA => step_unif_S hA)
    ha hb (fun _ hc => chord_cos ha hc hlh hi lo)

/-- The chord of `−sin` from `a`: inside `−cos`'s reading. -/
theorem chord_nsin {a c : Nat → QExpr} {lu hu cl ch : QExpr} (ha : Ev a lu hu) (hc : Ev c lu hu) (hlh : qle lu hu)
    (hi : CosHi lu hu ch) (lo : CosLo lu hu cl) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub (qneg ch) (qeps k)) χ ∧ qle χ (qadd (qneg cl) (qeps k)) ∧
      Ab (qsub (qsub (qneg (Sn (c n) n)) (qneg (Sn (a n) n))) (qmul (qsub (c n) (a n)) χ)) (qeps k) := fun k => by
  obtain ⟨N, hN⟩ := chord_sin ha hc hlh hi lo k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨χ, x1, x2, ⟨d1, d2⟩⟩ := hN n hn
  refine ⟨qneg χ, by unfold qsub at *; rat_linarith, by unfold qsub at *; rat_linarith, ?_⟩
  have e : qEq (qmul (qsub (c n) (a n)) (qneg χ)) (qneg (qmul (qsub (c n) (a n)) χ)) := by rat_ring
  generalize qmul (qsub (c n) (a n)) (qneg χ) = P at *; generalize qmul (qsub (c n) (a n)) χ = Q at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE SECOND-ORDER STEP OF `cos`: `2·(C(b) − C(a) + (b − a)·S(a)) ∈ (b − a)²·[−ch, −cl]`, eventually. -/
theorem Ev_cos2 {a b : Nat → QExpr} {lu hu cl ch : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu) (hlh : qle lu hu)
    (hi : CosHi lu hu ch) (lo : CosLo lu hu cl) : ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qneg ch)) (qeps k))
        (qadd (qsub (qsub (Cn (b n) n) (Cn (a n) n)) (qmul (qsub (b n) (a n)) (qneg (Sn (a n) n))))
              (qsub (qsub (Cn (b n) n) (Cn (a n) n)) (qmul (qsub (b n) (a n)) (qneg (Sn (a n) n))))) ∧
      qle (qadd (qsub (qsub (Cn (b n) n) (Cn (a n) n)) (qmul (qsub (b n) (a n)) (qneg (Sn (a n) n))))
              (qsub (qsub (Cn (b n) n) (Cn (a n) n)) (qmul (qsub (b n) (a n)) (qneg (Sn (a n) n)))))
        (qadd (qmul (qmul (qsub (b n) (a n)) (qsub (b n) (a n))) (qneg cl)) (qeps k)) :=
  chord2_gen (fun x n => Cn x n) (fun x n => qneg (Sn x n)) (fun _ _ n e => Cn_respects e n) (fun hA => step_unif_C hA)
    ha hb (fun _ hc => chord_nsin ha hc hlh hi lo)

end ZTrig

#print axioms ZTrig.bs_nat
#print axioms ZTrig.term_bound
#print axioms ZTrig.bs_const
#print axioms ZTrig.bs_lohi
#print axioms ZTrig.bs_jw
#print axioms ZTrig.bs_jw'
#print axioms ZTrig.sq_grid
#print axioms ZTrig.chord2_gen
#print axioms ZTrig.Ev_sin2
#print axioms ZTrig.chord_nsin
#print axioms ZTrig.Ev_cos2
