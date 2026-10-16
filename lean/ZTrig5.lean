import ZTrig4

/-!
# ZTrig5 — `cos` and `sin` of an operational real; `cos ρ = 0`, `sin ρ = 1`. Zero axioms.

Stage 5 of the full sine.

  * `CS_unif` — on `[−a, a]`, from some index on, the partial sums at two indices are within `ε_k`;
  * `CS_cauchy` — for a Cauchy argument eventually in `[−a, a]`, `C_n(x_n)` and `S_n(x_n)` are Cauchy:
    `cos x`, `sin x` are operational reals;
  * `cos_rho` — `C_n(ρ_n) → 0` (the run ends where `C_n` changes sign; the step moves it by `≤ H·2^−n`);
  * `sin_rho` — `S_n(ρ_n) → 1` (Pythagoras, and `S_n(ρ_n) ≥ 1/15` since `ρ_n ≥ 1`).
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-- UNIFORM ON `[−a, a]`: from some index on, `|C_m(x) − C_n(x)|, |S_m(x) − S_n(x)| ≤ ε_k`. -/
theorem CS_unif {a : QExpr} (ha : qle qzero a) (k : Nat) : ∃ M, ∀ m n, M ≤ m → M ≤ n → ∀ x, Ab x a →
    Ab (qsub (Cn x m) (Cn x n)) (qeps k) ∧ Ab (qsub (Sn x m) (Sn x n)) (qeps k) := by
  obtain ⟨K0, hg⟩ := good_exists a
  obtain ⟨M, hKM, hM⟩ := tm_small ha hg (k + 1)
  have gM : Good a M := good_mono hg hKM
  refine ⟨M, fun m n hm hn x hx => ?_⟩
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := CS_tail hx gM m hm
  obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := CS_tail hx gM n hn
  have t := hM M (Nat.le_refl M)
  have e := qeps_succ_add k
  generalize Cn x m = Cm at *; generalize Cn x n = Cnn at *; generalize Cn x M = CM at *
  generalize Sn x m = Sm at *; generalize Sn x n = Snn at *; generalize Sn x M = SM at *
  generalize tm a M = T at *
  unfold qsub at *
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩

/-- `x ≤ ε_{k+1} + e·H` with `e ≤ ε_{k+1+B}`, `H ≤ 2^B`: then `x ≤ ε_k`. -/
theorem eps_combine {x e H : QExpr} {k B : Nat} (h : qle x (qadd (qeps (k + 1)) (qmul e H)))
    (he : qle e (qeps (k + 1 + B))) (e0 : qle qzero e) (hH : qle H (qofInt (pow2 B))) (H0 : qle qzero H) :
    qle x (qeps k) := by
  have f1 := ZExp.scale he H0
  have f2 := scale_l hH (qeps_nonneg (k + 1 + B))
  have pb := qpow2_mul_eps B (k + 1)
  have c : qEq (qmul (qeps (k + 1 + B)) (qofInt (pow2 B))) (qmul (qofInt (pow2 B)) (qeps (k + 1 + B))) := qmul_comm _ _
  have s := qeps_succ_add k
  have g1 : qle (qmul e H) (qeps (k + 1)) := by
    clear h s
    generalize qmul e H = eH at *; generalize qmul (qeps (k + 1 + B)) H = w at *
    generalize qmul (qeps (k + 1 + B)) (qofInt (pow2 B)) = w2 at *
    generalize qmul (qofInt (pow2 B)) (qeps (k + 1 + B)) = w3 at *
    rat_linarith
  generalize qmul e H = eH at *
  clear f1 f2 pb c
  rat_linarith

/-- `cos x`, `sin x` OF AN OPERATIONAL REAL: a Cauchy argument eventually in `[−a, a]` gives Cauchy `C_n(x_n)`,
`S_n(x_n)`. -/
theorem CS_cauchy {x : Nat → QExpr} {a : QExpr} (ha : qle qzero a) (hc : ZRecip.Cauchy x) {N0 : Nat}
    (hb : ∀ n, N0 ≤ n → Ab (x n) a) :
    ZRecip.Cauchy (fun n => Cn (x n) n) ∧ ZRecip.Cauchy (fun n => Sn (x n) n) := by
  obtain ⟨H, hH⟩ := S_bounded ha
  have H0 : qle qzero H := qle_trans (S_nonneg ha 0) (hH 0)
  obtain ⟨B, hB1, _⟩ := qexpr_bound H
  have hB : qle H (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  have side : ∀ k, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      qle (qsub (Cn (x m) m) (Cn (x n) n)) (qeps k) ∧ qle (qsub (Sn (x m) m) (Sn (x n) n)) (qeps k) := by
    intro k
    obtain ⟨M, hM⟩ := CS_unif ha (k + 1 + 1)
    obtain ⟨N1, hN1⟩ := hc (k + 1 + B)
    refine ⟨N0 + (M + N1), fun m n hm hn => ?_⟩
    have bm := hb m (Nat.le_trans (Nat.le_add_right N0 _) hm)
    have bn := hb n (Nat.le_trans (Nat.le_add_right N0 _) hn)
    obtain ⟨⟨u1, u2⟩, ⟨v1, v2⟩⟩ := hM m n (Nat.le_trans (Nat.le_trans (Nat.le_add_right M N1) (Nat.le_add_left _ N0)) hm)
      (Nat.le_trans (Nat.le_trans (Nat.le_add_right M N1) (Nat.le_add_left _ N0)) hn) (x m) bm
    have cl := hN1 m n (Nat.le_trans (Nat.le_trans (Nat.le_add_left N1 M) (Nat.le_add_left _ N0)) hm)
      (Nat.le_trans (Nat.le_trans (Nat.le_add_left N1 M) (Nat.le_add_left _ N0)) hn)
    obtain ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩ := CS_lip bm bn ⟨cl.2, cl.1⟩ n
    have e2 := qeps_succ_le (k + 1)
    have fH := scale_l (hH n) (qeps_nonneg (k + 1 + B))
    have e1 := qeps_succ_add (k + 1)
    have ep := qeps_nonneg (k + 1 + B)
    have hC : qle (qsub (Cn (x m) m) (Cn (x n) n)) (qadd (qeps (k + 1)) (qmul (qeps (k + 1 + B)) H)) := by
      clear v1 v2 l3 l4 cl bm bn hb hc
      generalize Cn (x m) m = A at *; generalize Cn (x m) n = A' at *; generalize Cn (x n) n = A'' at *
      generalize qmul (qeps (k + 1 + B)) (S a n) = w at *; generalize qmul (qeps (k + 1 + B)) H = w' at *
      unfold qsub at *; rat_linarith
    have hS : qle (qsub (Sn (x m) m) (Sn (x n) n)) (qadd (qeps (k + 1)) (qmul (qeps (k + 1 + B)) H)) := by
      clear u1 u2 l1 l2 cl bm bn hb hc hC
      generalize Sn (x m) m = A at *; generalize Sn (x m) n = A' at *; generalize Sn (x n) n = A'' at *
      generalize qmul (qeps (k + 1 + B)) (S a n) = w at *; generalize qmul (qeps (k + 1 + B)) H = w' at *
      unfold qsub at *; rat_linarith
    exact ⟨eps_combine hC (qle_refl _) ep hB H0, eps_combine hS (qle_refl _) ep hB H0⟩
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨N, hN⟩ := side k
    exact ⟨N, fun m n hm hn => ⟨(hN m n hm hn).1, by have := (hN n m hn hm).1; unfold qsub at *; rat_linarith⟩⟩
  · obtain ⟨N, hN⟩ := side k
    exact ⟨N, fun m n hm hn => ⟨(hN m n hm hn).2, by have := (hN n m hn hm).2; unfold qsub at *; rat_linarith⟩⟩

/-! ## `cos ρ = 0`, `sin ρ = 1` -/

/-- `C_n(ρ_n) → 0`. -/
theorem cos_rho : Ev (fun n => Cn (rho n) n) qzero qzero := fun k => by
  obtain ⟨N0, hN0⟩ := rho_facts
  have h2 := two_pos
  obtain ⟨H, hH⟩ := S_bounded h2
  have H0 : qle qzero H := qle_trans (S_nonneg h2 0) (hH 0)
  obtain ⟨B, hB1, _⟩ := qexpr_bound H
  have hB : qle H (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  refine ⟨N0 + (k + 1 + B), fun n hn => ?_⟩
  obtain ⟨r1, r2, r3, r4⟩ := hN0 n (Nat.le_trans (Nat.le_add_right N0 _) hn)
  have en : qle (qeps n) (qeps (k + 1 + B)) := eps_anti (Nat.le_trans (Nat.le_add_left _ N0) hn)
  have e0 := qeps_nonneg n
  have hx : Ab (qadd (rho n) (qeps n)) (qadd qone qone) := ⟨by have := qle_of_qlt qone_pos; rat_linarith, r2⟩
  have hy : Ab (rho n) (qadd qone qone) := ⟨by have := qle_of_qlt qone_pos; rat_linarith, by rat_linarith⟩
  have hd : Ab (qsub (qadd (rho n) (qeps n)) (rho n)) (qeps n) := by
    unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨⟨l1, l2⟩, _⟩ := CS_lip hx hy hd n
  have neg : qle (Cn (qadd (rho n) (qeps n)) n) qzero := by
    cases qle_total qzero (Cn (qadd (rho n) (qeps n)) n) with
    | inl h => exact absurd h r4
    | inr h => exact h
  have fH := scale_l (hH n) e0
  have up : qle (Cn (rho n) n) (qadd (qeps (k + 1)) (qmul (qeps n) H)) := by
    clear r4 hx hy hd l2
    generalize Cn (rho n) n = C at *; generalize Cn (qadd (rho n) (qeps n)) n = C' at *
    generalize qmul (qeps n) (S (qadd qone qone) n) = w at *; generalize qmul (qeps n) H = w' at *
    have := qeps_nonneg (k + 1)
    unfold qsub at *; rat_linarith
  have u := eps_combine up en e0 hB H0
  show qle (qsub qzero (qeps k)) (Cn (rho n) n) ∧ qle (Cn (rho n) n) (qadd qzero (qeps k))
  have := qeps_nonneg k
  generalize Cn (rho n) n = C at *
  unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `S ≥ 0`, `|S² − 1| ≤ e`: then `|S − 1| ≤ e`. -/
theorem near_one {S e : QExpr} (h0 : qle qzero S) (h1 : qle (qsub (qmul S S) qone) e) (h2 : qle (qsub qone (qmul S S)) e) :
    qle (qsub S qone) e ∧ qle (qsub qone S) e := by
  cases qle_total S qone with
  | inl h =>
      have f := ZExp.scale (show qle qzero (qsub qone S) by unfold qsub; rat_linarith) h0
      have e1 : qEq (qmul (qsub qone S) S) (qsub S (qmul S S)) := by unfold qsub; rat_ring
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  | inr h =>
      have f := ZExp.scale (show qle qzero (qsub S qone) by unfold qsub; rat_linarith) h0
      have e1 : qEq (qmul (qsub S qone) S) (qsub (qmul S S) S) := by unfold qsub; rat_ring
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The corner of non-negative series is non-negative. -/
theorem corner_nonneg {B : Nat → QExpr} (hB : NN B) : ∀ (N : Nat) (A : Nat → QExpr), NN A → qle qzero (corner A B N)
  | 0, A, _ => by unfold corner; show qle qzero (qsub (qmul qzero qzero) qzero); unfold qsub; rat_linarith
  | N + 1, A, hA => by
      have r := corner_rec A B N
      have ih := corner_nonneg hB N (fun i => A (i + 1)) (fun i => hA (i + 1))
      have p := qmul_nonneg (bs_nonneg (fun i => hA (i + 1)) N) (hB N)
      generalize corner A B (N + 1) = X at *; generalize corner (fun i => A (i + 1)) B N = Y at *
      generalize qmul (bs (fun i => A (i + 1)) N) (B N) = Z at *
      rat_linarith

/-- `S_n(ρ_n) → 1`. -/
theorem sin_rho : Ev (fun n => Sn (rho n) n) qone qone := fun k => by
  obtain ⟨N0, hN0⟩ := rho_facts
  obtain ⟨Nc, hNc⟩ := cos_rho (k + 1)
  obtain ⟨Nk, hNk⟩ := K4_small (k + 1)
  refine ⟨N0 + (Nc + (Nk + 6)), fun n hn => ?_⟩
  have n6 : 6 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left 6 Nk) (Nat.le_add_left _ Nc))
    (Nat.le_add_left _ N0)) hn
  obtain ⟨r1, r2, r3, _⟩ := hN0 n (Nat.le_trans (Nat.le_add_right N0 _) hn)
  obtain ⟨c1, c2⟩ := hNc n (Nat.le_trans (Nat.le_trans (Nat.le_add_right Nc _) (Nat.le_add_left _ N0)) hn)
  have kk := hNk n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right Nk 6) (Nat.le_add_left _ Nc))
    (Nat.le_add_left _ N0)) hn)
  have hy : Ab (rho n) (qadd qone qone) := by
    have := qeps_nonneg n; have := qle_of_qlt qone_pos; exact ⟨by rat_linarith, by rat_linarith⟩
  have sl := sin_lower (x := rho n) (by have := qle_of_qlt qone_pos; rat_linarith)
    (by have := qeps_nonneg n; rat_linarith) (Nat.le_trans (Nat.le_succ 5) n6)
  have S0 := nonneg_of_scaled sl (by have := qle_of_qlt qone_pos; rat_linarith)
  have cz : qle (Cn (rho n) n) (qeps (k + 1)) := by
    have c2' : qle (Cn (rho n) n) (qadd qzero (qeps (k + 1))) := c2
    rat_linarith
  have cc := scale_l cz r3
  have cc2 := ZExp.scale cz (qeps_nonneg (k + 1))
  have mm := qeps_mul (k + 1) (k + 1)
  have sm := eps_anti (show k + 1 ≤ k + 1 + (k + 1) from Nat.le_add_right _ _)
  have C2 : qle (qmul (Cn (rho n) n) (Cn (rho n) n)) (qeps (k + 1)) := by
    clear c1 c2 kk sl S0 hy r1 r2
    generalize Cn (rho n) n = C at *; generalize qeps (k + 1 + (k + 1)) = e2 at *
    generalize qmul (qeps (k + 1)) (qeps (k + 1)) = ee at *
    rat_linarith
  cases n with
  | zero => exact absurd n6 (by decide)
  | succ N =>
      obtain ⟨p1, p2⟩ := pyth hy N
      have cn := corner_nonneg (tm_nonneg two_pos) (N + 1) (tm (qadd qone qone)) (tm_nonneg two_pos)
      have K2 : qle (qadd (corner (tm (qadd qone qone)) (tm (qadd qone qone)) (N + 1))
          (corner (tm (qadd qone qone)) (tm (qadd qone qone)) (N + 1))) (qeps (k + 1)) := by
        unfold K4 at kk
        generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) (N + 1) = K at *
        rat_linarith
      obtain ⟨u1, u2⟩ := near_one (S := Sn (rho (N + 1)) (N + 1)) (e := qadd (qeps (k + 1)) (qeps (k + 1))) S0
        (by
          clear c1 c2 kk sl hy r1 r2 cc cc2 mm sm cz
          have q0 := qmul_self_nonneg (Cn (rho (N + 1)) (N + 1))
          have ep := qeps_nonneg (k + 1)
          generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) (N + 1) = K at *
          generalize qmul (Cn (rho (N + 1)) (N + 1)) (Cn (rho (N + 1)) (N + 1)) = CC at *
          generalize qmul (Sn (rho (N + 1)) (N + 1)) (Sn (rho (N + 1)) (N + 1)) = SS at *
          unfold qsub at *; rat_linarith)
        (by
          clear c1 c2 kk sl hy r1 r2 cc cc2 mm sm cz
          generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) (N + 1) = K at *
          generalize qmul (Cn (rho (N + 1)) (N + 1)) (Cn (rho (N + 1)) (N + 1)) = CC at *
          generalize qmul (Sn (rho (N + 1)) (N + 1)) (Sn (rho (N + 1)) (N + 1)) = SS at *
          unfold qsub at *; rat_linarith)
      have e := qeps_succ_add k
      show qle (qsub qone (qeps k)) (Sn (rho (N + 1)) (N + 1)) ∧ qle (Sn (rho (N + 1)) (N + 1)) (qadd qone (qeps k))
      generalize Sn (rho (N + 1)) (N + 1) = S at *
      clear c1 c2 kk sl hy r1 r2 cc cc2 mm sm cz p1 p2 cn K2 C2 S0
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

end ZTrig

#print axioms ZTrig.CS_unif
#print axioms ZTrig.eps_combine
#print axioms ZTrig.CS_cauchy
#print axioms ZTrig.cos_rho
#print axioms ZTrig.near_one
#print axioms ZTrig.corner_nonneg
#print axioms ZTrig.sin_rho
