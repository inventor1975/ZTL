import ZAffine2

/-!
# ZAffineAtan — the affine form's `atan` step (`zaffine._atan`), on Lean's grid `atan`. Zero axioms.

The kernel reads `atan` over `[a, b]` (not across zero) by min-range: the slope `α` at the end where `ψ = 1/(1 + t²)`
is smaller (`b` when `0 ≤ a`, `a` when `b ≤ 0`), rounded down, so the remainder `r = atan − α·x` rises on `[a, b]`;
`r`'s range is read at the two ends from certified brackets of `atan a`, `atan b` (`zfunc.atan_pt_cert`, a Taylor
chain — `ZAtanCert`). Here, on `ZAtan.atseq`: `ψ ≥ P − ι` on `[a − ι, b + ι]` (`psi_floor_pos`/`_neg`, `P` the end's
`ψ`) and `α ≤ P` make `r` rise up to `ε_n` and `ι` (`r_rise`, from the grid sum's window, no mean value theorem);
outside `[a, b]` by at most `ι` the slope at most 1 bounds it — `rem_atan`, the `Rem` that `AffR.nl` takes.
-/

namespace ZAffine

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZAtan

theorem ab_mul {u v H A : QExpr} (hu : ZTrig.Ab u H) (hv : ZTrig.Ab v A) : ZTrig.Ab (qmul u v) (qmul H A) := by
  obtain ⟨u1, u2⟩ := hu; obtain ⟨v1, v2⟩ := hv
  have H0 : qle qzero H := by rat_linarith
  cases qle_total qzero v with
  | inl hv0 =>
      have f1 := ZExp.scale u2 hv0; have f2 := ZExp.scale u1 hv0
      have f3 := scale_l v2 H0
      have e : qEq (qmul (qneg H) v) (qneg (qmul H v)) := by rat_ring
      exact ⟨by rat_linarith, by rat_linarith⟩
  | inr hv0 =>
      have hv0' : qle qzero (qneg v) := by rat_linarith
      have f1 := ZExp.scale u2 hv0'; have f2 := ZExp.scale u1 hv0'
      have f3 := scale_l (by rat_linarith : qle (qneg v) A) H0
      have e1 : qEq (qmul u (qneg v)) (qneg (qmul u v)) := by rat_ring
      have e2 : qEq (qmul (qneg H) (qneg v)) (qmul H v) := by rat_ring
      have e3 : qEq (qmul H (qneg v)) (qneg (qmul H v)) := by rat_ring
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- `α ≤ ψ(b)` from `α·(1 + b²) ≤ 1`. -/
theorem le_psi {α b : QExpr} (h : qle (qmul α (qadd qone (qmul b b))) qone) : qle α (psi b) := by
  obtain ⟨p0, _, pc⟩ := psi_facts b
  have f := ZExp.scale h p0
  have e : qEq (qmul (qmul α (qadd qone (qmul b b))) (psi b)) (qmul α (qmul (qadd qone (qmul b b)) (psi b))) := by rat_ring
  have e2 := qmul_respects (qEq_refl α) pc
  have o := qmul_one α; have o2 := qone_mul (psi b)
  generalize qmul (qmul α (qadd qone (qmul b b))) (psi b) = X at *
  generalize qmul α (qmul (qadd qone (qmul b b)) (psi b)) = Y at *
  rat_linarith

/-- On `[a − ι, b + ι]`, `0 ≤ a ≤ b`: `ψ ≥ ψ(b) − ι`. -/
theorem psi_floor_pos {a b ι t : QExpr} (ha : qle qzero a) (hι : qle qzero ι) (h1 : qle (qsub a ι) t)
    (h2 : qle t (qadd b ι)) : qle (qsub (psi b) ι) (psi t) := by
  obtain ⟨_, b1, _⟩ := psi_facts b
  cases qle_total qzero t with
  | inl t0 =>
      cases qle_total t b with
      | inl tb => have := psi_anti_pos t0 tb; unfold qsub; rat_linarith
      | inr tb =>
          obtain ⟨l1, _⟩ := psi_lip (t := t) (z := b) (d := ι) (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
          unfold qsub at *; rat_linarith
  | inr t0 =>
      obtain ⟨_, _, _⟩ := psi_facts t
      have p0 : qEq (psi qzero) qone := by
        obtain ⟨_, _, c⟩ := psi_facts qzero
        have e : qEq (qmul (qadd qone (qmul qzero qzero)) (psi qzero)) (psi qzero) := by rat_ring
        exact qEq_trans (qEq_symm e) c
      obtain ⟨l1, _⟩ := psi_lip (t := t) (z := qzero) (d := ι) (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith)
      unfold qsub at *; rat_linarith

/-- On `[a − ι, b + ι]`, `a ≤ b ≤ 0`: `ψ ≥ ψ(a) − ι`. -/
theorem psi_floor_neg {a b ι t : QExpr} (hb : qle b qzero) (hι : qle qzero ι) (h1 : qle (qsub a ι) t)
    (h2 : qle t (qadd b ι)) : qle (qsub (psi a) ι) (psi t) := by
  obtain ⟨_, a1, _⟩ := psi_facts a
  cases qle_total t qzero with
  | inl t0 =>
      cases qle_total a t with
      | inl at' => have := psi_mono_neg t0 at'; unfold qsub; rat_linarith
      | inr at' =>
          obtain ⟨l1, _⟩ := psi_lip (t := t) (z := a) (d := ι) (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith)
          unfold qsub at *; rat_linarith
  | inr t0 =>
      have p0 : qEq (psi qzero) qone := by
        obtain ⟨_, _, c⟩ := psi_facts qzero
        have e : qEq (qmul (qadd qone (qmul qzero qzero)) (psi qzero)) (psi qzero) := by rat_ring
        exact qEq_trans (qEq_symm e) c
      obtain ⟨l1, _⟩ := psi_lip (t := t) (z := qzero) (d := ι) (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith)
      unfold qsub at *; rat_linarith

/-- THE REMAINDER RISES: `ψ ≥ P − ι` on `[y, y']`, `α ≤ P`, `|α| ≤ A`:
`r(y') − r(y) ≥ −ε_n·A − (y' − y + ε_n)·ι`, `r = atan − α·x`. -/
theorem r_rise {y y' α P ι A : QExpr} {n : Nat} (hy : InR y n) (hy' : InR y' n) (hyy : qle y y')
    (hαP : qle α P) (hαA : ZTrig.Ab α A) (hι : qle qzero ι) (hfl : ∀ t, qle y t → qle t y' → qle (qsub P ι) (psi t)) :
    qle (qsub (qneg (qmul (qeps n) A)) (qmul (qadd (qsub y' y) (qeps n)) ι))
      (qsub (qsub (atseq y' n) (qmul α y')) (qsub (atseq y n) (qmul α y))) := by
  obtain ⟨L, L0, L1, L2, l, _⟩ := atan_window hy hy' hyy (m := qsub P ι) (M := qone)
    (fun t h1 h2 => ⟨hfl t h1 h2, (psi_facts t).2.1⟩)
  have d0 : qle qzero (qsub y' y) := by unfold qsub; rat_linarith
  have h0 := qeps_nonneg n
  -- L·(P − ι) − α·d = L·(P − α) + (L − d)·α − L·ι
  have f1 := qmul_nonneg L0 (by unfold qsub; rat_linarith : qle qzero (qsub P α))
  have f2 := ab_mul (u := qsub L (qsub y' y)) (H := qeps n) ⟨by unfold qsub at *; rat_linarith, by unfold qsub at *; rat_linarith⟩ hαA
  have f3 := ZExp.scale L2 hι
  have e1 : qEq (qmul L (qsub P ι)) (qadd (qadd (qmul L (qsub P α)) (qmul (qsub L (qsub y' y)) α))
      (qsub (qmul (qsub y' y) α) (qmul L ι))) := by unfold qsub; rat_ring
  have e2 : qEq (qsub (qsub (atseq y' n) (qmul α y')) (qsub (atseq y n) (qmul α y)))
      (qsub (qsub (atseq y' n) (atseq y n)) (qmul (qsub y' y) α)) := by unfold qsub; rat_ring
  generalize qsub (atseq y' n) (atseq y n) = D at *
  generalize qmul L (qsub P ι) = A1 at *
  generalize qmul L (qsub P α) = A2 at *
  generalize qmul (qsub L (qsub y' y)) α = A3 at *
  generalize qmul (qsub y' y) α = A4 at *
  generalize qmul L ι = A5 at *
  generalize qmul (qadd (qsub y' y) (qeps n)) ι = A6 at *
  generalize qmul (qeps n) A = A7 at *
  obtain ⟨g1, _⟩ := f2
  unfold qsub at *; rat_linarith

/-- OUTSIDE BY `ι`: `|r(x) − r(z)| ≤ |x − z|·(1 + A) + ε_n` (slope at most 1). -/
theorem r_near {x z α A e : QExpr} {n : Nat} (hx : InR x n) (hz : InR z n) (hαA : ZTrig.Ab α A)
    (h1 : qle (qsub x z) e) (h2 : qle (qsub z x) e) (he : qle qzero e) :
    ZTrig.Ab (qsub (qsub (atseq x n) (qmul α x)) (qsub (atseq z n) (qmul α z)))
      (qadd (qmul e (qadd qone A)) (qeps n)) := by
  obtain ⟨a1, a2⟩ := atan_near hx hz h1 h2
  have m := ab_mul (u := qsub x z) (H := e) ⟨by unfold qsub at *; rat_linarith, h1⟩ hαA
  have e1 : qEq (qsub (qsub (atseq x n) (qmul α x)) (qsub (atseq z n) (qmul α z)))
      (qsub (qsub (atseq x n) (atseq z n)) (qmul (qsub x z) α)) := by unfold qsub; rat_ring
  have e2 : qEq (qmul e (qadd qone A)) (qadd e (qmul e A)) := by rat_ring
  generalize qsub (atseq x n) (atseq z n) = D at *
  generalize qmul (qsub x z) α = M at *
  generalize qmul e (qadd qone A) = E1 at *
  generalize qmul e A = E2 at *
  obtain ⟨m1, m2⟩ := m
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE CORE: `ψ ≥ P − ι` on `[a − ι, b + ι]`, `α ≤ P`, the ends' values certified below `a` and above `b`. -/
theorem rem_atan_core {a b α ζ δ P La Hb : QExpr} (hab : qle a b) (hαP : qle α P)
    (hfl : ∀ ι t, qle qzero ι → qle (qsub a ι) t → qle t (qadd b ι) → qle (qsub P ι) (psi t))
    (hLa : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub La (qeps k)) (atseq a n))
    (hHb : ∀ k, ∃ N, ∀ n, N ≤ n → qle (atseq b n) (qadd Hb (qeps k)))
    (hlo : qle (qsub ζ δ) (qsub La (qmul α a))) (hhi : qle (qsub Hb (qmul α b)) (qadd ζ δ)) :
    Rem (fun n x => atseq x n) a b α ζ δ := by
  obtain ⟨A, _, hA, _⟩ := abs_wit α
  have A0 : qle qzero A := by obtain ⟨h1, h2⟩ := hA; rat_linarith
  have o := qle_of_qlt qone_pos
  have ba : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  refine ⟨qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A), qone, by rat_linarith, qone_pos, fun k => ?_⟩
  obtain ⟨Ka, a1, a2⟩ := ZExp.exists_nat_bound a
  obtain ⟨Kb, b1, b2⟩ := ZExp.exists_nat_bound b
  unfold qsub at a1 a2 b1 b2
  obtain ⟨Bq, hB⟩ := eps_scaledA (by rat_linarith : qle qzero (qadd A qone))
  obtain ⟨N1, h1⟩ := hLa (k + 2)
  obtain ⟨N2, h2⟩ := hHb (k + 2)
  refine ⟨N1 + (N2 + ((Ka + Kb + 1 + 2) + (k + 2 + Bq))), fun n hn x ι ι0 ι1 hxa hxb => ?_⟩
  have A1 := h1 n (le4a hn)
  have B1 := h2 n (le4b hn)
  have hε := eps_of_le (le4d hn)
  have hb := hB (k + 2)
  have hε' := ZExp.scale hε (by rat_linarith : qle qzero (qadd A qone))
  have cm := qmul_comm (qeps n) (qadd A qone)
  have cm2 := qmul_comm (qeps (k + 2 + Bq)) (qadd A qone)
  have e1 := qeps_succ_add k; have e2 := qeps_succ_add (k + 1)
  have e0 := qeps_nonneg (k + 2); have en := qeps_nonneg n
  have q1 := ZTrig.qeps_le_one n
  have hn' := le4c hn
  have rx : InR x n := inR_of (ab_le (a := Ka + Kb + 1) ⟨by
      have := qnat_add Ka Kb; have := qnat_succ (Ka + Kb); have := qnat_nonneg Kb; unfold qsub at hxa; rat_linarith, by
      have := qnat_add Ka Kb; have := qnat_succ (Ka + Kb); have := qnat_nonneg Ka; rat_linarith⟩ (Nat.le_refl _)) hn'
  have ra : InR a n := inR_of (ab_le (a := Ka) ⟨by rat_linarith, by rat_linarith⟩
    (Nat.le_trans (Nat.le_add_right Ka Kb) (Nat.le_succ _))) hn'
  have rb : InR b n := inR_of (ab_le (a := Kb) ⟨by rat_linarith, by rat_linarith⟩
    (Nat.le_trans (Nat.le_add_left Kb Ka) (Nat.le_succ _))) hn'
  have fl : ∀ y y', qle (qsub a ι) y → qle y' (qadd b ι) → ∀ t, qle y t → qle t y' → qle (qsub P ι) (psi t) :=
    fun y y' hy hy' t h1 h2 => hfl ι t ι0 (qle_trans hy h1) (qle_trans h2 hy')
  -- the lower side: r(x) ≥ r(a) − ...
  have lower : qle (qsub (qsub (qsub (atseq a n) (qmul α a)) (qmul (qeps n) (qadd A qone)))
      (qmul ι (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)))) (qsub (atseq x n) (qmul α x)) := by
    have big := qmul_nonneg ι0 (by rat_linarith : qle qzero (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)))
    have em := qmul_nonneg en A0
    cases qle_total a x with
    | inl hx =>
        have rr := r_rise ra rx hx hαP hA ι0 (fl a x (by unfold qsub; rat_linarith) hxb)
        have f := ZExp.scale (by unfold qsub at *; rat_linarith : qle (qadd (qsub x a) (qeps n)) (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A))) ι0
        have c1 := qmul_comm (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) ι
        have e3 : qEq (qmul (qeps n) (qadd A qone)) (qadd (qmul (qeps n) A) (qeps n)) := by rat_ring
        generalize qmul (qadd (qsub x a) (qeps n)) ι = X1 at *
        generalize qmul (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) ι = X2 at *
        generalize qmul ι (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) = X3 at *
        generalize qmul (qeps n) (qadd A qone) = X4 at *
        generalize qmul (qeps n) A = X5 at *
        unfold qsub at *; rat_linarith
    | inr hx =>
        obtain ⟨n1, n2⟩ := r_near ra rx hA (e := ι) (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith) ι0
        have f := scale_l (by unfold qsub at *; rat_linarith : qle (qadd qone A) (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A))) ι0
        have e3 : qEq (qmul (qeps n) (qadd A qone)) (qadd (qmul (qeps n) A) (qeps n)) := by rat_ring
        generalize qmul ι (qadd qone A) = X1 at *
        generalize qmul ι (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) = X3 at *
        generalize qmul (qeps n) (qadd A qone) = X4 at *
        generalize qmul (qeps n) A = X5 at *
        unfold qsub at *; rat_linarith
  have upper : qle (qsub (atseq x n) (qmul α x)) (qadd (qadd (qsub (atseq b n) (qmul α b)) (qmul (qeps n) (qadd A qone)))
      (qmul ι (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)))) := by
    have big := qmul_nonneg ι0 (by rat_linarith : qle qzero (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)))
    have em := qmul_nonneg en A0
    cases qle_total x b with
    | inl hx =>
        have rr := r_rise rx rb hx hαP hA ι0 (fl x b hxa (by rat_linarith))
        have f := ZExp.scale (by unfold qsub at *; rat_linarith : qle (qadd (qsub b x) (qeps n)) (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A))) ι0
        have c1 := qmul_comm (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) ι
        have e3 : qEq (qmul (qeps n) (qadd A qone)) (qadd (qmul (qeps n) A) (qeps n)) := by rat_ring
        generalize qmul (qadd (qsub b x) (qeps n)) ι = X1 at *
        generalize qmul (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) ι = X2 at *
        generalize qmul ι (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) = X3 at *
        generalize qmul (qeps n) (qadd A qone) = X4 at *
        generalize qmul (qeps n) A = X5 at *
        unfold qsub at *; rat_linarith
    | inr hx =>
        obtain ⟨n1, n2⟩ := r_near rx rb hA (e := ι) (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith) ι0
        have f := scale_l (by unfold qsub at *; rat_linarith : qle (qadd qone A) (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A))) ι0
        have e3 : qEq (qmul (qeps n) (qadd A qone)) (qadd (qmul (qeps n) A) (qeps n)) := by rat_ring
        generalize qmul ι (qadd qone A) = X1 at *
        generalize qmul ι (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) = X3 at *
        generalize qmul (qeps n) (qadd A qone) = X4 at *
        generalize qmul (qeps n) A = X5 at *
        unfold qsub at *; rat_linarith
  show ZTrig.Ab (qsub (qsub (atseq x n) (qmul α x)) ζ) _
  generalize qmul ι (qadd (qadd (qsub b a) (qadd qone qone)) (qadd qone A)) = I at *
  generalize qmul (qeps n) (qadd A qone) = E at *
  generalize qmul (qeps (k + 2 + Bq)) (qadd A qone) = E' at *
  generalize qmul (qadd A qone) (qeps n) = E2 at *
  generalize qmul (qadd A qone) (qeps (k + 2 + Bq)) = E3 at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE KERNEL'S `atan` STEP, `0 ≤ a`: the slope at `b`, `α·(1 + b²) ≤ 1`. -/
theorem rem_atan_pos {a b α ζ δ La Hb : QExpr} (ha : qle qzero a) (hab : qle a b)
    (hα : qle (qmul α (qadd qone (qmul b b))) qone)
    (hLa : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub La (qeps k)) (atseq a n))
    (hHb : ∀ k, ∃ N, ∀ n, N ≤ n → qle (atseq b n) (qadd Hb (qeps k)))
    (hlo : qle (qsub ζ δ) (qsub La (qmul α a))) (hhi : qle (qsub Hb (qmul α b)) (qadd ζ δ)) :
    Rem (fun n x => atseq x n) a b α ζ δ :=
  rem_atan_core hab (le_psi hα) (fun _ _ ι0 h1 h2 => psi_floor_pos ha ι0 h1 h2) hLa hHb hlo hhi

/-- `b ≤ 0`: the slope at `a`, `α·(1 + a²) ≤ 1`. -/
theorem rem_atan_neg {a b α ζ δ La Hb : QExpr} (hb : qle b qzero) (hab : qle a b)
    (hα : qle (qmul α (qadd qone (qmul a a))) qone)
    (hLa : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub La (qeps k)) (atseq a n))
    (hHb : ∀ k, ∃ N, ∀ n, N ≤ n → qle (atseq b n) (qadd Hb (qeps k)))
    (hlo : qle (qsub ζ δ) (qsub La (qmul α a))) (hhi : qle (qsub Hb (qmul α b)) (qadd ζ δ)) :
    Rem (fun n x => atseq x n) a b α ζ δ :=
  rem_atan_core hab (le_psi hα) (fun _ _ ι0 h1 h2 => psi_floor_neg hb ι0 h1 h2) hLa hHb hlo hhi

end ZAffine

#print axioms ZAffine.ab_mul
#print axioms ZAffine.le_psi
#print axioms ZAffine.psi_floor_pos
#print axioms ZAffine.psi_floor_neg
#print axioms ZAffine.r_rise
#print axioms ZAffine.r_near
#print axioms ZAffine.rem_atan_core
#print axioms ZAffine.rem_atan_pos
#print axioms ZAffine.rem_atan_neg
