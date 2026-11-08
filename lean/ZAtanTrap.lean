import ZAtan
/-!
# ZAtanTrap — the TRAPEZOID LAW of `atan` on VR's continuum. Zero axioms.

The curator, 2026-11-08 ("делаем"): `atan`'s value reading was a Riemann enclosure, width `~d/N`; the trapezoid
rule makes it `~d³/N²`. What is proved: for `x ≤ y`, `h = y − x`,
  `|4(atan y − atan x) − 2h(ψ(x) + ψ(y))| ≤ h³`        (`ψ(t) = 1/(1 + t²)`; the true constant is `2/3`)
from the grid sums of `ZAtan` themselves — no integral, no mean value theorem. The steps:
  * THE DEVIATION FROM THE CHORD, exactly (`psi_dev`): with `m = −(x + y)ψ(x)ψ(y)` (the chord's slope, no
    division), `ψ(t) − ψ(x) − (t − x)·m = (t − x)(y − t)·ψ(x)ψ(t)ψ(y)·P`, `P = 1 − xt − ty − xy`;
  * `|ψ(x)ψ(t)ψ(y)·P| ≤ 1` (`piP_bound`) because `(1 + x²)(1 + t²)(1 + y²) = P² + (x + t + y − xty)²` — the squared
    modulus of `(1 + ix)(1 + it)(1 + iy)`; so the deviation is at most `(t − x)(y − t) ≤ h²/4` (`dev_bound`);
  * the grid sum of `ψ` over the points in `(x, y]` against the trapezoid, at one index (`trap_sum`), and in the
    limit (`ZRootAtan.r_atanLaws`'s `trap`).
MEASURED 2026-11-08 (Python, exact fractions, 20 000 random triples): the identity holds exactly; the deviation
reaches 0.9996 of `(t − x)(y − t)` (the bound is sharp); the trapezoid error of `atan` reaches `0.1666·h³`.
-/

namespace ZAtanTrap

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZAtan

/-- The chord's slope of `ψ` between `x` and `y`, without division. -/
def mch (x y : QExpr) : QExpr := qneg (qmul (qmul (psi x) (psi y)) (qadd x y))

/-- `P = 1 − xt − ty − xy`. -/
def PP (x t y : QExpr) : QExpr := qsub qone (qadd (qadd (qmul x t) (qmul t y)) (qmul x y))

/-- `ψ(y) − ψ(t) = ψ(y)ψ(t)·(y − t)·(1 − ty)` for `y·ψ(y) − t·ψ(t)`. -/
theorem psi_lin (t y : QExpr) :
    qEq (qsub (qmul y (psi y)) (qmul t (psi t))) (qmul (qmul (qmul (psi y) (psi t)) (qsub y t)) (qsub qone (qmul t y))) := by
  obtain ⟨_, _, cy⟩ := psi_facts y
  obtain ⟨_, _, ct⟩ := psi_facts t
  -- y·ψy = y·ψy·(1 + t²)ψt, t·ψt = t·ψt·(1 + y²)ψy
  have a1 : qEq (qmul y (psi y)) (qmul (qmul y (psi y)) (qmul (qadd qone (qmul t t)) (psi t))) :=
    qEq_trans (qEq_symm (qmul_one _)) (qmul_respects (qEq_refl _) (qEq_symm ct))
  have a2 : qEq (qmul t (psi t)) (qmul (qmul t (psi t)) (qmul (qadd qone (qmul y y)) (psi y))) :=
    qEq_trans (qEq_symm (qmul_one _)) (qmul_respects (qEq_refl _) (qEq_symm cy))
  have e : qEq (qsub (qmul (qmul y (psi y)) (qmul (qadd qone (qmul t t)) (psi t)))
      (qmul (qmul t (psi t)) (qmul (qadd qone (qmul y y)) (psi y))))
      (qmul (qmul (qmul (psi y) (psi t)) (qsub y t)) (qsub qone (qmul t y))) := by unfold qsub; rat_ring
  exact qEq_trans (qadd_respects a1 (qneg_respects a2)) e

/-- **THE DEVIATION FROM THE CHORD, EXACTLY.** -/
theorem psi_dev (x t y : QExpr) :
    qEq (qsub (qsub (psi t) (psi x)) (qmul (qsub t x) (mch x y)))
      (qmul (qmul (qsub t x) (qsub y t)) (qmul (qmul (qmul (psi x) (psi t)) (psi y)) (PP x t y))) := by
  have e1 := psi_diff t x
  have e2 := psi_diff y t
  have e3 := psi_lin t y
  -- X1, X2, X3 ≈ 0; the target is X1 + (t − x)ψx·(x·X2 + X3) by a ring identity
  have z1 : qEq (qsub (qsub (psi t) (psi x)) (qmul (qmul (qmul (psi t) (psi x)) (qadd x t)) (qsub x t))) qzero := by
    have := qadd_respects e1 (qEq_refl (qneg (qmul (qmul (qmul (psi t) (psi x)) (qadd x t)) (qsub x t))))
    unfold qsub at *; exact qEq_trans this (by rat_ring)
  have z2 : qEq (qsub (qsub (psi y) (psi t)) (qmul (qmul (qmul (psi y) (psi t)) (qadd t y)) (qsub t y))) qzero := by
    have := qadd_respects e2 (qEq_refl (qneg (qmul (qmul (qmul (psi y) (psi t)) (qadd t y)) (qsub t y))))
    unfold qsub at *; exact qEq_trans this (by rat_ring)
  have z3 : qEq (qsub (qsub (qmul y (psi y)) (qmul t (psi t)))
      (qmul (qmul (qmul (psi y) (psi t)) (qsub y t)) (qsub qone (qmul t y)))) qzero := by
    have := qadd_respects e3 (qEq_refl (qneg (qmul (qmul (qmul (psi y) (psi t)) (qsub y t)) (qsub qone (qmul t y)))))
    unfold qsub at *; exact qEq_trans this (by rat_ring)
  have c2 := qmul_respects (qEq_refl (qmul (qmul (qsub t x) (psi x)) x)) z2
  have c3 := qmul_respects (qEq_refl (qmul (qsub t x) (psi x))) z3
  have ring : qEq (qsub (qsub (qsub (psi t) (psi x)) (qmul (qsub t x) (mch x y)))
      (qmul (qmul (qsub t x) (qsub y t)) (qmul (qmul (qmul (psi x) (psi t)) (psi y)) (PP x t y))))
      (qadd (qadd (qsub (qsub (psi t) (psi x)) (qmul (qmul (qmul (psi t) (psi x)) (qadd x t)) (qsub x t)))
        (qmul (qmul (qmul (qsub t x) (psi x)) x)
          (qsub (qsub (psi y) (psi t)) (qmul (qmul (qmul (psi y) (psi t)) (qadd t y)) (qsub t y)))))
        (qmul (qmul (qsub t x) (psi x))
          (qsub (qsub (qmul y (psi y)) (qmul t (psi t)))
            (qmul (qmul (qmul (psi y) (psi t)) (qsub y t)) (qsub qone (qmul t y)))))) := by
    unfold mch PP qsub; rat_ring
  have z := qEq_trans ring (qadd_respects (qadd_respects z1 c2) c3)
  have zz : qEq (qadd (qadd qzero (qmul (qmul (qmul (qsub t x) (psi x)) x) qzero)) (qmul (qmul (qsub t x) (psi x)) qzero))
      qzero := by rat_ring
  have w := qEq_trans z zz
  generalize qsub (qsub (psi t) (psi x)) (qmul (qsub t x) (mch x y)) = L at w
  generalize qmul (qmul (qsub t x) (qsub y t)) (qmul (qmul (qmul (psi x) (psi t)) (psi y)) (PP x t y)) = R at w
  unfold qsub at w
  exact qle_antisymm (by have := qle_of_qEq w; rat_linarith) (by have := qle_of_qEq (qEq_symm w); rat_linarith)

/-- `a² ≤ 1` gives `|a| ≤ 1` (decided on the rationals). -/
theorem abs_of_sq {a : QExpr} (h : qle (qmul a a) qone) : ZTrig.Ab a qone := by
  constructor
  · cases qle_total (qneg qone) a with
    | inl l => exact l
    | inr l =>
        have n1 : qle qone (qneg a) := by rat_linarith
        have n0 : qle qzero (qneg a) := qle_trans (qle_of_qlt (qeps_pos 0)) (qle_trans (qle_of_qEq qeps_zero) n1)
        have s := ZExp.scale n1 n0
        have e1 : qEq (qmul qone (qneg a)) (qneg a) := qone_mul _
        have e2 : qEq (qmul (qneg a) (qneg a)) (qmul a a) := by rat_ring
        generalize qmul qone (qneg a) = A at *; generalize qmul (qneg a) (qneg a) = B at *
        generalize qmul a a = C at *
        rat_linarith
  · cases qle_total a qone with
    | inl l => exact l
    | inr l =>
        have a0 : qle qzero a := qle_trans (qle_of_qlt (qeps_pos 0)) (qle_trans (qle_of_qEq qeps_zero) l)
        have s := ZExp.scale l a0
        have e1 : qEq (qmul qone a) a := qone_mul _
        generalize qmul qone a = A at *; generalize qmul a a = C at *
        rat_linarith

/-- `Π = ψ(x)ψ(t)ψ(y)`. -/
def Pi3 (x t y : QExpr) : QExpr := qmul (qmul (psi x) (psi t)) (psi y)

/-- **`|ψ(x)ψ(t)ψ(y)·P| ≤ 1`**: `(1 + x²)(1 + t²)(1 + y²) = P² + Q²`, `Q = x + t + y − xty`. -/
theorem piP_bound (x t y : QExpr) : ZTrig.Ab (qmul (Pi3 x t y) (PP x t y)) qone := by
  obtain ⟨x0, x1, cx⟩ := psi_facts x
  obtain ⟨t0, t1, ct⟩ := psi_facts t
  obtain ⟨y0, y1, cy⟩ := psi_facts y
  -- Π·A = 1
  have hA : qEq (qmul (Pi3 x t y) (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y)))) qone := by
    have r : qEq (qmul (Pi3 x t y) (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y))))
        (qmul (qmul (qmul (qadd qone (qmul x x)) (psi x)) (qmul (qadd qone (qmul t t)) (psi t)))
          (qmul (qadd qone (qmul y y)) (psi y))) := by unfold Pi3; rat_ring
    refine qEq_trans r (qEq_trans (qmul_respects (qmul_respects cx ct) cy) ?_)
    rat_ring
  have sos : qEq (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y)))
      (qadd (qmul (PP x t y) (PP x t y))
        (qmul (qsub (qadd (qadd x t) y) (qmul (qmul x t) y)) (qsub (qadd (qadd x t) y) (qmul (qmul x t) y)))) := by
    unfold PP qsub; rat_ring
  have q2 := qmul_self_nonneg (qsub (qadd (qadd x t) y) (qmul (qmul x t) y))
  have P0 : qle qzero (Pi3 x t y) := qmul_nonneg (qmul_nonneg x0 t0) y0
  have P1 : qle (Pi3 x t y) qone := by
    have a := ZExp.scale x1 t0
    have ab : qle (qmul (psi x) (psi t)) qone := qle_trans (qle_trans a (qle_of_qEq (qone_mul _))) t1
    have b := ZExp.scale ab y0
    exact qle_trans (qle_trans b (qle_of_qEq (qone_mul _))) y1
  -- (ΠP)² = Π²P² ≤ Π²A = Π ≤ 1
  have PP2 : qle (qmul (PP x t y) (PP x t y))
      (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y))) := by
    have := qle_of_qEq (qEq_symm sos)
    generalize qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y)) = A at *
    generalize qmul (PP x t y) (PP x t y) = B at *
    generalize qmul (qsub (qadd (qadd x t) y) (qmul (qmul x t) y)) (qsub (qadd (qadd x t) y) (qmul (qmul x t) y)) = C at *
    rat_linarith
  have s := scale_l PP2 (qmul_self_nonneg (Pi3 x t y))
  have e1 : qEq (qmul (qmul (Pi3 x t y) (PP x t y)) (qmul (Pi3 x t y) (PP x t y)))
      (qmul (qmul (Pi3 x t y) (Pi3 x t y)) (qmul (PP x t y) (PP x t y))) := by rat_ring
  have e2 : qEq (qmul (qmul (Pi3 x t y) (Pi3 x t y))
      (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y)))) (Pi3 x t y) := by
    have r : qEq (qmul (qmul (Pi3 x t y) (Pi3 x t y))
        (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y))))
        (qmul (Pi3 x t y) (qmul (Pi3 x t y) (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y))))) := by
      rat_ring
    exact qEq_trans r (qEq_trans (qmul_respects (qEq_refl _) hA) (qmul_one _))
  apply abs_of_sq
  generalize qmul (qmul (Pi3 x t y) (PP x t y)) (qmul (Pi3 x t y) (PP x t y)) = L at *
  generalize qmul (qmul (Pi3 x t y) (Pi3 x t y)) (qmul (PP x t y) (PP x t y)) = M at *
  generalize qmul (qmul (Pi3 x t y) (Pi3 x t y))
    (qmul (qmul (qadd qone (qmul x x)) (qadd qone (qmul t t))) (qadd qone (qmul y y))) = N at *
  have := qle_of_qEq e1; have := qle_of_qEq e2
  rat_linarith

/-- **THE DEVIATION IS AT MOST `(t − x)(y − t)`.** -/
theorem dev_bound {x t y : QExpr} (h1 : qle x t) (h2 : qle t y) :
    ZTrig.Ab (qsub (qsub (psi t) (psi x)) (qmul (qsub t x) (mch x y))) (qmul (qsub t x) (qsub y t)) := by
  have u0 : qle qzero (qsub t x) := by unfold qsub; rat_linarith
  have v0 : qle qzero (qsub y t) := by unfold qsub; rat_linarith
  have uv0 := qmul_nonneg u0 v0
  have huv : ZTrig.Ab (qmul (qsub t x) (qsub y t)) (qmul (qsub t x) (qsub y t)) := ⟨by rat_linarith, qle_refl _⟩
  have m := ZTrig.mul_abs huv (piP_bound x t y)
  have e := psi_dev x t y
  have o := qmul_one (qmul (qsub t x) (qsub y t))
  unfold Pi3 at m
  obtain ⟨m1, m2⟩ := m
  generalize qmul (qmul (qsub t x) (qsub y t)) (qmul (qmul (qmul (psi x) (psi t)) (psi y)) (PP x t y)) = R at *
  generalize qmul (qmul (qsub t x) (qsub y t)) qone = W at *
  generalize qsub (qsub (psi t) (psi x)) (qmul (qsub t x) (mch x y)) = L at *
  have := qle_of_qEq e; have := qle_of_qEq (qEq_symm e)
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `4(t − x)(y − t) ≤ (y − x)²`. -/
theorem quarter (x t y : QExpr) :
    qle (qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul (qsub t x) (qsub y t))) (qmul (qsub y x) (qsub y x)) := by
  have s := qmul_self_nonneg (qsub (qsub y t) (qsub t x))
  have e : qEq (qmul (qsub y x) (qsub y x))
      (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul (qsub t x) (qsub y t)))
        (qmul (qsub (qsub y t) (qsub t x)) (qsub (qsub y t) (qsub t x)))) := by unfold qsub; rat_ring
  have := qle_of_qEq (qEq_symm e)
  generalize qmul (qsub y x) (qsub y x) = A at *
  generalize qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul (qsub t x) (qsub y t)) = B at *
  generalize qmul (qsub (qsub y t) (qsub t x)) (qsub (qsub y t) (qsub t x)) = C at *
  rat_linarith

/-! ## The grid sum against the trapezoid, at one index -/

/-- The prefix sums' difference is the sum over the grid points `t_{c+1}, …, t_{c+k}`. -/
theorem psum_split (n c : Nat) : ∀ k,
    qEq (qsub (psum n (c + k)) (psum n c)) (ZTrig.bs (fun j => qmul (qeps n) (psi (gpt n (c + 1 + j)))) k)
  | 0 => by show qEq (qsub (psum n c) (psum n c)) qzero; unfold qsub; rat_ring
  | k + 1 => by
      have ih := psum_split n c k
      show qEq (qsub (qadd (psum n (c + k)) (qmul (qeps n) (psi (gpt n (c + k + 1))))) (psum n c))
        (qadd (ZTrig.bs (fun j => qmul (qeps n) (psi (gpt n (c + 1 + j)))) k) (qmul (qeps n) (psi (gpt n (c + 1 + k)))))
      rw [Nat.add_right_comm c 1 k]
      generalize ZTrig.bs (fun j => qmul (qeps n) (psi (gpt n (c + 1 + j)))) k = B at *
      generalize qmul (qeps n) (psi (gpt n (c + k + 1))) = T at *
      unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `4·ε₂ = 1`. -/
theorem eps2_four : qEq (qmul (qadd (qadd qone qone) (qadd qone qone)) (qeps 2)) qone := by
  have a := qeps_succ_add 1
  have b := qeps_succ_add 0
  have z := qeps_zero
  have e : qEq (qmul (qadd (qadd qone qone) (qadd qone qone)) (qeps 2))
      (qadd (qadd (qeps 2) (qeps 2)) (qadd (qeps 2) (qeps 2))) := by rat_ring
  refine qEq_trans e ?_
  generalize qeps 2 = E2 at *; generalize qeps 1 = E1 at *; generalize qeps 0 = E0 at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- ONE TERM: `ε·ψ(t_j)` against its linear part, within `ε·h²/4`. -/
theorem term_dev {x y δ e g1 t : QExpr} {j : Nat} (hxt : qle x t) (hty : qle t y) (he : qle qzero e)
    (hδ : qEq δ (qsub g1 x)) (ht : qEq (qsub t g1) (qmul (qnat j) e)) :
    ZTrig.Ab (qsub (qmul e (psi t))
        (qadd (qmul (qmul (qnat j) e) (qmul e (mch x y))) (qadd (qmul e (psi x)) (qmul (qmul e δ) (mch x y)))))
      (qmul e (qmul (qeps 2) (qmul (qsub y x) (qsub y x)))) := by
  obtain ⟨d1, d2⟩ := dev_bound hxt hty
  have q := quarter x t y
  have f := eps2_four
  -- (t − x)(y − t) ≤ ε₂·h²
  have qq : qle (qmul (qsub t x) (qsub y t)) (qmul (qeps 2) (qmul (qsub y x) (qsub y x))) := by
    have s := scale_l q (qle_of_qlt (qeps_pos 2))
    have e1 : qEq (qmul (qeps 2) (qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul (qsub t x) (qsub y t))))
        (qmul (qmul (qadd (qadd qone qone) (qadd qone qone)) (qeps 2)) (qmul (qsub t x) (qsub y t))) := by rat_ring
    have e2 := qmul_respects f (qEq_refl (qmul (qsub t x) (qsub y t)))
    have e3 : qEq (qmul qone (qmul (qsub t x) (qsub y t))) (qmul (qsub t x) (qsub y t)) := qone_mul _
    generalize qmul (qeps 2) (qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul (qsub t x) (qsub y t))) = A at *
    generalize qmul (qmul (qadd (qadd qone qone) (qadd qone qone)) (qeps 2)) (qmul (qsub t x) (qsub y t)) = B at *
    generalize qmul qone (qmul (qsub t x) (qsub y t)) = C at *
    have := qle_of_qEq e1; have := qle_of_qEq e2; have := qle_of_qEq e3
    rat_linarith
  -- the term minus its linear part is e·dev + e·m·((t − x) − δ − j·e), the second ≈ 0
  have z : qEq (qsub (qsub (qsub t x) δ) (qmul (qnat j) e)) qzero := by
    unfold qsub at *
    exact qle_antisymm (by have := qle_of_qEq hδ; have := qle_of_qEq (qEq_symm hδ); have := qle_of_qEq ht;
                           have := qle_of_qEq (qEq_symm ht); rat_linarith)
      (by have := qle_of_qEq hδ; have := qle_of_qEq (qEq_symm hδ); have := qle_of_qEq ht;
          have := qle_of_qEq (qEq_symm ht); rat_linarith)
  have zz := qmul_respects (qEq_refl (qmul e (mch x y))) z
  have r : qEq (qsub (qmul e (psi t))
        (qadd (qmul (qmul (qnat j) e) (qmul e (mch x y))) (qadd (qmul e (psi x)) (qmul (qmul e δ) (mch x y)))))
      (qadd (qmul e (qsub (qsub (psi t) (psi x)) (qmul (qsub t x) (mch x y))))
        (qmul (qmul e (mch x y)) (qsub (qsub (qsub t x) δ) (qmul (qnat j) e)))) := by unfold qsub; rat_ring
  have z0 : qEq (qmul (qmul e (mch x y)) qzero) qzero := by rat_ring
  have s1 := scale_l d1 he
  have s2 := scale_l d2 he
  have s3 := scale_l qq he
  have n1 : qEq (qmul e (qneg (qmul (qsub t x) (qsub y t)))) (qneg (qmul e (qmul (qsub t x) (qsub y t)))) := by rat_ring
  generalize qmul e (qsub (qsub (psi t) (psi x)) (qmul (qsub t x) (mch x y))) = D at *
  generalize qmul (qmul e (mch x y)) (qsub (qsub (qsub t x) δ) (qmul (qnat j) e)) = Z at *
  generalize qmul (qmul e (mch x y)) qzero = Z0 at *
  generalize qmul e (qneg (qmul (qsub t x) (qsub y t))) = N at *
  generalize qmul e (qmul (qsub t x) (qsub y t)) = U at *
  generalize qmul e (qmul (qeps 2) (qmul (qsub y x) (qsub y x))) = W at *
  generalize qsub (qmul e (psi t))
    (qadd (qmul (qmul (qnat j) e) (qmul e (mch x y))) (qadd (qmul e (psi x)) (qmul (qmul e δ) (mch x y)))) = L at *
  have := qle_of_qEq r; have := qle_of_qEq (qEq_symm r); have := qle_of_qEq zz; have := qle_of_qEq (qEq_symm zz)
  have := qle_of_qEq z0; have := qle_of_qEq (qEq_symm z0); have := qle_of_qEq n1; have := qle_of_qEq (qEq_symm n1)
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- The error of the linear part's sum: `E = 4(K − h)ψx + m·Q`, `|E| ≤ 4e + e(8K + 2h)`. -/
theorem lin_err {K h e δ px m : QExpr} (hη1 : qle (qsub K h) e) (hη2 : qle (qneg e) (qsub K h))
    (hδ0 : qle qzero δ) (hδ1 : qle δ e) (hK : qle qzero K) (hh : qle qzero h) (p0 : qle qzero px) (p1 : qle px qone)
    (hm : ZTrig.Ab m qone) :
    ZTrig.Ab (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul (qsub K h) px))
        (qmul m (qsub (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul K δ))
          (qmul (qadd qone qone) (qmul (qsub K h) (qadd K h)))) (qmul (qadd qone qone) (qmul K e)))))
      (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) e)
        (qmul e (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd K K)) (qadd h h)))) := by
  have e0 : qle qzero e := qle_trans hδ0 hδ1
  have a1 := ZTrig.mul_abs (u := qsub K h) (v := px) ⟨hη2, hη1⟩ ⟨by rat_linarith, p1⟩
  have kd2 := scale_l hδ1 hK
  have kd1 := scale_l hδ0 hK
  have kh : ZTrig.Ab (qadd K h) (qadd K h) := ⟨by rat_linarith, qle_refl _⟩
  have a2 := ZTrig.mul_abs (u := qsub K h) (v := qadd K h) ⟨hη2, hη1⟩ kh
  have ke := qmul_nonneg hK e0
  have hQ : ZTrig.Ab (qsub (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qmul K δ))
        (qmul (qadd qone qone) (qmul (qsub K h) (qadd K h)))) (qmul (qadd qone qone) (qmul K e)))
      (qmul e (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd K K)) (qadd h h))) := by
    obtain ⟨b1, b2⟩ := a2
    have z : qEq (qmul K qzero) qzero := by rat_ring
    have := qle_of_qEq z
    unfold qsub at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  have a3 := ZTrig.mul_abs hm hQ
  obtain ⟨c1, c2⟩ := a1
  obtain ⟨d1, d2⟩ := a3
  clear kd1 kd2 kh hQ a2 ke
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

set_option maxRecDepth 8000 in
/-- The total, from the pieces: `S` the grid sum, `Sg` its linear part. -/
theorem trap_combine {S Sg J px py m h e δ : QExpr} {k : Nat}
    (hS : ZTrig.Ab (qsub S Sg) (qmul (qnat k) (qmul e (qmul (qeps 2) (qmul h h)))))
    (hSg : qEq Sg (qadd (qmul (qmul e (qmul e m)) J) (qmul (qnat k) (qadd (qmul e px) (qmul (qmul e δ) m)))))
    (hJ : qEq (qadd J J) (qsub (qmul (qnat k) (qnat k)) (qnat k)))
    (hpy : qEq (qsub (qsub py px) (qmul h m)) qzero)
    (hη1 : qle (qsub (qmul (qnat k) e) h) e) (hη2 : qle (qneg e) (qsub (qmul (qnat k) e) h))
    (hδ0 : qle qzero δ) (hδ1 : qle δ e) (hh : qle qzero h) (p0 : qle qzero px) (p1 : qle px qone)
    (hm : ZTrig.Ab m qone) (e1 : qle e qone) :
    ZTrig.Ab (qsub (qmul (qadd (qadd qone qone) (qadd qone qone)) S) (qmul (qmul (qadd qone qone) h) (qadd px py)))
      (qadd (qmul (qmul h h) h) (qmul e (qadd (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone))
        (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone))
          (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) h) (qmul h h))))) := by
  have e0 : qle qzero e := qle_trans hδ0 hδ1
  have hK : qle qzero (qmul (qnat k) e) := qmul_nonneg (qnat_nonneg k) e0
  have L := lin_err hη1 hη2 hδ0 hδ1 hK hh p0 p1 hm
  -- the linear part's identity
  have J2 := qmul_respects (qEq_refl (qmul (qmul e e) m)) hJ
  have f := eps2_four
  have F4 := qmul_respects f (qEq_refl (qmul (qnat k) (qmul e (qmul h h))))
  have pyh := qmul_respects (qEq_refl h) hpy
  -- K·h² ≤ (h + e)·h², e·K ≤ e·(h + e), e² ≤ e
  have Kle : qle (qmul (qnat k) e) (qadd h e) := by unfold qsub at hη1; rat_linarith
  have s1 := ZExp.scale Kle (qmul_self_nonneg h)
  have s2 := scale_l Kle e0
  have s3 := scale_l e1 e0
  obtain ⟨l1, l2⟩ := L
  obtain ⟨a1, a2⟩ := hS
  have := qle_of_qEq hSg; have := qle_of_qEq (qEq_symm hSg)
  have := qle_of_qEq J2; have := qle_of_qEq (qEq_symm J2)
  have := qle_of_qEq F4; have := qle_of_qEq (qEq_symm F4)
  have := qle_of_qEq pyh; have := qle_of_qEq (qEq_symm pyh)
  clear hSg J2 F4 pyh f hJ hpy
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- **THE TRAPEZOID AT ONE INDEX**: the grid sum of `ψ` over `(x, y]` against `h(ψ(x) + ψ(y))/2`. -/
theorem trap_index {x y : QExpr} {n : Nat} (hx : InR x n) (hy : InR y n) (hxy : qle x y) :
    ZTrig.Ab (qsub (qmul (qadd (qadd qone qone) (qadd qone qone)) (qsub (atseq y n) (atseq x n)))
        (qmul (qmul (qadd qone qone) (qsub y x)) (qadd (psi x) (psi y))))
      (qadd (qmul (qmul (qsub y x) (qsub y x)) (qsub y x)) (qmul (qeps n) (qadd (qadd (qmul (qadd (qadd qone qone)
        (qadd qone qone)) (qadd qone qone)) (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd
          (qadd qone qone) (qadd qone qone)) (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) (qsub y x))
            (qmul (qsub y x) (qsub y x)))))) := by
  have hS0 : qEq (qsub (atseq y n) (atseq x n)) (qsub (psum n (acnt y n (gridK n))) (psum n (acnt x n (gridK n)))) := by
    unfold atseq; unfold qsub; rat_ring
  obtain ⟨_, _, bx1, bx2⟩ := acnt_bracket hx.1 hx.2
  obtain ⟨_, _, by1, by2⟩ := acnt_bracket hy.1 hy.2
  have hc := acnt_mono hxy n (gridK n)
  generalize acnt x n (gridK n) = c at *
  generalize acnt y n (gridK n) = c' at *
  obtain ⟨k, hk⟩ := ZExp.le_ex hc
  subst hk
  have sp := psum_split n c k
  have e0 := qeps_nonneg n
  have e1 := ZTrig.qeps_le_one n
  have g1 := gpt_succ n c
  have gk := gpt_succ n (c + k)
  have gadd := gpt_add n c k
  have bx2' := qle_of_qlt bx2
  have by2' := qle_of_qlt by2
  -- every grid point t_j, j < k, lies in [x, y]; each term is its linear part within ε·h²/4
  have terms : ∀ j, j < k → ZTrig.Ab ((fun j => qsub (qmul (qeps n) (psi (gpt n (c + 1 + j))))
        (qadd (qmul (qmul (qnat j) (qeps n)) (qmul (qeps n) (mch x y)))
          (qadd (qmul (qeps n) (psi x)) (qmul (qmul (qeps n) (qsub (gpt n (c + 1)) x)) (mch x y))))) j)
      (qmul (qeps n) (qmul (qeps 2) (qmul (qsub y x) (qsub y x)))) := by
    intro j hj
    have m1 := gpt_mono (n := n) (Nat.le_add_right (c + 1) j)
    have hle : c + 1 + j ≤ c + k := by
      rw [Nat.add_right_comm]; exact Nat.add_le_add_left (Nat.succ_le_of_lt hj) c
    have m2 := gpt_mono (n := n) hle
    exact term_dev (qle_trans bx2' m1) (qle_trans m2 by1) e0 (qEq_refl _) (gpt_add n (c + 1) j)
  have A := ZTrig.bs_abs_c k terms
  have B := ZTrig.bs_sub (fun j => qmul (qeps n) (psi (gpt n (c + 1 + j))))
    (fun j => qadd (qmul (qmul (qnat j) (qeps n)) (qmul (qeps n) (mch x y)))
      (qadd (qmul (qeps n) (psi x)) (qmul (qmul (qeps n) (qsub (gpt n (c + 1)) x)) (mch x y)))) k
  have C := ZTrig.bs_jw' (qeps n) (qmul (qeps n) (mch x y))
    (qadd (qmul (qeps n) (psi x)) (qmul (qmul (qeps n) (qsub (gpt n (c + 1)) x)) (mch x y))) k
  have J := ZTrig.bs_nat k
  have hpy : qEq (qsub (qsub (psi y) (psi x)) (qmul (qsub y x) (mch x y))) qzero := by
    have d := psi_dev x y y
    exact qEq_trans d (by unfold qsub; rat_ring)
  obtain ⟨px0, px1, _⟩ := psi_facts x
  obtain ⟨pm1, pm2⟩ := psi_P x y
  have hm : ZTrig.Ab (mch x y) qone := by unfold mch; exact ⟨by rat_linarith, by rat_linarith⟩
  have hh : qle qzero (qsub y x) := by unfold qsub; rat_linarith
  have hη1 : qle (qsub (qmul (qnat k) (qeps n)) (qsub y x)) (qeps n) := by
    unfold qsub at *; have := qle_of_qEq gadd; have := qle_of_qEq (qEq_symm gadd)
    have := qle_of_qEq g1; have := qle_of_qEq (qEq_symm g1); rat_linarith
  have hη2 : qle (qneg (qeps n)) (qsub (qmul (qnat k) (qeps n)) (qsub y x)) := by
    unfold qsub at *; have := qle_of_qEq gadd; have := qle_of_qEq (qEq_symm gadd)
    have := qle_of_qEq gk; have := qle_of_qEq (qEq_symm gk); rat_linarith
  have hδ0 : qle qzero (qsub (gpt n (c + 1)) x) := by unfold qsub; rat_linarith
  have hδ1 : qle (qsub (gpt n (c + 1)) x) (qeps n) := by
    unfold qsub at *; have := qle_of_qEq g1; have := qle_of_qEq (qEq_symm g1); rat_linarith
  -- the pieces into trap_combine, with S the grid sum
  have hS : ZTrig.Ab (qsub (ZTrig.bs (fun j => qmul (qeps n) (psi (gpt n (c + 1 + j)))) k)
      (ZTrig.bs (fun j => qadd (qmul (qmul (qnat j) (qeps n)) (qmul (qeps n) (mch x y)))
        (qadd (qmul (qeps n) (psi x)) (qmul (qmul (qeps n) (qsub (gpt n (c + 1)) x)) (mch x y)))) k))
      (qmul (qnat k) (qmul (qeps n) (qmul (qeps 2) (qmul (qsub y x) (qsub y x))))) := by
    obtain ⟨a1, a2⟩ := A
    have := qle_of_qEq B; have := qle_of_qEq (qEq_symm B)
    exact ⟨by rat_linarith, by rat_linarith⟩
  have R := trap_combine hS C J hpy hη1 hη2 hδ0 hδ1 hh px0 px1 hm e1
  obtain ⟨r1, r2⟩ := R
  have t1 := qEq_trans hS0 sp
  have u1 := qmul_respects (qEq_refl (qadd (qadd qone qone) (qadd qone qone))) t1
  clear A B C J terms hS sp hS0 t1
  have := qle_of_qEq u1; have := qle_of_qEq (qEq_symm u1)
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## In the limit: VR's operational reals -/

theorem ab_real' (x : RExpr) : ∃ K N, ∀ n, N ≤ n → ZTrig.Ab (x.seq n) (qnat K) := by
  obtain ⟨B, N, h⟩ := rbounded x
  refine ⟨2 ^ B, N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := h n hn
  have e := ZLn.qnat_pow2 B
  unfold qsub at h1 h2
  exact ⟨by rat_linarith, by rat_linarith⟩

set_option maxRecDepth 8000 in
/-- **THE TRAPEZOID LAW, TERMWISE**: for `xₙ ≤ yₙ`, the defect `4Δ − 2h(ψ(x) + ψ(y))` is within `h³` up to every
`ε_k`, from some index on. -/
theorem trap_seq (x y : RExpr) (hord : ∀ n, qle (x.seq n) (y.seq n)) : ∀ k, ∃ N, ∀ n, N ≤ n →
    qle (qsub (qneg (qmul (qmul (qsub (y.seq n) (x.seq n)) (qsub (y.seq n) (x.seq n))) (qsub (y.seq n) (x.seq n))))
      (qsub (qmul (qadd (qadd qone qone) (qadd qone qone)) (qsub (atseq (y.seq n) n) (atseq (x.seq n) n)))
        (qmul (qmul (qadd qone qone) (qsub (y.seq n) (x.seq n))) (qadd (psi (x.seq n)) (psi (y.seq n)))))) (qeps k) ∧
    qle (qsub (qsub (qmul (qadd (qadd qone qone) (qadd qone qone)) (qsub (atseq (y.seq n) n) (atseq (x.seq n) n)))
        (qmul (qmul (qadd qone qone) (qsub (y.seq n) (x.seq n))) (qadd (psi (x.seq n)) (psi (y.seq n)))))
      (qmul (qmul (qsub (y.seq n) (x.seq n)) (qsub (y.seq n) (x.seq n))) (qsub (y.seq n) (x.seq n)))) (qeps k) := by
  obtain ⟨Kx, Nx, hx⟩ := ab_real' x
  obtain ⟨Ky, Ny, hy⟩ := ab_real' y
  have k0 := qnat_nonneg Kx
  have k1 := qnat_nonneg Ky
  -- the constant 12 + 10A + A², A = Kx + Ky
  have A0 : qle qzero (qadd (qnat Kx) (qnat Ky)) := by rat_linarith
  have CA0 : qle qzero (qadd (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone))
      (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone))
        (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) (qadd (qnat Kx) (qnat Ky)))
          (qmul (qadd (qnat Kx) (qnat Ky)) (qadd (qnat Kx) (qnat Ky))))) := by
    have := qmul_self_nonneg (qadd (qnat Kx) (qnat Ky))
    have z : qle qzero (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone)) (qadd (qadd qone qone) (qadd qone qone)))
      (qadd qone qone)) (qadd (qnat Kx) (qnat Ky))) := qmul_nonneg (by have := qle_of_qlt qone_pos; rat_linarith) A0
    have z2 : qle qzero (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone)) :=
      qmul_nonneg (by have := qle_of_qlt qone_pos; rat_linarith) (by have := qle_of_qlt qone_pos; rat_linarith)
    have := qle_of_qlt qone_pos
    rat_linarith
  obtain ⟨B, hB⟩ := eps_scaledA CA0
  intro k
  refine ⟨Nx + Ny + (Kx + 2) + (Ky + 2) + (k + B), fun n hn => ?_⟩
  have ax := hx n (ZTrig.le_l' (ZTrig.le_l' (ZTrig.le_l' (ZTrig.le_l' hn))))
  have ay := hy n (ZTrig.le_r' (ZTrig.le_l' (ZTrig.le_l' (ZTrig.le_l' hn))))
  have rx := inR_of ax (ZTrig.le_r' (ZTrig.le_l' (ZTrig.le_l' hn)))
  have ry := inR_of ay (ZTrig.le_r' (ZTrig.le_l' hn))
  have T := trap_index rx ry (hord n)
  have en := ZLn.eps_anti (ZTrig.le_r' hn)
  have bk := hB k
  -- ε_n·C(h) ≤ ε_{k+B}·C(A) ≤ ε_k
  obtain ⟨x1, x2⟩ := ax
  obtain ⟨y1, y2⟩ := ay
  have h0 : qle qzero (qsub (y.seq n) (x.seq n)) := by unfold qsub; have := hord n; rat_linarith
  have hA : qle (qsub (y.seq n) (x.seq n)) (qadd (qnat Kx) (qnat Ky)) := by unfold qsub; rat_linarith
  have hh2 : qle (qmul (qsub (y.seq n) (x.seq n)) (qsub (y.seq n) (x.seq n)))
      (qmul (qadd (qnat Kx) (qnat Ky)) (qadd (qnat Kx) (qnat Ky))) := by
    have a := ZExp.scale hA h0
    have b := scale_l hA A0
    exact qle_trans a b
  have Cle : qle (qadd (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone))
      (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone))
        (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) (qsub (y.seq n) (x.seq n)))
          (qmul (qsub (y.seq n) (x.seq n)) (qsub (y.seq n) (x.seq n)))))
      (qadd (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone))
      (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone))
        (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) (qadd (qnat Kx) (qnat Ky)))
          (qmul (qadd (qnat Kx) (qnat Ky)) (qadd (qnat Kx) (qnat Ky))))) := by
    have := scale_l hA (by have := qle_of_qlt qone_pos; rat_linarith :
      qle qzero (qadd (qadd (qadd (qadd qone qone) (qadd qone qone)) (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)))
    rat_linarith
  have c1 := scale_l Cle (qeps_nonneg n)
  have c2 := ZExp.scale en CA0
  obtain ⟨t1, t2⟩ := T
  generalize qmul (qeps n) (qadd (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone))
      (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone))
        (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) (qsub (y.seq n) (x.seq n)))
          (qmul (qsub (y.seq n) (x.seq n)) (qsub (y.seq n) (x.seq n))))) = EC at *
  generalize qmul (qeps n) (qadd (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone))
      (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone))
        (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) (qadd (qnat Kx) (qnat Ky)))
          (qmul (qadd (qnat Kx) (qnat Ky)) (qadd (qnat Kx) (qnat Ky))))) = EA at *
  generalize qmul (qeps (k + B)) (qadd (qadd (qmul (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone))
      (qadd (qadd qone qone) (qadd qone qone))) (qadd (qmul (qadd (qadd (qadd (qadd qone qone) (qadd qone qone))
        (qadd (qadd qone qone) (qadd qone qone))) (qadd qone qone)) (qadd (qnat Kx) (qnat Ky)))
          (qmul (qadd (qnat Kx) (qnat Ky)) (qadd (qnat Kx) (qnat Ky))))) = EB at *
  generalize qsub (qmul (qadd (qadd qone qone) (qadd qone qone)) (qsub (atseq (y.seq n) n) (atseq (x.seq n) n)))
    (qmul (qmul (qadd qone qone) (qsub (y.seq n) (x.seq n))) (qadd (psi (x.seq n)) (psi (y.seq n)))) = R at *
  generalize qmul (qmul (qsub (y.seq n) (x.seq n)) (qsub (y.seq n) (x.seq n))) (qsub (y.seq n) (x.seq n)) = H3 at *
  clear hx hy x1 x2 y1 y2 rx ry hh2 Cle hA h0
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZAtanTrap

#print axioms ZAtanTrap.psi_lin
#print axioms ZAtanTrap.psi_dev
#print axioms ZAtanTrap.abs_of_sq
#print axioms ZAtanTrap.piP_bound
#print axioms ZAtanTrap.dev_bound
#print axioms ZAtanTrap.quarter
#print axioms ZAtanTrap.psum_split
#print axioms ZAtanTrap.eps2_four
#print axioms ZAtanTrap.term_dev
#print axioms ZAtanTrap.lin_err
#print axioms ZAtanTrap.trap_combine
#print axioms ZAtanTrap.trap_index
#print axioms ZAtanTrap.trap_seq
