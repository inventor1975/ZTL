import ZRealCF
import ZExpLaw
import ZLn
/-!
# VR's operational exponential is a lawful `exp` for `check_none` — so `exp` and `ln` hold on VR's continuum.
Zero axioms.

`ZExp.rexpR x` (`n ↦ eseq (xₙ) n`: the partial sums for a non-negative argument, their reciprocal below zero, read
from ZTL, not copied) satisfies `ZExpLaw.ExpLaws ZRealCF.rCF`. No addition law is used.

* The laws at dyadic points (`lo`, `hi`, `recip`): a dyadic is a CONSTANT sequence with a rational value `q`. So
  `lo` is `n!·S(q, n) ≤ n!·S(q, m)` (`S_mono`), `hi` is the tail bound `S(q, m) ≤ S(q, n) + 2·tₙ(q)` (`S_between`),
  and `recip` is `S(q, m)·(1/S(q, m)) = 1`.
* The general laws (`congr`, `mono`, `pos`, `strict`) come from `E_mono`, `E_lip`, `S_bounded`, `E_slope` and
  `tm_small`, at one index where the arguments are bounded (`E_floor`: a uniform floor `ε_C` on `[−R, R]`).
* `rExpLaws`, and `vr_no_solution_exp`: `check_none` on VR's continuum with VR's own `exp`.
* `ln`: `rln y` for `y > 0` (the grid answers of `ZLn.lnseq`, Cauchy by `ZLn.ln_cauchy`) and `rexp_rln`:
  `exp (ln y) = y`. So both nodes HAVE values on VR's continuum (the two `example`s): the theorem is not
  vacuous for systems with `exp` or `ln`.
-/

namespace ZRealExp
open VR VR.Numbers VR.CSR ZNumBin ZExpLaw ZRealCF ZExp ZLn

/-! ## Constant sequences -/

theorem num_seq : ∀ (k m : Nat), qEq ((CR.numeral RExpr.cr k).seq m) (qnat k)
  | 0, _ => qEq_refl _
  | k + 1, m => by
      have ih := num_seq k m
      have e := qnat_succ k
      change qEq (qadd qone ((CR.numeral RExpr.cr k).seq m)) (qnat (k + 1))
      exact qEq_trans (qEq_trans (qadd_respects (qEq_refl _) ih) (qadd_comm _ _)) (qEq_symm e)

/-- The rational value of a dyadic. -/
def qD (d : D) : QExpr := qmul (qsub (qnat d.m.p) (qnat d.m.n)) (qeps d.e)

theorem hp_seq : ∀ (e m : Nat), qEq ((hp rOH e).seq m) (qeps e)
  | 0, _ => qEq_symm qeps_zero
  | e + 1, m => by
      have ih := hp_seq e m
      change qEq (qmul (qeps 1) ((hp rOH e).seq m)) (qeps (e + 1))
      have m1 := ZRealCF.qeps_mul 1 e
      rw [show 1 + e = e + 1 from Nat.add_comm 1 e] at m1
      exact qEq_trans (qmul_respects (qEq_refl _) ih) m1

theorem dv_seq (d : D) (m : Nat) : qEq ((dv rOH d).seq m) (qD d) := by
  change qEq (qmul (qadd ((CR.numeral RExpr.cr d.m.p).seq m) (qneg ((CR.numeral RExpr.cr d.m.n).seq m)))
    ((hp rOH d.e).seq m)) (qD d)
  unfold qD qsub
  exact qmul_respects (qadd_respects (num_seq _ _) (qneg_respects (num_seq _ _))) (hp_seq _ _)

/-- A constant pre-real's `≤` is the rational `≤` of its value (Archimedes through `qexpr_bound`). -/
theorem const_le {a b : RExpr} {qa qb : QExpr} (ha : ∀ m, qEq (a.seq m) qa) (hb : ∀ m, qEq (b.seq m) qb)
    (h : rle a b) : qle qa qb := by
  cases qle.decidable qa qb with
  | isTrue hq => exact hq
  | isFalse hq =>
      exfalso
      have h' : qle qb qa := (qle_total qa qb).resolve_left hq
      have hpos : qlt qzero (qsub qa qb) := qlt_iff_le_not_le.mpr
        ⟨by unfold qsub; rat_linarith, fun h0 => hq (by unfold qsub at h0; rat_linarith)⟩
      obtain ⟨B, hB⟩ := qexpr_bound (qinv' (qsub qa qb))
      have hnz : ¬ qEq (qsub qa qb) qzero := fun h0 => qlt_irrefl _ (qlt_respects (qEq_refl _) h0 hpos)
      have hc := qmul_inv'_cancel hnz
      obtain ⟨N, hN⟩ := h (B + 1)
      have s := hN N (Nat.le_refl N)
      have s' := qle_respects (by unfold qsub; exact qadd_respects (ha N) (qneg_respects (hb N))) (qEq_refl _) s
      obtain ⟨b1, b2⟩ := hB
      have i0 := qinv'_nonneg_of_pos hpos
      have m1 := qmul_le_mul_of_nonneg (a := qsub qa qb) (b := qeps (B + 1)) (c := qinv' (qsub qa qb)) s' i0
      have hs : qEq (qsub (qinv' (qsub qa qb)) qzero) (qinv' (qsub qa qb)) := by unfold qsub; rat_ring
      have m2 := qmul_le_mul_of_nonneg (a := qinv' (qsub qa qb)) (b := qofInt (pow2 B)) (c := qeps (B + 1))
        (by rat_linarith) (qeps_nonneg _)
      have p := qpow2_mul_eps B 1
      rw [show 1 + B = B + 1 from Nat.add_comm 1 B] at p
      have e1 := qeps_succ_add 0
      have e0 := qeps_zero
      have z := qeps_pos 1
      exact (qlt_iff_le_not_le.mp z).2 (by rat_linarith)

/-! ## The rational partial sums -/

def pwq (x : QExpr) : Nat → QExpr
  | 0 => qone
  | n + 1 => qmul x (pwq x n)

def Wq (x : QExpr) : Nat → QExpr
  | 0 => qzero
  | n + 1 => qmul (qnat (n + 1)) (qadd (Wq x n) (pwq x n))

theorem pwq_respects {x y : QExpr} (h : qEq x y) : ∀ n, qEq (pwq x n) (pwq y n)
  | 0 => qEq_refl _
  | n + 1 => qmul_respects h (pwq_respects h n)

theorem Wq_respects {x y : QExpr} (h : qEq x y) : ∀ n, qEq (Wq x n) (Wq y n)
  | 0 => qEq_refl _
  | n + 1 => qmul_respects (qEq_refl _) (qadd_respects (Wq_respects h n) (pwq_respects h n))

theorem pw_seq (a : RExpr) : ∀ n m, qEq ((ZExpLaw.pw rCF a n).seq m) (pwq (a.seq m) n)
  | 0, _ => qEq_refl _
  | n + 1, m => qmul_respects (qEq_refl _) (pw_seq a n m)

theorem W_seq (a : RExpr) : ∀ n m, qEq ((ZExpLaw.W rCF a n).seq m) (Wq (a.seq m) n)
  | 0, _ => qEq_refl _
  | n + 1, m => qmul_respects (num_seq (n + 1) m) (qadd_respects (W_seq a n m) (pw_seq a n m))

/-- `n! · tₙ(x) = xⁿ`. -/
theorem tm_fact (x : QExpr) : ∀ n, qEq (qmul (qnat (fact n)) (tm x n)) (pwq x n)
  | 0 => by change qEq (qmul (qnat 1) qone) qone; exact qEq_trans (qmul_one _) (qEq_refl _)
  | n + 1 => by
      have ih := tm_fact x n
      have ts := tm_succ x n
      have fm := qnat_mul (n + 1) (fact n)
      change qEq (qmul (qnat ((n + 1) * fact n)) (tm x (n + 1))) (qmul x (pwq x n))
      have e1 : qEq (qmul (qnat ((n + 1) * fact n)) (tm x (n + 1)))
          (qmul (qnat (fact n)) (qmul (qnat (n + 1)) (tm x (n + 1)))) :=
        qEq_trans (qmul_respects fm (qEq_refl _)) (by rat_ring)
      refine qEq_trans e1 (qEq_trans (qmul_respects (qEq_refl _) ts) ?_)
      have e2 : qEq (qmul (qnat (fact n)) (qmul (tm x n) x)) (qmul x (qmul (qnat (fact n)) (tm x n))) := by rat_ring
      exact qEq_trans e2 (qmul_respects (qEq_refl _) ih)

/-- `W n x = n! · S(x, n)`. -/
theorem Wq_S (x : QExpr) : ∀ n, qEq (Wq x n) (qmul (qnat (fact n)) (S x n))
  | 0 => by change qEq qzero (qmul (qnat 1) qzero); exact qEq_symm (qmul_zero _)
  | n + 1 => by
      have ih := Wq_S x n
      have tf := tm_fact x n
      have fm := qnat_mul (n + 1) (fact n)
      change qEq (qmul (qnat (n + 1)) (qadd (Wq x n) (pwq x n))) (qmul (qnat ((n + 1) * fact n)) (qadd (S x n) (tm x n)))
      refine qEq_trans (qmul_respects (qEq_refl _) (qadd_respects ih (qEq_symm tf))) ?_
      refine qEq_trans ?_ (qmul_respects (qEq_symm fm) (qEq_refl _))
      rat_ring

/-! ## `eseq` and equality, and `eˣ · e^(−x) = 1` -/

theorem eseq_respects {x y : QExpr} (h : qEq x y) (m : Nat) : qEq (eseq x m) (eseq y m) := by
  cases qle.decidable qzero x with
  | isTrue hx =>
      have hy := qle_respects (qEq_refl _) h hx
      rw [eseq_pos hx, eseq_pos hy]; exact S_respects h m
  | isFalse hx =>
      have hy : ¬ qle qzero y := fun hy => hx (qle_respects (qEq_refl _) (qEq_symm h) hy)
      rw [eseq_neg hx, eseq_neg hy]; exact qinv'_respects (S_respects (qneg_respects h) m)

theorem eseq_recip (x : QExpr) (m : Nat) (hm : 1 ≤ m) : qEq (qmul (eseq x m) (eseq (qneg x) m)) qone := by
  obtain ⟨j, rfl⟩ := le_ex hm
  cases qle.decidable qzero x with
  | isTrue hx =>
      rw [eseq_pos hx]
      cases qle.decidable qzero (qneg x) with
      | isTrue hnx =>
          rw [eseq_pos hnx]
          have z : qEq x qzero := qle_antisymm (by rat_linarith) hx
          have z' : qEq (qneg x) qzero := qEq_trans (qneg_respects z) (by rat_ring)
          have s1 := qEq_trans (S_respects z (1 + j)) (by rw [Nat.add_comm]; exact S_zero j)
          have s2 := qEq_trans (S_respects z' (1 + j)) (by rw [Nat.add_comm]; exact S_zero j)
          exact qEq_trans (qmul_respects s1 s2) (qmul_one _)
      | isFalse hnx =>
          rw [eseq_neg hnx]
          have nn : qEq (qneg (qneg x)) x := by rat_ring
          have s1 := S_ge_one' hx (Nat.le_add_right 1 j)
          have hnz : ¬ qEq (S x (1 + j)) qzero := fun h0 =>
            (qlt_iff_le_not_le.mp qone_pos).2 (qle_respects (qEq_refl _) h0 s1)
          exact qEq_trans (qmul_respects (qEq_refl _) (qinv'_respects (S_respects nn _))) (qmul_inv'_cancel hnz)
  | isFalse hx =>
      rw [eseq_neg hx]
      have hnx := neg_nonneg_of_not hx
      rw [eseq_pos hnx]
      have s1 := S_ge_one' hnx (Nat.le_add_right 1 j)
      have hnz : ¬ qEq (S (qneg x) (1 + j)) qzero := fun h0 =>
        (qlt_iff_le_not_le.mp qone_pos).2 (qle_respects (qEq_refl _) h0 s1)
      exact qEq_trans (qmul_comm _ _) (qmul_inv'_cancel hnz)

/-! ## The laws at dyadic points -/

theorem law_lo (n : Nat) (d : D) (h0 : rle rzero (dv rOH d)) :
    rle (ZExpLaw.W rCF (dv rOH d) n) (rmul (CR.numeral RExpr.cr (fact n)) (rexpR (dv rOH d))) := by
  have ha := dv_seq d
  have q0 : qle qzero (qD d) := const_le (fun _ => qEq_refl qzero) ha h0
  refine rle_of_eventually n (fun m hm => ?_)
  obtain ⟨j, rfl⟩ := le_ex hm
  have w := qEq_trans (W_seq (dv rOH d) n (n + j)) (qEq_trans (Wq_respects (ha (n + j)) n) (Wq_S (qD d) n))
  have r : qEq (qmul ((CR.numeral RExpr.cr (fact n)).seq (n + j)) (eseq ((dv rOH d).seq (n + j)) (n + j)))
      (qmul (qnat (fact n)) (S (qD d) (n + j))) := by
    refine qmul_respects (num_seq _ _) ?_
    rw [← eseq_pos q0]; exact eseq_respects (ha _) _
  have sm := S_mono q0 n j
  have f0 := qnat_nonneg (fact n)
  have mm := qmul_le_mul_of_nonneg (c := qnat (fact n)) sm f0
  change qle ((ZExpLaw.W rCF (dv rOH d) n).seq (n + j))
    (qmul ((CR.numeral RExpr.cr (fact n)).seq (n + j)) (eseq ((dv rOH d).seq (n + j)) (n + j)))
  have c1 : qEq (qmul (S (qD d) n) (qnat (fact n))) (qmul (qnat (fact n)) (S (qD d) n)) := by rat_ring
  have c2 : qEq (qmul (S (qD d) (n + j)) (qnat (fact n))) (qmul (qnat (fact n)) (S (qD d) (n + j))) := by rat_ring
  rat_linarith

theorem law_hi (n : Nat) (d : D) (h0 : rle rzero (dv rOH d))
    (h2 : rle (radd (dv rOH d) (dv rOH d)) (CR.numeral RExpr.cr (n + 1))) :
    rle (rmul (CR.numeral RExpr.cr (fact n)) (rexpR (dv rOH d)))
      (radd (ZExpLaw.W rCF (dv rOH d) n) (rmul (CR.numeral RExpr.cr 2) (ZExpLaw.pw rCF (dv rOH d) n))) := by
  have ha := dv_seq d
  have q0 : qle qzero (qD d) := const_le (fun _ => qEq_refl qzero) ha h0
  have hg : Good (qD d) n := const_le (fun m => qadd_respects (ha m) (ha m)) (fun m => num_seq (n + 1) m) h2
  refine rle_of_eventually n (fun m hm => ?_)
  obtain ⟨b1, b2⟩ := S_between q0 hg m hm
  have w := qEq_trans (W_seq (dv rOH d) n m) (qEq_trans (Wq_respects (ha m) n) (Wq_S (qD d) n))
  have pwe := qEq_trans (pw_seq (dv rOH d) n m) (pwq_respects (ha m) n)
  have tf := tm_fact (qD d) n
  have two := num_seq 2 m
  have q2 : qEq (qnat 2) (qadd qone qone) := qEq_trans (qnat_succ 1) (qadd_respects (qnat_succ 0) (qEq_refl _) |> fun h => qEq_trans h (qadd_respects (qzero_add qone) (qEq_refl _)))
  have r : qEq (qmul ((CR.numeral RExpr.cr (fact n)).seq m) (eseq ((dv rOH d).seq m) m))
      (qmul (qnat (fact n)) (S (qD d) m)) := by
    refine qmul_respects (num_seq _ _) ?_
    rw [← eseq_pos q0]; exact eseq_respects (ha _) _
  have f0 := qnat_nonneg (fact n)
  have mm := qmul_le_mul_of_nonneg (c := qnat (fact n)) b2 f0
  change qle (qmul ((CR.numeral RExpr.cr (fact n)).seq m) (eseq ((dv rOH d).seq m) m))
    (qadd ((ZExpLaw.W rCF (dv rOH d) n).seq m) (qmul ((CR.numeral RExpr.cr 2).seq m) ((ZExpLaw.pw rCF (dv rOH d) n).seq m)))
  have c1 : qEq (qmul (S (qD d) m) (qnat (fact n))) (qmul (qnat (fact n)) (S (qD d) m)) := by rat_ring
  have c2 : qEq (qmul (qadd (S (qD d) n) (qadd (tm (qD d) n) (tm (qD d) n))) (qnat (fact n)))
      (qadd (qmul (qnat (fact n)) (S (qD d) n)) (qadd (qmul (qnat (fact n)) (tm (qD d) n)) (qmul (qnat (fact n)) (tm (qD d) n)))) := by rat_ring
  have c3 : qEq (qmul ((CR.numeral RExpr.cr 2).seq m) ((ZExpLaw.pw rCF (dv rOH d) n).seq m))
      (qmul (qadd qone qone) (pwq (qD d) n)) := qmul_respects (qEq_trans two q2) pwe
  have c4 : qEq (qmul (qadd qone qone) (pwq (qD d) n)) (qadd (pwq (qD d) n) (pwq (qD d) n)) := by rat_ring
  rat_linarith

theorem law_recip (d : D) : rEq (rmul (rexpR (dv rOH d)) (rexpR (rneg (dv rOH d)))) rone := by
  intro k
  refine ⟨1, fun m hm => ?_⟩
  have e := eseq_recip ((dv rOH d).seq m) m hm
  change qclose (qmul (eseq ((dv rOH d).seq m) m) (eseq (qneg ((dv rOH d).seq m)) m)) qone (qeps k)
  exact qclose_respects (qEq_symm e) (qEq_refl _) (qEq_refl _) (qclose_refl _ _ (qeps_nonneg k))

/-! ## The general laws -/

/-- A common bound `R` for two pre-reals past some index, with `1` to spare. -/
theorem bound2 (a b : RExpr) : ∃ R N, qle qzero R ∧ ∀ n, N ≤ n →
    qclose (a.seq n) qzero R ∧ qclose (b.seq n) qzero R ∧ ∀ e, qle qzero e → qle e qone → qclose (qadd (b.seq n) e) qzero R := by
  obtain ⟨A, Na, hA⟩ := rbounded a
  obtain ⟨B, Nb, hB⟩ := rbounded b
  have e1 : qEq (qofInt oneI) qone := qEq_refl _
  have pa : qle qzero (qofInt (pow2 A)) := by
    have := qofInt_le (one_le_pow2 A); have := qle_of_qlt qone_pos; rat_linarith
  have pb : qle qzero (qofInt (pow2 B)) := by
    have := qofInt_le (one_le_pow2 B); have := qle_of_qlt qone_pos; rat_linarith
  have p1 := qle_of_qlt qone_pos
  refine ⟨qadd (qadd (qofInt (pow2 A)) (qofInt (pow2 B))) qone, Na + Nb, by rat_linarith, fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := hA n (Nat.le_trans (Nat.le_add_right _ _) hn)
  obtain ⟨b1, b2⟩ := hB n (Nat.le_trans (Nat.le_add_left _ _) hn)
  unfold qsub at a1 a2 b1 b2
  refine ⟨⟨by unfold qsub; rat_linarith, by unfold qsub; rat_linarith⟩, ⟨by unfold qsub; rat_linarith, by unfold qsub; rat_linarith⟩,
    fun e e0 e1 => ⟨by unfold qsub; rat_linarith, by unfold qsub; rat_linarith⟩⟩

theorem r_mono {a b : RExpr} (h : rle a b) : rle (rexpR a) (rexpR b) := by
  obtain ⟨R, NR, R0, hR⟩ := bound2 a b
  obtain ⟨H, hH⟩ := S_bounded R0
  obtain ⟨C, hC⟩ := qexpr_bound H
  intro k
  obtain ⟨N1, h1⟩ := h (k + C)
  refine ⟨NR + N1 + 1, fun m hm => ?_⟩
  cases m with
  | zero => exact absurd hm (Nat.not_succ_le_zero _)
  | succ m' =>
  have mR : NR ≤ m' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_add_right NR N1) (Nat.le_add_right _ 1)) hm
  have m1 : N1 ≤ m' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_add_left N1 NR) (Nat.le_add_right _ 1)) hm
  obtain ⟨aR, bR, bR'⟩ := hR (m' + 1) mR
  have hab := h1 (m' + 1) m1
  have ep := qeps_nonneg (k + C)
  have e1 : qle (qeps (k + C)) qone := by
    have := qeps_le_add 0 (k + C); rw [Nat.zero_add] at this; exact qle_trans this (qle_of_qEq qeps_zero)
  have bR2 := bR' (qeps (k + C)) ep e1
  unfold qsub at hab
  have lab : qle (a.seq (m' + 1)) (qadd (b.seq (m' + 1)) (qeps (k + C))) := by rat_linarith
  have mo := E_mono lab m'
  have cl : qclose (qadd (b.seq (m' + 1)) (qeps (k + C))) (b.seq (m' + 1)) (qeps (k + C)) := by
    constructor <;> (unfold qsub; rat_linarith)
  obtain ⟨l1, _⟩ := E_lip bR2 bR cl m'
  have hHm := hH (m' + 1)
  obtain ⟨hC1, _⟩ := hC
  unfold qsub at hC1
  have hHC : qle H (qofInt (pow2 C)) := by rat_linarith
  have s1 := scale_l (qle_trans hHm hHC) ep
  have e2 := qpow2_mul_eps C k
  have e3 : qEq (qmul (qeps (k + C)) (qofInt (pow2 C))) (qmul (qofInt (pow2 C)) (qeps (k + C))) := qmul_comm _ _
  change qle (qsub (eseq (a.seq (m' + 1)) (m' + 1)) (eseq (b.seq (m' + 1)) (m' + 1))) (qeps k)
  unfold qsub at l1 ⊢
  rat_linarith

/-- A uniform floor: within `R` of zero, `E_{n+1}(x) ≥ ε_C` when `S_{n+1}(R) ≤ 2^C`. -/
theorem E_floor {x R : QExpr} {C n : Nat} (hx : qclose x qzero R) (hS : qle (S R (n + 1)) (qofInt (pow2 C))) :
    qle (qeps C) (eseq x (n + 1)) := by
  obtain ⟨x1, x2⟩ := hx
  unfold qsub at x1 x2
  have hR : qle qzero R := by rat_linarith
  have mo := E_mono (by rat_linarith : qle (qneg R) x) n
  have q1 : qle (qeps C) qone := by
    have := qeps_le_add 0 C; rw [Nat.zero_add] at this; exact qle_trans this (qle_of_qEq qeps_zero)
  refine qle_trans ?_ mo
  cases qle.decidable qzero (qneg R) with
  | isTrue h =>
      rw [eseq_pos h]; exact qle_trans q1 (S_ge_one h n)
  | isFalse h =>
      rw [eseq_neg h]
      have e0 : qEq (qneg (qneg R)) R := by rat_ring
      have se : qEq (S (qneg (qneg R)) (n + 1)) (S R (n + 1)) := by
        exact S_respects e0 (n + 1)
      have g1 : qle qone (S (qneg (qneg R)) (n + 1)) := S_ge_one (neg_nonneg_of_not h) n
      obtain ⟨i0, _, ic⟩ := inv_facts g1
      have hX : qle (S (qneg (qneg R)) (n + 1)) (qofInt (pow2 C)) := qle_trans (qle_of_qEq se) hS
      have f1 := scale hX i0
      have f2 : qle qone (qmul (qofInt (pow2 C)) (qinv' (S (qneg (qneg R)) (n + 1)))) := by rat_linarith
      have f3 := scale_l f2 (qeps_nonneg C)
      have p2 : qEq (qmul (qofInt (pow2 C)) (qeps C)) qone := by
        have := qpow2_mul_eps C 0; rw [Nat.zero_add] at this; exact qEq_trans this qeps_zero
      have p3 : qEq (qmul (qeps C) (qmul (qofInt (pow2 C)) (qinv' (S (qneg (qneg R)) (n + 1)))))
          (qmul (qmul (qofInt (pow2 C)) (qeps C)) (qinv' (S (qneg (qneg R)) (n + 1)))) := by rat_ring
      have p4 := qmul_respects p2 (qEq_refl (qinv' (S (qneg (qneg R)) (n + 1))))
      have p5 := qone_mul (qinv' (S (qneg (qneg R)) (n + 1)))
      have p6 : qEq (qmul (qeps C) qone) (qeps C) := by rat_ring
      rat_linarith
  
theorem r_congr {a b : RExpr} (h : rEq a b) : rEq (rexpR a) (rexpR b) :=
  rle_antisymm (r_mono (rle_of_rEq h)) (r_mono (rle_of_rEq (rEq_symm h)))

theorem r_pos (a : RExpr) : rlt rzero (rexpR a) := by
  obtain ⟨B, N, hb⟩ := rbounded a
  have hR : qle qzero (qofInt (pow2 B)) := qofInt_le (pow2_nonneg B)
  obtain ⟨H, hH⟩ := S_bounded hR
  obtain ⟨C, hC, _⟩ := qexpr_bound H
  unfold qsub at hC
  refine ⟨C, N + 1, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n' =>
  have f := E_floor (hb (n' + 1) (Nat.le_trans (Nat.le_add_right N 1) hn))
    (qle_trans (hH (n' + 1)) (by rat_linarith : qle H (qofInt (pow2 C))))
  change qle (qeps C) (qsub (eseq (a.seq (n' + 1)) (n' + 1)) qzero)
  unfold qsub; rat_linarith

theorem r_strict {a b : RExpr} (h : rlt rzero (radd b (rneg a))) :
    rlt rzero (radd (rexpR b) (rneg (rexpR a))) := by
  obtain ⟨k, N0, hk⟩ := h
  obtain ⟨R, NR, R0, hR⟩ := bound2 a b
  obtain ⟨H, hH⟩ := S_bounded R0
  obtain ⟨C, hC, _⟩ := qexpr_bound H
  unfold qsub at hC
  have hHC : qle H (qofInt (pow2 C)) := by rat_linarith
  obtain ⟨K, hg⟩ := good_exists R
  obtain ⟨Nt, _, ht⟩ := tm_small R0 hg (C + 1)
  refine ⟨k + (C + 1), N0 + NR + Nt + 1, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n' =>
  have n0 : N0 ≤ n' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N0 NR) (Nat.le_add_right _ Nt)) (Nat.le_add_right _ 1)) hn
  have nR : NR ≤ n' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left NR N0) (Nat.le_add_right _ Nt)) (Nat.le_add_right _ 1)) hn
  have nt : Nt ≤ n' := Nat.le_of_succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left Nt (N0 + NR))) hn)
  obtain ⟨aR, bR, _⟩ := hR (n' + 1) nR
  have d := hk (n' + 1) n0
  change qle (qeps k) (qsub (qadd (b.seq (n' + 1)) (qneg (a.seq (n' + 1)))) qzero) at d
  unfold qsub at d
  have hab : qle (a.seq (n' + 1)) (b.seq (n' + 1)) := by
    have := qeps_nonneg k; rat_linarith
  obtain ⟨sl, _⟩ := E_slope hab aR bR n'
  have fl := E_floor aR (qle_trans (hH (n' + 1)) hHC)
  have tt := ht n' nt
  have t0 := tm_nonneg R0 n'
  have e1 := qeps_succ_add C
  have g1 : qle (qeps (C + 1)) (qsub (eseq (a.seq (n' + 1)) (n' + 1)) (tm R n')) := by
    unfold qsub; rat_linarith
  have g2 : qle (qeps k) (qsub (b.seq (n' + 1)) (a.seq (n' + 1))) := by unfold qsub; rat_linarith
  have m1 := scale g2 (qle_trans (qeps_nonneg (C + 1)) g1)
  have m2 := scale_l g1 (qeps_nonneg k)
  have em := ZRealCF.qeps_mul k (C + 1)
  change qle (qeps (k + (C + 1)))
    (qsub (qadd (eseq (b.seq (n' + 1)) (n' + 1)) (qneg (eseq (a.seq (n' + 1)) (n' + 1)))) qzero)
  unfold qsub at sl m1 m2 ⊢
  rat_linarith

/-- **VR's operational exponential is lawful.** -/
theorem rExpLaws : ExpLaws rCF rexpR where
  congr := fun h => r_congr h
  mono := fun h => r_mono h
  pos := r_pos
  strict := fun h => r_strict h
  recip := law_recip
  lo := law_lo
  hi := law_hi

/-- **`check_none` ON VR'S CONTINUUM, with `exp` and `ln`.** The exponential is VR's own `rexpR`; the reading's
`exp`/`ln` nodes take its laws from `rExpLaws`, so their values exist and are VR's. Zero axioms. -/
theorem vr_no_solution_exp {atn sn cs : RExpr → RExpr} (c : ZNone.Cert) (Sy : ZNone.Sys) (B : ZIv.Box) (h : ZNone.chk Sy B c = true)
    (p : Nat → RExpr) (hp : ZIv.InBox rCF B p)
    (hE : ∀ e ∈ Sy.eqs, ∃ v, ZXE.Val rCF rexpR atn sn cs p e v ∧ rEq v rzero)
    (hN : ∀ n ∈ Sy.neqs, ∃ v, ZXE.Val rCF rexpR atn sn cs p n v ∧ (rlt rzero v ∨ rlt rzero (rneg v))) :
    False :=
  vr_no_solution rexpR atn sn cs c Sy B h p hp hE hN

/-- Nonvacuity of the `exp` node: for any point, `exp x₀` HAS a value on VR's continuum — `rexpR (p 0)`. -/
example (atn sn cs : RExpr → RExpr) (p : Nat → RExpr) : ZXE.Val rCF rexpR atn sn cs p (.exp (.var 0)) (rexpR (p 0)) :=
  .exp rExpLaws (.var (rEq_refl _)) (rEq_refl _)

#print axioms rExpLaws
#print axioms vr_no_solution_exp
/-! ## The logarithm of a positive VR real -/

/-- A positive pre-real is eventually in `[ε_k, 2^B]`. -/
theorem pos_range {y : RExpr} (hy : rlt rzero y) :
    ∃ k B N, ∀ n, N ≤ n → qle (qeps k) (y.seq n) ∧ qle (y.seq n) (qofInt (pow2 B)) := by
  obtain ⟨k, N, hk⟩ := hy
  obtain ⟨B, Nb, hb⟩ := rbounded y
  refine ⟨k, B, N + Nb, fun n hn => ⟨?_, ?_⟩⟩
  · have := hk n (Nat.le_trans (Nat.le_add_right N Nb) hn)
    change qle (qeps k) (qsub (y.seq n) qzero) at this
    unfold qsub at this; rat_linarith
  · obtain ⟨h1, _⟩ := hb n (Nat.le_trans (Nat.le_add_left Nb N) hn)
    unfold qsub at h1; rat_linarith

/-- `ln y`, `y > 0`, on VR's continuum: the grid answers of `ZLn.lnseq`, Cauchy by `ZLn.ln_cauchy`. -/
def rln (y : RExpr) (hy : rlt rzero y) : RExpr :=
  ⟨fun n => lnseq (y.seq n) n, by
    obtain ⟨k, B, N, hr⟩ := pos_range hy
    exact ln_cauchy (lu := qeps k) (hu := qofInt (pow2 B)) y.cauchy
      (ZSlopeExp.Ev_of_exact N hr) (qeps_pos k)⟩

/-- **`exp (ln y) = y`** on VR's continuum: the grid brackets `y` between `E(x)` and `E(x + ε_n)`, and `E` is
Lipschitz on the range of the answers. -/
theorem rexp_rln (y : RExpr) (hy : rlt rzero y) : rEq (rexpR (rln y hy)) y := by
  obtain ⟨k, B, N, hr⟩ := pos_range hy
  have hlo := qeps_pos k
  obtain ⟨N0, hb⟩ := ln_bracket_unif (yhi := qofInt (pow2 B)) hlo
  have i0 := qinv'_nonneg_of_pos hlo
  have hB0 : qle qzero (qofInt (pow2 B)) := qofInt_le (pow2_nonneg B)
  have p1 := qle_of_qlt qone_pos
  obtain ⟨R, hRe⟩ : ∃ R, qEq R (qadd (qadd (qadd (qinv' (qeps k)) qone) (qofInt (pow2 B))) qone) :=
    ⟨_, qEq_refl _⟩
  have R0 : qle qzero R := by rat_linarith
  obtain ⟨H, hH⟩ := S_bounded R0
  obtain ⟨C, hC, _⟩ := qexpr_bound H
  unfold qsub at hC
  have hHC : qle H (qofInt (pow2 C)) := by rat_linarith
  intro j
  refine ⟨N + N0 + (j + C) + 2, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n1 =>
  cases n1 with
  | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
  | succ n' =>
  have h0 : N + N0 + (j + C) ≤ n' := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hn)
  have hN : N ≤ n' + 2 := Nat.le_trans (Nat.le_trans (Nat.le_add_right N N0) (Nat.le_add_right _ (j + C)))
    (Nat.le_trans h0 (Nat.le_add_right n' 2))
  have hN0 : N0 ≤ n' := Nat.le_trans (Nat.le_trans (Nat.le_add_left N0 N) (Nat.le_add_right _ (j + C))) h0
  have hjC : j + C ≤ n' + 2 := Nat.le_trans (Nat.le_trans (Nat.le_add_left (j + C) (N + N0)) h0) (Nat.le_add_right n' 2)
  obtain ⟨y1, y2⟩ := hr (n' + 2) hN
  have br := hb (y.seq (n' + 2)) y1 y2 n' hN0
  obtain ⟨g1, g2⟩ := ln_range hlo y1 y2 br
  obtain ⟨b1, b2⟩ := br
  have e1 : qle (qeps (n' + 2)) qone := qle_trans (eps_anti (Nat.zero_le _)) (qle_of_qEq qeps_zero)
  have ep := qeps_nonneg (n' + 2)
  have xR : qclose (lnseq (y.seq (n' + 2)) (n' + 2)) qzero R := by
    constructor <;> (unfold qsub; rat_linarith)
  have xeR : qclose (qadd (lnseq (y.seq (n' + 2)) (n' + 2)) (qeps (n' + 2))) qzero R := by
    constructor <;> (unfold qsub; rat_linarith)
  have cl : qclose (qadd (lnseq (y.seq (n' + 2)) (n' + 2)) (qeps (n' + 2))) (lnseq (y.seq (n' + 2)) (n' + 2))
      (qeps (n' + 2)) := by
    constructor <;> (unfold qsub; rat_linarith)
  obtain ⟨l1, _⟩ := E_lip xeR xR cl (n' + 1)
  have yu : qle (y.seq (n' + 2)) (eseq (qadd (lnseq (y.seq (n' + 2)) (n' + 2)) (qeps (n' + 2))) (n' + 2)) := by
    cases qle_total (eseq (qadd (lnseq (y.seq (n' + 2)) (n' + 2)) (qeps (n' + 2))) (n' + 2)) (y.seq (n' + 2)) with
    | inl h => exact absurd h b2
    | inr h => exact h
  have s1 := scale_l (qle_trans (hH (n' + 2)) hHC) ep
  have hC0 : qle qzero (qofInt (pow2 C)) := qofInt_le (pow2_nonneg C)
  have s2 := scale (eps_anti hjC) hC0
  have c1 : qEq (qmul (qeps (n' + 2)) (qofInt (pow2 C))) (qmul (qofInt (pow2 C)) (qeps (n' + 2))) := qmul_comm _ _
  have c2 : qEq (qmul (qeps (j + C)) (qofInt (pow2 C))) (qmul (qofInt (pow2 C)) (qeps (j + C))) := qmul_comm _ _
  have c3 := qpow2_mul_eps C j
  have ej := qeps_nonneg j
  change qclose (eseq (lnseq (y.seq (n' + 2)) (n' + 2)) (n' + 2)) (y.seq (n' + 2)) (qeps j)
  unfold qsub at l1
  constructor <;> (unfold qsub; rat_linarith)

/-- Nonvacuity of the `ln` node: at a point with `x₀ > 0`, `ln x₀` HAS a value on VR's continuum — `rln`. -/
example (atn sn cs : RExpr → RExpr) (p : Nat → RExpr) (h : rlt rzero (p 0)) : ZXE.Val rCF rexpR atn sn cs p (.ln (.var 0)) (rln (p 0) h) :=
  .ln rExpLaws (.var (rEq_refl _)) h (rexp_rln _ h)

#print axioms rexp_rln
#print axioms law_lo
#print axioms law_hi
#print axioms law_recip

end ZRealExp

#print axioms ZRealExp.const_le
#print axioms ZRealExp.dv_seq
