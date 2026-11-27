import ZExpAdd4

/-!
# ZExpAdd5 — STAGE 5: exp(x + y) = exp x · exp y for REAL x, y (VR's `rexpR`). Zero axioms.

Stage 4 holds at pre-rationals, each pair with its own index past which the partial sums agree. On VR's reals the
argument moves with the index, so the law is needed UNIFORMLY on a bounded set (`uniform_law`): for |a|, |b| ≤ R and
every n past one N, |E_n(a)·E_n(b) − E_n(a+b)| ≤ ε. It follows from stage 4 at a LATER index M (chosen per pair —
it only has to exist) and the uniform Cauchy property `ZExp.E_unif`, through
    E_n(a)E_n(b) − E_n(a+b) = (E_n a − E_M a)·E_n b + E_M a·(E_n b − E_M b) + (E_M a·E_M b − E_M(a+b)) + (E_M(a+b) − E_n(a+b)),
each part ≤ ε/4 (the bounds |E| ≤ 2^B from `S_bounded`). Then `rexpR_add`: the arguments of VR's reals are bounded
(`rbounded`), so the uniform law applies at each index.
-/

namespace ZExpAdd5
open VR VR.Numbers ZExp ZExpAdd4

theorem close_add_bound {a b R : QExpr} (ha : qclose a qzero R) (hb : qclose b qzero R) :
    qclose (qadd a b) qzero (qadd R R) := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  constructor <;> (unfold qsub at *; rat_linarith)

theorem close_widen {a R : QExpr} (ha : qclose a qzero R) (hR : qle qzero R) : qclose a qzero (qadd R R) := by
  obtain ⟨a1, a2⟩ := ha
  constructor <;> (unfold qsub at *; rat_linarith)

/-- |E_{m+1}(y)| ≤ 2^B on |y| ≤ R2, H ≤ 2^B the bound of S(R2, ·). -/
theorem E_bound {y R2 H : QExpr} {B : Nat} (hy : qclose y qzero R2) (hH : ∀ n, qle (S R2 n) H)
    (hB : qclose H qzero (qofInt (pow2 B))) (m : Nat) : qclose (eseq y (m + 1)) qzero (qofInt (pow2 B)) := by
  have h0 := E_nonneg y m
  have h1 := qle_trans (E_le_SR hy m) (hH (m + 1))
  obtain ⟨b1, b2⟩ := hB
  have hp : qle qzero (qofInt (pow2 B)) := qofInt_le (VR.Numbers.pow2_nonneg B)
  constructor <;> (unfold qsub at *; rat_linarith)

/-- **THE LAW, UNIFORMLY** on |a|, |b| ≤ R. -/
theorem uniform_law {R : QExpr} (hR : qle qzero R) (k : Nat) :
    ∃ N, ∀ a b, qclose a qzero R → qclose b qzero R → ∀ n, N ≤ n →
      qclose (qmul (eseq a n) (eseq b n)) (eseq (qadd a b) n) (qeps k) := by
  have hR2 : qle qzero (qadd R R) := qle_respects (qadd_zero qzero) (qEq_refl _) (ZExpAdd2.qadd_le_add hR hR)
  obtain ⟨H, hH⟩ := S_bounded hR2
  obtain ⟨B, hB⟩ := qexpr_bound H
  obtain ⟨N1, hU⟩ := E_unif hR2 (k + 2 + B)
  refine ⟨N1 + 1, fun a b ha hb n hn => ?_⟩
  have ha2 := close_widen ha hR
  have hb2 := close_widen hb hR
  have hs2 := close_add_bound ha hb
  -- stage 4 at a later index M
  obtain ⟨N2, h4⟩ := rexp_add a b (k + 2 + B)
  let M := n + N2
  have hnM : n ≤ M := Nat.le_add_right n N2
  have hN1n : N1 ≤ n := Nat.le_trans (Nat.le_add_right N1 1) hn
  have hN1M : N1 ≤ M := Nat.le_trans hN1n hnM
  have d1 := hU a ha2 n M hN1n hN1M
  have d2 := hU b hb2 n M hN1n hN1M
  have d4 := hU (qadd a b) hs2 M n hN1M hN1n
  have d3 : qclose (qmul (eseq a M) (eseq b M)) (eseq (qadd a b) M) (qeps (k + 2 + B)) :=
    h4 M (Nat.le_add_left N2 n)
  -- bounds: n = n' + 1, M = M' + 1
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n => rfl⟩
  have bnb := E_bound hb2 hH hB n'
  have bMa : qclose (eseq a M) qzero (qofInt (pow2 B)) := by
    have e : M = (n' + N2) + 1 := by show n' + 1 + N2 = n' + N2 + 1; rw [Nat.add_right_comm]
    rw [e]; exact E_bound ha2 hH hB (n' + N2)
  -- the two products
  have p1 := qmul_abs_bound (show qclose (qsub (eseq a (n' + 1)) (eseq a M)) qzero (qeps (k + 2 + B)) from by
      obtain ⟨u1, u2⟩ := d1
      have hz : qEq (qsub (qsub (eseq a (n' + 1)) (eseq a M)) qzero) (qsub (eseq a (n' + 1)) (eseq a M)) := by
        unfold qsub; rat_ring
      constructor <;> rat_linarith) bnb
  have p2 := qmul_abs_bound bMa (show qclose (qsub (eseq b (n' + 1)) (eseq b M)) qzero (qeps (k + 2 + B)) from by
      obtain ⟨u1, u2⟩ := d2
      have hz : qEq (qsub (qsub (eseq b (n' + 1)) (eseq b M)) qzero) (qsub (eseq b (n' + 1)) (eseq b M)) := by
        unfold qsub; rat_ring
      constructor <;> rat_linarith)
  have q1 := VR.Numbers.qpow2_mul_eps B (k + 2)
  have e1 := VR.Numbers.qeps_succ_add k
  have e2 := VR.Numbers.qeps_succ_add (k + 1)
  have hle : qle (qeps (k + 2 + B)) (qeps (k + 2)) := VR.Numbers.qeps_le_add (k + 2) B
  have hs : qEq (qsub (qmul (eseq a (n' + 1)) (eseq b (n' + 1))) (eseq (qadd a b) (n' + 1)))
      (qadd (qmul (qsub (eseq a (n' + 1)) (eseq a M)) (eseq b (n' + 1)))
        (qadd (qmul (eseq a M) (qsub (eseq b (n' + 1)) (eseq b M)))
          (qadd (qsub (qmul (eseq a M) (eseq b M)) (eseq (qadd a b) M))
            (qsub (eseq (qadd a b) M) (eseq (qadd a b) (n' + 1)))))) := by
    unfold qsub; rat_ring
  obtain ⟨p11, p12⟩ := p1
  obtain ⟨p21, p22⟩ := p2
  obtain ⟨d31, d32⟩ := d3
  obtain ⟨d41, d42⟩ := d4
  have hc1 : qEq (qmul (qeps (k + 2 + B)) (qofInt (pow2 B))) (qeps (k + 2)) :=
    qEq_trans (qmul_comm _ _) q1
  have hc2 : qEq (qmul (qofInt (pow2 B)) (qeps (k + 2 + B))) (qeps (k + 2)) := q1
  constructor <;> (unfold qsub at *; rat_linarith)

/-- **STAGE 5: exp(x + y) = exp x · exp y on VR's reals.** -/
theorem rexpR_add (x y : RExpr) : rEq (rmul (rexpR x) (rexpR y)) (rexpR (radd x y)) := by
  intro k
  obtain ⟨Bx, Nx, hbx⟩ := rbounded x
  obtain ⟨By, Ny, hby⟩ := rbounded y
  let R := qadd (qofInt (pow2 Bx)) (qofInt (pow2 By))
  have hR : qle qzero R :=
    qle_respects (qadd_zero qzero) (qEq_refl _)
      (ZExpAdd2.qadd_le_add (qofInt_le (VR.Numbers.pow2_nonneg Bx)) (qofInt_le (VR.Numbers.pow2_nonneg By)))
  obtain ⟨N, hN⟩ := uniform_law hR k
  refine ⟨N + Nx + Ny, fun n hn => ?_⟩
  have hnx : Nx ≤ n := Nat.le_trans (Nat.le_add_left Nx N) (Nat.le_trans (Nat.le_add_right _ Ny) hn)
  have hny : Ny ≤ n := Nat.le_trans (Nat.le_add_left Ny (N + Nx)) hn
  have hnN : N ≤ n := Nat.le_trans (Nat.le_add_right N Nx) (Nat.le_trans (Nat.le_add_right _ Ny) hn)
  have ax : qclose (x.seq n) qzero R := by
    obtain ⟨u1, u2⟩ := hbx n hnx
    have p1 : qle qzero (qofInt (pow2 Bx)) := qofInt_le (VR.Numbers.pow2_nonneg Bx)
    have p2 : qle qzero (qofInt (pow2 By)) := qofInt_le (VR.Numbers.pow2_nonneg By)
    show qclose _ qzero (qadd (qofInt (pow2 Bx)) (qofInt (pow2 By)))
    constructor <;> (unfold qsub at *; rat_linarith)
  have ay : qclose (y.seq n) qzero R := by
    obtain ⟨u1, u2⟩ := hby n hny
    have p1 : qle qzero (qofInt (pow2 Bx)) := qofInt_le (VR.Numbers.pow2_nonneg Bx)
    have p2 : qle qzero (qofInt (pow2 By)) := qofInt_le (VR.Numbers.pow2_nonneg By)
    show qclose _ qzero (qadd (qofInt (pow2 Bx)) (qofInt (pow2 By)))
    constructor <;> (unfold qsub at *; rat_linarith)
  exact hN (x.seq n) (y.seq n) ax ay n hnN

end ZExpAdd5

#print axioms ZExpAdd5.close_add_bound
#print axioms ZExpAdd5.close_widen
#print axioms ZExpAdd5.E_bound
#print axioms ZExpAdd5.uniform_law
#print axioms ZExpAdd5.rexpR_add
