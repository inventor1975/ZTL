import ZRoot
import ZRealExp
/-!
# ZRootVR — VR's operational continuum is complete in `ZRoot`'s sense, so a sign change gives a root there.
Zero axioms.

* NESTED DYADIC INTERVALS: the lower ends are a pre-real (`n ↦ lo n`), Cauchy because the width halves — and that
  pre-real lies in every interval.
* ARCHIMEDES: `x > 0` in VR is witnessed by a precision `ε_k` below `x` from some index on (`rlt`), which IS a
  dyadic below `x`.

Then `ZRoot.root_exists` holds on VR's continuum: the first example, `√2` (a root of `x² − 2` in `[1, 2]`), is a
VR real.
-/

namespace ZRootVR
open VR VR.Numbers VR.CSR ZNumBin ZField ZPoly ZIv ZRealCF ZExp ZRealExp ZRoot

theorem ql_mono {q : Nat → QExpr} (h : ∀ k, qle (q k) (q (k + 1))) : ∀ {k n : Nat}, k ≤ n → qle (q k) (q n) := by
  intro k n hkn
  induction hkn with
  | refl => exact qle_refl _
  | step _ ih => exact qle_trans ih (h _)

theorem qh_anti {q : Nat → QExpr} (h : ∀ k, qle (q (k + 1)) (q k)) : ∀ {k n : Nat}, k ≤ n → qle (q n) (q k) := by
  intro k n hkn
  induction hkn with
  | refl => exact qle_refl _
  | step _ ih => exact qle_trans (h _) ih

/-- **VR's continuum is complete** (nested dyadic intervals, Archimedes). -/
theorem vr_complete : Complete rCF where
  nest := by
    intro lo hi W hlo hhi hord hwid
    have L1 : ∀ k, qle (qD (lo k)) (qD (lo (k + 1))) := fun k => const_le (dv_seq _) (dv_seq _) (hlo k)
    have L2 : ∀ k, qle (qD (hi (k + 1))) (qD (hi k)) := fun k => const_le (dv_seq _) (dv_seq _) (hhi k)
    have L3 : ∀ k, qle (qD (lo k)) (qD (hi k)) := fun k => const_le (dv_seq _) (dv_seq _) (hord k)
    have L4 : ∀ k, qle (qadd (qD (hi k)) (qneg (qD (lo k)))) (qmul (qD W) (qeps k)) := fun k =>
      const_le (fun m => qadd_respects (dv_seq _ m) (qneg_respects (dv_seq _ m)))
        (fun m => qmul_respects (dv_seq _ m) (hp_seq k m)) (hwid k)
    obtain ⟨C, hC, _⟩ := qexpr_bound (qD W)
    unfold qsub at hC
    have hWC : qle (qD W) (qofInt (pow2 C)) := by rat_linarith
    have cau : ∀ k, ∃ N, ∀ m n, N ≤ m → N ≤ n → qclose (qD (lo m)) (qD (lo n)) (qeps k) := by
      intro k
      refine ⟨k + C, fun m n hm hn => ?_⟩
      have a1 := ql_mono (q := fun k => qD (lo k)) L1 hm; have a2 := ql_mono (q := fun k => qD (lo k)) L1 hn
      have b1 := qh_anti (q := fun k => qD (hi k)) L2 hm; have b2 := qh_anti (q := fun k => qD (hi k)) L2 hn
      have c1 := L3 m; have c2 := L3 n
      have w := L4 (k + C)
      have s := scale hWC (qeps_nonneg (k + C))
      have e := qpow2_mul_eps C k
      have e' : qEq (qmul (qofInt (pow2 C)) (qeps (k + C))) (qmul (qeps (k + C)) (qofInt (pow2 C))) := qmul_comm _ _
      have e'' : qEq (qmul (qD W) (qeps (k + C))) (qmul (qeps (k + C)) (qD W)) := qmul_comm _ _
      constructor <;> (unfold qsub; rat_linarith)
    let x : RExpr := ⟨fun n => qD (lo n), cau⟩
    refine ⟨x, fun k => ⟨?_, ?_⟩⟩
    · exact rle_of_eventually k (fun n hn => by
        have := ql_mono (q := fun k => qD (lo k)) L1 hn
        have e := dv_seq (lo k) n
        change qle ((dv rOH (lo k)).seq n) (qD (lo n))
        rat_linarith)
    · exact rle_of_eventually k (fun n hn => by
        have a := L3 n
        have b := qh_anti (q := fun k => qD (hi k)) L2 hn
        have e := dv_seq (hi k) n
        change qle (qD (lo n)) ((dv rOH (hi k)).seq n)
        rat_linarith)
  arch := by
    intro y hy
    obtain ⟨k, N, hk⟩ := hy
    refine ⟨k, rle_of_eventually N (fun n hn => ?_)⟩
    have h := hk n hn
    change qle (qeps k) (qsub (y.seq n) qzero) at h
    have e := hp_seq k n
    unfold qsub at h
    change qle ((hp rOH k).seq n) (y.seq n)
    rat_linarith

/-- **A sign change gives a root on VR's continuum.** -/
theorem vr_root (f : PE) (a b : D) (cB cC : Nat) (K : Iv)
    (hab : dle a b = true) (hfa : dle (evalD a f) dz = true) (hfb : dle dz (evalD b f) = true)
    (hW : dle (dadd b (dneg a)) ⟨⟨2 ^ cB, 0⟩, 0⟩ = true)
    (hK : ivE (B2 a b) (dd f) = some K) (hK2 : dle K.2 ⟨⟨2 ^ cC, 0⟩, 0⟩ = true) :
    ∃ x : RExpr, rle (dv rOH a) x ∧ rle x (dv rOH b) ∧ rEq (eval rOH (fun _ => x) f) rzero :=
  root_exists rCF vr_complete f a b cB cC K hab hfa hfb hW hK hK2

/-! ## √2 is a VR real: a root of `x² − 2` in `[1, 2]` (`f(1) = −1`, `f(2) = 2`; the divided difference
`x + y` read on `[1, 2]²` below `2³`). -/
def sq2 : PE := .sub (.pow (.var 0) 2) (.cst ⟨⟨2, 0⟩, 0⟩)
def one : D := ⟨⟨1, 0⟩, 0⟩
def two : D := ⟨⟨2, 0⟩, 0⟩

theorem sqrt2_exists : ∃ x : RExpr, rle (dv rOH one) x ∧ rle x (dv rOH two) ∧
    rEq (eval rOH (fun _ => x) sq2) rzero := by
  obtain ⟨K, hK⟩ : ∃ K, ivE (B2 one two) (dd sq2) = some K := ⟨_, rfl⟩
  exact vr_root sq2 one two 0 3 K (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hK
    (by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel)

/-- The other side of the fork: on `[2, 3]` there is no sign change (`f(2) = 2 > 0`) — the certificate's first
check is refused, so no root is claimed there. -/
example : dle (evalD two sq2) dz = false := by decide +kernel

end ZRootVR

#print axioms ZRootVR.vr_complete
#print axioms ZRootVR.vr_root
#print axioms ZRootVR.sqrt2_exists
