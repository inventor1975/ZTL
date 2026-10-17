import ZTaylorPt

/-!
# ZAtanCert — `atan` at a rational point, certified by a Taylor chain from `atan 0 = 0`. Zero axioms.

`VRead.atan` takes the values of `atan` at the ends of its argument's reading as facts about two rational points.
They are certified here: `atan 0 = 0` exactly (`atan_zero`), and one step (`atan_step`) carries a reading of
`atan x0` to one of `atan x1` through `ZTaylorPt.taylor_value` — the kernel's own series of `atan x` (`CRead.atan`)
over the box `[lo, hi] ∋ x0, x1` for the remainder, and over the point box `[x0, x0]` for the coefficients
`t ≥ 1` (rational there; the value coefficient is the chain's previous reading). The series' value coefficient needs
a value reading of `atan` over the box: the crude `|atan y| ≤ |y|` (`crude_read`) is enough — `c_0` enters nowhere
else. The checker in the run (`zfunc._cert_atan`) mirrors the chain and the series in exact arithmetic.
-/

namespace ZAtanCert

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZJet ZJetRead ZJetClose
  ZTaylorPt

theorem atan_zero : Ev (fun n => ZAtan.atseq qzero n) qzero qzero :=
  Ev_of_exact 0 (fun n _ => ⟨qle_of_qEq (qEq_symm (ZAtan.atseq_zero n)), qle_of_qEq (ZAtan.atseq_zero n)⟩)

/-- The crude value reading of `atan x` over `[lo, hi]`, `|lo|, |hi| ≤ Y`. -/
theorem crude_read {lo hi Y : QExpr} (hl : ZTrig.Ab lo Y) (hh : ZTrig.Ab hi Y) :
    VRead (fun _ => (lo, hi)) (.atan (.var 0)) (qneg Y) Y :=
  VRead.atan (VRead.var (qle_refl _) (qle_refl _)) (ZAtan.atan_crude hl).1 (ZAtan.atan_crude hh).2

/-- ONE STEP OF THE CHAIN: a reading of `atan x0` and the kernel's series give one of `atan x1`. -/
theorem atan_step {x0 x1 lo hi L H Rl Rh : QExpr} {m : Nat} {cP cB P T : Nat → QExpr × QExpr}
    (a0 : qle lo x0) (b0 : qle x0 hi) (a1 : qle lo x1) (b1 : qle x1 hi)
    (rB : CRead (fun _ => (lo, hi)) 0 m (.atan (.var 0)) cB)
    (rP : CRead (fun _ => (x0, x0)) 0 m (.atan (.var 0)) cP)
    (h0 : Ev (fun n => ZAtan.atseq x0 n) L H) (hP0 : Hull (P 0) L H)
    (hPt : ∀ t, t < m → 0 < t → Hull (P t) (cP t).1 (cP t).2)
    (hT : ∀ t, t < m → Corners (T t).1 (T t).2 (P t).1 (P t).2 (qpowN (qsub x1 x0) t) (qpowN (qsub x1 x0) t))
    (hR : Corners Rl Rh (cB m).1 (cB m).2 (qpowN (qsub x1 x0) m) (qpowN (qsub x1 x0) m)) :
    Ev (fun n => ZAtan.atseq x1 n) (qadd (ZTrig.bs (fun t => (T t).1) m) Rl) (qadd (ZTrig.bs (fun t => (T t).2) m) Rh) := by
  have hp : InBox qOrd (fun _ => (lo, hi)) (fun _ => x0) := fun _ => ⟨a0, b0⟩
  have hp0 : InBox qOrd (fun _ => (x0, x0)) (fun _ => x0) := fun _ => ⟨qle_refl _, qle_refl _⟩
  have q0 : upd (fun _ => x0) 0 x1 0 = x1 := upd_at _ 0 x1
  have hq : InBox qOrd (fun _ => (lo, hi)) (upd (fun _ => x0) 0 x1) := fun j => by
    show qle lo (upd (fun _ => x0) 0 x1 j) ∧ qle (upd (fun _ => x0) 0 x1 j) hi
    unfold upd
    cases Nat.decEq j 0 with
    | isTrue _ => exact ⟨a1, b1⟩
    | isFalse _ => exact ⟨a0, b0⟩
  have hfix : ∀ j, j ≠ 0 → upd (fun _ => x0) 0 x1 j = x0 := fun j hj => by
    unfold upd
    cases Nat.decEq j 0 with
    | isTrue h => exact absurd h hj
    | isFalse _ => rfl
  have hP : ∀ t, t < m → Ev (fun n => J 0 n (fun _ => x0) (.atan (.var 0)) t) (P t).1 (P t).2 := fun t ht => by
    cases t with
    | zero =>
        refine Ev_hull (Ev_congr_ev 0 (fun n _ => qEq_symm (J_zero 0 n (fun _ => x0) (.atan (.var 0)))) h0) hP0
    | succ t => exact Ev_hull (cread_sound hp0 rP (t + 1) (Nat.le_of_lt ht)) (hPt (t + 1) ht (Nat.succ_pos t))
  have tv := taylor_value rB hp hq hfix (P := P) (T := T) hP (by rw [q0]; exact hT) (by rw [q0]; exact hR)
  refine Ev_congr (fun n => ?_) tv
  show qEq (ZAtan.atseq (upd (fun _ => x0) 0 x1 0) n) (ZAtan.atseq x1 n)
  rw [q0]; exact qEq_refl _

end ZAtanCert

#print axioms ZAtanCert.atan_zero
#print axioms ZAtanCert.crude_read
#print axioms ZAtanCert.atan_step
