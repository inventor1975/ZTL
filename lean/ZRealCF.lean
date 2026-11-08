import ZNone
import VR.Numbers.RealsOp
/-!
# VR's operational reals are a constructive ordered field `ZField.CF` — so `check_none` holds on VR's continuum.

Module 5b of the Lean-checked `check_none` (curator, 2026-11-07: "Б" — "на континууме как в VR"). VR's pre-reals
`RExpr` (sequences of pre-rationals with a Cauchy modulus, read from VRCycle, not copied) with `rle`, `rlt`
(`VR.Numbers.RealsOp`) satisfy every law of `CF`. Each law is proved at ONE well-chosen index of the sequences,
where the comparison of two pre-rationals is decidable (`qle_total`), and carried to the tail by the modulus —
no excluded middle on reals. Zero axioms.

Part 1: VR's ordered ring with a half (`ZNumBin.OH`).
-/

namespace ZRealCF
open VR VR.Numbers VR.CSR

/-- The tail of a Cauchy sequence stays within `ε_k` of its term at the index the modulus gives. -/
theorem tail (x : RExpr) (k : Nat) : ∃ N, ∀ n, N ≤ n → qclose (x.seq n) (x.seq N) (qeps k) := by
  obtain ⟨N, hN⟩ := x.cauchy k
  exact ⟨N, fun n hn => hN n N hn (Nat.le_refl N)⟩

theorem numeral_seq_nonneg : ∀ (c m : Nat), qle qzero ((CR.numeral RExpr.cr c).seq m)
  | 0, m => qle_refl _
  | c + 1, m => by
      have ih := numeral_seq_nonneg c m
      have h1 : qle qzero qone := qle_of_qlt (qeps_pos 0)
      change qle qzero (qadd qone ((CR.numeral RExpr.cr c).seq m))
      rat_linarith

theorem numeral_seq_ge_one (c m : Nat) : qle qone ((CR.numeral RExpr.cr (c + 1)).seq m) := by
  have ih := numeral_seq_nonneg c m
  change qle qone (qadd qone ((CR.numeral RExpr.cr c).seq m))
  rat_linarith

/-- VR's pre-reals as an ordered ring (VR's `OCR`; `lt` is that structure's `a + 1 ≤ b`, unused here). -/
def rOCR : OCR RExpr := { RExpr.cr with
  le := rle
  lt := fun a b => rle (radd a rone) b
  lt_def := fun _ _ => Iff.rfl
  le_respects := fun h1 h2 h => rle_respects h1 h2 h
  le_refl := rle_refl
  le_trans := fun h1 h2 => rle_trans h1 h2
  le_add_right := fun {a b} c h k => by
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun n hn => ?_⟩
    have h0 := hN n hn
    have hs : qEq (qsub (qadd (a.seq n) (c.seq n)) (qadd (b.seq n) (c.seq n))) (qsub (a.seq n) (b.seq n)) := by
      unfold qsub; rat_ring
    change qle (qsub (qadd (a.seq n) (c.seq n)) (qadd (b.seq n) (c.seq n))) (qeps k)
    rat_linarith
  zero_le_one := fun k => ⟨0, fun n _ => by
    have h1 := qeps_nonneg k
    have h2 : qle qzero qone := qle_of_qlt (qeps_pos 0)
    have hs : qEq (qsub qzero qone) (qneg qone) := by unfold qsub; rat_ring
    change qle (qsub qzero qone) (qeps k)
    rat_linarith⟩
  one_pos := fun h => by
    obtain ⟨N, hN⟩ := h 1
    have h0 := hN N (Nat.le_refl N)
    change qle (qsub qone qzero) (qeps 1) at h0
    have e1 := qeps_succ_add 0
    have e0 := qeps_zero
    have hs : qEq (qsub qone qzero) qone := by unfold qsub; rat_ring
    exact (qlt_iff_le_not_le.mp (qeps_pos 0)).2 (by rat_linarith)
  le_of_smul := fun c {x} h k => by
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun n hn => ?_⟩
    have h0 := hN n hn
    change qle (qsub qzero (qmul ((CR.numeral RExpr.cr (c + 1)).seq n) (x.seq n))) (qeps k) at h0
    change qle (qsub qzero (x.seq n)) (qeps k)
    have hk := qeps_nonneg k
    have hc := numeral_seq_ge_one c n
    cases qle_total qzero (x.seq n) with
    | inl hx =>
        have hs : qEq (qsub qzero (x.seq n)) (qneg (x.seq n)) := by unfold qsub; rat_ring
        rat_linarith
    | inr hx =>
        have m := qmul_nonneg (a := qsub ((CR.numeral RExpr.cr (c + 1)).seq n) qone) (b := qneg (x.seq n))
          (by unfold qsub; rat_linarith) (by rat_linarith)
        have e : qEq (qmul (qsub ((CR.numeral RExpr.cr (c + 1)).seq n) qone) (qneg (x.seq n)))
            (qadd (qneg (qmul ((CR.numeral RExpr.cr (c + 1)).seq n) (x.seq n))) (x.seq n)) := by
          unfold qsub; rat_ring
        have hs1 : qEq (qsub qzero (qmul ((CR.numeral RExpr.cr (c + 1)).seq n) (x.seq n)))
            (qneg (qmul ((CR.numeral RExpr.cr (c + 1)).seq n) (x.seq n))) := by unfold qsub; rat_ring
        have hs2 : qEq (qsub qzero (x.seq n)) (qneg (x.seq n)) := by unfold qsub; rat_ring
        rat_linarith }

#print axioms rOCR

def rhalf : RExpr := rofQ (qeps 1)

theorem rmul_nonneg {a b : RExpr} (ha : rle rzero a) (hb : rle rzero b) : rle rzero (rmul a b) := by
  obtain ⟨A, Na, hA⟩ := rbounded a
  obtain ⟨Bb, Nb, hB⟩ := rbounded b
  intro k
  obtain ⟨N1, h1⟩ := ha (k + Bb)
  obtain ⟨N2, h2⟩ := hb (k + A)
  refine ⟨Na + Nb + N1 + N2, fun n hn => ?_⟩
  have g1 : Na ≤ n := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hn))
  have g2 : Nb ≤ n := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hn))
  have g3 : N1 ≤ n := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) hn)
  have g4 : N2 ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  obtain ⟨ba1, ba2⟩ := hA n g1
  obtain ⟨bb1, bb2⟩ := hB n g2
  have la := h1 n g3
  have lb := h2 n g4
  change qle (qsub qzero (a.seq n)) (qeps (k + Bb)) at la
  change qle (qsub qzero (b.seq n)) (qeps (k + A)) at lb
  change qle (qsub qzero (qmul (a.seq n) (b.seq n))) (qeps k)
  have hk := qeps_nonneg k
  have hka := qeps_nonneg (k + A)
  have hkb := qeps_nonneg (k + Bb)
  have pa := qpow2_mul_eps A k
  have pb := qpow2_mul_eps Bb k
  have s0 : qEq (qsub qzero (qmul (a.seq n) (b.seq n))) (qneg (qmul (a.seq n) (b.seq n))) := by unfold qsub; rat_ring
  have sa : qEq (qsub qzero (a.seq n)) (qneg (a.seq n)) := by unfold qsub; rat_ring
  have sb : qEq (qsub qzero (b.seq n)) (qneg (b.seq n)) := by unfold qsub; rat_ring
  have sa' : qEq (qsub (a.seq n) qzero) (a.seq n) := by unfold qsub; rat_ring
  have sb' : qEq (qsub (b.seq n) qzero) (b.seq n) := by unfold qsub; rat_ring
  cases qle_total qzero (a.seq n) with
  | inl a0 =>
      cases qle_total qzero (b.seq n) with
      | inl b0 => have m := qmul_nonneg a0 b0; rat_linarith
      | inr b0 =>
          -- a·b ≥ −ε·a ≥ −ε·2^A = −ε_k
          have m1 := qmul_nonneg (a := qadd (b.seq n) (qeps (k + A))) (b := a.seq n) (by rat_linarith) a0
          have m2 := qmul_le_mul_of_nonneg (a := a.seq n) (b := qofInt (pow2 A)) (c := qeps (k + A)) (by rat_linarith) hka
          have e1 : qEq (qmul (qadd (b.seq n) (qeps (k + A))) (a.seq n))
              (qadd (qmul (a.seq n) (b.seq n)) (qmul (a.seq n) (qeps (k + A)))) := by rat_ring
          rat_linarith
  | inr a0 =>
      cases qle_total qzero (b.seq n) with
      | inl b0 =>
          have m1 := qmul_nonneg (a := qadd (a.seq n) (qeps (k + Bb))) (b := b.seq n) (by rat_linarith) b0
          have m2 := qmul_le_mul_of_nonneg (a := b.seq n) (b := qofInt (pow2 Bb)) (c := qeps (k + Bb)) (by rat_linarith) hkb
          have e1 : qEq (qmul (qadd (a.seq n) (qeps (k + Bb))) (b.seq n))
              (qadd (qmul (a.seq n) (b.seq n)) (qmul (b.seq n) (qeps (k + Bb)))) := by rat_ring
          rat_linarith
      | inr b0 =>
          have m := qmul_nonneg (a := qneg (a.seq n)) (b := qneg (b.seq n)) (by rat_linarith) (by rat_linarith)
          have e : qEq (qmul (qneg (a.seq n)) (qneg (b.seq n))) (qmul (a.seq n) (b.seq n)) := by rat_ring
          rat_linarith

/-- VR's pre-reals with a half. -/
def rOH : ZNumBin.OH RExpr := { rOCR with
  half := rhalf
  half_spec := rEq_of_seq (fun _ => qEq_trans (qeps_succ_add 0) qeps_zero)
  mul_nonneg := fun ha hb => rmul_nonneg ha hb }

#print axioms rmul_nonneg
#print axioms rOH

/-! ## Part 2: the laws of `CF` -/

theorem qeps_mul (a b : Nat) : qEq (qmul (qeps a) (qeps b)) (qeps (a + b)) := by
  have h := pow2_add a b
  change imul (imul oneI oneI) (pow2 (a + b)) ≈ᵢ imul oneI (imul (pow2 a) (pow2 b))
  calc imul (imul oneI oneI) (pow2 (a + b)) ≈ᵢ imul oneI (pow2 (a + b)) := by int_ring
    _ ≈ᵢ imul oneI (imul (pow2 a) (pow2 b)) := imul_respects _ _ _ _ (intEq_refl _) h

/-- From the modulus at precision `k`: past an index `M ≥ N`, the tail is within `ε_k` of the term at `M`. -/
theorem close_from (x : RExpr) (k : Nat) : ∃ N, ∀ M, N ≤ M → ∀ n, M ≤ n → qclose (x.seq n) (x.seq M) (qeps k) := by
  obtain ⟨N, hN⟩ := x.cauchy k
  exact ⟨N, fun M hM n hn => hN n M (Nat.le_trans hM hn) hM⟩

/-- `ε_{k+1} ≤ x_M` at an index where the tail is `ε_{k+3}`-close: `x > 0`. -/
theorem pos_at {x : RExpr} {k M : Nat} (hc : ∀ n, M ≤ n → qclose (x.seq n) (x.seq M) (qeps (k + 3)))
    (h : qle (qeps (k + 1)) (x.seq M)) : rlt rzero x := by
  refine ⟨k + 2, M, fun n hn => ?_⟩
  obtain ⟨_, c2⟩ := hc n hn
  have e2 := qeps_succ_add (k + 1)
  have e3 := qeps_succ_add (k + 2)
  have z := qeps_nonneg (k + 3)
  have hs : qEq (qsub (x.seq n) (qsub qzero qzero)) (x.seq n) := by unfold qsub; rat_ring
  have hs2 : qEq (qsub (x.seq n) (x.seq M)) (qadd (x.seq n) (qneg (x.seq M))) := by unfold qsub; rat_ring
  change qle (qeps (k + 2)) (qsub (x.seq n) (qsub qzero qzero))
  rat_linarith

theorem rneg_seq (x : RExpr) (n : Nat) : (rneg x).seq n = qneg (x.seq n) := rfl

/-- Positivity splits over a sum (at one index the larger summand is decided). -/
theorem split_pos {a b : RExpr} (h : rlt rzero (radd a b)) : rlt rzero a ∨ rlt rzero b := by
  obtain ⟨k, N, hk⟩ := h
  obtain ⟨Na, ha⟩ := close_from a (k + 3)
  obtain ⟨Nb, hb⟩ := close_from b (k + 3)
  have hM1 : Na ≤ N + Na + Nb := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have hM2 : Nb ≤ N + Na + Nb := Nat.le_add_left _ _
  have hM0 : N ≤ N + Na + Nb := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have s := hk _ hM0
  change qle (qeps k) (qsub (qadd (a.seq (N + Na + Nb)) (b.seq (N + Na + Nb))) qzero) at s
  have e1 := qeps_succ_add k
  have hs : qEq (qsub (qadd (a.seq (N + Na + Nb)) (b.seq (N + Na + Nb))) qzero)
      (qadd (a.seq (N + Na + Nb)) (b.seq (N + Na + Nb))) := by unfold qsub; rat_ring
  cases qle_total (qeps (k + 1)) (a.seq (N + Na + Nb)) with
  | inl h1 => exact Or.inl (pos_at (ha _ hM1) h1)
  | inr h1 => exact Or.inr (pos_at (hb _ hM2) (by rat_linarith))

/-- The bounded case of a product: `|a| ≤ ε_{k+B+1}`, `|b| ≤ 2^B` give `a·b ≤ ε_{k+1}`. -/
theorem prod_small {a b : QExpr} {k B : Nat} (ha1 : qle a (qeps (k + B + 1))) (ha2 : qle (qneg (qeps (k + B + 1))) a)
    (hb : qclose b qzero (qofInt (pow2 B))) : qle (qmul a b) (qeps (k + 1)) := by
  have hq : qclose a qzero (qeps (k + 1 + B)) := by
    have e : (k + B + 1) = (k + 1 + B) := by rw [Nat.add_assoc, Nat.add_comm B 1, ← Nat.add_assoc]
    rw [← e]
    have hs : qEq (qsub a qzero) a := by unfold qsub; rat_ring
    constructor <;> rat_linarith
  have m := qmul_abs_bound hq hb
  have p := qpow2_mul_eps B (k + 1)
  have hs : qEq (qsub (qmul a b) qzero) (qmul a b) := by unfold qsub; rat_ring
  have c : qEq (qmul (qeps (k + 1 + B)) (qofInt (pow2 B))) (qmul (qofInt (pow2 B)) (qeps (k + 1 + B))) := by rat_ring
  obtain ⟨m1, _⟩ := m
  rat_linarith

/-- Positivity of a product gives apartness of the first factor. -/
theorem pos_mul_left {a b : RExpr} (h : rlt rzero (rmul a b)) : rlt rzero a ∨ rlt rzero (rneg a) := by
  obtain ⟨k, N, hk⟩ := h
  obtain ⟨B, Nb, hB⟩ := rbounded b
  obtain ⟨Na, ha⟩ := close_from a (k + B + 1 + 3)
  have hM0 : N ≤ N + Nb + Na := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hM1 : Nb ≤ N + Nb + Na := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have hM2 : Na ≤ N + Nb + Na := Nat.le_add_left _ _
  have s := hk _ hM0
  change qle (qeps k) (qsub (qmul (a.seq (N + Nb + Na)) (b.seq (N + Nb + Na))) qzero) at s
  have hs : qEq (qsub (qmul (a.seq (N + Nb + Na)) (b.seq (N + Nb + Na))) qzero)
      (qmul (a.seq (N + Nb + Na)) (b.seq (N + Nb + Na))) := by unfold qsub; rat_ring
  cases qle_total (qeps (k + B + 1 + 1)) (a.seq (N + Nb + Na)) with
  | inl h1 => exact Or.inl (pos_at (ha _ hM2) h1)
  | inr h1 =>
      cases qle_total (a.seq (N + Nb + Na)) (qneg (qeps (k + B + 1 + 1))) with
      | inl h2 =>
          refine Or.inr (pos_at (k := k + B + 1) (M := N + Nb + Na) (fun n hn => ?_) (by rw [rneg_seq]; rat_linarith))
          obtain ⟨c1, c2⟩ := ha _ hM2 n hn
          have hs2 : qEq (qsub ((rneg a).seq n) ((rneg a).seq (N + Nb + Na)))
              (qneg (qsub (a.seq n) (a.seq (N + Nb + Na)))) := by rw [rneg_seq, rneg_seq]; unfold qsub; rat_ring
          constructor <;> rat_linarith
      | inr h2 =>
          exfalso
          have e1 := qeps_succ_add k
          have z := qeps_pos (k + 1)
          have hsm : qle (qeps (k + B + 1 + 1)) (qeps (k + B + 1)) := qeps_succ_le (k + B + 1)
          have p := prod_small (a := a.seq (N + Nb + Na)) (b := b.seq (N + Nb + Na)) (k := k) (B := B) (by rat_linarith) (by rat_linarith) (hB _ hM1)
          exact (qlt_iff_le_not_le.mp z).2 (by rat_linarith)

#print axioms split_pos
#print axioms pos_mul_left

theorem rpos_not_le {a : RExpr} (h : rlt rzero a) (h' : rle a rzero) : False := by
  obtain ⟨k, N, hk⟩ := h
  obtain ⟨N', hN'⟩ := h' (k + 1)
  have s1 := hk (N + N') (Nat.le_add_right _ _)
  have s2 := hN' (N + N') (Nat.le_add_left _ _)
  have e1 := qeps_succ_add k
  have hs1 : qEq (qsub (a.seq (N + N')) (rzero.seq (N + N'))) (a.seq (N + N')) := by
    change qEq (qsub (a.seq (N + N')) qzero) (a.seq (N + N')); unfold qsub; rat_ring
  change qle (qeps k) (qsub (a.seq (N + N')) qzero) at s1
  change qle (qsub (a.seq (N + N')) qzero) (qeps (k + 1)) at s2
  have hs0 : qEq (qsub (a.seq (N + N')) qzero) (a.seq (N + N')) := by unfold qsub; rat_ring
  exact (qlt_iff_le_not_le.mp (qeps_pos (k + 1))).2 (by rat_linarith)

theorem rpos_mono {a b : RExpr} (h : rlt rzero a) (h' : rle a b) : rlt rzero b := by
  obtain ⟨k, N, hk⟩ := h
  obtain ⟨N', hN'⟩ := h' (k + 1)
  refine ⟨k + 1, N + N', fun n hn => ?_⟩
  have s1 := hk n (Nat.le_trans (Nat.le_add_right _ _) hn)
  have s2 := hN' n (Nat.le_trans (Nat.le_add_left _ _) hn)
  have e1 := qeps_succ_add k
  change qle (qeps k) (qsub (a.seq n) qzero) at s1
  change qle (qeps (k + 1)) (qsub (b.seq n) qzero)
  have hs1 : qEq (qsub (a.seq n) qzero) (a.seq n) := by unfold qsub; rat_ring
  have hs2 : qEq (qsub (b.seq n) qzero) (b.seq n) := by unfold qsub; rat_ring
  have hs3 : qEq (qsub (a.seq n) (b.seq n)) (qadd (a.seq n) (qneg (b.seq n))) := by unfold qsub; rat_ring
  rat_linarith

theorem rpos_mul {a b : RExpr} (ha : rlt rzero a) (hb : rlt rzero b) : rlt rzero (rmul a b) := by
  obtain ⟨k1, N1, h1⟩ := ha
  obtain ⟨k2, N2, h2⟩ := hb
  refine ⟨k1 + k2, N1 + N2, fun n hn => ?_⟩
  have s1 := h1 n (Nat.le_trans (Nat.le_add_right _ _) hn)
  have s2 := h2 n (Nat.le_trans (Nat.le_add_left _ _) hn)
  change qle (qeps k1) (qsub (a.seq n) qzero) at s1
  change qle (qeps k2) (qsub (b.seq n) qzero) at s2
  change qle (qeps (k1 + k2)) (qsub (qmul (a.seq n) (b.seq n)) qzero)
  have hs1 : qEq (qsub (a.seq n) qzero) (a.seq n) := by unfold qsub; rat_ring
  have hs2 : qEq (qsub (b.seq n) qzero) (b.seq n) := by unfold qsub; rat_ring
  have hs3 : qEq (qsub (qmul (a.seq n) (b.seq n)) qzero) (qmul (a.seq n) (b.seq n)) := by unfold qsub; rat_ring
  have z1 := qeps_nonneg k1
  have z2 := qeps_nonneg k2
  have m1 := qmul_le_mul_of_nonneg (a := qeps k1) (b := a.seq n) (c := qeps k2) (by rat_linarith) z2
  have m2 := qmul_le_mul_of_nonneg (a := qeps k2) (b := b.seq n) (c := a.seq n) (by rat_linarith) (by rat_linarith)
  have e := qeps_mul k1 k2
  rat_linarith

theorem rinv {a : RExpr} (h : rlt rzero a ∨ rlt rzero (rneg a)) : ∃ b, rEq (rmul a b) rone := by
  cases h with
  | inl hp =>
      obtain ⟨k, N, hw⟩ := (rlt_zero_iff a).mp hp
      exact ⟨rinvPos a k N hw, rinvPos_mul a k N hw⟩
  | inr hn =>
      obtain ⟨k, N, hw⟩ := (rlt_zero_iff (rneg a)).mp hn
      refine ⟨rneg (rinvPos (rneg a) k N hw), rEq_trans ?_ (rinvPos_mul (rneg a) k N hw)⟩
      exact rEq_of_seq (fun n => by
        change qEq (qmul (a.seq n) (qneg ((rinvPos (rneg a) k N hw).seq n)))
          (qmul (qneg (a.seq n)) ((rinvPos (rneg a) k N hw).seq n))
        rat_ring)

set_option maxRecDepth 20000 in
/-- COTRANSITIVITY: `a < b` puts every `x` below `b` or above `a` — decided at ONE index, on pre-rationals. -/
theorem rcotrans {a b : RExpr} (h : rlt rzero (radd b (rneg a))) (x : RExpr) : rle x b ∨ rle a x := by
  obtain ⟨k, N, hk⟩ := h
  obtain ⟨Nx, hx⟩ := close_from x (k + 3)
  obtain ⟨Na, ha⟩ := close_from a (k + 3)
  obtain ⟨Nb, hb⟩ := close_from b (k + 3)
  have g0 : N ≤ N + Nx + Na + Nb := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have gx : Nx ≤ N + Nx + Na + Nb := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have ga : Na ≤ N + Nx + Na + Nb := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have gb : Nb ≤ N + Nx + Na + Nb := Nat.le_add_left _ _
  have s := hk _ g0
  change qle (qeps k) (qsub (qadd (b.seq (N + Nx + Na + Nb)) (qneg (a.seq (N + Nx + Na + Nb)))) qzero) at s
  have hs : qEq (qsub (qadd (b.seq (N + Nx + Na + Nb)) (qneg (a.seq (N + Nx + Na + Nb)))) qzero)
      (qadd (b.seq (N + Nx + Na + Nb)) (qneg (a.seq (N + Nx + Na + Nb)))) := by unfold qsub; rat_ring
  have e1 := qeps_succ_add k
  have e2 := qeps_succ_add (k + 1)
  have e3 := qeps_succ_add (k + 2)
  have z := qeps_nonneg (k + 3)
  cases qle_total (qadd (x.seq (N + Nx + Na + Nb)) (x.seq (N + Nx + Na + Nb)))
      (qadd (a.seq (N + Nx + Na + Nb)) (b.seq (N + Nx + Na + Nb))) with
  | inl hm =>
      left
      intro j
      refine ⟨N + Nx + Na + Nb, fun n hn => ?_⟩
      obtain ⟨cx1, cx2⟩ := hx _ gx n hn
      obtain ⟨cb1, cb2⟩ := hb _ gb n hn
      have zj := qeps_nonneg j
      unfold qsub at *
      rat_linarith
  | inr hm =>
      right
      intro j
      refine ⟨N + Nx + Na + Nb, fun n hn => ?_⟩
      obtain ⟨cx1, cx2⟩ := hx _ gx n hn
      obtain ⟨ca1, ca2⟩ := ha _ ga n hn
      have zj := qeps_nonneg j
      unfold qsub at *
      rat_linarith

set_option maxRecDepth 20000 in
/-- `≤` from "not `>`": at one index the difference is decided; the large case would make it positive. -/
theorem rle_of_not_pos {a b : RExpr} (h : ¬ rlt rzero (radd a (rneg b))) : rle a b := by
  intro k
  obtain ⟨Na, ha⟩ := close_from a (k + 4)
  obtain ⟨Nb, hb⟩ := close_from b (k + 4)
  have ga : Na ≤ Na + Nb := Nat.le_add_right _ _
  have gb : Nb ≤ Na + Nb := Nat.le_add_left _ _
  have e1 := qeps_succ_add k
  have e2 := qeps_succ_add (k + 1)
  have e3 := qeps_succ_add (k + 2)
  have e4 := qeps_succ_add (k + 3)
  have z := qeps_nonneg (k + 4)
  cases qle_total (qsub (a.seq (Na + Nb)) (b.seq (Na + Nb))) (qeps (k + 1)) with
  | inl hs =>
      refine ⟨Na + Nb, fun n hn => ?_⟩
      obtain ⟨ca1, ca2⟩ := ha _ ga n hn
      obtain ⟨cb1, cb2⟩ := hb _ gb n hn
      unfold qsub at *
      rat_linarith
  | inr hs =>
      exfalso
      apply h
      refine pos_at (x := radd a (rneg b)) (k := k) (M := Na + Nb) (fun n hn => ?_) ?_
      · obtain ⟨ca1, ca2⟩ := ha _ ga n hn
        obtain ⟨cb1, cb2⟩ := hb _ gb n hn
        change qclose (qadd (a.seq n) (qneg (b.seq n))) (qadd (a.seq (Na + Nb)) (qneg (b.seq (Na + Nb)))) (qeps (k + 3))
        unfold qclose qsub at *
        constructor <;> rat_linarith
      · change qle (qeps (k + 1)) (qadd (a.seq (Na + Nb)) (qneg (b.seq (Na + Nb))))
        unfold qsub at hs
        rat_linarith

set_option maxRecDepth 20000 in
/-- Tightness: not apart from 0 means equal to 0 — decided at one index per precision. -/
theorem rap_tight {a : RExpr} (h : ¬ (rlt rzero a ∨ rlt rzero (rneg a))) : rEq a rzero := by
  intro k
  obtain ⟨Na, ha⟩ := close_from a (k + 3)
  have e1 := qeps_succ_add k
  have e2 := qeps_succ_add (k + 1)
  have e3 := qeps_succ_add (k + 2)
  have z := qeps_nonneg (k + 3)
  cases qle_total (qeps (k + 1)) (a.seq Na) with
  | inl h1 => exact (h (Or.inl (pos_at (ha _ (Nat.le_refl _)) h1))).elim
  | inr h1 =>
      cases qle_total (a.seq Na) (qneg (qeps (k + 1))) with
      | inl h2 =>
          refine (h (Or.inr (pos_at (x := rneg a) (k := k) (M := Na) (fun n hn => ?_) ?_))).elim
          · obtain ⟨c1, c2⟩ := ha _ (Nat.le_refl _) n hn
            change qclose (qneg (a.seq n)) (qneg (a.seq Na)) (qeps (k + 3))
            unfold qclose qsub at *
            constructor <;> rat_linarith
          · change qle (qeps (k + 1)) (qneg (a.seq Na)); rat_linarith
      | inr h2 =>
          refine ⟨Na, fun n hn => ?_⟩
          obtain ⟨c1, c2⟩ := ha _ (Nat.le_refl _) n hn
          change qclose (a.seq n) qzero (qeps k)
          unfold qclose qsub at *
          constructor <;> rat_linarith

#print axioms rpos_not_le
#print axioms rpos_mono
#print axioms rpos_mul
#print axioms rinv
#print axioms rcotrans
#print axioms rle_of_not_pos
#print axioms rap_tight

/-! ## The instance -/

/-- **VR's operational reals are a constructive ordered field** (`ZField.CF`) — every law on `[]`. -/
def rCF : ZField.CF RExpr := { rOH with
  pos := fun x => rlt rzero x
  pos_congr := fun h hp => rlt_respects (rEq_refl _) h hp
  pos_nonneg := fun h => rle_of_rlt h
  pos_not_le := fun h h' => rpos_not_le h h'
  pos_mono := fun h h' => rpos_mono h h'
  pos_mul := fun h1 h2 => rpos_mul h1 h2
  pos_half := ⟨1, 0, fun n _ => by
    change qle (qeps 1) (qsub (qeps 1) qzero)
    have hs : qEq (qsub (qeps 1) qzero) (qeps 1) := by unfold qsub; rat_ring
    rat_linarith⟩
  ap_add := fun {a b} h => by
    cases h with
    | inl hp =>
        cases split_pos hp with
        | inl ha => exact Or.inl (Or.inl ha)
        | inr hb => exact Or.inr (Or.inl hb)
    | inr hn =>
        have e : rEq (rneg (radd a b)) (radd (rneg a) (rneg b)) := rEq_of_seq (fun n => by
          change qEq (qneg (qadd (a.seq n) (b.seq n))) (qadd (qneg (a.seq n)) (qneg (b.seq n))); rat_ring)
        cases split_pos (rlt_respects (rEq_refl _) e hn) with
        | inl ha => exact Or.inl (Or.inr ha)
        | inr hb => exact Or.inr (Or.inr hb)
  ap_mul := fun {a b} h => by
    cases h with
    | inl hp => exact pos_mul_left hp
    | inr hn =>
        have e : rEq (rneg (rmul a b)) (rmul (rneg a) b) := rEq_of_seq (fun n => by
          change qEq (qneg (qmul (a.seq n) (b.seq n))) (qmul (qneg (a.seq n)) (b.seq n)); rat_ring)
        have e2 : rEq (rneg (rneg a)) a := rEq_of_seq (fun n => by
          change qEq (qneg (qneg (a.seq n))) (a.seq n); rat_ring)
        cases pos_mul_left (rlt_respects (rEq_refl _) e hn) with
        | inl h1 => exact Or.inr h1
        | inr h1 => exact Or.inl (rlt_respects (rEq_refl _) e2 h1)
  inv := fun h => rinv h
  cotrans := fun h x => rcotrans h x
  le_of_not_pos := fun h => rle_of_not_pos h
  ap_tight := fun h => rap_tight h }

/-- **`check_none` ON VR'S CONTINUUM.** An accepted certificate leaves no point of the box, in VR's operational
reals, and no values of the expressions there (a quotient's value needs its divisor apart from 0 — the
reciprocal is a partial operation on the continuum), where every equation is 0 and every condition apart from 0.
Zero axioms. -/
theorem vr_no_solution (ex atn : RExpr → RExpr) (c : ZNone.Cert) (Sy : ZNone.Sys) (B : ZIv.Box) (h : ZNone.chk Sy B c = true)
    (p : Nat → RExpr) (hp : ZIv.InBox rCF B p)
    (hE : ∀ e ∈ Sy.eqs, ∃ v, ZXE.Val rCF ex atn p e v ∧ rEq v rzero)
    (hN : ∀ n ∈ Sy.neqs, ∃ v, ZXE.Val rCF ex atn p n v ∧ (rlt rzero v ∨ rlt rzero (rneg v))) :
    False :=
  ZNone.chk_sound rCF ex atn c Sy B p h hp hE hN

#print axioms rCF
#print axioms vr_no_solution

end ZRealCF
