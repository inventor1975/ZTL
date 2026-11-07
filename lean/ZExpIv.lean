import ZExpLaw
import ZDivIv
/-!
# ZExpIv — bounds of `exp` at a dyadic from its partial sums, and the interval readings of `exp` and `ln`.
Zero axioms.

For `d ≥ 0`: `n!·Tₙ(d) ≤ n!·e^d ≤ n!·Tₙ(d) + 2dⁿ` when `2d ≤ n + 1` (`ExpLaws.lo`, `hi`); `W n d = n!·Tₙ(d)` is
computed EXACTLY on dyadics, and the division by `n!` is computed, then CHECKED (`q·n! ≤ W`, `U·n! ≥ W + 2dⁿ`).
For `d < 0`: `e^d = 1/e^(−d)` (`recip`), through the reciprocal interval. The interval of `exp` on `[l, h]` is
`[low(rdn l), up(rup h)]` by monotonicity (the endpoints rounded first, so the sums stay small). The logarithm is
read through `exp`: Newton's candidates (untrusted), then CHECKED `e^Lb ≤ l`, `h ≤ e^Ub`, and reflection.
Arguments are matched into their fields before the bounds (measured 2026-11-08: the kernel did not reduce the
bounds of an unevaluated `(f x).m`; matched first, it did).
-/

namespace ZExpIv
open VR.CSR ZNumBin ZField ZIv ZAff ZDivIv ZExpLaw

theorem cond_some' {b : Bool} {x K : D} (h : cond b (some x) none = some K) : b = true ∧ x = K := by
  cases b with
  | false => cases h
  | true => exact ⟨rfl, Option.some.inj h⟩

/-! ## Exact partial sums on dyadics -/

def natD (k : Nat) : D := ⟨⟨k, 0⟩, 0⟩

def pwD (d : D) : Nat → D
  | 0 => oneD
  | n + 1 => dmul d (pwD d n)

def WD (d : D) : Nat → D
  | 0 => zeroD
  | n + 1 => dmul (natD (n + 1)) (dadd (WD d n) (pwD d n))

variable {α : Type} (S : CF α)

theorem dv_natD (k : Nat) : S.r (dv S.toOH (natD k)) (CR.numeral S.toCR k) := by
  show S.r (S.mul (S.add (nI S.toOH k) (S.neg (CR.numeral S.toCR 0))) S.one) (nI S.toOH k)
  show S.r (S.mul (S.add (nI S.toOH k) (S.neg S.zero)) S.one) (nI S.toOH k)
  cr_ring S.toCR

theorem dv_pwD (d : D) : ∀ n, S.r (dv S.toOH (pwD d n)) (pw S (dv S.toOH d) n)
  | 0 => dv_oneD S
  | n + 1 => S.trans (dv_mul S.toOH _ _) (S.mul_congr (S.refl _) (dv_pwD d n))

theorem dv_WD (d : D) : ∀ n, S.r (dv S.toOH (WD d n)) (W S (dv S.toOH d) n)
  | 0 => dv_zeroD S
  | n + 1 => S.trans (dv_mul S.toOH _ _) (S.mul_congr (dv_natD S (n + 1))
      (S.trans (dv_add S.toOH _ _) (S.add_congr (dv_WD d n) (dv_pwD S d n))))

theorem fact_pos : ∀ n, 1 ≤ fact n
  | 0 => Nat.le_refl 1
  | n + 1 => by
      show 1 ≤ (n + 1) * fact n
      exact Nat.le_trans (fact_pos n) (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))

theorem pos_numeral_fact (n : Nat) : S.pos (CR.numeral S.toCR (fact n)) := by
  have l := nI_le S.toOH (fact_pos n)
  have one : S.r (nI S.toOH 1) S.one := by show S.r (S.add S.one S.zero) S.one; cr_ring S.toCR
  exact S.pos_mono (pos_one S) (S.le_respects one (S.refl _) l)

/-! ## Division by `n!`, computed then checked -/

/-- `x / F` at `K` more bits, rounded down or up (a candidate; the check decides). -/
def divD (x : D) (F K : Nat) (up : Bool) : D :=
  let z := znorm x.m
  let num := z.p * 2 ^ K
  cond up ⟨⟨(num + F - 1) / F, 0⟩, x.e + K⟩ ⟨⟨num / F, 0⟩, x.e + K⟩

variable {ex : α → α} (H : ExpLaws S ex)
include H

/-- `q·n! ≤ x ≤ n!·eᵃ`, `n! > 0`: `q ≤ eᵃ`. -/
theorem le_of_scaled {q : D} {n : Nat} {x a : α} (hq : S.le (S.mul (dv S.toOH q) (CR.numeral S.toCR (fact n))) x)
    (hx : S.le x (S.mul (CR.numeral S.toCR (fact n)) (ex a))) : S.le (dv S.toOH q) (ex a) := by
  apply S.le_of_not_pos
  intro hp
  have pp := S.pos_mul hp (pos_numeral_fact S n)
  exact S.pos_not_le pp (by cr_linarith S.toOCR [hq, hx])

/-- `n!·eᵃ ≤ x ≤ U·n!`: `eᵃ ≤ U`. -/
theorem ge_of_scaled {U : D} {n : Nat} {x a : α} (hU : S.le x (S.mul (dv S.toOH U) (CR.numeral S.toCR (fact n))))
    (hx : S.le (S.mul (CR.numeral S.toCR (fact n)) (ex a)) x) : S.le (ex a) (dv S.toOH U) := by
  apply S.le_of_not_pos
  intro hp
  have pp := S.pos_mul hp (pos_numeral_fact S n)
  exact S.pos_not_le pp (by cr_linarith S.toOCR [hU, hx])

/-! ## Bounds at a dyadic -/

/-- The order of the partial sum: `2·⌈d⌉ + 64` (so that `2d ≤ n + 1`, checked). -/
def ordN (d : D) : Nat := 2 * ((znorm d.m).p / 2 ^ d.e + 1) + 64

/-- `[L, U] ∋ e^d` for `d ≥ 0`, from the partial sums, with every inequality the proof needs CHECKED. -/
def expPosB (d : D) : Option Iv :=
  let n := ordN d
  let w := WD d n
  let t := dadd w (dmul (natD 2) (pwD d n))
  let F := fact n
  let L := divD w F 64 false
  let U := divD t F 64 true
  cond (dle (dmul L (natD F)) w && dle t (dmul U (natD F)) && dle (dadd d d) (natD (n + 1)) && !(isNeg d))
    (some (L, U)) none

omit H in
theorem and4' {a b c d : Bool} (H : (a && b && c && d) = true) : a = true ∧ b = true ∧ c = true ∧ d = true := by
  have s1 := and_true_split H
  have s2 := and_true_split s1.1
  have s3 := and_true_split s2.1
  exact ⟨s3.1, s3.2, s2.2, s1.2⟩

theorem mem_expPosB {d : D} {K : Iv} (h : expPosB d = some K) : Mem S (ex (dv S.toOH d)) K := by
  unfold expPosB at h
  dsimp only at h
  obtain ⟨hb, hK⟩ := cond_some h
  subst hK
  obtain ⟨c1, c2, c3, c4⟩ := and4' hb
  have hn : isNeg d = false := by
    cases h' : isNeg d with
    | true => rw [h'] at c4; cases c4
    | false => rfl
  have d0 : S.le S.zero (dv S.toOH d) := dv_nonneg_of S hn
  have eW := dv_WD S d (ordN d)
  have eP := dv_pwD S d (ordN d)
  have eF := dv_natD S (fact (ordN d))
  have l1 := S.le_respects (S.trans (dv_mul S.toOH _ _) (S.mul_congr (S.refl _) eF)) eW (dle_sound S.toOH c1)
  have lo := H.lo (ordN d) d d0
  have et : S.r (dv S.toOH (dadd (WD d (ordN d)) (dmul (natD 2) (pwD d (ordN d)))))
      (S.add (W S (dv S.toOH d) (ordN d)) (S.mul (CR.numeral S.toCR 2) (pw S (dv S.toOH d) (ordN d)))) :=
    S.trans (dv_add S.toOH _ _) (S.add_congr eW (S.trans (dv_mul S.toOH _ _) (S.mul_congr (dv_natD S 2) eP)))
  have l2 := S.le_respects et (S.trans (dv_mul S.toOH _ _) (S.mul_congr (S.refl _) eF)) (dle_sound S.toOH c2)
  have l3 := S.le_respects (dv_add S.toOH d d) (dv_natD S (ordN d + 1)) (dle_sound S.toOH c3)
  have hi := H.hi (ordN d) d d0 l3
  exact ⟨le_of_scaled S H l1 lo, ge_of_scaled S H l2 hi⟩

/-- `[L, U] ∋ e^d` for any dyadic, matched into its fields first; `d < 0` through `1/e^(−d)`. -/
def expAt (d : D) : Option Iv :=
  match d with
  | ⟨⟨p, q⟩, e⟩ =>
    cond (isNeg ⟨⟨p, q⟩, e⟩)
      (match expPosB (dneg ⟨⟨p, q⟩, e⟩) with
        | none => none
        | some B => ivInv B)
      (expPosB ⟨⟨p, q⟩, e⟩)

omit H in
theorem expAt_eq (d : D) : expAt d = cond (isNeg d)
    (match expPosB (dneg d) with
      | none => none
      | some B => ivInv B) (expPosB d) := by
  obtain ⟨⟨p, q⟩, e⟩ := d; rfl

theorem mem_expAt {d : D} {K : Iv} (h : expAt d = some K) : Mem S (ex (dv S.toOH d)) K := by
  rw [expAt_eq] at h
  cases hn : isNeg d with
  | false => rw [hn, cond_false] at h; exact mem_expPosB S H h
  | true =>
      rw [hn, cond_true] at h
      cases hB : expPosB (dneg d) with
      | none => rw [hB] at h; cases h
      | some B =>
          rw [hB] at h
          have mB := mem_expPosB S H hB
          have eneg : S.r (ex (dv S.toOH (dneg d))) (ex (S.neg (dv S.toOH d))) := H.congr (dv_neg S.toOH _)
          have rc := H.recip d
          have one : S.r (S.mul (ex (dv S.toOH (dneg d))) (ex (dv S.toOH d))) S.one :=
            S.trans (S.trans (S.mul_congr eneg (S.refl _)) (S.mul_comm _ _)) rc
          exact mem_inv S mB h one

/-! ## The readings -/

def comb : Option Iv → Option Iv → Option Iv
  | none, _ => none
  | some _, none => none
  | some A, some B => some (A.1, B.2)

omit H in
theorem comb_some {a b : Option Iv} {K : Iv} (h : comb a b = some K) :
    ∃ A B, a = some A ∧ b = some B ∧ K = (A.1, B.2) := by
  cases a with
  | none => cases h
  | some A =>
      cases b with
      | none => cases h
      | some B => exact ⟨A, B, rfl, rfl, (Option.some.inj h).symm⟩

/-- `exp` on `[l, h]`: `[low(l'), up(h')]`, `l' ≤ l`, `h ≤ h'` rounded to a coarse grid first. -/
def ivExp (I : Iv) : Option Iv := comb (expAt (rdnA I.1)) (expAt (rupA I.2))

theorem mem_exp {x : α} {I K : Iv} (hx : Mem S x I) (h : ivExp I = some K) : Mem S (ex x) K := by
  obtain ⟨A, B, hA, hB, hK⟩ := comb_some h
  subst hK
  have mA := mem_expAt S H hA
  have mB := mem_expAt S H hB
  have l := H.mono (S.le_trans (rdnA_le S.toOH I.1) hx.1)
  have u := H.mono (S.le_trans hx.2 (le_rupA S.toOH I.2))
  exact ⟨S.le_trans mA.1 l, S.le_trans u mB.2⟩

/-- `ln 2`, a dyadic approximation (only a starting point: everything below is checked). -/
def ln2 : D := ⟨⟨45426, 0⟩, 16⟩

/-- Newton's iteration for `ln x` on dyadics, `c ← c + x·e^(−c) − 1` — UNTRUSTED, a candidate only. -/
def lnNewton (x : D) : Nat → D → D
  | 0, c => c
  | k + 1, c =>
      match expAt (dneg c) with
      | none => c
      | some E => lnNewton x k (rdnA (dadd (dadd c (dmul x E.2)) (dneg oneD)))

def lnGuess (x : D) : D :=
  let z := znorm x.m
  lnNewton x 8 (rdnA (dmul ⟨⟨z.p.log2, x.e⟩, 0⟩ ln2))

def tiny : D := ⟨⟨1, 0⟩, 40⟩

/-- `ln` on `[l, h]`, `l > 0`, with candidates `Lb`, `Ub` (any — CHECKED: `e^Lb ≤ l`, `h ≤ e^Ub`). -/
def ivLnC (Lb Ub : D) (I : Iv) : Option Iv :=
  cond (posX I.1)
    (match expAt Lb with
      | none => none
      | some A => match expAt Ub with
          | none => none
          | some B => cond (dle A.2 I.1 && dle I.2 B.1) (some (Lb, Ub)) none)
    none

theorem mem_lnC (Lb Ub : D) {x v : α} {I K : Iv} (hx : Mem S x I) (hv : S.r (ex v) x)
    (h : ivLnC Lb Ub I = some K) : Mem S v K := by
  unfold ivLnC at h
  cases hp : posX I.1 with
  | false => rw [hp] at h; cases h
  | true =>
      rw [hp] at h
      cases hA : expAt Lb with
      | none => rw [hA] at h; cases h
      | some A =>
          rw [hA] at h
          dsimp only at h
          cases hB : expAt Ub with
          | none => rw [hB] at h; cases h
          | some B =>
              rw [hB] at h
              obtain ⟨hb, hK⟩ := cond_some h
              subst hK
              have c := and_true_split hb
              have mA := mem_expAt S H hA
              have mB := mem_expAt S H hB
              have c1 := dle_sound S.toOH c.1
              have c2 := dle_sound S.toOH c.2
              have hv1 := S.le_respects (S.refl _) (S.symm hv) hx.1
              have hv2 := S.le_respects (S.symm hv) (S.refl _) hx.2
              exact ⟨ex_reflect H (S.le_trans mA.2 (S.le_trans c1 hv1)), ex_reflect H (S.le_trans hv2 (S.le_trans c2 mB.1))⟩

def ivLn (I : Iv) : Option Iv := ivLnC (dadd (lnGuess I.1) (dneg tiny)) (dadd (lnGuess I.2) tiny) I

theorem mem_ln {x v : α} {I K : Iv} (hx : Mem S x I) (hv : S.r (ex v) x) (h : ivLn I = some K) : Mem S v K :=
  mem_lnC S H _ _ hx hv h

end ZExpIv
