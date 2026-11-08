import ZKraw
/-!
# ZKrawSys — a SYSTEM `F(x) = 0` (laws with exp / ln / division) has a solution in a cube on VR's continuum, and only
one there. Zero axioms.

`G(x) = x − Y·F(x)` (`Gsys`, built here, so the theorem speaks of `F`); `ZKraw.krawczyk` gives a unique fixed point of
`G`. A fixed point is a zero of `F` when `Y` is invertible, and that is CHECKED in dyadics: a second matrix `Z` with
every row of `|I − Z·Y|` summing to `≤ ½` (`chkZ`). Then `Y·v = 0` gives `v = M·v` with `M = I − Z·Y`, so every
`|vᵢ| ≤ ½·max|vⱼ|`, so `v = 0` (`lin_inj`).
-/

namespace ZKrawSys
open VR VR.Numbers VR.CSR ZNumBin ZField ZIv ZDivIv ZXE ZRealCF ZExp ZRealExp ZRootExp ZRootDiv ZRootPVR ZRootPar ZBanach
  ZKraw

/-! ## Finite sums (any `CF`) -/

section G
variable {α : Type} (S : CF α)

def sumS (f : Nat → α) : Nat → α
  | 0 => S.zero
  | n + 1 => S.add (sumS f n) (f n)

variable {S}

theorem sumS_congr {f g : Nat → α} : ∀ {n : Nat}, (∀ j, j < n → S.r (f j) (g j)) → S.r (sumS S f n) (sumS S g n)
  | 0, _ => S.refl _
  | n + 1, h => S.add_congr (sumS_congr (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))

theorem sumS_zero {f : Nat → α} : ∀ {n : Nat}, (∀ j, j < n → S.r (f j) S.zero) → S.r (sumS S f n) S.zero
  | 0, _ => S.refl _
  | n + 1, h => S.trans (S.add_congr (sumS_zero (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n)))
      (S.zero_add _)

theorem sumS_add (f g : Nat → α) : ∀ n, S.r (sumS S (fun j => S.add (f j) (g j)) n) (S.add (sumS S f n) (sumS S g n))
  | 0 => S.symm (S.zero_add _)
  | n + 1 => by
      show S.r (S.add (sumS S (fun j => S.add (f j) (g j)) n) (S.add (f n) (g n)))
        (S.add (S.add (sumS S f n) (f n)) (S.add (sumS S g n) (g n)))
      exact S.trans (S.add_congr (sumS_add f g n) (S.refl _)) (by cr_ring S.toCR)

theorem sumS_mul (c : α) (f : Nat → α) : ∀ n, S.r (S.mul c (sumS S f n)) (sumS S (fun j => S.mul c (f j)) n)
  | 0 => by show S.r (S.mul c S.zero) S.zero; cr_ring S.toCR
  | n + 1 => by
      show S.r (S.mul c (S.add (sumS S f n) (f n))) (S.add (sumS S (fun j => S.mul c (f j)) n) (S.mul c (f n)))
      exact S.trans (by cr_ring S.toCR : S.r _ (S.add (S.mul c (sumS S f n)) (S.mul c (f n))))
        (S.add_congr (sumS_mul c f n) (S.refl _))

theorem sumS_swap (f : Nat → Nat → α) (m : Nat) : ∀ n,
    S.r (sumS S (fun i => sumS S (fun j => f i j) m) n) (sumS S (fun j => sumS S (fun i => f i j) n) m)
  | 0 => S.symm (sumS_zero (fun _ _ => S.refl _))
  | n + 1 => by
      refine S.trans (S.add_congr (sumS_swap f m n) (S.refl _)) ?_
      exact S.symm (sumS_add (fun j => sumS S (fun i => f i j) n) (fun j => f n j) m)

theorem sumS_bd {f g : Nat → α} : ∀ {n : Nat}, (∀ j, j < n → ZKron.Bd S.toOH (f j) (g j)) →
    ZKron.Bd S.toOH (sumS S f n) (sumS S g n)
  | 0, _ => ⟨by show S.le (S.neg S.zero) S.zero; cr_linarith S.toOCR [], S.le_refl _⟩
  | n + 1, h => by
      obtain ⟨a1, a2⟩ := sumS_bd (f := f) (g := g) (fun j hj => h j (Nat.lt_succ_of_lt hj))
      obtain ⟨b1, b2⟩ := h n (Nat.lt_succ_self n)
      exact ⟨by show S.le (S.neg (S.add _ _)) (S.add _ _); cr_linarith S.toOCR [a1, b1],
        by show S.le (S.add _ _) (S.add _ _); cr_linarith S.toOCR [a2, b2]⟩

/-- `Σⱼ [i = j]·vⱼ = vᵢ` for `i < n`. -/
theorem sumS_kron (v : Nat → α) (i : Nat) : ∀ n, i < n →
    S.r (sumS S (fun j => S.mul (dv S.toOH (cond (Nat.beq i j) ZRootExp.d1 dz0)) (v j)) n) (v i)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
      show S.r (S.add (sumS S _ n) (S.mul (dv S.toOH (cond (Nat.beq i n) ZRootExp.d1 dz0)) (v n))) (v i)
      cases Nat.lt_or_ge i n with
      | inl hlt =>
          have hne : Nat.beq i n = false := by
            cases e : Nat.beq i n with
            | false => rfl
            | true => exact absurd (Nat.eq_of_beq_eq_true e) (Nat.ne_of_lt hlt)
          rw [hne]
          refine S.trans (S.add_congr (sumS_kron v i n hlt) (S.trans (S.mul_congr dv_dz0 (S.refl _)) (S.zero_mul _))) ?_
          cr_ring S.toCR
      | inr hge =>
          have e : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
          subst e
          rw [ZKron.beq_self]
          have z : S.r (sumS S (fun j => S.mul (dv S.toOH (cond (Nat.beq i j) ZRootExp.d1 dz0)) (v j)) i) S.zero :=
            sumS_zero (fun j hj => by
              have hne : Nat.beq i j = false := by
                cases e : Nat.beq i j with
                | false => rfl
                | true => exact absurd (Nat.eq_of_beq_eq_true e) (Nat.ne_of_gt hj)
              rw [hne]; exact S.trans (S.mul_congr dv_dz0 (S.refl _)) (S.zero_mul _))
          refine S.trans (S.add_congr z (S.mul_congr (dv_d1 S) (S.refl _))) ?_
          exact S.trans (S.zero_add _) (S.one_mul _)

end G

/-! ## Dyadic sums and absolute values -/

def dsum (f : Nat → D) : Nat → D
  | 0 => dz0
  | n + 1 => dadd (dsum f n) (f n)

def dabs (x : D) : D := dmax x (dneg x)

section G2
variable {α : Type} (S : CF α)

theorem dv_dsum (f : Nat → D) : ∀ n, S.r (dv S.toOH (dsum f n)) (sumS S (fun j => dv S.toOH (f j)) n)
  | 0 => dv_dz0
  | n + 1 => S.trans (dv_add S.toOH _ _) (S.add_congr (dv_dsum f n) (S.refl _))

theorem dabs_bd (x : D) : S.le (S.neg (dv S.toOH (dabs x))) (dv S.toOH x) ∧ S.le (dv S.toOH x) (dv S.toOH (dabs x)) := by
  have m1 := dmax_l S x (dneg x)
  have m2 := dmax_r S x (dneg x)
  have e := dv_neg S.toOH x
  have m2' := S.le_respects e (S.refl _) m2
  show S.le (S.neg (dv S.toOH (dmax x (dneg x)))) (dv S.toOH x) ∧ S.le (dv S.toOH x) (dv S.toOH (dmax x (dneg x)))
  exact ⟨by cr_linarith S.toOCR [m2'], m1⟩

theorem sumS_neg (f : Nat → α) : ∀ n, S.r (sumS S (fun j => S.neg (f j)) n) (S.neg (sumS S f n))
  | 0 => by show S.r S.zero (S.neg S.zero); cr_ring S.toCR
  | n + 1 => by
      show S.r (S.add (sumS S (fun j => S.neg (f j)) n) (S.neg (f n))) (S.neg (S.add (sumS S f n) (f n)))
      exact S.trans (S.add_congr (sumS_neg f n) (S.refl _)) (by cr_ring S.toCR)

theorem sumS_mulR (c : α) (f : Nat → α) (n : Nat) : S.r (S.mul (sumS S f n) c) (sumS S (fun j => S.mul (f j) c) n) :=
  S.trans (S.mul_comm _ _) (S.trans (sumS_mul c f n) (sumS_congr (fun _ _ => S.mul_comm _ _)))

theorem sub_self_zero {a b : α} (h : S.r (S.add a (S.neg b)) a) : S.r b S.zero :=
  S.trans (by cr_ring S.toCR : S.r b (S.add a (S.neg (S.add a (S.neg b))))) (S.trans (S.add_congr (S.refl _)
    (S.neg_congr h)) (S.add_neg _))

end G2

/-! ## `Y` is invertible: `|I − Z·Y|` has rows `≤ ½` -/

/-- `M = I − Z·Y`, exactly in dyadics. -/
def Mdy (d : Nat) (Y Z : Nat → Nat → D) (i j : Nat) : D :=
  dadd (cond (Nat.beq i j) ZRootExp.d1 dz0) (dneg (dsum (fun k => dmul (Z i k) (Y k j)) d))

def chkZ (d : Nat) (Y Z : Nat → Nat → D) : Bool :=
  allB d (fun i => dle (dsum (fun j => dabs (Mdy d Y Z i j)) d) hD)

section Lin
variable {α : Type} (S : CF α)

/-- `Σⱼ Mᵢⱼ·vⱼ = vᵢ − Σₖ Zᵢₖ·(Σⱼ Yₖⱼ·vⱼ)`. -/
theorem lin_expand (d : Nat) (Y Z : Nat → Nat → D) (v : Nat → α) (i : Nat) (hi : i < d) :
    S.r (sumS S (fun j => S.mul (dv S.toOH (Mdy d Y Z i j)) (v j)) d)
      (S.add (v i) (S.neg (sumS S (fun k => S.mul (dv S.toOH (Z i k)) (sumS S (fun j => S.mul (dv S.toOH (Y k j)) (v j)) d)) d))) := by
  have eP : ∀ j, S.r (dv S.toOH (dsum (fun k => dmul (Z i k) (Y k j)) d))
      (sumS S (fun k => S.mul (dv S.toOH (Z i k)) (dv S.toOH (Y k j))) d) := fun j =>
    S.trans (dv_dsum S _ d) (sumS_congr (fun k _ => dv_mul S.toOH _ _))
  have e1 : S.r (sumS S (fun j => S.mul (dv S.toOH (Mdy d Y Z i j)) (v j)) d)
      (sumS S (fun j => S.add (S.mul (dv S.toOH (cond (Nat.beq i j) ZRootExp.d1 dz0)) (v j))
        (S.neg (S.mul (sumS S (fun k => S.mul (dv S.toOH (Z i k)) (dv S.toOH (Y k j))) d) (v j)))) d) :=
    sumS_congr (fun j _ => by
      refine S.trans (S.mul_congr (S.trans (dv_add S.toOH _ _) (S.add_congr (S.refl _)
        (S.trans (dv_neg S.toOH _) (S.neg_congr (eP j))))) (S.refl _)) ?_
      cr_ring S.toCR)
  refine S.trans e1 (S.trans (sumS_add _ _ d) (S.add_congr (sumS_kron v i d hi) ?_))
  refine S.trans (sumS_neg S _ d) (S.neg_congr ?_)
  refine S.trans (sumS_congr (fun j _ => sumS_mulR S (v j) _ d)) ?_
  refine S.trans (sumS_swap (fun j k => S.mul (S.mul (dv S.toOH (Z i k)) (dv S.toOH (Y k j))) (v j)) d d) ?_
  refine sumS_congr (fun k _ => ?_)
  refine S.trans (sumS_congr (fun j _ => (by cr_ring S.toCR :
    S.r (S.mul (S.mul (dv S.toOH (Z i k)) (dv S.toOH (Y k j))) (v j)) (S.mul (dv S.toOH (Z i k)) (S.mul (dv S.toOH (Y k j)) (v j)))))) ?_
  exact S.symm (sumS_mul _ _ d)

/-- One halving: `|vⱼ| ≤ B` for all `j < d` gives `|Σⱼ Mᵢⱼ vⱼ| ≤ ½·B`. -/
theorem lin_half (d : Nat) (Y Z : Nat → Nat → D) (v : Nat → α) {B : α} (B0 : S.le S.zero B)
    (hB : ∀ j, j < d → ZKron.Bd S.toOH (v j) B)
    (i : Nat) (hrow : dle (dsum (fun j => dabs (Mdy d Y Z i j)) d) hD = true) :
    ZKron.Bd S.toOH (sumS S (fun j => S.mul (dv S.toOH (Mdy d Y Z i j)) (v j)) d) (S.mul (hp S.toOH 1) B) := by
  have b := sumS_bd (S := S) (f := fun j => S.mul (dv S.toOH (Mdy d Y Z i j)) (v j))
    (g := fun j => S.mul (dv S.toOH (dabs (Mdy d Y Z i j))) B) (fun j hj =>
      prod_bd S (dabs_bd S _).1 (dabs_bd S _).2 (hB j hj))
  have e := S.trans (S.symm (sumS_mulR S B (fun j => dv S.toOH (dabs (Mdy d Y Z i j))) d))
    (S.mul_congr (S.symm (dv_dsum S (fun j => dabs (Mdy d Y Z i j)) d)) (S.refl _))
  have l := le_mul_right S.toOH (S.le_respects (S.refl _) (ZRootPVR.dv_hp_gen S 1) (dle_sound S.toOH hrow)) B0
  exact bd_widen S (ZKron.bd_congr S.toOH (S.refl _) e b) l

end Lin


/-! ## On VR's continuum -/

theorem real_bound (x : RExpr) : ∃ C, ZKron.Bd rCF.toOH x (nI rOH (2 ^ C)) := by
  obtain ⟨B, N, hb⟩ := rbounded x
  have e : ∀ m, qEq ((nI rOH (2 ^ B)).seq m) (qofInt (pow2 B)) := fun m => qEq_trans (num_seq (2 ^ B) m) (ZLn.qnat_pow2 B)
  refine ⟨B, rle_of_eventually N (fun n hn => ?_), rle_of_eventually N (fun n hn => ?_)⟩
  · obtain ⟨h1, h2⟩ := hb n hn
    have := e n
    change qle (qneg ((nI rOH (2 ^ B)).seq n)) (x.seq n)
    unfold qsub at h1 h2; rat_linarith
  · obtain ⟨h1, h2⟩ := hb n hn
    have := e n
    change qle (x.seq n) ((nI rOH (2 ^ B)).seq n)
    unfold qsub at h1 h2; rat_linarith

theorem vec_bound (v : Vec) : ∀ d, ∃ C, ∀ j, j < d → ZKron.Bd rCF.toOH (v j) (nI rOH (2 ^ C))
  | 0 => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | d + 1 => by
      obtain ⟨C1, h1⟩ := vec_bound v d
      obtain ⟨C2, h2⟩ := real_bound (v d)
      have m1 : rle (nI rOH (2 ^ C1)) (nI rOH (2 ^ (C1 + C2))) :=
        nI_le rOH (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
      have m2 : rle (nI rOH (2 ^ C2)) (nI rOH (2 ^ (C1 + C2))) :=
        nI_le rOH (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
      refine ⟨C1 + C2, fun j hj => ?_⟩
      cases Nat.lt_or_ge j d with
      | inl hlt => exact bd_widen rCF (h1 j hlt) m1
      | inr hge =>
          have e : j = d := Nat.le_antisymm (Nat.le_of_lt_succ hj) hge
          subst e; exact bd_widen rCF h2 m2

/-- **`Y` IS INVERTIBLE**: `Y·v = 0` gives `v = 0`, under the dyadic check `chkZ`. -/
theorem lin_inj {d : Nat} {Y Z : Nat → Nat → D} (hz : chkZ d Y Z = true) (v : Vec)
    (hv : ∀ k, k < d → rEq (sumS rCF (fun j => rmul (dv rOH (Y k j)) (v j)) d) rzero) : ∀ i, i < d → rEq (v i) rzero := by
  have fix : ∀ i, i < d → rEq (v i) (sumS rCF (fun j => rmul (dv rOH (Mdy d Y Z i j)) (v j)) d) := by
    intro i hi
    have z : rEq (sumS rCF (fun k => rmul (dv rOH (Z i k)) (sumS rCF (fun j => rmul (dv rOH (Y k j)) (v j)) d)) d) rzero :=
      sumS_zero (S := rCF) (fun k hk => rEq_trans (rmul_respects (rEq_refl _) (hv k hk)) (rmul_zero _))
    refine rEq_symm (rEq_trans (lin_expand rCF d Y Z v i hi) ?_)
    exact rEq_trans (radd_respects (rEq_refl _) (rneg_respects z)) (rEq_trans (radd_respects (rEq_refl _)
      (rEq_of_seq fun _ => qEq_refl _)) (radd_zero _))
  obtain ⟨C, hC⟩ := vec_bound v d
  have iter : ∀ t, ∀ i, i < d → ZKron.Bd rCF.toOH (v i) (rmul (hp rOH t) (nI rOH (2 ^ C))) := by
    intro t
    induction t with
    | zero => exact fun i hi => ZKron.bd_congr rCF.toOH (rCF.refl _) (rEq_symm (rone_mul _)) (hC i hi)
    | succ t ih =>
        intro i hi
        have B0 : rle rzero (rmul (hp rOH t) (nI rOH (2 ^ C))) := rCF.mul_nonneg (hp_nonneg rOH t) (nI_nonneg rOH _)
        have hl := lin_half rCF d Y Z v B0 ih i (allB_sound hz i hi)
        refine ZKron.bd_congr rCF.toOH (rEq_symm (fix i hi)) ?_ hl
        exact rEq_trans (rEq_symm (rmul_assoc _ _ _)) (rmul_respects (half_hp rCF t) (rEq_refl _))
  intro i hi
  apply eq_of_bd_all rCF ZRootVR.vr_complete
  intro J
  exact ZKron.bd_congr rCF.toOH (rCF.refl _) (rEq_trans (rmul_comm _ _) (ZRootPar.twoL J C)) (iter (J + C) i hi)

/-- A dyadic matrix from rows. -/
def nthR : List (List D) → Nat → List D
  | [], _ => []
  | a :: _, 0 => a
  | _ :: as, n + 1 => nthR as n
def mat (M : List (List D)) (i j : Nat) : D := nthD (nthR M i) j

/-! ## The system -/

def sumX (f : Nat → XE) : Nat → XE
  | 0 => .cst dz0
  | n + 1 => .add (sumX f n) (f n)

/-- `G(x) = x − Y·F(x)`. -/
def Gsys (d : Nat) (Y : Nat → Nat → D) (Fs : Nat → XE) : Nat → XE :=
  fun k => .sub (.var k) (sumX (fun j => .mul (.cst (Y k j)) (Fs j)) d)

theorem evR_sumX (env : Vec) (f : Nat → XE) : ∀ n, rEq (evR env (sumX f n)) (sumS rCF (fun j => evR env (f j)) n)
  | 0 => dv_dz0 (S := rCF)
  | n + 1 => radd_respects (evR_sumX env f n) (rEq_refl _)

theorem G_val {d : Nat} {Y : Nat → Nat → D} {Fs : Nat → XE} (u : Vec) {k : Nat} (hk : k < d) :
    rEq (evR (trunc d u) (Gsys d Y Fs k)) (radd (u k) (rneg (sumS rCF (fun j => rmul (dv rOH (Y k j)) (evR (trunc d u) (Fs j))) d))) := by
  show rEq (radd (trunc d u k) (rneg (evR (trunc d u) (sumX (fun j => .mul (.cst (Y k j)) (Fs j)) d)))) _
  rw [trunc_lt hk]
  exact radd_respects (rEq_refl _) (rneg_respects (evR_sumX _ _ d))

/-- **A SYSTEM OF LAWS HAS ITS SOLUTION ON VR's CONTINUUM — and only one in the cube**, under the kernel-checked
certificates `chkK` (Krawczyk, for `G = x − Y·F`) and `chkZ` (`Y` invertible). -/
theorem sys_root {d : Nat} {ys : List D} {r rh : D} {R E : Nat} {Y Z : Nat → Nat → D} {Fs : Nat → XE}
    (h : chkK d ys r rh R E (Gsys d Y Fs) = true) (hz : chkZ d Y Z = true) :
    ∃ x : Vec, InC d ys r x ∧ (∀ i, i < d → rEq (evR (trunc d x) (Fs i)) rzero) ∧
      ∀ u, InC d ys r u → (∀ i, i < d → rEq (evR (trunc d u) (Fs i)) rzero) → ∀ i, i < d → rEq (u i) (x i) := by
  obtain ⟨x, hx, hf, hu⟩ := krawczyk h
  refine ⟨x, hx, ?_, fun u hu' hF => hu u hu' (fun k hk => ?_)⟩
  · apply lin_inj hz
    intro k hk
    exact sub_self_zero rCF (rEq_trans (rEq_symm (G_val x hk)) (hf k hk))
  · refine rEq_trans (G_val u hk) ?_
    have z : rEq (sumS rCF (fun j => rmul (dv rOH (Y k j)) (evR (trunc d u) (Fs j))) d) rzero :=
      sumS_zero (S := rCF) (fun j hj => rEq_trans (rmul_respects (rEq_refl _) (hF j hj)) (rmul_zero _))
    exact rEq_trans (radd_respects (rEq_refl _) (rneg_respects z)) (rEq_trans (radd_respects (rEq_refl _)
      (rEq_of_seq fun _ => qEq_refl _)) (radd_zero _))

end ZKrawSys

#print axioms ZKrawSys.sumS_swap
#print axioms ZKrawSys.sumS_kron
#print axioms ZKrawSys.sumS_bd
#print axioms ZKrawSys.lin_inj
#print axioms ZKrawSys.sys_root
