import ZRootPar
/-!
# ZBanach — a contraction with an approximate rational oracle has its fixed point on VR's continuum, in any finite
dimension, and only one in its box. Zero axioms.

Step 3 of the root programme (multidimensional existence). The constructive route is the CONTRACTION form of
Krawczyk's test: `G(x) = x − Y·F(x)` maps the box into itself (with a margin) and halves sup-distances, so its
iterates converge; the fixed point is a zero of `F` (a separate check makes `Y` invertible). No fixed-point theorem of
Brouwer's kind is used (that is not constructive); the limit is built without choice:

* the ORACLE `gₙ` approximates `G` on rational vectors of the box, uniformly, from some level on (Prop-existential);
* the `n`-th approximant is `gₙ` iterated `n` times from the centre: a RATIONAL vector `rₙ`;
* `rₙ` tracks the real iterates `Gᵏ(y)` within `2⁻ʲ` (the halving absorbs the oracle's error), and those are Cauchy
  (`2ᴱ·2⁻ᵏ`), so `rₙ` is Cauchy: its limit `x*` is a VR real vector, in the box (closed), `G(x*) = x*`, unique.
-/

namespace ZBanach
open VR VR.Numbers VR.CSR ZNumBin ZField ZRealCF ZExp ZRealExp ZRootPVR

/-! ## Generic bounds (any `CF`) -/

section G
variable {α : Type} (S : CF α)

theorem bd_tri {a b c δ1 δ2 : α} (h1 : ZKron.Bd S.toOH (S.add a (S.neg b)) δ1) (h2 : ZKron.Bd S.toOH (S.add b (S.neg c)) δ2) :
    ZKron.Bd S.toOH (S.add a (S.neg c)) (S.add δ1 δ2) := by
  obtain ⟨a1, a2⟩ := h1; obtain ⟨b1, b2⟩ := h2
  exact ⟨by cr_linarith S.toOCR [a1, b1], by cr_linarith S.toOCR [a2, b2]⟩

theorem bd_refl {a δ : α} (h : S.le S.zero δ) : ZKron.Bd S.toOH (S.add a (S.neg a)) δ :=
  ⟨by cr_linarith S.toOCR [h], by cr_linarith S.toOCR [h]⟩

theorem bd_eq {a b δ : α} (e : S.r a b) (h : S.le S.zero δ) : ZKron.Bd S.toOH (S.add a (S.neg b)) δ :=
  ZKron.bd_congr S.toOH (S.add_congr (S.refl _) (S.neg_congr e)) (S.refl _) (bd_refl S h)

theorem four_hp (J : Nat) : S.r (S.add (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))))
    (hp S.toOH J) := by
  have e1 := ZRoot.hp_succ_half S (J + 1)
  have e2 := ZRoot.hp_succ_half S J
  exact S.trans (S.add_congr e1 e1) e2

/-- Bounded by every `2⁻ʲ`: zero. -/
theorem eq_of_bd_all {u : α} (hc : ZRoot.Complete S) (h : ∀ j, ZKron.Bd S.toOH u (hp S.toOH j)) : S.r u S.zero := by
  apply S.ap_tight
  intro hap
  cases hap with
  | inl hpos =>
      obtain ⟨J, hJ⟩ := hc.arch hpos
      exact contra_hp S hJ (h (J + 1)).2
  | inr hneg =>
      obtain ⟨J, hJ⟩ := hc.arch hneg
      have l := (h (J + 1)).1
      exact contra_hp S hJ (by cr_linarith S.toOCR [l])

theorem half_hp (j : Nat) : S.r (S.mul (hp S.toOH 1) (hp S.toOH j)) (hp S.toOH (j + 1)) :=
  S.trans (S.symm (hp_add S.toOH 1 j)) (by rw [Nat.add_comm 1 j]; exact S.refl _)

theorem pos_nI (E : Nat) : S.pos (nI S.toOH (2 ^ E)) := by
  have l := nI_le S.toOH (Nat.two_pow_pos E)
  have one : S.r (nI S.toOH 1) S.one := by show S.r (S.add S.one S.zero) S.one; cr_ring S.toCR
  exact S.pos_mono (pos_one S) (S.le_respects one (S.refl _) l)

theorem nI_hp0 (E : Nat) : S.r (nI S.toOH (2 ^ E)) (S.mul (nI S.toOH (2 ^ E)) (hp S.toOH 0)) :=
  S.symm (S.trans (S.mul_comm _ _) (S.one_mul _))

theorem half_step (n h : α) (k : Nat) : S.r (S.mul (hp S.toOH 1) (S.mul n h)) (S.mul n (S.mul (hp S.toOH 1) h)) := by
  cr_ring S.toCR

/-- The invariant's step: `n·h + (n·A − n·(h + h)) ≈ n·A − n·(g + g)` when `g + g ≈ h`. -/
theorem beta_step {n h g A : α} (e : S.r (S.add g g) h) :
    S.r (S.add (S.mul n h) (S.add (S.mul n A) (S.neg (S.mul n (S.add h h))))) (S.add (S.mul n A) (S.neg (S.mul n (S.add g g)))) := by
  refine S.trans ?_ (S.add_congr (S.refl _) (S.neg_congr (S.mul_congr (S.refl _) (S.symm e))))
  cr_ring S.toCR

theorem beta_le {n A h : α} (hn : S.le S.zero n) (hh : S.le S.zero h) :
    S.le (S.add (S.mul n A) (S.neg (S.mul n (S.add h h)))) (S.mul n A) := by
  have p := S.mul_nonneg hn (OCR.nonneg_add S.toOCR hh hh)
  cr_linarith S.toOCR [p]

/-- Four pieces each below `2⁻⁽ᴶ⁺²⁾` stay below `2⁻ᴶ`. -/
theorem four_le {a b n h : α} (J : Nat) (ha : S.le a (hp S.toOH (J + 2))) (hb : S.le b (hp S.toOH (J + 2)))
    (hnh : S.le (S.mul n h) (hp S.toOH (J + 2))) : S.le (S.add a (S.add (S.mul n (S.add h h)) b)) (hp S.toOH J) := by
  have e := four_hp S J
  have d : S.r (S.mul n (S.add h h)) (S.add (S.mul n h) (S.mul n h)) := by cr_ring S.toCR
  have l : S.le (S.add a (S.add (S.mul n (S.add h h)) b))
      (S.add (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) := by
    cr_linarith S.toOCR [ha, hb, hnh]
  exact S.le_respects (S.refl _) e l

theorem four_le' {a b n h : α} (J : Nat) (ha : S.le a (hp S.toOH (J + 2))) (hb : S.le b (hp S.toOH (J + 2)))
    (hnh : S.le (S.mul n h) (hp S.toOH (J + 2))) : S.le (S.add a (S.add b (S.mul n (S.add h h)))) (hp S.toOH J) :=
  S.le_respects (S.add_congr (S.refl _) (S.add_comm _ _)) (S.refl _) (four_le S J ha hb hnh)

theorem sub_zero_eq {a b : α} (h : S.r (S.add a (S.neg b)) S.zero) : S.r a b :=
  S.trans (by cr_ring S.toCR : S.r a (S.add (S.add a (S.neg b)) b)) (S.trans (S.add_congr h (S.refl _)) (S.zero_add _))

theorem two_le {a b : α} (J : Nat) (ha : S.le a (hp S.toOH (J + 1))) (hb : S.le b (hp S.toOH (J + 1))) :
    S.le (S.add a b) (hp S.toOH J) := by
  have e := ZRoot.hp_succ_half S J
  have l : S.le (S.add a b) (S.add (hp S.toOH (J + 1)) (hp S.toOH (J + 1))) := by cr_linarith S.toOCR [ha, hb]
  exact S.le_respects (S.refl _) e l

theorem half_le {δ : α} (h : S.le S.zero δ) : S.le (S.mul (hp S.toOH 1) δ) δ := by
  have l := le_mul_right S.toOH (ZRootPVR.hp_le_one S 1) h
  exact S.le_respects (S.refl _) (S.one_mul _) l

end G

/-! ## Vectors and sup-closeness on the first `d` coordinates -/

abbrev Vec := Nat → RExpr

def Cl (d : Nat) (u v : Vec) (δ : RExpr) : Prop := ∀ i, i < d → ZKron.Bd rCF.toOH (radd (u i) (rneg (v i))) δ

theorem cl_tri {d : Nat} {u v w : Vec} {δ1 δ2 : RExpr} (h1 : Cl d u v δ1) (h2 : Cl d v w δ2) : Cl d u w (radd δ1 δ2) :=
  fun i hi => bd_tri rCF (h1 i hi) (h2 i hi)

theorem cl_mono {d : Nat} {u v : Vec} {δ δ' : RExpr} (h : Cl d u v δ) (e : rle δ δ') : Cl d u v δ' :=
  fun i hi => bd_widen rCF (h i hi) e

theorem cl_congr {d : Nat} {u v : Vec} {δ δ' : RExpr} (h : Cl d u v δ) (e : rEq δ δ') : Cl d u v δ' :=
  fun i hi => ZKron.bd_congr rCF.toOH (rCF.refl _) e (h i hi)

theorem cl_symm {d : Nat} {u v : Vec} {δ : RExpr} (h : Cl d u v δ) : Cl d v u δ :=
  fun i hi => ZRootPar.bd_swap rCF (h i hi)

theorem cl_refl {d : Nat} {u : Vec} {δ : RExpr} (h : rle rzero δ) : Cl d u u δ := fun _ _ => bd_refl rCF h

/-- Finitely many coordinates have a common index. -/
theorem common_d {P : Nat → Nat → Prop} : ∀ d : Nat, (∀ i, i < d → ∃ N, ∀ n, N ≤ n → P i n) →
    ∃ N, ∀ n, N ≤ n → ∀ i, i < d → P i n
  | 0, _ => ⟨0, fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | d + 1, h => by
      obtain ⟨N1, h1⟩ := common_d d (fun i hi => h i (Nat.lt_succ_of_lt hi))
      obtain ⟨N2, h2⟩ := h d (Nat.lt_succ_self d)
      refine ⟨N1 + N2, fun n hn i hi => ?_⟩
      cases Nat.lt_or_ge i d with
      | inl hlt => exact h1 n (ZRootExp.lA hn) i hlt
      | inr hge =>
          have e : i = d := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
          subst e
          exact h2 n (ZRootExp.lB hn)

/-! ## From a real bound between constants to a rational one -/

theorem qclose_of_bd {a b : QExpr} {j : Nat} (h : ZKron.Bd rCF.toOH (radd (rofQ a) (rneg (rofQ b))) (hp rOH j)) :
    qclose a b (qeps j) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : rEq (hp rOH j) (rofQ (qeps j)) := rEq_of_seq (fun m => hp_seq j m)
  have l1 : rle (rofQ (qneg (qeps j))) (rofQ (qsub a b)) :=
    rle_respects (rEq_trans (rneg_respects e1) (rEq_of_seq fun _ => qEq_refl _)) (rEq_of_seq fun _ => qEq_refl _) h1
  have l2 : rle (rofQ (qsub a b)) (rofQ (qeps j)) := rle_respects (rEq_of_seq fun _ => qEq_refl _) e1 h2
  exact ⟨ZRootExp.q_of_rle l2, ZRootExp.q_of_rle l1⟩

/-! ## The contraction with an oracle -/

theorem hp_le {a b : Nat} (h : a ≤ b) : rle (hp rOH b) (hp rOH a) := by
  obtain ⟨t, rfl⟩ := le_ex h
  exact hp_anti rCF a t

theorem bound4 (E J n : Nat) (hn : J + 2 + E ≤ n) :
    rle (rmul (nI rOH (2 ^ E)) (hp rOH n)) (hp rOH (J + 2)) :=
  rCF.le_trans (ZIv.le_mul_left' rCF (hp_le hn) (nI_nonneg rOH _)) (rCF.le_respects (rCF.symm (ZRootPar.twoL (J + 2) E))
    (rCF.refl _) (rCF.le_refl _))

/-- The hypotheses: the box `In` (first `d` coordinates), the map `Gv`, its rational oracle `gv`, the centre `y0`, the
margin `2⁻ᴿ` of the mapping-into, the diameter `2ᴱ`. -/
structure KS (d : Nat) (Gv : Vec → Vec) (gv : Nat → (Nat → QExpr) → Nat → QExpr) (In : Vec → Prop)
    (y0 : Nat → QExpr) (R E : Nat) : Prop where
  into : ∀ u w, In u → Cl d w (Gv u) (hp rOH R) → In w
  contr : ∀ u v δ, In u → In v → rlt rzero δ → Cl d u v δ → Cl d (Gv u) (Gv v) (rmul (hp rOH 1) δ)
  orac : ∀ j, ∃ N, ∀ n, N ≤ n → ∀ z : Nat → QExpr, In (fun i => rofQ (z i)) →
    Cl d (fun i => rofQ (gv n z i)) (Gv (fun i => rofQ (z i))) (hp rOH j)
  center : In (fun i => rofQ (y0 i))
  diam : ∀ u v, In u → In v → Cl d u v (nI rOH (2 ^ E))
  closed : ∀ u, (∀ j, ∃ w, In w ∧ Cl d u w (hp rOH j)) → In u
  out : ∀ n z i, d ≤ i → gv n z i = qzero

section K
variable {d : Nat} {Gv : Vec → Vec} {gv : Nat → (Nat → QExpr) → Nat → QExpr} {In : Vec → Prop}
  {y0 : Nat → QExpr} {R E : Nat}

/-- The oracle at level `n`, iterated `k` times from the centre. -/
def it (gv : Nat → (Nat → QExpr) → Nat → QExpr) (y0 : Nat → QExpr) (n : Nat) : Nat → Nat → QExpr
  | 0 => y0
  | k + 1 => gv n (it gv y0 n k)

/-- The real iterates. -/
def X (Gv : Vec → Vec) (y0 : Nat → QExpr) : Nat → Vec
  | 0 => fun i => rofQ (y0 i)
  | k + 1 => Gv (X Gv y0 k)

variable (H : KS d Gv gv In y0 R E)
include H

theorem X_in : ∀ k, In (X Gv y0 k)
  | 0 => H.center
  | k + 1 => H.into _ _ (X_in k) (cl_refl (hp_nonneg rOH R))

/-- **THE RATIONAL ITERATES TRACK THE REAL ONES** within `2⁻ʲ` (the halving absorbs the oracle's error). -/
theorem track {j : Nat} (hj : R ≤ j) : ∃ N, ∀ n, N ≤ n → ∀ k,
    In (fun i => rofQ (it gv y0 n k i)) ∧ Cl d (fun i => rofQ (it gv y0 n k i)) (X Gv y0 k) (hp rOH j) := by
  obtain ⟨N, hN⟩ := H.orac (j + 1)
  refine ⟨N, fun n hn k => ?_⟩
  induction k with
  | zero => exact ⟨H.center, cl_refl (hp_nonneg rOH j)⟩
  | succ k ih =>
      obtain ⟨hi, hc⟩ := ih
      have o := hN n hn (it gv y0 n k) hi
      have c := cl_congr (H.contr _ _ (hp rOH j) hi (X_in H k) (ZNone.pos_hp rCF j) hc) (half_hp rCF j)
      exact ⟨H.into _ _ hi (cl_mono o (hp_le (Nat.le_succ_of_le hj))),
        cl_congr (cl_tri o c) (ZRoot.hp_succ_half rCF j)⟩

theorem X_step : ∀ k, Cl d (X Gv y0 (k + 1)) (X Gv y0 k) (rmul (nI rOH (2 ^ E)) (hp rOH k))
  | 0 => cl_congr (H.diam _ _ (X_in H 1) (X_in H 0)) (nI_hp0 rCF E)
  | k + 1 => by
      have pδ : rlt rzero (rmul (nI rOH (2 ^ E)) (hp rOH k)) := rCF.pos_mul (pos_nI rCF E) (ZNone.pos_hp rCF k)
      have c := H.contr _ _ _ (X_in H (k + 1)) (X_in H k) pδ (X_step k)
      exact cl_congr c (rCF.trans (half_step rCF _ _ k) (rCF.mul_congr (rCF.refl _) (half_hp rCF k)))

/-- The real iterates are Cauchy: `|X(k+t) − X(k)| ≤ 2ᴱ·2·2⁻ᵏ`. -/
theorem X_far (k : Nat) : ∀ t, Cl d (X Gv y0 (k + t)) (X Gv y0 k) (rmul (nI rOH (2 ^ E)) (radd (hp rOH k) (hp rOH k))) := by
  have inv : ∀ t, Cl d (X Gv y0 (k + t)) (X Gv y0 k) (radd (rmul (nI rOH (2 ^ E)) (radd (hp rOH k) (hp rOH k)))
      (rneg (rmul (nI rOH (2 ^ E)) (radd (hp rOH (k + t)) (hp rOH (k + t)))))) := by
    intro t
    induction t with
    | zero =>
        exact fun i _ => bd_eq rCF (rCF.refl _) (rCF.le_respects (rCF.refl _) (rCF.symm (rCF.add_neg _)) (rCF.le_refl _))
    | succ t ih =>
        exact cl_congr (cl_tri (X_step H (k + t)) ih) (beta_step rCF (ZRoot.hp_succ_half rCF (k + t)))
  exact fun t => cl_mono (inv t) (beta_le rCF (nI_nonneg rOH _) (hp_nonneg rOH _))

/-- The `n`-th approximant: the level-`n` oracle iterated `n` times. -/
def rq (gv : Nat → (Nat → QExpr) → Nat → QExpr) (y0 : Nat → QExpr) (n : Nat) : Nat → QExpr := it gv y0 n n

theorem rq_cauchy (i : Nat) : ∀ J, ∃ M, ∀ m n, M ≤ m → M ≤ n → qclose (rq gv y0 m i) (rq gv y0 n i) (qeps J) := by
  intro J
  cases Nat.lt_or_ge i d with
  | inr hge =>
      have z : ∀ m, 1 ≤ m → rq gv y0 m i = qzero := by
        intro m hm
        cases m with
        | zero => exact absurd hm (Nat.not_succ_le_zero _)
        | succ m' => exact H.out _ _ i hge
      refine ⟨1, fun m n hm hn => ?_⟩
      rw [z m hm, z n hn]; exact qclose_refl _ _ (qeps_nonneg J)
  | inl hlt =>
      obtain ⟨N, hN⟩ := track H (j := J + 2 + R) (Nat.le_add_left _ _)
      have hq : rle (hp rOH (J + 2 + R)) (hp rOH (J + 2)) := hp_le (Nat.le_add_right _ _)
      have key : ∀ m n, N + (J + 2 + E) ≤ m → m ≤ n → qclose (rq gv y0 m i) (rq gv y0 n i) (qeps J) := by
        intro m n hm hmn
        obtain ⟨t, rfl⟩ := le_ex hmn
        have a := (hN m (ZRootExp.lA hm) m).2
        have b := cl_symm (X_far H m t)
        have c := cl_symm (hN (m + t) (Nat.le_trans (ZRootExp.lA hm) (Nat.le_add_right _ _)) (m + t)).2
        have bd := (cl_tri a (cl_tri b c)) i hlt
        apply qclose_of_bd
        exact bd_widen rCF bd (four_le rCF J hq hq (bound4 E J m (ZRootExp.lB hm)))
      refine ⟨N + (J + 2 + E), fun m n hm hn => ?_⟩
      cases Nat.le_total m n with
      | inl h => exact key m n hm h
      | inr h => exact qclose_symm (key n m hn h)

/-- **THE FIXED POINT**: the limit of the rational approximants. -/
def xs (H : KS d Gv gv In y0 R E) : Vec := fun i => ⟨fun n => rq gv y0 n i, rq_cauchy H i⟩

theorem near (J k : Nat) (hk : J + 2 + E ≤ k) : Cl d (xs H) (X Gv y0 k) (hp rOH J) := by
  obtain ⟨N1, h1⟩ := common_d (P := fun i n => ZKron.Bd rCF.toOH (radd (xs H i) (rneg (rofQ ((xs H i).seq n))))
    (hp rOH (J + 2))) d (fun i _ => approx_close (xs H i) (J + 2))
  obtain ⟨N2, h2⟩ := track H (j := J + 2 + R) (Nat.le_add_left _ _)
  have hq : rle (hp rOH (J + 2 + R)) (hp rOH (J + 2)) := hp_le (Nat.le_add_right _ _)
  have a : Cl d (xs H) (fun i => rofQ (rq gv y0 (k + (N1 + N2)) i)) (hp rOH (J + 2)) :=
    fun i hi => h1 _ (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_left _ _)) i hi
  have b := (h2 (k + (N1 + N2)) (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_left _ _)) (k + (N1 + N2))).2
  have c := X_far H k (N1 + N2)
  exact cl_mono (cl_tri a (cl_tri b c)) (four_le' rCF J (rCF.le_refl _) hq (bound4 E J k hk))

theorem xs_in : In (xs H) :=
  H.closed (xs H) (fun j => ⟨X Gv y0 (j + 2 + E), X_in H _, near H j (j + 2 + E) (Nat.le_refl _)⟩)

/-- **`G(x*) = x*`.** -/
theorem xs_fixed : ∀ i, i < d → rEq (Gv (xs H) i) (xs H i) := by
  intro i hi
  apply sub_zero_eq rCF
  apply eq_of_bd_all rCF ZRootVR.vr_complete
  intro J
  have n1 := near H (J + 1) (J + 1 + 2 + E) (Nat.le_refl _)
  have c := H.contr _ _ _ (xs_in H) (X_in H _) (ZNone.pos_hp rCF (J + 1)) n1
  have n2 := cl_symm (near H (J + 1) (J + 1 + 2 + E + 1) (Nat.le_succ _))
  have t := cl_tri c n2
  exact bd_widen rCF (t i hi) (two_le rCF J (half_le rCF (hp_nonneg rOH _)) (rCF.le_refl _))

/-- **ONLY ONE** fixed point in the box. -/
theorem xs_unique (u : Vec) (hu : In u) (hf : ∀ i, i < d → rEq (Gv u i) (u i)) : ∀ i, i < d → rEq (u i) (xs H i) := by
  have fx := xs_fixed H
  have claim : ∀ t, Cl d u (xs H) (rmul (nI rOH (2 ^ E)) (hp rOH t)) := by
    intro t
    induction t with
    | zero => exact cl_congr (H.diam u (xs H) hu (xs_in H)) (nI_hp0 rCF E)
    | succ t ih =>
        have pδ : rlt rzero (rmul (nI rOH (2 ^ E)) (hp rOH t)) := rCF.pos_mul (pos_nI rCF E) (ZNone.pos_hp rCF t)
        have c := H.contr _ _ _ hu (xs_in H) pδ ih
        exact fun i hi => ZKron.bd_congr rCF.toOH (rCF.add_congr (hf i hi) (rCF.neg_congr (fx i hi)))
          (rCF.trans (half_step rCF _ _ t) (rCF.mul_congr (rCF.refl _) (half_hp rCF t))) (c i hi)
  intro i hi
  apply sub_zero_eq rCF
  apply eq_of_bd_all rCF ZRootVR.vr_complete
  intro J
  exact ZKron.bd_congr rCF.toOH (rCF.refl _) (ZRootPar.twoL J E) (claim (J + E) i hi)

/-- **A CONTRACTION OF A BOX WITH AN APPROXIMATE RATIONAL ORACLE HAS ITS FIXED POINT ON VR's CONTINUUM — and only one
in the box.** -/
theorem banach : ∃ x : Vec, In x ∧ (∀ i, i < d → rEq (Gv x i) (x i)) ∧
    ∀ u, In u → (∀ i, i < d → rEq (Gv u i) (u i)) → ∀ i, i < d → rEq (u i) (x i) :=
  ⟨xs H, xs_in H, xs_fixed H, xs_unique H⟩

end K

end ZBanach

#print axioms ZBanach.eq_of_bd_all
#print axioms ZBanach.qclose_of_bd
#print axioms ZBanach.common_d
#print axioms ZBanach.track
#print axioms ZBanach.X_far
#print axioms ZBanach.rq_cauchy
#print axioms ZBanach.near
#print axioms ZBanach.banach
