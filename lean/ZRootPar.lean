import ZRootDiv
/-!
# ZRootPar — roots of laws with REAL PARAMETERS (exp, ln, division, fractional powers) on VR's continuum.
Zero axioms.

Step 2c of the root programme. A law `F(x, p)` with parameters `pᵢ` on dyadic intervals (`ZRootPVR.PS`): for EVERY
real parameter vector `p` in the inner box (`InnerIn μ`), the law has a root in `[a, b]`, and only one.

The family for `ZRootAbs.Fam`: `Fₙ(x) = F(x, p⁽ⁿ⁾)` with the `n`-th rational approximants of the parameters
(`ZRootPVR.pn`), `F_p(x) = F(x, p)`.
* MONOTONE in `x` on the box: the slope reading with directions `Vx` (`x` moves, the parameters do not).
* UNIFORMLY CLOSE (`conv`): the SAME slope reading with directions `Vp` (`x` fixed, each parameter moves by
  `s·δ`, `s ∈ [−1, 1]`) gives `|Fₙ(x) − F_p(x)| ≤ 2ᴸ·δ` — a Lipschitz bound in the parameters, read by the kernel.
* THE ORACLE: the rational reading with the parameters' `n`-th terms; uniformly Cauchy on the bounded set of
  environments (`ZRootDiv.uc_evqD`).
* COVERS (`chkT`, `tree_root`): a wide box split by a tree of overlapping cuts; a real parameter is placed in a part
  by cotransitivity, not by a decision.

Generated instances: `ZPumpRoot` (the pump, Swamee–Jain, 10 parameters), `ZOilRoot` (the oil cooler, ε-NTU,
16-box cover) — `tools/zlaw2lean.py`.
-/

namespace ZRootPar
open VR VR.Numbers VR.CSR ZNumBin ZField ZPoly ZIv ZDivIv ZExpLaw ZExpIv ZXE ZRealCF ZExp ZRealExp ZRootExp ZRootDiv
  ZRootPVR

/-! ## Generic pieces (any `CF`) -/

/-- `[−1, 1]`. -/
def pm1 : Iv := (dneg ZRootExp.d1, ZRootExp.d1)

section G
variable {α : Type} (S : CF α)

theorem dv_d1 : S.r (dv S.toOH ZRootExp.d1) S.one := by
  show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) S.one
  cr_ring S.toCR

theorem mem_pm1 {s : α} (h1 : S.le (S.neg S.one) s) (h2 : S.le s S.one) : Mem S s pm1 :=
  ⟨S.le_respects (S.symm (S.trans (dv_neg S.toOH _) (S.neg_congr (dv_d1 S)))) (S.refl _) h1,
   S.le_respects (S.refl _) (S.symm (dv_d1 S)) h2⟩

/-- A difference bounded by `δ > 0` is `s·δ` with `s ∈ [−1, 1]`. -/
theorem sl_of_bd {u δ : α} (hb : ZKron.Bd S.toOH u δ) (hδ : S.pos δ) : SlIn S u δ pm1 := by
  intro hn
  obtain ⟨t, ht⟩ := S.inv (Or.inl hδ)
  have t0 := inv_nonneg hδ ht
  have l1 := le_mul_left' S hb.1 t0
  have l2 := le_mul_left' S hb.2 t0
  have e1 : S.r (S.mul t (S.neg δ)) (S.neg S.one) :=
    S.trans (by cr_ring S.toCR : S.r _ (S.neg (S.mul δ t))) (S.neg_congr ht)
  have e2 : S.r (S.mul t δ) S.one := S.trans (S.mul_comm _ _) ht
  have e3 : S.r (S.mul t u) (S.mul u t) := S.mul_comm _ _
  refine hn ⟨S.mul u t, mem_pm1 S (S.le_respects e1 e3 l1) (S.le_respects e3 e2 l2), ?_⟩
  refine S.symm (S.trans (by cr_ring S.toCR : S.r _ (S.mul u (S.mul δ t))) ?_)
  exact S.trans (S.mul_congr (S.refl _) ht) (S.trans (S.mul_comm _ _) (S.one_mul _))

/-- A slope reading inside `[−M, M]` bounds the difference by `M·δ`. -/
theorem bd_of_sl {Δ δ M : α} {K : Iv} (h : SlIn S Δ δ K) (hδ0 : S.le S.zero δ)
    (h1 : S.le (S.neg M) (dv S.toOH K.1)) (h2 : S.le (dv S.toOH K.2) M) : ZKron.Bd S.toOH Δ (S.mul M δ) := by
  constructor
  · apply S.le_of_not_pos
    intro hpos
    apply h
    intro ⟨s, hs, he⟩
    have l := le_mul_left' S (S.le_trans h1 hs.1) hδ0
    have l' : S.le (S.neg (S.mul M δ)) Δ :=
      S.le_respects (by cr_ring S.toCR) (S.trans (S.mul_comm _ _) (S.symm he)) l
    exact S.pos_not_le hpos (by cr_linarith S.toOCR [l'])
  · apply S.le_of_not_pos
    intro hpos
    apply h
    intro ⟨s, hs, he⟩
    have l := le_mul_left' S (S.le_trans hs.2 h2) hδ0
    have l' : S.le Δ (S.mul M δ) :=
      S.le_respects (S.trans (S.mul_comm _ _) (S.symm he)) (S.mul_comm _ _) l
    exact S.pos_not_le hpos (by cr_linarith S.toOCR [l'])

theorem bd_neg {u δ : α} (h : ZKron.Bd S.toOH u δ) : ZKron.Bd S.toOH (S.neg u) δ := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by cr_linarith S.toOCR [h2], by cr_linarith S.toOCR [h1]⟩

/-- **MONOTONE WITH THE READ SLOPES**, for a family of environments `env x` moving along `x`. -/
theorem mono_gen {ex : α → α} (H : ExpLaws S ex) (Hs : ExpSlope S ex) {e : XE} {F : α → α}
    {env : α → Nat → α} {B : Box} {V : Nat → Iv} {a b c L : α}
    (hin : ∀ x, S.le a x → S.le x b → InBox S B (env x))
    (hval : ∀ x, S.le a x → S.le x b → Val S ex (env x) e (F x))
    (hd : ∀ x y, ∀ i, SlIn S (S.add (env y i) (S.neg (env x i))) (S.add y (S.neg x)) (V i))
    {K : Iv} (hK : slX B V e = some K) (hc : S.le c (dv S.toOH K.1)) (hL : S.le (dv S.toOH K.2) L) :
    ZRootAbs.Mono S F a b c L := by
  intro x y hax hxy hyb
  have hxb := S.le_trans hxy hyb
  have hay := S.le_trans hax hxy
  have sl := slX_sound H Hs (hin x hax hxb) (hin y hay hyb) (hd x y) e (hval x hax hxb) (hval y hay hyb) hK
  have d0 : S.le S.zero (S.add y (S.neg x)) := by cr_linarith S.toOCR [hxy]
  constructor
  · apply S.le_of_not_pos
    intro hpos
    apply sl
    intro ⟨s, hs, he⟩
    have l := le_mul_left' S (S.le_trans hc hs.1) d0
    have l' := S.le_respects (S.mul_comm _ _) (S.trans (S.mul_comm _ _) (S.symm he)) l
    exact S.pos_not_le hpos (by cr_linarith S.toOCR [l'])
  · apply S.le_of_not_pos
    intro hpos
    apply sl
    intro ⟨s, hs, he⟩
    have l := le_mul_left' S (S.le_trans hs.2 hL) d0
    have l' := S.le_respects (S.trans (S.mul_comm _ _) (S.symm he)) (S.mul_comm _ _) l
    exact S.pos_not_le hpos (by cr_linarith S.toOCR [l'])

theorem lo_gen {ex : α → α} {e : XE} {B : Box} {env : Nat → α} {v : α} (hb : InBox S B env)
    (hv : Val S ex env e v) {K : Iv} (hK : ivX B e = some K) (h : dle K.2 dz0 = true) : S.le v S.zero :=
  S.le_trans (ivX_sound S hb hv K hK).2 (S.le_respects (S.refl _) dv_dz0 (dle_sound S.toOH h))

theorem hi_gen {ex : α → α} {e : XE} {B : Box} {env : Nat → α} {v : α} (hb : InBox S B env)
    (hv : Val S ex env e v) {K : Iv} (hK : ivX B e = some K) (h : dle dz0 K.1 = true) : S.le S.zero v :=
  S.le_trans (S.le_respects dv_dz0 (S.refl _) (dle_sound S.toOH h)) (ivX_sound S hb hv K hK).1

/-- `Bd (u − w)` gives `Bd (w − u)`. -/
theorem bd_swap {u w δ : α} (h : ZKron.Bd S.toOH (S.add u (S.neg w)) δ) : ZKron.Bd S.toOH (S.add w (S.neg u)) δ := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by cr_linarith S.toOCR [h2], by cr_linarith S.toOCR [h1]⟩

theorem neg_one_le : S.le (S.neg S.one) S.zero := by
  have := S.toOCR.zero_le_one; cr_linarith S.toOCR [this]

/-- `u + h ≤ v` gives `h ≤ v − u`. -/
theorem gap_le {u v h : α} (g : S.le (S.add u h) v) : S.le h (S.add v (S.neg u)) := by cr_linarith S.toOCR [g]

end G

/-! ## The parameters on VR's continuum -/

/-- `x` moves, the parameters do not. -/
def Vx : Nat → Iv := fun i => cond (Nat.beq i 0) ZIv.one zI
/-- `x` does not move, each parameter moves by `s·δ`, `s ∈ [−1, 1]`. -/
def Vp : Nat → Iv := fun i => cond (Nat.beq i 0) zI pm1

/-- The environment: `x` at variable `0`, the parameters `q`, zero elsewhere. -/
def envP (a : D) (ps : PS) (q : Nat → RExpr) (x : RExpr) : Nat → RExpr := ZRootP.setv (envOf a ps q) 0 x
/-- The law with parameters `q`, as a function of `x` on VR's continuum. -/
def FP (e : XE) (a : D) (ps : PS) (q : Nat → RExpr) (x : RExpr) : RExpr := evR (envP a ps q x) e
/-- The rational environment of the oracle: `t` at `0`, the parameters' `n`-th terms. -/
def qenvD (ps : PS) (p : Nat → RExpr) (n : Nat) (t : QExpr) : Nat → QExpr :=
  fun i => cond (Nat.beq i 0) t (cond (isP i ps) ((p i).seq n) qzero)
def gP (e : XE) (ps : PS) (p : Nat → RExpr) (n : Nat) (t : QExpr) : QExpr := evqD n (qenvD ps p n t) e

theorem mem_of_isP {i : Nat} : ∀ {ps : PS}, isP i ps = true → ∃ c, List.Mem c ps ∧ c.1 = i
  | [], h => by cases h
  | c :: cs, h => by
      cases hb : Nat.beq i c.1 with
      | true => exact ⟨c, .head _, (Nat.eq_of_beq_eq_true hb).symm⟩
      | false =>
          have h' : isP i cs = true := by
            have h0 : (Nat.beq i c.1 || isP i cs) = true := h
            rw [hb] at h0; exact h0
          obtain ⟨d, hd, e⟩ := mem_of_isP h'
          exact ⟨d, .tail _ hd, e⟩

theorem parIn_mem {q : Nat → RExpr} {c : Nat × Iv × D} : ∀ {ps : PS}, ParIn q ps → List.Mem c ps →
    rle (dv rOH c.2.1.1) (q c.1) ∧ rle (q c.1) (dv rOH c.2.1.2)
  | _ :: _, ⟨h, _⟩, .head _ => h
  | _ :: _, ⟨_, hs⟩, .tail _ hm => parIn_mem hs hm

theorem hd_x (a : D) (ps : PS) (q : Nat → RExpr) (x y : RExpr) : ∀ i,
    SlIn rCF (rCF.add (envP a ps q y i) (rCF.neg (envP a ps q x i))) (rCF.add y (rCF.neg x)) (Vx i) := by
  intro i
  show SlIn rCF (rCF.add (cond (Nat.beq i 0) y (envOf a ps q i)) (rCF.neg (cond (Nat.beq i 0) x (envOf a ps q i))))
    (rCF.add y (rCF.neg x)) (cond (Nat.beq i 0) ZIv.one zI)
  cases h : Nat.beq i 0 with
  | true => exact sl_ret (mem_one rCF) (rCF.symm (rCF.one_mul _))
  | false => exact sl_ret mem_zI (rCF.trans (rCF.add_neg _) (rCF.symm (rCF.zero_mul _)))

theorem hd_p (a : D) (ps : PS) (p : Nat → RExpr) (n J : Nat) (x : RExpr)
    (hcl : ∀ c, List.Mem c ps → ZKron.Bd rCF.toOH (radd (p c.1) (rneg (rofQ ((p c.1).seq n)))) (hp rOH J)) : ∀ i,
    SlIn rCF (rCF.add (envP a ps (pn p n) x i) (rCF.neg (envP a ps p x i))) (hp rOH J) (Vp i) := by
  intro i
  show SlIn rCF (rCF.add (cond (Nat.beq i 0) x (cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (pn p n i) rzero)))
      (rCF.neg (cond (Nat.beq i 0) x (cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (p i) rzero)))))
    (hp rOH J) (cond (Nat.beq i 0) zI pm1)
  cases h : Nat.beq i 0 with
  | true => exact sl_ret mem_zI (rCF.trans (rCF.add_neg _) (rCF.symm (rCF.zero_mul _)))
  | false =>
      cases hP : isP i ps with
      | true =>
          obtain ⟨c, hc, hci⟩ := mem_of_isP hP
          subst hci
          exact sl_of_bd rCF (bd_swap rCF (hcl c hc)) (ZNone.pos_hp rCF J)
      | false =>
          refine sl_ret (s := rCF.zero) (mem_pm1 rCF ?_ ?_) (rCF.trans (rCF.add_neg _) (rCF.symm (rCF.zero_mul _)))
          · exact neg_one_le rCF
          · exact rCF.toOCR.zero_le_one

/-- A real between two dyadics whose terms are all `y` is within a fixed bound. -/
theorem iv_bound (lo hi : D) : ∃ R, qle qzero R ∧ ∀ (z : RExpr) (y : QExpr), (∀ m, qEq (z.seq m) y) →
    rle (dv rOH lo) z → rle z (dv rOH hi) → qclose y qzero R := by
  obtain ⟨Ca, hCa⟩ := qexpr_bound (qD lo)
  obtain ⟨Cb, hCb⟩ := qexpr_bound (qD hi)
  have pa : qle qzero (qofInt (pow2 Ca)) := qofInt_le (pow2_nonneg Ca)
  have pb : qle qzero (qofInt (pow2 Cb)) := qofInt_le (pow2_nonneg Cb)
  have p1 := qle_of_qlt qone_pos
  refine ⟨qadd (qadd (qofInt (pow2 Ca)) (qofInt (pow2 Cb))) qone, by rat_linarith, fun z y hz h1 h2 => ?_⟩
  obtain ⟨N1, k1⟩ := h1 0
  obtain ⟨N2, k2⟩ := h2 0
  have a1 := k1 (N1 + N2) (Nat.le_add_right _ _)
  have a2 := k2 (N1 + N2) (Nat.le_add_left _ _)
  have d1 := dv_seq lo (N1 + N2)
  have d2 := hz (N1 + N2)
  have d3 := dv_seq hi (N1 + N2)
  have e0 := qeps_zero
  obtain ⟨ca1, ca2⟩ := hCa
  obtain ⟨cb1, cb2⟩ := hCb
  unfold qsub at a1 a2 ca1 ca2 cb1 cb2
  constructor <;> (unfold qsub; rat_linarith)

theorem ps_bound : ∀ ps : PS, ∃ R, qle qzero R ∧ ∀ c, List.Mem c ps → ∀ (z : RExpr) (y : QExpr),
    (∀ m, qEq (z.seq m) y) → rle (dv rOH c.2.1.1) z → rle z (dv rOH c.2.1.2) → qclose y qzero R
  | [] => ⟨qzero, qle_refl _, fun c h => by cases h⟩
  | c :: cs => by
      obtain ⟨R1, r1, h1⟩ := iv_bound c.2.1.1 c.2.1.2
      obtain ⟨R2, r2, h2⟩ := ps_bound cs
      refine ⟨qadd R1 R2, by rat_linarith, fun d hd z y hz l1 l2 => ?_⟩
      cases hd with
      | head => exact qclose_mono (h1 z y hz l1 l2) (by rat_linarith)
      | tail _ hm => exact qclose_mono (h2 d hm z y hz l1 l2) (by rat_linarith)

/-- The placeholder at variable `0` is overwritten by `x`: the box holds the environment whatever it is. -/
theorem inbox_swap {B : Box} {a a' : D} {ps : PS} {q : Nat → RExpr} {x : RExpr}
    (h : InBox rCF B (ZRootP.setv (envOf a' ps q) 0 x)) : InBox rCF B (ZRootP.setv (envOf a ps q) 0 x) := by
  intro i I hI
  have k := h i I hI
  revert k
  show (rle (dv rOH I.1) (cond (Nat.beq i 0) x (cond (Nat.beq i 0) (dv rOH a') (cond (isP i ps) (q i) rzero))) ∧
      rle (cond (Nat.beq i 0) x (cond (Nat.beq i 0) (dv rOH a') (cond (isP i ps) (q i) rzero))) (dv rOH I.2)) →
    (rle (dv rOH I.1) (cond (Nat.beq i 0) x (cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (q i) rzero))) ∧
      rle (cond (Nat.beq i 0) x (cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (q i) rzero))) (dv rOH I.2))
  cases Nat.beq i 0 <;> exact id

/-- The environment's terms are the oracle's environment. -/
theorem env_seq (a : D) (ps : PS) (p : Nat → RExpr) (n m : Nat) (t : D) : ∀ i,
    qEq ((envP a ps (pn p n) (dv rOH t) i).seq m) (qenvD ps p n (qD t) i) := by
  intro i
  show qEq ((cond (Nat.beq i 0) (dv rOH t) (cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (pn p n i) rzero))).seq m)
    (cond (Nat.beq i 0) (qD t) (cond (isP i ps) ((p i).seq n) qzero))
  cases h : Nat.beq i 0 with
  | true => exact dv_seq t m
  | false =>
      cases hP : isP i ps with
      | true => exact qEq_refl _
      | false => exact qEq_refl _

section Root
variable (e : XE) (a b : D) (ps : PS) (p : Nat → RExpr)

/-- **THE ORACLE IS UNIFORMLY CLOSE** once the approximants are in the box. -/
theorem orac_P {N0 : Nat} (hN0 : ∀ n, N0 ≤ n → ParIn (pn p n) ps) : ∀ j, ∃ N, ∀ n, N ≤ n → ∀ t : D,
    rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
    ZKron.Bd rCF.toOH (radd (FP e a ps (pn p n) (dv rOH t)) (rneg (rofQ (gP e ps p n (qD t))))) (hp rOH j) := by
  intro j
  obtain ⟨Rt, rt, hRt⟩ := iv_bound a b
  obtain ⟨Rp, rp, hRp⟩ := ps_bound ps
  have R0 : qle qzero (qadd Rt Rp) := by rat_linarith
  obtain ⟨_, _, _, cau⟩ := uc_evqD e _ R0
  obtain ⟨Nu, _, hN⟩ := cau j
  refine ⟨Nu + N0, fun n hn t hat htb => ?_⟩
  have pin := hN0 n (lB hn)
  have hρ : ∀ i, qclose (qenvD ps p n (qD t) i) qzero (qadd Rt Rp) := by
    intro i
    show qclose (cond (Nat.beq i 0) (qD t) (cond (isP i ps) ((p i).seq n) qzero)) qzero (qadd Rt Rp)
    cases h : Nat.beq i 0 with
    | true => exact qclose_mono (hRt (dv rOH t) (qD t) (dv_seq t) hat htb) (by rat_linarith)
    | false =>
        cases hP : isP i ps with
        | true =>
            obtain ⟨c, hc, hci⟩ := mem_of_isP hP
            subst hci
            obtain ⟨l1, l2⟩ := parIn_mem pin hc
            exact qclose_mono (hRp c hc _ ((p c.1).seq n) (fun _ => qEq_refl _) l1 l2) (by rat_linarith)
        | false => exact qclose_refl _ _ R0
  have key : ∀ m, Nu ≤ m → qclose (evqD m (qenvD ps p n (qD t)) e) (evqD n (qenvD ps p n (qD t)) e) (qeps j) :=
    fun m hm => hN m n _ hm (lA hn) hρ
  show rle (rneg (hp rOH j)) _ ∧ rle _ (hp rOH j)
  constructor
  · refine rle_of_eventually Nu fun m hm => ?_
    have s1 := evR_seq (envP a ps (pn p n) (dv rOH t)) m e
    have s2 := evqD_respects m (env_seq a ps p n m t) e
    have s3 := hp_seq j m
    obtain ⟨k1, k2⟩ := key m hm
    change qle (qneg ((hp rOH j).seq m))
      (qadd ((evR (envP a ps (pn p n) (dv rOH t)) e).seq m) (qneg (evqD n (qenvD ps p n (qD t)) e)))
    unfold qsub at k1 k2
    rat_linarith
  · refine rle_of_eventually Nu fun m hm => ?_
    have s1 := evR_seq (envP a ps (pn p n) (dv rOH t)) m e
    have s2 := evqD_respects m (env_seq a ps p n m t) e
    have s3 := hp_seq j m
    obtain ⟨k1, k2⟩ := key m hm
    change qle (qadd ((evR (envP a ps (pn p n) (dv rOH t)) e).seq m) (qneg (evqD n (qenvD ps p n (qD t)) e)))
      ((hp rOH j).seq m)
    unfold qsub at k1 k2
    rat_linarith

theorem twoL (j L : Nat) : rCF.r (rCF.mul (nI rOH (2 ^ L)) (hp rOH (j + L))) (hp rOH j) := by
  refine rCF.trans (rCF.mul_congr (rCF.refl _) (hp_add rOH j L)) ?_
  refine rCF.trans (mul_swap rCF _ _ _) ?_
  exact rCF.trans (rCF.mul_congr (rCF.refl _) (two_hp rOH L)) (rCF.trans (rCF.mul_comm _ _) (rCF.one_mul _))

/-- **THE APPROXIMANTS' LAW IS UNIFORMLY CLOSE TO THE LAW** (the Lipschitz reading in the parameters). -/
theorem conv_P {N0 L : Nat} (hN0 : ∀ n, N0 ≤ n → ParIn (pn p n) ps) (hpin : ParIn p ps)
    (hP : posOK (BoxOf a b ps) e = true) {Kp : Iv} (hKp : slX (BoxOf a b ps) Vp e = some Kp)
    (h1 : dle (dneg ⟨⟨2 ^ L, 0⟩, 0⟩) Kp.1 = true) (h2 : dle Kp.2 ⟨⟨2 ^ L, 0⟩, 0⟩ = true) :
    ∀ j, ∃ N, ∀ n, N ≤ n → ∀ x, rle (dv rOH a) x → rle x (dv rOH b) →
      ZKron.Bd rCF.toOH (radd (FP e a ps (pn p n) x) (rneg (FP e a ps p x))) (hp rOH j) := by
  intro j
  obtain ⟨Nc, hNc⟩ := common_N (P := fun i n => ZKron.Bd rCF.toOH (radd (p i) (rneg (rofQ ((p i).seq n))))
    (hp rOH (j + L))) ps (fun c _ => approx_close (p c.1) (j + L))
  refine ⟨Nc + N0, fun n hn x hx1 hx2 => ?_⟩
  have pin := hN0 n (lB hn)
  have sl := slX_sound rExpLaws r_slope (inbox_env hpin ⟨hx1, hx2⟩) (inbox_env pin ⟨hx1, hx2⟩)
    (hd_p a ps p n (j + L) x (hNc n (lA hn))) e (val_evR (inbox_env hpin ⟨hx1, hx2⟩) e hP)
    (val_evR (inbox_env pin ⟨hx1, hx2⟩) e hP) hKp
  have e1 : rCF.r (dv rOH (dneg ⟨⟨2 ^ L, 0⟩, 0⟩)) (rCF.neg (nI rOH (2 ^ L))) :=
    rCF.trans (dv_neg rOH _) (rCF.neg_congr (ZRoot.dv_nat rCF (2 ^ L)))
  have bd := bd_of_sl rCF sl (hp_nonneg rOH (j + L))
    (rCF.le_respects e1 (rCF.refl _) (dle_sound rOH h1))
    (rCF.le_respects (rCF.refl _) (ZRoot.dv_nat rCF (2 ^ L)) (dle_sound rOH h2))
  exact ZKron.bd_congr rCF.toOH (rCF.refl _) (twoL j L) bd

end Root

/-- **THE CERTIFICATE** for a law with parameters `ps`: the denominators / `ln` arguments read `≥ 2⁻⁶⁴` on the box;
the slope in `x` read in `[2⁻ˢ, 2ᶜ]`; the slope in the parameters read in `[−2ᴸ, 2ᴸ]`; `F(a) ≤ 0 ≤ F(b)` read for
every parameter in the box; width `≤ 2ᴮ`. Checked by the kernel. -/
def chkP (e : XE) (a b : D) (ps : PS) (s C B L : Nat) : Bool :=
  dle a b && posOK (BoxOf a b ps) e &&
    optB (slX (BoxOf a b ps) Vx e) (fun K => dle ⟨⟨1, 0⟩, s⟩ K.1 && dle K.2 ⟨⟨2 ^ C, 0⟩, 0⟩) &&
    optB (slX (BoxOf a b ps) Vp e) (fun K => dle (dneg ⟨⟨2 ^ L, 0⟩, 0⟩) K.1 && dle K.2 ⟨⟨2 ^ L, 0⟩, 0⟩) &&
    optB (ivX (BoxOf a a ps) e) (fun K => dle K.2 dz0) &&
    optB (ivX (BoxOf b b ps) e) (fun K => dle dz0 K.1) &&
    dle (dadd b (dneg a)) ⟨⟨2 ^ B, 0⟩, 0⟩

/-- **FOR EVERY REAL PARAMETER VECTOR IN THE INNER BOX, THE LAW HAS ITS ROOT ON VR's CONTINUUM — and only one in
`[a, b]`.** -/
theorem par_root (e : XE) (a b : D) (ps : PS) (s C B L : Nat) (h : chkP e a b ps s C B L = true)
    {μ : Nat} (p : Nat → RExpr) (hin : InnerIn μ p ps) :
    ∃ x : RExpr, (rle (dv rOH a) x ∧ rle x (dv rOH b)) ∧ rEq (FP e a ps p x) rzero ∧
      ∀ y, rle (dv rOH a) y → rle y (dv rOH b) → rEq (FP e a ps p y) rzero → rEq y x := by
  obtain ⟨h6, hW⟩ := and2 h
  obtain ⟨h5, hb'⟩ := and2 h6
  obtain ⟨h4, ha'⟩ := and2 h5
  obtain ⟨h3, hKp'⟩ := and2 h4
  obtain ⟨h2, hK'⟩ := and2 h3
  obtain ⟨hab, hP⟩ := and2 h2
  obtain ⟨K, hK, hKc⟩ := optB_some hK'
  obtain ⟨hc, hL⟩ := and2 hKc
  obtain ⟨Kp, hKp, hKpc⟩ := optB_some hKp'
  obtain ⟨hp1, hp2⟩ := and2 hKpc
  obtain ⟨Ka, hKa, ha⟩ := optB_some ha'
  obtain ⟨Kb, hKb, hb⟩ := optB_some hb'
  have hab' := dle_sound rOH hab
  obtain ⟨N0, hN0⟩ := approx_in ps p hin
  have hpin := parIn_inner p hin
  have hM : ∀ q, ParIn q ps → ZRootAbs.Mono rCF (FP e a ps q) (dv rOH a) (dv rOH b) (hp rOH s) (nI rOH (2 ^ C)) :=
    fun q hq => mono_gen rCF rExpLaws r_slope (env := envP a ps q)
      (fun x h1 h2 => inbox_env hq ⟨h1, h2⟩) (fun x h1 h2 => val_evR (inbox_env hq ⟨h1, h2⟩) e hP)
      (fun x y => hd_x a ps q x y) hK
      (rCF.le_respects (ZRootPVR.dv_hp s) (rCF.refl _) (dle_sound rOH hc))
      (rCF.le_respects (rCF.refl _) (ZRoot.dv_nat rCF (2 ^ C)) (dle_sound rOH hL))
  have hends : ∀ q, ParIn q ps → rle (FP e a ps q (dv rOH a)) rzero ∧ rle rzero (FP e a ps q (dv rOH b)) :=
    fun q hq => ⟨lo_gen rCF (inbox_env (b := a) hq ⟨rCF.le_refl _, rCF.le_refl _⟩)
        (val_evR (inbox_env hq ⟨rCF.le_refl _, hab'⟩) e hP) hKa ha,
      hi_gen rCF (inbox_swap (inbox_env (a := b) (b := b) hq ⟨rCF.le_refl _, rCF.le_refl _⟩))
        (val_evR (inbox_env hq ⟨hab', rCF.le_refl _⟩) e hP) hKb hb⟩
  have H : ZRootAbs.Fam (fun n => FP e a ps (pn p n)) (FP e a ps p) (gP e ps p) a b s C B N0 := {
    hab := hab
    mono := fun n hn => hM _ (hN0 n hn)
    monoP := hM p hpin
    ends := fun n hn => hends _ (hN0 n hn)
    conv := conv_P e a b ps p hN0 hpin hP hKp hp1 hp2
    orac := orac_P e a b ps p hN0
    wid := hW }
  exact ⟨ZRootAbs.froot H, ZRootAbs.froot_in H, ZRootAbs.froot_is_root H,
    fun y h1 h2 hy => ZRootAbs.froot_unique H ⟨h1, h2⟩ (ZRootAbs.froot_in H) hy (ZRootAbs.froot_is_root H)⟩

/-! ## Covers: a tree of cuts in the parameters

A wide parameter box may need splitting before the readings decide. A cut at parameter `i`, value `c`, half-overlap
`w`: the left box carries `[lo, c + w]`, the right `[c − w, hi]`. A real parameter is NOT located by deciding
`pᵢ ≤ c` (that is not decidable on the continuum): the overlap leaves a gap `[c − w + m, c + w − m]` of positive
width, and cotransitivity (`rcotrans`) puts `pᵢ` in the left inner box or the right one. -/

/-- The parameter `i`'s interval replaced by `I`. -/
def setI (i : Nat) (I : Iv) : PS → PS
  | [] => []
  | c :: cs => cond (Nat.beq c.1 i) ((c.1, I, c.2.2) :: setI i I cs) (c :: setI i I cs)

theorem isP_setI (i j : Nat) (I : Iv) : ∀ ps : PS, isP j (setI i I ps) = isP j ps
  | [] => rfl
  | c :: cs => by
      show isP j (cond (Nat.beq c.1 i) ((c.1, I, c.2.2) :: setI i I cs) (c :: setI i I cs)) = (Nat.beq j c.1 || isP j cs)
      cases Nat.beq c.1 i with
      | true => show (Nat.beq j c.1 || isP j (setI i I cs)) = _; rw [isP_setI i j I cs]
      | false => show (Nat.beq j c.1 || isP j (setI i I cs)) = _; rw [isP_setI i j I cs]

/-- The margin `2⁻ᵘ`. -/
def mg (μ : Nat) : D := ⟨⟨1, 0⟩, μ⟩

theorem lookI_inner {μ : Nat} {q : Nat → RExpr} {j : Nat} {I : Iv} : ∀ {ps : PS}, InnerIn μ q ps → lookI j ps = some I →
    rle (dv rOH (dadd I.1 (mg μ))) (q j) ∧ rle (q j) (dv rOH (dadd I.2 (dneg (mg μ))))
  | [], _, h => by cases h
  | c :: cs, ⟨hc, hcs⟩, h => by
      have h' : cond (Nat.beq j c.1) (some c.2.1) (lookI j cs) = some I := h
      cases hb : Nat.beq j c.1 with
      | true =>
          rw [hb] at h'; cases h'
          have := Nat.eq_of_beq_eq_true hb; subst this; exact hc
      | false => rw [hb] at h'; exact lookI_inner hcs h'

theorem innerIn_setI {μ : Nat} {q : Nat → RExpr} {i : Nat} {I : Iv}
    (h1 : rle (dv rOH (dadd I.1 (mg μ))) (q i)) (h2 : rle (q i) (dv rOH (dadd I.2 (dneg (mg μ))))) :
    ∀ {ps : PS}, InnerIn μ q ps → InnerIn μ q (setI i I ps)
  | [], _ => trivial
  | c :: cs, ⟨hc, hcs⟩ => by
      show InnerIn μ q (cond (Nat.beq c.1 i) ((c.1, I, c.2.2) :: setI i I cs) (c :: setI i I cs))
      cases hb : Nat.beq c.1 i with
      | true =>
          have e := Nat.eq_of_beq_eq_true hb
          subst e
          exact ⟨⟨h1, h2⟩, innerIn_setI h1 h2 hcs⟩
      | false => exact ⟨hc, innerIn_setI h1 h2 hcs⟩

theorem evR_congr {x y : Nat → RExpr} (h : ∀ i, x i = y i) : ∀ e : XE, evR x e = evR y e
  | .var i => h i
  | .cst _ => rfl
  | .add a b => by show radd _ _ = radd _ _; rw [evR_congr h a, evR_congr h b]
  | .sub a b => by show radd _ (rneg _) = radd _ (rneg _); rw [evR_congr h a, evR_congr h b]
  | .mul a b => by show rmul _ _ = rmul _ _; rw [evR_congr h a, evR_congr h b]
  | .pow a k => by show powS rOH _ k = powS rOH _ k; rw [evR_congr h a]
  | .exp a => by show rexpR _ = rexpR _; rw [evR_congr h a]
  | .div a b => by show rmul _ (rinvT _) = rmul _ (rinvT _); rw [evR_congr h a, evR_congr h b]
  | .ln a => by show rlnT _ = rlnT _; rw [evR_congr h a]

/-- The law does not see the intervals, only which variables are parameters. -/
theorem FP_setI (e : XE) (a : D) (ps : PS) (i : Nat) (I : Iv) (q : Nat → RExpr) (x : RExpr) :
    FP e a (setI i I ps) q x = FP e a ps q x := by
  apply evR_congr
  intro j
  show cond (Nat.beq j 0) x (cond (Nat.beq j 0) (dv rOH a) (cond (isP j (setI i I ps)) (q j) rzero)) =
    cond (Nat.beq j 0) x (cond (Nat.beq j 0) (dv rOH a) (cond (isP j ps) (q j) rzero))
  rw [isP_setI]

inductive PT where
  | leaf : PT
  | cut : Nat → D → D → PT → PT → PT

/-- **THE COVER CERTIFICATE**: every leaf's box passes `chkP`; every cut's gap `[c − w + m, c + w − m]` has width
`≥ m`. -/
def chkT (e : XE) (a b : D) (s C B L μ : Nat) : PS → PT → Bool
  | ps, .leaf => chkP e a b ps s C B L
  | ps, .cut i c w l r => optB (lookI i ps) (fun I =>
      dle (dadd (dadd (dadd c (dneg w)) (mg μ)) (mg μ)) (dadd (dadd c w) (dneg (mg μ))) &&
      chkT e a b s C B L μ (setI i (I.1, dadd c w) ps) l && chkT e a b s C B L μ (setI i (dadd c (dneg w), I.2) ps) r)

/-- **ON A COVERED BOX, FOR EVERY REAL PARAMETER VECTOR IN THE INNER BOX, THE ROOT EXISTS AND IS UNIQUE.** -/
theorem tree_root (e : XE) (a b : D) (s C B L μ : Nat) : ∀ (t : PT) (ps : PS), chkT e a b s C B L μ ps t = true →
    ∀ (p : Nat → RExpr), InnerIn μ p ps →
    ∃ x : RExpr, (rle (dv rOH a) x ∧ rle x (dv rOH b)) ∧ rEq (FP e a ps p x) rzero ∧
      ∀ y, rle (dv rOH a) y → rle y (dv rOH b) → rEq (FP e a ps p y) rzero → rEq y x
  | .leaf, ps, h, p, hin => par_root e a b ps s C B L h p hin
  | .cut i c w l r, ps, h, p, hin => by
      obtain ⟨I, hI, hc⟩ := optB_some h
      obtain ⟨h12, hr⟩ := and2 hc
      obtain ⟨hgap, hl⟩ := and2 h12
      obtain ⟨b1, b2⟩ := lookI_inner hin hI
      have gap := dle_sound rOH hgap
      have e1 := dv_add rOH (dadd (dadd c (dneg w)) (mg μ)) (mg μ)
      have e2 := ZRootPVR.dv_hp μ
      have pos : rlt rzero (radd (dv rOH (dadd (dadd c w) (dneg (mg μ)))) (rneg (dv rOH (dadd (dadd c (dneg w)) (mg μ))))) := by
        have g' : rCF.le (rCF.add (dv rOH (dadd (dadd c (dneg w)) (mg μ))) (hp rOH μ))
            (dv rOH (dadd (dadd c w) (dneg (mg μ)))) :=
          rCF.le_respects (rCF.trans e1 (rCF.add_congr (rCF.refl _) e2)) (rCF.refl _) gap
        exact rCF.pos_mono (ZNone.pos_hp rCF μ) (gap_le rCF g')
      cases rcotrans pos (p i) with
      | inl hle =>
          have hin' := innerIn_setI (I := (I.1, dadd c w)) b1 hle hin
          obtain ⟨x, hx, hr', hu⟩ := tree_root e a b s C B L μ l _ hl p hin'
          exact ⟨x, hx, FP_setI e a ps i _ p x ▸ hr', fun y h1 h2 hy => hu y h1 h2 ((FP_setI e a ps i _ p y).symm ▸ hy)⟩
      | inr hge =>
          have hin' := innerIn_setI (I := (dadd c (dneg w), I.2)) hge b2 hin
          obtain ⟨x, hx, hr', hu⟩ := tree_root e a b s C B L μ r _ hr p hin'
          exact ⟨x, hx, FP_setI e a ps i _ p x ▸ hr', fun y h1 h2 hy => hu y h1 h2 ((FP_setI e a ps i _ p y).symm ▸ hy)⟩

/-! ## Example: `x·eˣ = c` for every real `c` near 1 -/

/-- `x·eˣ − c`, the parameter `c` at variable `1`. -/
def lamE : XE := .sub (.mul (.var 0) (.exp (.var 0))) (.var 1)
/-- `c ∈ [7/8, 9/8]`. -/
def lamPS : PS := [(1, (⟨⟨7, 0⟩, 3⟩, ⟨⟨9, 0⟩, 3⟩), dz0)]

/-- **LAMBERT'S `W(c)` FOR EVERY REAL `c` IN `[7/8 + 2⁻ᵘ, 9/8 − 2⁻ᵘ]`**: `x·eˣ = c` has one root in `[0, 1]`. -/
theorem lambert_exists {μ : Nat} (c : Nat → RExpr) (hin : InnerIn μ c lamPS) :
    ∃ x : RExpr, (rle (dv rOH dz0) x ∧ rle x (dv rOH ZRootExp.d1)) ∧ rEq (FP lamE dz0 lamPS c x) rzero ∧
      ∀ y, rle (dv rOH dz0) y → rle y (dv rOH ZRootExp.d1) → rEq (FP lamE dz0 lamPS c y) rzero → rEq y x :=
  par_root lamE dz0 ZRootExp.d1 lamPS 0 3 0 0 (by decide +kernel) c hin

/-- The fork's other side: with `c` up to `3` the right end is not read positive (`e − 3 < 0`) — refused. -/
example : chkP lamE dz0 ZRootExp.d1 [(1, (⟨⟨7, 0⟩, 3⟩, ⟨⟨3, 0⟩, 0⟩), dz0)] 0 3 0 0 = false := by decide +kernel

end ZRootPar

#print axioms ZRootPar.mono_gen
#print axioms ZRootPar.bd_of_sl
#print axioms ZRootPar.sl_of_bd
#print axioms ZRootPar.hd_p
#print axioms ZRootPar.hd_x
#print axioms ZRootPar.orac_P
#print axioms ZRootPar.conv_P
#print axioms ZRootPar.par_root
#print axioms ZRootPar.lambert_exists
#print axioms ZRootPar.tree_root
