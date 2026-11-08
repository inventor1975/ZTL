import ZBanach
/-!
# ZKraw — Krawczyk's test (the contraction form) for systems of laws with exp / ln / division, on VR's continuum.
Zero axioms.

A system of `d` laws `Gₖ(x₀, …, x_{d−1})` (`ZXE.XE`; in practice `G(x) = x − Y·F(x)` with a preconditioner `Y`,
built by `tools/zkraw2lean.py`) on the cube `|xᵢ − yᵢ| ≤ r`. The kernel checks (`chkK`):
* every denominator and `ln` argument reads `≥ 2⁻⁶⁴` on the cube;
* CONTRACTION: each row of the slope readings `Sₖⱼ` (direction `eⱼ`: one variable moves at a time — a staircase, so
  `x − Y·F(x)` keeps its cancellation) has `Σⱼ max|Sₖⱼ| ≤ ½`;
* INTO: the reading of `Gₖ` at the centre, widened by `rh ≥ r/2`, lies in the cube shrunk by `2⁻ᴿ`;
* the cube's diameter `2r ≤ 2ᴱ`.
Then `ZBanach.banach`: `G` has a fixed point in the cube, and only one (`krawczyk`).
-/

namespace ZKraw
open VR VR.Numbers VR.CSR ZNumBin ZField ZIv ZDivIv ZXE ZRealCF ZExp ZRealExp ZRootExp ZRootDiv ZRootPVR ZRootPar ZBanach

/-! ## Indices -/

theorem blt_t {i d : Nat} (h : i < d) : Nat.blt i d = true := Nat.ble_eq_true_of_le h

theorem blt_f {i d : Nat} (h : d ≤ i) : Nat.blt i d = false := by
  cases e : Nat.blt i d with
  | false => rfl
  | true => exact absurd (Nat.le_trans (Nat.le_of_ble_eq_true e) h) (Nat.not_succ_le_self i)

def nthD : List D → Nat → D
  | [], _ => dz0
  | a :: _, 0 => a
  | _ :: as, n + 1 => nthD as n

def nthX : List XE → Nat → XE
  | [], _ => .cst dz0
  | a :: _, 0 => a
  | _ :: as, n + 1 => nthX as n

/-- `f k` for every `k < d`. -/
def allB : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | d + 1, f => f d && allB d f

theorem allB_sound {f : Nat → Bool} : ∀ {d : Nat}, allB d f = true → ∀ k, k < d → f k = true
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | d + 1, h, k, hk => by
      obtain ⟨h1, h2⟩ := and2 h
      cases Nat.lt_or_ge k d with
      | inl hlt => exact allB_sound h2 k hlt
      | inr hge =>
          have e : k = d := Nat.le_antisymm (Nat.le_of_lt_succ hk) hge
          subst e; exact h1

/-! ## Generic inequalities (any `CF`) -/

section G
variable {α : Type} (S : CF α)

theorem half_of_two {r t : α} (h : S.le r (S.add t t)) : S.le (S.mul (hp S.toOH 1) r) t := by
  have l := ZIv.le_mul_left' S h (hp_nonneg S.toOH 1)
  have e := ZRoot.hp_succ_half S 0
  have e2 : S.r (S.mul (hp S.toOH 1) (S.add t t)) (S.mul (S.add (hp S.toOH 1) (hp S.toOH 1)) t) := by cr_ring S.toCR
  have e3 : S.r (S.mul (S.add (hp S.toOH 1) (hp S.toOH 1)) t) t :=
    S.trans (S.mul_congr e (S.refl _)) (S.one_mul _)
  exact S.le_respects (S.refl _) (S.trans e2 e3) l

theorem into_core {lo hi Vl Vu rh hR gu vc w hr : α} (hV1 : S.le Vl vc) (hV2 : S.le vc Vu)
    (hG : ZKron.Bd S.toOH (S.add gu (S.neg vc)) hr) (hrh : S.le hr rh) (hw : ZKron.Bd S.toOH (S.add w (S.neg gu)) hR)
    (c1 : S.le (S.add (S.add lo hR) rh) Vl) (c2 : S.le (S.add (S.add Vu rh) hR) hi) : S.le lo w ∧ S.le w hi := by
  obtain ⟨g1, g2⟩ := hG; obtain ⟨w1, w2⟩ := hw
  exact ⟨by cr_linarith S.toOCR [hV1, g1, hrh, w1, c1], by cr_linarith S.toOCR [hV2, g2, hrh, w2, c2]⟩

theorem diam_core {lo hi u v W : α} (hu1 : S.le lo u) (hu2 : S.le u hi) (hv1 : S.le lo v) (hv2 : S.le v hi)
    (hW : S.le (S.add hi (S.neg lo)) W) : ZKron.Bd S.toOH (S.add u (S.neg v)) W :=
  ⟨by cr_linarith S.toOCR [hu1, hv2, hW], by cr_linarith S.toOCR [hu2, hv1, hW]⟩

theorem cube_core {y r u : α} (h1 : S.le (S.add y (S.neg r)) u) (h2 : S.le u (S.add y r)) :
    ZKron.Bd S.toOH (S.add u (S.neg y)) r :=
  ⟨by cr_linarith S.toOCR [h1], by cr_linarith S.toOCR [h2]⟩

theorem cen_core {y r : α} (h : S.le S.zero r) : S.le (S.add y (S.neg r)) y ∧ S.le y (S.add y r) :=
  ⟨by cr_linarith S.toOCR [h], by cr_linarith S.toOCR [h]⟩

theorem closed_lo {lo u : α} (hc : ZRoot.Complete S)
    (h : ∀ J, ∃ w, S.le lo w ∧ ZKron.Bd S.toOH (S.add u (S.neg w)) (hp S.toOH J)) : S.le lo u := by
  apply S.le_of_not_pos
  intro hpos
  obtain ⟨J, hJ⟩ := hc.arch hpos
  obtain ⟨w, hw, hb⟩ := h (J + 1)
  obtain ⟨b1, _⟩ := hb
  exact contra_hp S hJ (by cr_linarith S.toOCR [hw, b1])

theorem closed_hi {hi u : α} (hc : ZRoot.Complete S)
    (h : ∀ J, ∃ w, S.le w hi ∧ ZKron.Bd S.toOH (S.add u (S.neg w)) (hp S.toOH J)) : S.le u hi := by
  apply S.le_of_not_pos
  intro hpos
  obtain ⟨J, hJ⟩ := hc.arch hpos
  obtain ⟨w, hw, hb⟩ := h (J + 1)
  obtain ⟨_, b2⟩ := hb
  exact contra_hp S hJ (by cr_linarith S.toOCR [hw, b2])

theorem width_core {y r lo hi W : α} (e1 : S.r lo (S.add y (S.neg r))) (e2 : S.r hi (S.add y r))
    (h : S.le (S.add r r) W) : S.le (S.add hi (S.neg lo)) W :=
  S.le_respects (S.symm (S.trans (S.add_congr e2 (S.neg_congr e1)) (by cr_ring S.toCR))) (S.refl _) h

/-- `s ∈ [−A, A]`, `|d| ≤ δ`: `|s·d| ≤ A·δ`. -/
theorem prod_bd {s dd A δ : α} (hs1 : S.le (S.neg A) s) (hs2 : S.le s A) (hd : ZKron.Bd S.toOH dd δ) :
    ZKron.Bd S.toOH (S.mul s dd) (S.mul A δ) := by
  obtain ⟨d1, d2⟩ := hd
  have A0 : S.le S.zero A := by cr_linarith S.toOCR [hs1, hs2]
  have δ0 : S.le S.zero δ := by cr_linarith S.toOCR [d1, d2]
  have p := S.mul_nonneg A0 δ0
  have e1 : S.r (S.mul (S.neg A) (S.neg δ)) (S.mul A δ) := by cr_ring S.toCR
  have e2 : S.r (S.mul (S.neg A) δ) (S.neg (S.mul A δ)) := by cr_ring S.toCR
  have e3 : S.r (S.mul A (S.neg δ)) (S.neg (S.mul A δ)) := by cr_ring S.toCR
  constructor
  · exact mul_lower S hs1 hs2 d1 d2
      (S.le_respects (S.refl _) (S.symm e1) (by cr_linarith S.toOCR [p]))
      (S.le_respects (S.refl _) (S.symm e2) (S.le_refl _))
      (S.le_respects (S.refl _) (S.symm e3) (S.le_refl _))
      (by cr_linarith S.toOCR [p])
  · exact mul_upper S hs1 hs2 d1 d2
      (S.le_respects (S.symm e1) (S.refl _) (S.le_refl _))
      (S.le_respects (S.symm e2) (S.refl _) (by cr_linarith S.toOCR [p]))
      (S.le_respects (S.symm e3) (S.refl _) (by cr_linarith S.toOCR [p]))
      (S.le_refl _)

theorem neg_flip {a M s : α} (h1 : S.le (S.neg a) M) (h2 : S.le a s) : S.le (S.neg M) s := by
  cr_linarith S.toOCR [h1, h2]

/-- A bound holding for every `s·d`, `s` in the reading, holds for the difference (stability under `¬¬`). -/
theorem bd_of_slin {Δ dd A : α} {K : Iv} (h : SlIn S Δ dd K) (k : ∀ s, Mem S s K → ZKron.Bd S.toOH (S.mul s dd) A) :
    ZKron.Bd S.toOH Δ A := by
  constructor
  · apply S.le_of_not_pos
    intro hpos
    apply h
    intro ⟨s, hs, he⟩
    have l := (k s hs).1
    exact S.pos_not_le hpos (by have l' := S.le_respects (S.refl _) (S.symm he) l; cr_linarith S.toOCR [l'])
  · apply S.le_of_not_pos
    intro hpos
    apply h
    intro ⟨s, hs, he⟩
    have l := (k s hs).2
    exact S.pos_not_le hpos (by have l' := S.le_respects (S.symm he) (S.refl _) l; cr_linarith S.toOCR [l'])

end G

/-! ## The cube, the truncated vectors, the map and its oracle -/

section Def
variable (d : Nat) (ys : List D) (r : D) (Gs : Nat → XE)

def lo (i : Nat) : D := dadd (nthD ys i) (dneg r)
def hi (i : Nat) : D := dadd (nthD ys i) r
def Bc : Box := fun i => cond (Nat.blt i d) (some (lo ys r i, hi ys r i)) none
def Bp : Box := fun i => cond (Nat.blt i d) (some (nthD ys i, nthD ys i)) none
def trunc (u : Vec) : Vec := fun i => cond (Nat.blt i d) (u i) rzero
def truncQ (z : Nat → QExpr) : Nat → QExpr := fun i => cond (Nat.blt i d) (z i) qzero
def Gv (u : Vec) : Vec := fun k => cond (Nat.blt k d) (evR (trunc d u) (Gs k)) rzero
def gv (n : Nat) (z : Nat → QExpr) : Nat → QExpr := fun k => cond (Nat.blt k d) (evqD n (truncQ d z) (Gs k)) qzero
def y0 : Nat → QExpr := fun i => qD (nthD ys i)
def InC (u : Vec) : Prop := InBox rCF (Bc d ys r) u
/-- The centre, as reals. -/
def cen : Vec := fun i => cond (Nat.blt i d) (dv rOH (nthD ys i)) rzero

end Def

def hD : D := ⟨⟨1, 0⟩, 1⟩
def mR (R : Nat) : D := ⟨⟨1, 0⟩, R⟩

/-- The direction `eₜ`: only variable `t` moves. -/
def ej (t : Nat) : Nat → Iv := fun i => cond (Nat.beq i t) ZIv.one zI
/-- A bound on `|s|` for `s ∈ K`. -/
def amx (K : Iv) : D := dmax (dneg K.1) K.2
/-- `Σ_{j<t} max|Sⱼ|`, `Sⱼ` the slope reading of `G` in the direction `eⱼ` (a row of `I − Y·J`). -/
def rowS (B : Box) (G : XE) : Nat → Option D
  | 0 => some dz0
  | t + 1 => match rowS B G t with
    | none => none
    | some s => match slX B (ej t) G with
      | none => none
      | some K => some (dadd s (amx K))

def optD (o : Option D) (f : D → Bool) : Bool :=
  match o with
  | some s => f s
  | none => false

theorem optD_some {o : Option D} {f : D → Bool} (h : optD o f = true) : ∃ s, o = some s ∧ f s = true := by
  cases o with
  | none => cases h
  | some s => exact ⟨s, rfl, h⟩

/-- **THE CERTIFICATE.** -/
def chkK (d : Nat) (ys : List D) (r rh : D) (R E : Nat) (Gs : Nat → XE) : Bool :=
  posX r && dle r (dadd rh rh) && dle (dadd r r) ⟨⟨2 ^ E, 0⟩, 0⟩ &&
  allB d (fun k =>
    posOK (Bc d ys r) (Gs k) &&
    optD (rowS (Bc d ys r) (Gs k) d) (fun s => dle s hD) &&
    optB (ivX (Bp d ys) (Gs k)) (fun V =>
      dle (dadd (dadd (lo ys r k) (mR R)) rh) V.1 && dle (dadd (dadd V.2 rh) (mR R)) (hi ys r k)))

section L
variable {d : Nat} {ys : List D} {r : D} {Gs : Nat → XE}

theorem trunc_lt {u : Vec} {i : Nat} (h : i < d) : trunc d u i = u i := by
  show cond (Nat.blt i d) (u i) rzero = u i; rw [blt_t h]; rfl
theorem trunc_ge {u : Vec} {i : Nat} (h : d ≤ i) : trunc d u i = rzero := by
  show cond (Nat.blt i d) (u i) rzero = rzero; rw [blt_f h]; rfl
theorem Gv_lt {u : Vec} {k : Nat} (h : k < d) : Gv d Gs u k = evR (trunc d u) (Gs k) := by
  show cond (Nat.blt k d) _ rzero = _; rw [blt_t h]; rfl
theorem gv_lt {n : Nat} {z : Nat → QExpr} {k : Nat} (h : k < d) : gv d Gs n z k = evqD n (truncQ d z) (Gs k) := by
  show cond (Nat.blt k d) _ qzero = _; rw [blt_t h]; rfl
theorem gv_ge {n : Nat} {z : Nat → QExpr} {k : Nat} (h : d ≤ k) : gv d Gs n z k = qzero := by
  show cond (Nat.blt k d) _ qzero = _; rw [blt_f h]; rfl

theorem inC_get {u : Vec} (hu : InC d ys r u) {i : Nat} (h : i < d) :
    rle (dv rOH (lo ys r i)) (u i) ∧ rle (u i) (dv rOH (hi ys r i)) :=
  hu i (lo ys r i, hi ys r i) (by show cond (Nat.blt i d) _ none = _; rw [blt_t h]; rfl)

theorem inC_of {u : Vec} (h : ∀ i, i < d → rle (dv rOH (lo ys r i)) (u i) ∧ rle (u i) (dv rOH (hi ys r i))) :
    InC d ys r u := by
  intro i I hI
  cases Nat.lt_or_ge i d with
  | inl hlt =>
      have e : Bc d ys r i = some (lo ys r i, hi ys r i) := by
        show cond (Nat.blt i d) _ none = _; rw [blt_t hlt]; rfl
      rw [e] at hI; cases hI; exact h i hlt
  | inr hge =>
      have e : Bc d ys r i = none := by show cond (Nat.blt i d) _ none = _; rw [blt_f hge]; rfl
      rw [e] at hI; cases hI

theorem inC_trunc {u : Vec} (hu : InC d ys r u) : InBox rCF (Bc d ys r) (trunc d u) :=
  inC_of (fun i hi => by rw [trunc_lt hi]; exact inC_get hu hi)

theorem dv_lo (i : Nat) : rEq (dv rOH (lo ys r i)) (radd (dv rOH (nthD ys i)) (rneg (dv rOH r))) :=
  rEq_trans (dv_add rOH _ _) (radd_respects (rEq_refl _) (dv_neg rOH _))
theorem dv_hi (i : Nat) : rEq (dv rOH (hi ys r i)) (radd (dv rOH (nthD ys i)) (dv rOH r)) := dv_add rOH _ _

theorem sl_zero {δ : RExpr} : SlIn rCF (rCF.add rzero (rCF.neg rzero)) δ pm1 :=
  sl_ret (s := rCF.zero) (mem_pm1 rCF (neg_one_le rCF) rCF.toOCR.zero_le_one)
    (rCF.trans (rCF.add_neg _) (rCF.symm (rCF.zero_mul _)))

theorem amx_bd {s : RExpr} {K : Iv} (h : Mem rCF s K) : rle (rneg (dv rOH (amx K))) s ∧ rle s (dv rOH (amx K)) := by
  have m1 := dmax_l rCF (dneg K.1) K.2
  have m2 := dmax_r rCF (dneg K.1) K.2
  have e := dv_neg rOH K.1
  have m1' : rle (rneg (dv rOH K.1)) (dv rOH (amx K)) := rCF.le_respects e (rCF.refl _) m1
  exact ⟨by have := h.1; exact neg_flip rCF m1' this, rCF.le_trans h.2 m2⟩

/-- The staircase from `p` to `q`: the first `t` coordinates from `q`, the rest from `p`. -/
def stair (p q : Vec) (t : Nat) : Vec := fun i => cond (Nat.blt i t) (q i) (p i)

theorem inbox_stair {B : Box} {p q : Vec} (hp' : InBox rCF B p) (hq : InBox rCF B q) (t : Nat) :
    InBox rCF B (stair p q t) := by
  intro i I hI
  show rle _ (cond (Nat.blt i t) (q i) (p i)) ∧ rle (cond (Nat.blt i t) (q i) (p i)) _
  cases Nat.blt i t with
  | true => exact hq i I hI
  | false => exact hp' i I hI

theorem stair_step_hd (p q : Vec) (t : Nat) : ∀ i,
    SlIn rCF (rCF.add (stair p q (t + 1) i) (rCF.neg (stair p q t i))) (rCF.add (q t) (rCF.neg (p t))) (ej t i) := by
  intro i
  show SlIn rCF (rCF.add (cond (Nat.blt i (t + 1)) (q i) (p i)) (rCF.neg (cond (Nat.blt i t) (q i) (p i))))
    (rCF.add (q t) (rCF.neg (p t))) (cond (Nat.beq i t) ZIv.one zI)
  cases h : Nat.beq i t with
  | true =>
      have e := Nat.eq_of_beq_eq_true h
      subst e
      rw [blt_t (Nat.lt_succ_self i), blt_f (Nat.le_refl i)]
      exact sl_ret (mem_one rCF) (rCF.symm (rCF.one_mul _))
  | false =>
      have ne : i ≠ t := fun e => by subst e; rw [ZKron.beq_self] at h; cases h
      cases Nat.lt_or_ge i t with
      | inl hlt =>
          rw [blt_t (Nat.lt_succ_of_lt hlt), blt_t hlt]
          exact sl_ret mem_zI (rCF.trans (rCF.add_neg _) (rCF.symm (rCF.zero_mul _)))
      | inr hge =>
          have hgt : t + 1 ≤ i := Nat.lt_of_le_of_ne hge (fun e => ne e.symm)
          rw [blt_f hgt, blt_f hge]
          exact sl_ret mem_zI (rCF.trans (rCF.add_neg _) (rCF.symm (rCF.zero_mul _)))

/-- **THE STAIRCASE LIPSCHITZ READING**: `|G(q) − G(p)| ≤ (Σⱼ max|Sⱼ|)·δ` when `|qⱼ − pⱼ| ≤ δ`. -/
theorem lip_stair {p q : Vec} (hp' : InBox rCF (Bc d ys r) p) (hq : InBox rCF (Bc d ys r) q) {δ : RExpr}
    (hcl : ∀ i, i < d → ZKron.Bd rCF.toOH (radd (q i) (rneg (p i))) δ) {G : XE}
    (hpos : posOK (Bc d ys r) G = true) :
    ∀ t, t ≤ d → ∀ sv, rowS (Bc d ys r) G t = some sv →
      ZKron.Bd rCF.toOH (radd (evR (stair p q t) G) (rneg (evR p G))) (rmul (dv rOH sv) δ)
  | 0, _, sv, h => by
      cases h
      have e : evR (stair p q 0) G = evR p G := evR_congr (fun i => rfl) G
      rw [e]
      have z : rEq (rmul (dv rOH dz0) δ) rzero := rCF.trans (rCF.mul_congr dv_dz0 (rCF.refl _)) (rCF.zero_mul _)
      exact ZKron.bd_congr rCF.toOH (rCF.refl _) (rEq_symm z) (bd_refl rCF (rle_refl _))
  | t + 1, ht, sv, h => by
      unfold rowS at h
      cases h1 : rowS (Bc d ys r) G t with
      | none => rw [h1] at h; cases h
      | some s0 =>
      rw [h1] at h; dsimp only at h
      cases h2 : slX (Bc d ys r) (ej t) G with
      | none => rw [h2] at h; cases h
      | some K =>
      rw [h2] at h; dsimp only at h
      cases h
      have ih := lip_stair hp' hq hcl hpos t (Nat.le_of_succ_le ht) s0 h1
      have sl := slX_sound rExpLaws r_slope (inbox_stair hp' hq t) (inbox_stair hp' hq (t + 1))
        (stair_step_hd p q t) G (val_evR (inbox_stair hp' hq t) G hpos) (val_evR (inbox_stair hp' hq (t + 1)) G hpos) h2
      have st : ZKron.Bd rCF.toOH (radd (evR (stair p q (t + 1)) G) (rneg (evR (stair p q t) G)))
          (rmul (dv rOH (amx K)) δ) := by
        refine bd_of_slin rCF sl (fun s hs => ?_)
        obtain ⟨a1, a2⟩ := amx_bd hs
        exact prod_bd rCF a1 a2 (hcl t ht)
      have tot := bd_tri rCF st ih
      refine ZKron.bd_congr rCF.toOH (rCF.refl _) ?_ tot
      exact rCF.trans (rCF.symm (rCF.add_mul _ _ _)) (rCF.mul_congr (rCF.trans (rCF.add_comm _ _) (rEq_symm (dv_add rOH _ _))) (rCF.refl _))

theorem stair_end {p q : Vec} (hout : ∀ i, d ≤ i → p i = q i) (G : XE) : evR (stair p q d) G = evR q G :=
  evR_congr (fun i => by
    show cond (Nat.blt i d) (q i) (p i) = q i
    cases Nat.lt_or_ge i d with
    | inl hlt => rw [blt_t hlt]; rfl
    | inr hge => rw [blt_f hge]; exact hout i hge) G

/-- The data the certificate gives for one law. -/
theorem chk_k {rh : D} {R E : Nat} (h : chkK d ys r rh R E Gs = true) {k : Nat} (hk : k < d) :
    posOK (Bc d ys r) (Gs k) = true ∧
    (∃ sv, rowS (Bc d ys r) (Gs k) d = some sv ∧ dle sv hD = true) ∧
    (∃ V, ivX (Bp d ys) (Gs k) = some V ∧ dle (dadd (dadd (lo ys r k) (mR R)) rh) V.1 = true ∧
      dle (dadd (dadd V.2 rh) (mR R)) (hi ys r k) = true) := by
  obtain ⟨_, hall⟩ := and2 h
  obtain ⟨h12, h3⟩ := and2 (allB_sound hall k hk)
  obtain ⟨h1, h2⟩ := and2 h12
  obtain ⟨sv, hsv, hsc⟩ := optD_some h2
  obtain ⟨V, hV, hVc⟩ := optB_some h3
  exact ⟨h1, ⟨sv, hsv, hsc⟩, ⟨V, hV, (and2 hVc).1, (and2 hVc).2⟩⟩

/-- The contraction bound from a row sum `≤ ½`. -/
theorem lip_half {p q : Vec} (hp' : InBox rCF (Bc d ys r) p) (hq : InBox rCF (Bc d ys r) q)
    (hout : ∀ i, d ≤ i → p i = q i) {δ : RExpr} (hδ0 : rle rzero δ)
    (hcl : ∀ i, i < d → ZKron.Bd rCF.toOH (radd (q i) (rneg (p i))) δ) {G : XE}
    (hpos : posOK (Bc d ys r) G = true) {sv : D} (hsv : rowS (Bc d ys r) G d = some sv) (hs : dle sv hD = true) :
    ZKron.Bd rCF.toOH (radd (evR q G) (rneg (evR p G))) (rmul (hp rOH 1) δ) := by
  have b := lip_stair hp' hq hcl hpos d (Nat.le_refl _) sv hsv
  rw [stair_end hout] at b
  exact bd_widen rCF b (le_mul_right rOH (rCF.le_respects (rCF.refl _) (ZRootPVR.dv_hp 1) (dle_sound rOH hs)) hδ0)

theorem chk_g {rh : D} {R E : Nat} (h : chkK d ys r rh R E Gs = true) :
    posX r = true ∧ dle r (dadd rh rh) = true ∧ dle (dadd r r) ⟨⟨2 ^ E, 0⟩, 0⟩ = true := by
  obtain ⟨h1, _⟩ := and2 h
  obtain ⟨h12, h3⟩ := and2 h1
  obtain ⟨h1', h2⟩ := and2 h12
  exact ⟨h1', h2, h3⟩

theorem cen_lt {i : Nat} (h : i < d) : cen d ys i = dv rOH (nthD ys i) := by
  show cond (Nat.blt i d) _ rzero = _; rw [blt_t h]; rfl
theorem cen_ge {i : Nat} (h : d ≤ i) : cen d ys i = rzero := by
  show cond (Nat.blt i d) _ rzero = _; rw [blt_f h]; rfl

theorem cen_bounds (hr0 : rle rzero (dv rOH r)) {i : Nat} :
    rle (dv rOH (lo ys r i)) (dv rOH (nthD ys i)) ∧ rle (dv rOH (nthD ys i)) (dv rOH (hi ys r i)) := by
  obtain ⟨c1, c2⟩ := cen_core rCF (y := dv rOH (nthD ys i)) hr0
  exact ⟨rCF.le_respects (rEq_symm (dv_lo i)) (rCF.refl _) c1, rCF.le_respects (rCF.refl _) (rEq_symm (dv_hi i)) c2⟩

theorem cen_inC (hr0 : rle rzero (dv rOH r)) : InBox rCF (Bc d ys r) (cen d ys) :=
  inC_of (fun i hi => by rw [cen_lt hi]; exact cen_bounds hr0)

theorem cen_inP : InBox rCF (Bp d ys) (cen d ys) := by
  intro i I hI
  cases Nat.lt_or_ge i d with
  | inl hlt =>
      have e : Bp d ys i = some (nthD ys i, nthD ys i) := by
        show cond (Nat.blt i d) _ none = _; rw [blt_t hlt]; rfl
      rw [e] at hI; cases hI
      show rle _ (cen d ys i) ∧ rle (cen d ys i) _
      rw [cen_lt hlt]; exact ⟨rle_refl _, rle_refl _⟩
  | inr hge =>
      have e : Bp d ys i = none := by show cond (Nat.blt i d) _ none = _; rw [blt_f hge]; rfl
      rw [e] at hI; cases hI

/-- A rational vector of the cube is bounded. -/
theorem cube_bound : ∀ (d : Nat), ∃ R0, qle qzero R0 ∧ ∀ i, i < d → ∀ (z : RExpr) (y : QExpr), (∀ m, qEq (z.seq m) y) →
    rle (dv rOH (lo ys r i)) z → rle z (dv rOH (hi ys r i)) → qclose y qzero R0
  | 0 => ⟨qzero, qle_refl _, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | d + 1 => by
      obtain ⟨R1, r1, h1⟩ := cube_bound d
      obtain ⟨R2, r2, h2⟩ := iv_bound (lo ys r d) (hi ys r d)
      refine ⟨qadd R1 R2, by rat_linarith, fun i hi z y hz l1 l2 => ?_⟩
      cases Nat.lt_or_ge i d with
      | inl hlt => exact qclose_mono (h1 i hlt z y hz l1 l2) (by rat_linarith)
      | inr hge =>
          have e : i = d := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
          subst e
          exact qclose_mono (h2 z y hz l1 l2) (by rat_linarith)

/-- **THE CERTIFICATE GIVES THE HYPOTHESES OF `ZBanach`.** -/
theorem ks_of_chk {rh : D} {R E : Nat} (h : chkK d ys r rh R E Gs = true) :
    KS d (Gv d Gs) (gv d Gs) (InC d ys r) (y0 ys) R E := by
  obtain ⟨hr, hrh, hE⟩ := chk_g h
  have rpos : rCF.pos (dv rOH r) := pos_of_posX rCF hr
  have hr0 : rle rzero (dv rOH r) := rCF.pos_nonneg rpos
  have hrh' : rle (dv rOH r) (radd (dv rOH rh) (dv rOH rh)) := rCF.le_respects (rCF.refl _) (dv_add rOH _ _) (dle_sound rOH hrh)
  have ehR : rEq (dv rOH (mR R)) (hp rOH R) := ZRootPVR.dv_hp R
  exact {
    into := fun u w hu hcl => inC_of (fun i hI => by
      obtain ⟨hpos, ⟨sv, hsv, hs⟩, ⟨V, hV, c1, c2⟩⟩ := chk_k h hI
      have vc := ivX_sound rCF cen_inP (val_evR (cen_inC hr0) _ hpos) V hV
      have hcl' : ∀ j, j < d → ZKron.Bd rCF.toOH (radd (trunc d u j) (rneg (cen d ys j))) (dv rOH r) := by
        intro j hj
        rw [trunc_lt hj, cen_lt hj]
        obtain ⟨l1, l2⟩ := inC_get hu hj
        exact cube_core rCF (rCF.le_respects (dv_lo j) (rCF.refl _) l1) (rCF.le_respects (rCF.refl _) (dv_hi j) l2)
      have hout : ∀ j, d ≤ j → cen d ys j = trunc d u j := fun j hj => by rw [cen_ge hj, trunc_ge hj]
      have L := lip_half (cen_inC hr0) (inC_trunc hu) hout hr0 hcl' hpos hsv hs
      have hw := hcl i hI
      rw [Gv_lt hI] at hw
      have c1' : rle (radd (radd (dv rOH (lo ys r i)) (hp rOH R)) (dv rOH rh)) (dv rOH V.1) :=
        rCF.le_respects (rEq_trans (dv_add rOH _ _) (radd_respects (rEq_trans (dv_add rOH _ _)
          (radd_respects (rEq_refl _) ehR)) (rEq_refl _))) (rCF.refl _) (dle_sound rOH c1)
      have c2' : rle (radd (radd (dv rOH V.2) (dv rOH rh)) (hp rOH R)) (dv rOH (hi ys r i)) :=
        rCF.le_respects (rEq_trans (dv_add rOH _ _) (radd_respects (dv_add rOH _ _) ehR)) (rCF.refl _) (dle_sound rOH c2)
      exact into_core rCF vc.1 vc.2 L (half_of_two rCF hrh') hw c1' c2')
    contr := fun u v δ hu hv hδ hcl k hk => by
      obtain ⟨hpos, ⟨sv, hsv, hs⟩, _⟩ := chk_k h hk
      have hcl' : ∀ i, i < d → ZKron.Bd rCF.toOH (radd (trunc d u i) (rneg (trunc d v i))) δ := by
        intro i hi; rw [trunc_lt hi, trunc_lt hi]; exact hcl i hi
      have hout : ∀ i, d ≤ i → trunc d v i = trunc d u i := fun i hi => by rw [trunc_ge hi, trunc_ge hi]
      rw [Gv_lt hk, Gv_lt hk]
      exact lip_half (inC_trunc hv) (inC_trunc hu) hout (rCF.pos_nonneg hδ) hcl' hpos hsv hs
    orac := fun j => by
      obtain ⟨R0, r0, hR0⟩ := cube_bound (ys := ys) (r := r) d
      have hz : ∀ (z : Nat → QExpr), InC d ys r (fun i => rofQ (z i)) → ∀ i, qclose (truncQ d z i) qzero R0 := by
        intro z hz i
        cases Nat.lt_or_ge i d with
        | inl hi =>
            show qclose (cond (Nat.blt i d) (z i) qzero) qzero R0
            rw [blt_t hi]
            obtain ⟨l1, l2⟩ := inC_get hz hi
            exact hR0 i hi _ (z i) (fun _ => qEq_refl _) l1 l2
        | inr hi =>
            show qclose (cond (Nat.blt i d) (z i) qzero) qzero R0
            rw [blt_f hi]; exact qclose_refl _ _ r0
      obtain ⟨N, hN⟩ := common_d (P := fun k n => ∀ m (z : Nat → QExpr), n ≤ m → (∀ i, qclose (z i) qzero R0) →
          qclose (evqD m z (Gs k)) (evqD n z (Gs k)) (qeps j)) d (fun k _ => by
        obtain ⟨_, _, _, cau⟩ := uc_evqD (Gs k) R0 r0
        obtain ⟨Nk, _, hNk⟩ := cau j
        exact ⟨Nk, fun n hn m z hm hzz => hNk m n z (Nat.le_trans hn hm) hn hzz⟩)
      refine ⟨N, fun n hn z hzin k hk => ?_⟩
      show ZKron.Bd rCF.toOH (radd (rofQ (gv d Gs n z k)) (rneg (Gv d Gs (fun i => rofQ (z i)) k))) (hp rOH j)
      rw [gv_lt hk, Gv_lt hk]
      have key := hN n hn k hk
      have sq : ∀ m i, qEq ((trunc d (fun i => rofQ (z i)) i).seq m) (truncQ d z i) := by
        intro m i
        show qEq ((cond (Nat.blt i d) (rofQ (z i)) rzero).seq m) (cond (Nat.blt i d) (z i) qzero)
        cases Nat.blt i d with
        | true => exact qEq_refl _
        | false => exact qEq_refl _
      show rle (rneg (hp rOH j)) _ ∧ rle _ (hp rOH j)
      constructor
      · refine rle_of_eventually n fun m hm => ?_
        have s1 := evR_seq (trunc d (fun i => rofQ (z i))) m (Gs k)
        have s2 := evqD_respects m (sq m) (Gs k)
        have s3 := hp_seq j m
        obtain ⟨k1, k2⟩ := key m (truncQ d z) hm (hz z hzin)
        change qle (qneg ((hp rOH j).seq m))
          (qadd (evqD n (truncQ d z) (Gs k)) (qneg ((evR (trunc d (fun i => rofQ (z i))) (Gs k)).seq m)))
        unfold qsub at k1 k2
        rat_linarith
      · refine rle_of_eventually n fun m hm => ?_
        have s1 := evR_seq (trunc d (fun i => rofQ (z i))) m (Gs k)
        have s2 := evqD_respects m (sq m) (Gs k)
        have s3 := hp_seq j m
        obtain ⟨k1, k2⟩ := key m (truncQ d z) hm (hz z hzin)
        change qle (qadd (evqD n (truncQ d z) (Gs k)) (qneg ((evR (trunc d (fun i => rofQ (z i))) (Gs k)).seq m)))
          ((hp rOH j).seq m)
        unfold qsub at k1 k2
        rat_linarith
    center := inC_of (fun i hi => by
      obtain ⟨c1, c2⟩ := cen_bounds (ys := ys) hr0 (i := i)
      have e := ZRootPVR.dv_rofQ (nthD ys i)
      exact ⟨rCF.le_respects (rCF.refl _) e c1, rCF.le_respects e (rCF.refl _) c2⟩)
    diam := fun u v hu hv i hi => by
      obtain ⟨u1, u2⟩ := inC_get hu hi
      obtain ⟨v1, v2⟩ := inC_get hv hi
      have hW : rle (radd (dv rOH r) (dv rOH r)) (nI rOH (2 ^ E)) :=
        rCF.le_respects (dv_add rOH _ _) (ZRoot.dv_nat rCF _) (dle_sound rOH hE)
      exact diam_core rCF u1 u2 v1 v2 (width_core rCF (dv_lo i) (dv_hi i) hW)
    closed := fun u hcl => inC_of (fun i hi =>
      ⟨closed_lo rCF ZRootVR.vr_complete (fun J => by
          obtain ⟨w, hw, hc⟩ := hcl J; exact ⟨w i, (inC_get hw hi).1, hc i hi⟩),
       closed_hi rCF ZRootVR.vr_complete (fun J => by
          obtain ⟨w, hw, hc⟩ := hcl J; exact ⟨w i, (inC_get hw hi).2, hc i hi⟩)⟩)
    out := fun _ _ _ hi => gv_ge hi }

/-- **KRAWCZYK ON VR's CONTINUUM**: under the kernel-checked certificate, the system `x = G(x)` has a solution in the
cube, and only one there. -/
theorem krawczyk {rh : D} {R E : Nat} (h : chkK d ys r rh R E Gs = true) :
    ∃ x : Vec, InC d ys r x ∧ (∀ k, k < d → rEq (evR (trunc d x) (Gs k)) (x k)) ∧
      ∀ u, InC d ys r u → (∀ k, k < d → rEq (evR (trunc d u) (Gs k)) (u k)) → ∀ i, i < d → rEq (u i) (x i) := by
  obtain ⟨x, hx, hf, hu⟩ := banach (ks_of_chk h)
  refine ⟨x, hx, fun k hk => ?_, fun u hu' hfu => hu u hu' (fun k hk => ?_)⟩
  · have := hf k hk; rw [Gv_lt hk] at this; exact this
  · rw [Gv_lt hk]; exact hfu k hk

end L

end ZKraw

#print axioms ZKraw.inC_trunc
#print axioms ZKraw.allB_sound
#print axioms ZKraw.lip_stair
#print axioms ZKraw.ks_of_chk
#print axioms ZKraw.krawczyk
