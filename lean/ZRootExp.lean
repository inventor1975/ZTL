import ZRootAbs
/-!
# ZRootExp — a sign change of a law WITH `exp` gives a root on VR's continuum. Zero axioms.

Step 2 of the root programme (curator, 2026-11-08: "Начинай"): `ZRootAbs` holds for an abstract family with an
approximate rational oracle; here the family is a law built from `+ − · ^n` and `exp`, read three ways.

* THE SLOPE READING `slX`: an interval `K` with `F(y) − F(x) = s·(y − x)` for some `s ∈ K` — kept under a double
  negation (`SlIn`), so no division and no decision of `y = x`; the conclusions drawn from it are inequalities,
  which are stable. The exponential's chord lies between its end slopes (`ExpSlope`): `(y−x)·eˣ ≤ eʸ − eˣ ≤
  (y−x)·eʸ`; VR's `rexpR` satisfies it (from `ZExp.E_slope`).
* THE VALUE READING `ivX` (from `ZXE`) — the end signs.
* THE ORACLE: the law evaluated termwise on rationals, `exp ↦ eseq · n` — VR's own sequence for the value at a
  rational point; it converges uniformly on bounded sets (`E_unif`, `E_lip`).

Contents: the slope reading and its soundness (any `CF`, `slX_sound`); monotonicity and end signs (`mono_of_slX`,
`lo_end`, `hi_end`); VR's chord law (`r_slope`); the oracle's uniform convergence (`uc_evq`, `orac_of`); the kernel
certificate `chkE` and **`exp_root`**: existence AND uniqueness of the root. Example: the omega constant
(`x·eˣ = 1`), `omega_exists`. Not covered yet: division, `ln` (they need a lower bound away from 0), parameters.
-/

namespace ZRootExp
open VR.CSR ZNumBin ZField ZPoly ZIv ZDivIv ZExpLaw ZExpIv ZXE

section Slope
variable {α : Type} (S : CF α)

/-- The exponential's chord lies between its end slopes. -/
def ExpSlope (ex : α → α) : Prop :=
  ∀ x y : α, S.le x y → S.le (S.mul (S.add y (S.neg x)) (ex x)) (S.add (ex y) (S.neg (ex x))) ∧
    S.le (S.add (ex y) (S.neg (ex x))) (S.mul (S.add y (S.neg x)) (ex y))

/-- `Δ = s·d` for some `s ∈ K` — not refuted. -/
def SlIn (Δ d : α) (K : Iv) : Prop := ¬¬ ∃ s, Mem S s K ∧ S.r Δ (S.mul s d)

variable {S}

theorem sl_bind {Δ d Δ' : α} {K K' : Iv} (h : SlIn S Δ d K)
    (k : ∀ s, Mem S s K → S.r Δ (S.mul s d) → SlIn S Δ' d K') : SlIn S Δ' d K' :=
  fun hn => h (fun ⟨s, hs, he⟩ => k s hs he hn)

theorem sl_ret {Δ d s : α} {K : Iv} (hs : Mem S s K) (he : S.r Δ (S.mul s d)) : SlIn S Δ d K :=
  fun hn => hn ⟨s, hs, he⟩

theorem sl_congr {Δ Δ' d : α} {K : Iv} (e : S.r Δ' Δ) (h : SlIn S Δ d K) : SlIn S Δ' d K :=
  sl_bind h (fun _ hs he => sl_ret hs (S.trans e he))

theorem sl_add {Δ1 Δ2 d : α} {K1 K2 K : Iv} (h1 : SlIn S Δ1 d K1) (h2 : SlIn S Δ2 d K2)
    (h : ivAdd K1 K2 = some K) : SlIn S (S.add Δ1 Δ2) d K :=
  sl_bind h1 fun s1 m1 e1 => sl_bind h2 fun s2 m2 e2 =>
    sl_ret (mem_add S m1 m2 h) (S.trans (S.add_congr e1 e2) (by cr_ring S.toCR))

theorem sl_sub {Δ1 Δ2 d : α} {K1 K2 K : Iv} (h1 : SlIn S Δ1 d K1) (h2 : SlIn S Δ2 d K2)
    (h : ivSub K1 K2 = some K) : SlIn S (S.add Δ1 (S.neg Δ2)) d K :=
  sl_bind h1 fun s1 m1 e1 => sl_bind h2 fun s2 m2 e2 =>
    sl_ret (mem_sub S m1 m2 h) (S.trans (S.add_congr e1 (S.neg_congr e2)) (by cr_ring S.toCR))

theorem sl_mulR {Δ d w : α} {K V K' : Iv} (h : SlIn S Δ d K) (hw : Mem S w V) (hK : ivMul K V = some K') :
    SlIn S (S.mul Δ w) d K' :=
  sl_bind h fun s hs he => sl_ret (mem_mul S hs hw hK) (S.trans (S.mul_congr he (S.refl _)) (by cr_ring S.toCR))

theorem sl_mulL {Δ d w : α} {K V K' : Iv} (hw : Mem S w V) (h : SlIn S Δ d K) (hK : ivMul V K = some K') :
    SlIn S (S.mul w Δ) d K' :=
  sl_bind h fun s hs he => sl_ret (mem_mul S hw hs hK) (S.trans (S.mul_congr (S.refl _) he) (by cr_ring S.toCR))

/-- The chord quotient of a nonnegative difference lies between the end values. -/
theorem chord_aux {ex : α → α} {x y t : α}
    (hb : S.le (S.mul (S.add y (S.neg x)) (ex x)) (S.add (ex y) (S.neg (ex x))) ∧
      S.le (S.add (ex y) (S.neg (ex x))) (S.mul (S.add y (S.neg x)) (ex y)))
    (ht : S.r (S.mul (S.add y (S.neg x)) t) S.one) (ht0 : S.le S.zero t) :
    S.le (ex x) (S.mul (S.add (ex y) (S.neg (ex x))) t) ∧ S.le (S.mul (S.add (ex y) (S.neg (ex x))) t) (ex y) := by
  have l1 := le_mul_left' S hb.1 ht0
  have l2 := le_mul_left' S hb.2 ht0
  have e1 : S.r (S.mul t (S.mul (S.add y (S.neg x)) (ex x))) (S.mul (S.mul (S.add y (S.neg x)) t) (ex x)) := by
    cr_ring S.toCR
  have e2 : S.r (S.mul t (S.mul (S.add y (S.neg x)) (ex y))) (S.mul (S.mul (S.add y (S.neg x)) t) (ex y)) := by
    cr_ring S.toCR
  have f1 := S.trans e1 (S.trans (S.mul_congr ht (S.refl _)) (S.one_mul _))
  have f2 := S.trans e2 (S.trans (S.mul_congr ht (S.refl _)) (S.one_mul _))
  have g : S.r (S.mul t (S.add (ex y) (S.neg (ex x)))) (S.mul (S.add (ex y) (S.neg (ex x))) t) := S.mul_comm _ _
  exact ⟨S.le_respects f1 g l1, S.le_respects g f2 l2⟩

/-- A reciprocal of a positive element is nonnegative. -/
theorem inv_nonneg {d t : α} (hd : S.pos d) (ht : S.r (S.mul d t) S.one) : S.le S.zero t := by
  apply S.le_of_not_pos
  intro hn
  have hn' : S.pos (S.neg t) := S.pos_congr (by cr_ring S.toCR) hn
  have p := S.pos_mul hd hn'
  have e : S.r (S.mul d (S.neg t)) (S.neg S.one) :=
    S.trans (by cr_ring S.toCR : S.r _ (S.neg (S.mul d t))) (S.neg_congr ht)
  exact S.pos_not_le (S.pos_congr e p) (by cr_linarith S.toOCR [])

/-- **THE CHORD OF `exp`**: `e^{u'} − e^{u} = σ·(u' − u)` with `σ` in any interval holding both end values. -/
theorem exp_chord {ex : α → α} (H : ExpLaws S ex) (Hs : ExpSlope S ex) {u u' : α} {V : Iv}
    (hu : Mem S (ex u) V) (hu' : Mem S (ex u') V) :
    SlIn S (S.add (ex u') (S.neg (ex u))) (S.add u' (S.neg u)) V := by
  intro hn
  apply nn_case (ap S (S.add u' (S.neg u)))
  · intro hap
    obtain ⟨t, ht⟩ := S.inv hap
    cases hap with
    | inl hpos =>
        have h0 := S.pos_nonneg hpos
        have hle : S.le u u' := by cr_linarith S.toOCR [h0]
        obtain ⟨c1, c2⟩ := chord_aux (Hs u u' hle) ht (inv_nonneg hpos ht)
        refine hn ⟨S.mul (S.add (ex u') (S.neg (ex u))) t,
          ⟨S.le_trans hu.1 c1, S.le_trans c2 hu'.2⟩, ?_⟩
        refine S.symm (S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add (ex u') (S.neg (ex u)))
          (S.mul (S.add u' (S.neg u)) t))) ?_)
        exact S.trans (S.mul_congr (S.refl _) ht) (S.trans (S.mul_comm _ _) (S.one_mul _))
    | inr hneg =>
        have h0 := S.pos_nonneg hneg
        have hle : S.le u' u := by cr_linarith S.toOCR [h0]
        have hpos' : S.pos (S.add u (S.neg u')) := S.pos_congr (by cr_ring S.toCR) hneg
        have ht' : S.r (S.mul (S.add u (S.neg u')) (S.neg t)) S.one :=
          S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add u' (S.neg u)) t)) ht
        obtain ⟨c1, c2⟩ := chord_aux (Hs u' u hle) ht' (inv_nonneg hpos' ht')
        have eσ : S.r (S.mul (S.add (ex u) (S.neg (ex u'))) (S.neg t)) (S.mul (S.add (ex u') (S.neg (ex u))) t) := by
          cr_ring S.toCR
        refine hn ⟨S.mul (S.add (ex u') (S.neg (ex u))) t,
          ⟨S.le_trans hu'.1 (S.le_respects (S.refl _) eσ c1), S.le_trans (S.le_respects eσ (S.refl _) c2) hu.2⟩, ?_⟩
        refine S.symm (S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add (ex u') (S.neg (ex u)))
          (S.mul (S.add u' (S.neg u)) t))) ?_)
        exact S.trans (S.mul_congr (S.refl _) ht) (S.trans (S.mul_comm _ _) (S.one_mul _))
  · intro hna
    have hz := S.ap_tight hna
    have huu : S.r u' u := S.trans (by cr_ring S.toCR : S.r u' (S.add u (S.add u' (S.neg u))))
      (S.trans (S.add_congr (S.refl _) hz) (S.trans (S.add_comm _ _) (S.zero_add _)))
    have he := H.congr huu
    refine hn ⟨ex u, hu, ?_⟩
    refine S.trans (S.add_congr he (S.refl _)) (S.trans (S.add_neg _) ?_)
    exact S.symm (S.trans (S.mul_congr (S.refl _) hz) (by cr_ring S.toCR))

/-- Slopes compose: `Δ = σ·δ`, `δ = s·d` give `Δ = (σ s)·d`. -/
theorem sl_comp {Δ δ d : α} {V Kp K : Iv} (h1 : SlIn S Δ δ V) (h2 : SlIn S δ d Kp) (hK : ivMul V Kp = some K) :
    SlIn S Δ d K :=
  fun hn => h1 (fun ⟨σ, hσ, e1⟩ => h2 (fun ⟨s, hs, e2⟩ => hn ⟨S.mul σ s, mem_mul S hσ hs hK,
    S.trans e1 (S.trans (S.mul_congr (S.refl _) e2) (by cr_ring S.toCR))⟩))

/-- A reading with a reciprocal is apart from zero. -/
theorem ap_of_inv {x : α} {I J : Iv} (hx : Mem S x I) (h : ivInv I = some J) : ap S x := by
  unfold ivInv at h
  cases hp : posX I.1 with
  | true => exact Or.inl (S.pos_mono (pos_of_posX S hp) hx.1)
  | false =>
      rw [hp] at h
      cases hn : negX I.2 with
      | false => rw [hn] at h; cases h
      | true =>
          have p2 : S.pos (dv S.toOH (dneg I.2)) := pos_of_posX S (d := dneg I.2) hn
          have e := dv_neg S.toOH I.2
          have l : S.le (dv S.toOH (dneg I.2)) (S.neg x) :=
            S.le_respects (S.symm e) (S.refl _) (by cr_linarith S.toOCR [hx.2])
          exact Or.inr (S.pos_mono p2 l)

/-- **THE SLOPE OF A QUOTIENT**: `v' − v = w'·((a' − a) − v·(b' − b))` with `b'·w' = 1`. -/
theorem sl_div {va va' vb vb' v v' d : α} {Ka Kb Vv Vq W M T K : Iv}
    (ha : SlIn S (S.add va' (S.neg va)) d Ka) (hb : SlIn S (S.add vb' (S.neg vb)) d Kb)
    (hv : Mem S v Vv) (hq' : Mem S vb' Vq) (hap' : ap S vb')
    (e1 : S.r (S.mul vb v) va) (e2 : S.r (S.mul vb' v') va')
    (hW : ivInv Vq = some W) (hM : ivMul Vv Kb = some M) (hT : ivSub Ka M = some T) (hK : ivMul W T = some K) :
    SlIn S (S.add v' (S.neg v)) d K := by
  obtain ⟨w, hw⟩ := S.inv hap'
  have mw := mem_inv S hq' hW hw
  have hK' := sl_mulL mw (sl_sub ha (sl_mulL hv hb hM) hT) hK
  refine sl_congr (S.symm ?_) hK'
  refine S.trans (S.mul_congr (S.refl _) (S.add_congr (S.add_congr (S.symm e2) (S.neg_congr (S.symm e1))) (S.refl _))) ?_
  refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.mul vb' w) (S.add v' (S.neg v)))) ?_
  exact S.trans (S.mul_congr hw (S.refl _)) (S.one_mul _)

/-- **THE SLOPE OF `ln`**: `a' − a = τ·(v' − v)` with `τ` in `a`'s reading (the chord of `exp`), so
`v' − v = w·(a' − a)` with `τ·w = 1`. -/
theorem sl_ln {ex : α → α} (H : ExpLaws S ex) (Hs : ExpSlope S ex) {va va' v v' d : α} {Ka Va W K : Iv}
    (ha : SlIn S (S.add va' (S.neg va)) d Ka) (hm : Mem S va Va) (hm' : Mem S va' Va)
    (e1 : S.r (ex v) va) (e2 : S.r (ex v') va') (hW : ivInv Va = some W) (hK : ivMul W Ka = some K) :
    SlIn S (S.add v' (S.neg v)) d K := by
  have ch := exp_chord H Hs (mem_congr S e1 hm) (mem_congr S e2 hm')
  intro hn
  apply ch
  intro ⟨τ, hτ, eτ⟩
  apply ha
  intro ⟨s, hs, es⟩
  obtain ⟨w, hw⟩ := S.inv (ap_of_inv hτ hW)
  have mw := mem_inv S hτ hW hw
  refine hn ⟨S.mul w s, mem_mul S mw hs hK, ?_⟩
  refine S.trans (S.symm (S.one_mul _)) (S.trans (S.mul_congr (S.symm hw) (S.refl _)) ?_)
  refine S.trans (by cr_ring S.toCR : S.r _ (S.mul w (S.mul τ (S.add v' (S.neg v))))) ?_
  refine S.trans (S.mul_congr (S.refl _) (S.symm eτ)) ?_
  refine S.trans (S.mul_congr (S.refl _) (S.add_congr e2 (S.neg_congr e1))) ?_
  exact S.trans (S.mul_congr (S.refl _) es) (by cr_ring S.toCR)

end Slope

/-! ## The slope reading -/

def dz0 : D := ⟨⟨0, 0⟩, 0⟩
def zI : Iv := (dz0, dz0)

/-- Slopes of `aⁿ` from `a`'s slope `Ka` and value `Va`: `a'ⁿ⁺¹ − aⁿ⁺¹ = (a' − a)·a'ⁿ + a·(a'ⁿ − aⁿ)`. -/
def slPow (Ka Va : Iv) : Nat → Option Iv
  | 0 => some zI
  | n + 1 => match slPow Ka Va n with
      | none => none
      | some Kn => match ivPow Va n with
        | none => none
        | some Pn => lift2 ivAdd (ivMul Ka Pn) (ivMul Va Kn)

/-- THE SLOPE READING over a box: `p'q' − pq = (p' − p)·q' + p·(q' − q)`; `e^{u'} − e^{u} = σ·(u' − u)` with `σ`
in the value interval of `exp u`. Division: `v' − v = w'·((a' − a) − v·(b' − b))`, `b'w' = 1`; `ln`: `v' − v = w·(a' − a)`, `w` in the
reciprocal of `a`'s reading. -/
def slX (B : Box) (V : Nat → Iv) : XE → Option Iv
  | .var i => some (V i)
  | .cst _ => some zI
  | .add p q => lift2 ivAdd (slX B V p) (slX B V q)
  | .sub p q => lift2 ivSub (slX B V p) (slX B V q)
  | .mul p q => match slX B V p with
      | none => none
      | some Kp => match slX B V q with
        | none => none
        | some Kq => match ivX B p with
          | none => none
          | some Vp => match ivX B q with
            | none => none
            | some Vq => lift2 ivAdd (ivMul Kp Vq) (ivMul Vp Kq)
  | .pow p n => match slX B V p with
      | none => none
      | some Kp => match ivX B p with
        | none => none
        | some Vp => slPow Kp Vp n
  | .exp p => match slX B V p with
      | none => none
      | some Kp => match ivX B (.exp p) with
        | none => none
        | some V => ivMul V Kp
  | .div p q => match slX B V p with
      | none => none
      | some Kp => match slX B V q with
        | none => none
        | some Kq => match ivX B (.div p q) with
          | none => none
          | some Vv => match ivX B q with
            | none => none
            | some Vq => match ivInv Vq with
              | none => none
              | some W => match ivMul Vv Kq with
                | none => none
                | some M => match ivSub Kp M with
                  | none => none
                  | some T => ivMul W T
  | .ln p => match slX B V p with
      | none => none
      | some Kp => match ivX B p with
        | none => none
        | some Vp => match ivInv Vp with
          | none => none
          | some W => ivMul W Kp

section Sound
variable {α : Type} {S : CF α}

theorem mem_zI : Mem S S.zero zI := mem_congr S (S.symm (zv_isZ S.toOH (c := dz0) rfl)) (mem_cst S dz0)

theorem sl_pow {d va va' : α} {Ka Va : Iv} (ha : SlIn S (S.add va' (S.neg va)) d Ka)
    (hm : Mem S va Va) (hm' : Mem S va' Va) :
    ∀ n K, slPow Ka Va n = some K → SlIn S (S.add (powS S.toOH va' n) (S.neg (powS S.toOH va n))) d K
  | 0, K, h => by
      cases h
      exact sl_ret mem_zI (S.trans (S.add_neg _) (S.symm (S.zero_mul _)))
  | n + 1, K, h => by
      unfold slPow at h
      cases h1 : slPow Ka Va n with
      | none => rw [h1] at h; cases h
      | some Kn =>
        cases h2 : ivPow Va n with
        | none => rw [h1, h2] at h; cases h
        | some Pn =>
          rw [h1, h2] at h
          obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
          have A := sl_mulR ha (mem_pow S hm' n Pn h2) ex
          have B := sl_mulL hm (sl_pow ha hm hm' n Kn h1) ey
          refine sl_congr ?_ (sl_add A B hk)
          show S.r (S.add (S.mul va' (powS S.toOH va' n)) (S.neg (S.mul va (powS S.toOH va n)))) _
          cr_ring S.toCR

/-- **THE SLOPE READING IS SOUND**: at two points of the box whose coordinates differ by `sᵢ·d`, `sᵢ ∈ Vᵢ`, the values
`v, v'` of `e` satisfy `v' − v = s·d` for some `s` in the reading — not refuted. -/
theorem slX_sound {ex : α → α} (H : ExpLaws S ex) (Hs : ExpSlope S ex) {B : Box} {V : Nat → Iv}
    {p q : Nat → α} {d : α}
    (hp : InBox S B p) (hq : InBox S B q) (hd : ∀ i, SlIn S (S.add (q i) (S.neg (p i))) d (V i)) :
    ∀ (e : XE) {v v' : α} {K : Iv}, Val S ex p e v → Val S ex q e v' → slX B V e = some K →
      SlIn S (S.add v' (S.neg v)) d K
  | .var i, v, v', K, hv, hv', h => by
      cases hv with
      | var e1 =>
      cases hv' with
      | var e2 =>
      cases h
      exact sl_congr (S.add_congr e2 (S.neg_congr e1)) (hd i)
  | .cst c, v, v', K, hv, hv', h => by
      cases hv with
      | cst e1 =>
      cases hv' with
      | cst e2 =>
      cases h
      exact sl_ret mem_zI (S.trans (S.add_congr e2 (S.neg_congr e1)) (S.trans (S.add_neg _) (S.symm (S.zero_mul _))))
  | .add a b, v, v', K, hv, hv', h => by
      cases hv with
      | add ha hb e1 =>
      cases hv' with
      | add ha' hb' e2 =>
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      refine sl_congr ?_ (sl_add (slX_sound H Hs hp hq hd a ha ha' ex) (slX_sound H Hs hp hq hd b hb hb' ey) hk)
      exact S.trans (S.add_congr e2 (S.neg_congr e1)) (by cr_ring S.toCR)
  | .sub a b, v, v', K, hv, hv', h => by
      cases hv with
      | sub ha hb e1 =>
      cases hv' with
      | sub ha' hb' e2 =>
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      refine sl_congr ?_ (sl_sub (slX_sound H Hs hp hq hd a ha ha' ex) (slX_sound H Hs hp hq hd b hb hb' ey) hk)
      exact S.trans (S.add_congr e2 (S.neg_congr e1)) (by cr_ring S.toCR)
  | .mul a b, v, v', K, hv, hv', h => by
      cases hv with
      | @mul _ _ va vb _ ha hb e1 =>
      cases hv' with
      | @mul _ _ va' vb' _ ha' hb' e2 =>
      unfold slX at h
      cases h1 : slX B V a with
      | none => rw [h1] at h; cases h
      | some Ka =>
      cases h2 : slX B V b with
      | none => rw [h1, h2] at h; cases h
      | some Kb =>
      cases h3 : ivX B a with
      | none => rw [h1, h2, h3] at h; cases h
      | some Va =>
      cases h4 : ivX B b with
      | none => rw [h1, h2, h3, h4] at h; cases h
      | some Vb =>
      rw [h1, h2, h3, h4] at h
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      have A := sl_mulR (slX_sound H Hs hp hq hd a ha ha' h1) (ivX_sound S hq hb' Vb h4) ex
      have B := sl_mulL (ivX_sound S hp ha Va h3) (slX_sound H Hs hp hq hd b hb hb' h2) ey
      refine sl_congr ?_ (sl_add A B hk)
      exact S.trans (S.add_congr e2 (S.neg_congr e1)) (by cr_ring S.toCR)
  | .pow a n, v, v', K, hv, hv', h => by
      cases hv with
      | @pow _ va _ _ ha e1 =>
      cases hv' with
      | @pow _ va' _ _ ha' e2 =>
      unfold slX at h
      cases h1 : slX B V a with
      | none => rw [h1] at h; cases h
      | some Ka =>
      cases h3 : ivX B a with
      | none => rw [h1, h3] at h; cases h
      | some Va =>
      rw [h1, h3] at h
      refine sl_congr (S.add_congr e2 (S.neg_congr e1)) (sl_pow (slX_sound H Hs hp hq hd a ha ha' h1)
        (ivX_sound S hp ha Va h3) (ivX_sound S hq ha' Va h3) n K h)
  | .exp a, v, v', K, hv, hv', h => by
      cases hv with
      | @exp _ va _ H1 ha e1 =>
      cases hv' with
      | @exp _ va' _ H2 ha' e2 =>
      unfold slX at h
      cases h1 : slX B V a with
      | none => rw [h1] at h; cases h
      | some Ka =>
      cases h3 : ivX B (.exp a) with
      | none => rw [h1, h3] at h; cases h
      | some V =>
      rw [h1, h3] at h
      have m := ivX_sound S hp (Val.exp H ha (S.refl _)) V h3
      have m' := ivX_sound S hq (Val.exp H ha' (S.refl _)) V h3
      exact sl_congr (S.add_congr e2 (S.neg_congr e1))
        (sl_comp (exp_chord H Hs m m') (slX_sound H Hs hp hq hd a ha ha' h1) h)
  | .div a b, v, v', K, hv, hv', h => by
      cases hv with
      | @div _ _ va vb _ ha hb hap e1 =>
      cases hv' with
      | @div _ _ va' vb' _ ha' hb' hap' e2 =>
      unfold slX at h
      cases h1 : slX B V a with
      | none => rw [h1] at h; cases h
      | some Ka =>
      rw [h1] at h; dsimp only at h
      cases h2 : slX B V b with
      | none => rw [h2] at h; cases h
      | some Kb =>
      rw [h2] at h; dsimp only at h
      cases h3 : ivX B (.div a b) with
      | none => rw [h3] at h; cases h
      | some Vv =>
      rw [h3] at h; dsimp only at h
      cases h4 : ivX B b with
      | none => rw [h4] at h; cases h
      | some Vq =>
      rw [h4] at h; dsimp only at h
      cases h5 : ivInv Vq with
      | none => rw [h5] at h; cases h
      | some W =>
      rw [h5] at h; dsimp only at h
      cases h6 : ivMul Vv Kb with
      | none => rw [h6] at h; cases h
      | some M =>
      rw [h6] at h; dsimp only at h
      cases h7 : ivSub Ka M with
      | none => rw [h7] at h; cases h
      | some T =>
      rw [h7] at h; dsimp only at h
      exact sl_div (slX_sound H Hs hp hq hd a ha ha' h1) (slX_sound H Hs hp hq hd b hb hb' h2)
        (ivX_sound S hp (Val.div ha hb hap e1) Vv h3) (ivX_sound S hq hb' Vq h4) hap' e1 e2 h5 h6 h7 h
  | .ln a, v, v', K, hv, hv', h => by
      cases hv with
      | @ln _ va _ H1 ha _ e1 =>
      cases hv' with
      | @ln _ va' _ H2 ha' _ e2 =>
      unfold slX at h
      cases h1 : slX B V a with
      | none => rw [h1] at h; cases h
      | some Ka =>
      rw [h1] at h; dsimp only at h
      cases h2 : ivX B a with
      | none => rw [h2] at h; cases h
      | some Va =>
      rw [h2] at h; dsimp only at h
      cases h3 : ivInv Va with
      | none => rw [h3] at h; cases h
      | some W =>
      rw [h3] at h; dsimp only at h
      exact sl_ln H Hs (slX_sound H Hs hp hq hd a ha ha' h1) (ivX_sound S hp ha Va h2) (ivX_sound S hq ha' Va h2)
        e1 e2 h3 h

end Sound

/-! ## The law as a function: monotone with the read slopes, signed at the ends by the value reading -/

def isE : XE → Bool
  | .var _ => true
  | .cst _ => true
  | .add a b => isE a && isE b
  | .sub a b => isE a && isE b
  | .mul a b => isE a && isE b
  | .pow a _ => isE a
  | .exp a => isE a
  | .div _ _ => false
  | .ln _ => false

theorem and2 {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

section Law
variable {α : Type} (S : CF α)

/-- The value of an `exp`-law (no division, no `ln`): total. -/
def evX (ex : α → α) (p : Nat → α) : XE → α
  | .var i => p i
  | .cst c => dv S.toOH c
  | .add a b => S.add (evX ex p a) (evX ex p b)
  | .sub a b => S.add (evX ex p a) (S.neg (evX ex p b))
  | .mul a b => S.mul (evX ex p a) (evX ex p b)
  | .pow a n => powS S.toOH (evX ex p a) n
  | .exp a => ex (evX ex p a)
  | .div _ _ => S.zero
  | .ln _ => S.zero

variable {S}

theorem val_evX {ex : α → α} (H : ExpLaws S ex) (p : Nat → α) :
    ∀ e : XE, isE e = true → Val S ex p e (evX S ex p e)
  | .var _, _ => .var (S.refl _)
  | .cst _, _ => .cst (S.refl _)
  | .add a b, h => .add (val_evX H p a (and2 h).1) (val_evX H p b (and2 h).2) (S.refl _)
  | .sub a b, h => .sub (val_evX H p a (and2 h).1) (val_evX H p b (and2 h).2) (S.refl _)
  | .mul a b, h => .mul (val_evX H p a (and2 h).1) (val_evX H p b (and2 h).2) (S.refl _)
  | .pow a n, h => .pow n (val_evX H p a h) (S.refl _)
  | .exp a, h => .exp H (val_evX H p a h) (S.refl _)
  | .div _ _, h => by cases h
  | .ln _, h => by cases h

/-- The one-variable box `[a, b]` (every variable is `x`). -/
def cB (a b : D) : Box := fun _ => some (a, b)

theorem inbox_c {a b : D} {x : α} (h1 : S.le (dv S.toOH a) x) (h2 : S.le x (dv S.toOH b)) :
    InBox S (cB a b) (fun _ => x) := fun _ _ h => by cases h; exact ⟨h1, h2⟩

/-- **MONOTONE WITH THE READ SLOPES**: `c ≤ K.lo`, `K.hi ≤ L` give `c·(y−x) ≤ F y − F x ≤ L·(y−x)` on `[a, b]`. -/
theorem mono_of_slX {ex : α → α} (H : ExpLaws S ex) (Hs : ExpSlope S ex) {e : XE} (hE : isE e = true)
    {a b : D} {K : Iv} (hK : slX (cB a b) (fun _ => ZIv.one) e = some K) {c L : α}
    (hc : S.le c (dv S.toOH K.1)) (hL : S.le (dv S.toOH K.2) L) :
    ZRootAbs.Mono S (fun x => evX S ex (fun _ => x) e) (dv S.toOH a) (dv S.toOH b) c L := by
  intro x y hax hxy hyb
  have sl := slX_sound H Hs (inbox_c hax (S.le_trans hxy hyb)) (inbox_c (S.le_trans hax hxy) hyb)
    (fun _ => sl_ret (mem_one S) (S.symm (S.one_mul _))) e (val_evX H _ e hE) (val_evX H _ e hE) hK
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

/-- The same for any function whose values are values of `e` on `[a, b]` (division and `ln` included). -/
theorem mono_of_val {ex : α → α} (H : ExpLaws S ex) (Hs : ExpSlope S ex) {e : XE} {F : α → α} {a b : D}
    (hF : ∀ x, S.le (dv S.toOH a) x → S.le x (dv S.toOH b) → Val S ex (fun _ => x) e (F x))
    {K : Iv} (hK : slX (cB a b) (fun _ => ZIv.one) e = some K) {c L : α}
    (hc : S.le c (dv S.toOH K.1)) (hL : S.le (dv S.toOH K.2) L) :
    ZRootAbs.Mono S F (dv S.toOH a) (dv S.toOH b) c L := by
  intro x y hax hxy hyb
  have hxb := S.le_trans hxy hyb
  have hay := S.le_trans hax hxy
  have sl := slX_sound H Hs (inbox_c hax hxb) (inbox_c hay hyb)
    (fun _ => sl_ret (mem_one S) (S.symm (S.one_mul _))) e (hF x hax hxb) (hF y hay hyb) hK
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

theorem dv_dz0 : S.r (dv S.toOH dz0) S.zero := zv_isZ S.toOH (c := dz0) rfl

/-- The value reading at the left end below zero gives `F(a) ≤ 0`. -/
theorem lo_end {ex : α → α} (H : ExpLaws S ex) {e : XE} (hE : isE e = true) {a : D} {K : Iv}
    (hK : ivX (cB a a) e = some K) (h : dle K.2 dz0 = true) :
    S.le (evX S ex (fun _ => dv S.toOH a) e) S.zero :=
  S.le_trans (ivX_sound S (inbox_c (S.le_refl _) (S.le_refl _)) (val_evX H _ e hE) K hK).2
    (S.le_respects (S.refl _) dv_dz0 (dle_sound S.toOH h))

/-- The value reading at the right end above zero gives `0 ≤ F(b)`. -/
theorem hi_end {ex : α → α} (H : ExpLaws S ex) {e : XE} (hE : isE e = true) {b : D} {K : Iv}
    (hK : ivX (cB b b) e = some K) (h : dle dz0 K.1 = true) :
    S.le S.zero (evX S ex (fun _ => dv S.toOH b) e) :=
  S.le_trans (S.le_respects dv_dz0 (S.refl _) (dle_sound S.toOH h))
    (ivX_sound S (inbox_c (S.le_refl _) (S.le_refl _)) (val_evX H _ e hE) K hK).1

theorem lo_val {ex : α → α} {e : XE} {a : D} {v : α} (hv : Val S ex (fun _ => dv S.toOH a) e v) {K : Iv}
    (hK : ivX (cB a a) e = some K) (h : dle K.2 dz0 = true) : S.le v S.zero :=
  S.le_trans (ivX_sound S (inbox_c (S.le_refl _) (S.le_refl _)) hv K hK).2
    (S.le_respects (S.refl _) dv_dz0 (dle_sound S.toOH h))

theorem hi_val {ex : α → α} {e : XE} {b : D} {v : α} (hv : Val S ex (fun _ => dv S.toOH b) e v) {K : Iv}
    (hK : ivX (cB b b) e = some K) (h : dle dz0 K.1 = true) : S.le S.zero v :=
  S.le_trans (S.le_respects dv_dz0 (S.refl _) (dle_sound S.toOH h))
    (ivX_sound S (inbox_c (S.le_refl _) (S.le_refl _)) hv K hK).1

end Law


/-! ## VR's `exp` satisfies the chord law (from `ZExp.E_slope` on the sequences) -/

section VRSlope
open VR VR.Numbers ZRealCF ZExp ZRealExp

/-- The smaller of two rationals (decided by `qle`). -/
def qmin (a b : QExpr) : QExpr :=
  match qle.decidable a b with
  | .isTrue _ => a
  | .isFalse _ => b

theorem qmin_cases (a b : QExpr) : (qmin a b = a ∧ qle a b) ∨ (qmin a b = b ∧ qle b a) := by
  unfold qmin
  cases qle.decidable a b with
  | isTrue h => exact Or.inl ⟨rfl, h⟩
  | isFalse h =>
      cases qle_total a b with
      | inl h' => exact absurd h' h
      | inr h' => exact Or.inr ⟨rfl, h'⟩

theorem qmin_le_l (a b : QExpr) : qle (qmin a b) a := by
  rcases qmin_cases a b with ⟨e, _⟩ | ⟨e, h⟩ <;> rw [e]
  · exact qle_refl _
  · exact h

theorem qmin_le_r (a b : QExpr) : qle (qmin a b) b := by
  rcases qmin_cases a b with ⟨e, h⟩ | ⟨e, _⟩ <;> rw [e]
  · exact h
  · exact qle_refl _

theorem qmin_close {a a' b b' e : QExpr} (ha : qclose a a' e) (hb : qclose b b' e) :
    qclose (qmin a b) (qmin a' b') e := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold qsub at a1 a2 b1 b2
  rcases qmin_cases a b with ⟨e1, h1⟩ | ⟨e1, h1⟩ <;> rcases qmin_cases a' b' with ⟨e2, h2⟩ | ⟨e2, h2⟩ <;>
    rw [e1, e2] <;> (constructor <;> (unfold qsub; rat_linarith))

/-- The termwise minimum of two reals. -/
def rmin (x y : RExpr) : RExpr := ⟨fun n => qmin (x.seq n) (y.seq n), fun k => by
  obtain ⟨N1, h1⟩ := x.cauchy k
  obtain ⟨N2, h2⟩ := y.cauchy k
  exact ⟨N1 + N2, fun m n hm hn => qmin_close
    (h1 m n (Nat.le_trans (Nat.le_add_right _ _) hm) (Nat.le_trans (Nat.le_add_right _ _) hn))
    (h2 m n (Nat.le_trans (Nat.le_add_left _ _) hm) (Nat.le_trans (Nat.le_add_left _ _) hn))⟩⟩

theorem rmin_eq {x y : RExpr} (h : rle x y) : rEq (rmin x y) x := by
  refine rle_antisymm (rle_of_eventually 0 fun n _ => qmin_le_l _ _) (fun k => ?_)
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h0 := qeps_nonneg k
  change qle (qsub (x.seq n) (qmin (x.seq n) (y.seq n))) (qeps k)
  rcases qmin_cases (x.seq n) (y.seq n) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> (unfold qsub at *; rat_linarith)

/-- The chord law for termwise ordered sequences. -/
theorem slope_ord {x y : RExpr} (hn : ∀ n, qle (x.seq n) (y.seq n)) :
    rle (rmul (radd y (rneg x)) (rexpR x)) (radd (rexpR y) (rneg (rexpR x))) ∧
    rle (radd (rexpR y) (rneg (rexpR x))) (rmul (radd y (rneg x)) (rexpR y)) := by
  obtain ⟨R, NR, R0, hR⟩ := bound2 x y
  constructor
  · intro k
    obtain ⟨C, hC, _⟩ := qexpr_bound R
    obtain ⟨K, hg⟩ := good_exists R
    obtain ⟨Nt, _, hNt⟩ := tm_small R0 hg (k + C)
    refine ⟨NR + Nt + 1, fun m hm => ?_⟩
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ n =>
    have nR : NR ≤ n + 1 := Nat.le_trans (Nat.le_trans (Nat.le_add_right NR Nt) (Nat.le_add_right _ 1)) hm
    have nt : Nt ≤ n := Nat.le_of_succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left Nt NR)) hm)
    obtain ⟨xR, yR, _⟩ := hR (n + 1) nR
    obtain ⟨lo, _⟩ := E_slope (hn (n + 1)) xR yR n
    have tt := hNt n nt
    have t0 := tm_nonneg R0 n
    have P0 : qle qzero (qofInt (pow2 C)) := qofInt_le (pow2_nonneg C)
    obtain ⟨x1, x2⟩ := xR
    obtain ⟨y1, y2⟩ := yR
    unfold qsub at x1 x2 y1 y2 hC
    have dxy : qle (qsub (y.seq (n + 1)) (x.seq (n + 1))) (qadd (qofInt (pow2 C)) (qofInt (pow2 C))) := by
      unfold qsub; rat_linarith
    have s1 := scale dxy t0
    have e1 : qEq (qmul (qadd (qofInt (pow2 C)) (qofInt (pow2 C))) (tm R n))
        (qmul (qofInt (pow2 C)) (qadd (tm R n) (tm R n))) := by rat_ring
    have s2 := scale_l tt P0
    have e2 := qpow2_mul_eps C k
    have e3 : qEq (qmul (qsub (y.seq (n + 1)) (x.seq (n + 1))) (qsub (eseq (x.seq (n + 1)) (n + 1)) (tm R n)))
        (qadd (qmul (qsub (y.seq (n + 1)) (x.seq (n + 1))) (eseq (x.seq (n + 1)) (n + 1)))
          (qneg (qmul (qsub (y.seq (n + 1)) (x.seq (n + 1))) (tm R n)))) := by unfold qsub; rat_ring
    change qle (qsub (qmul (qadd (y.seq (n + 1)) (qneg (x.seq (n + 1)))) (eseq (x.seq (n + 1)) (n + 1)))
      (qadd (eseq (y.seq (n + 1)) (n + 1)) (qneg (eseq (x.seq (n + 1)) (n + 1))))) (qeps k)
    unfold qsub at lo s1 e3 ⊢
    rat_linarith
  · refine rle_of_eventually (NR + 1) fun m hm => ?_
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ n =>
    obtain ⟨xR, yR, _⟩ := hR (n + 1) (Nat.le_trans (Nat.le_add_right _ _) hm)
    obtain ⟨_, up⟩ := E_slope (hn (n + 1)) xR yR n
    unfold qsub at up
    exact up

/-- **VR's `exp` SATISFIES THE CHORD LAW.** -/
theorem r_slope : ExpSlope rCF rexpR := by
  intro x y h
  have e : rEq (rmin x y) x := rmin_eq h
  obtain ⟨l, u⟩ := slope_ord (x := rmin x y) (y := y) (fun n => qmin_le_r _ _)
  have ex := r_congr e
  have ed : rCF.r (rCF.add y (rCF.neg (rmin x y))) (rCF.add y (rCF.neg x)) :=
    rCF.add_congr (rCF.refl y) (rCF.neg_congr e)
  have eE : rCF.r (rCF.add (rexpR y) (rCF.neg (rexpR (rmin x y)))) (rCF.add (rexpR y) (rCF.neg (rexpR x))) :=
    rCF.add_congr (rCF.refl _) (rCF.neg_congr ex)
  exact ⟨rCF.le_respects (rCF.mul_congr ed ex) eE l, rCF.le_respects eE (rCF.mul_congr ed (rCF.refl _)) u⟩

end VRSlope

/-! ## The oracle: the law read termwise on rationals, uniformly convergent on bounded sets -/

section Oracle
open VR VR.Numbers ZRealCF ZExp ZRealExp

def qpw (x : QExpr) : Nat → QExpr
  | 0 => qone
  | k + 1 => qmul x (qpw x k)

/-- The `n`-th rational reading of the law at `q`: VR's own `n`-th term, `exp ↦ eseq · n`. -/
def evq (n : Nat) (q : QExpr) : XE → QExpr
  | .var _ => q
  | .cst c => qD c
  | .add a b => qadd (evq n q a) (evq n q b)
  | .sub a b => qadd (evq n q a) (qneg (evq n q b))
  | .mul a b => qmul (evq n q a) (evq n q b)
  | .pow a k => qpw (evq n q a) k
  | .exp a => eseq (evq n q a) n
  | .div _ _ => qzero
  | .ln _ => qzero

theorem qpw_respects {x y : QExpr} (h : qEq x y) : ∀ k, qEq (qpw x k) (qpw y k)
  | 0 => qEq_refl _
  | k + 1 => qmul_respects h (qpw_respects h k)

theorem evq_respects (n : Nat) {q q' : QExpr} (h : qEq q q') : ∀ e : XE, qEq (evq n q e) (evq n q' e)
  | .var _ => h
  | .cst _ => qEq_refl _
  | .add a b => qadd_respects (evq_respects n h a) (evq_respects n h b)
  | .sub a b => qadd_respects (evq_respects n h a) (qneg_respects (evq_respects n h b))
  | .mul a b => qmul_respects (evq_respects n h a) (evq_respects n h b)
  | .pow a k => qpw_respects (evq_respects n h a) k
  | .exp a => eseq_respects (evq_respects n h a) n
  | .div _ _ => qEq_refl _
  | .ln _ => qEq_refl _

theorem powS_seq (x : RExpr) (n : Nat) : ∀ k, qEq ((powS rCF.toOH x k).seq n) (qpw (x.seq n) k)
  | 0 => qEq_refl _
  | k + 1 => qmul_respects (qEq_refl _) (powS_seq x n k)

/-- The value's `n`-th term IS the rational reading at the argument's `n`-th term. -/
theorem evX_seq (x : RExpr) (n : Nat) : ∀ e : XE,
    qEq ((evX rCF rexpR (fun _ => x) e).seq n) (evq n (x.seq n) e)
  | .var _ => qEq_refl _
  | .cst c => dv_seq c n
  | .add a b => qadd_respects (evX_seq x n a) (evX_seq x n b)
  | .sub a b => qadd_respects (evX_seq x n a) (qneg_respects (evX_seq x n b))
  | .mul a b => qmul_respects (evX_seq x n a) (evX_seq x n b)
  | .pow a k => qEq_trans (powS_seq _ n k) (qpw_respects (evX_seq x n a) k)
  | .exp a => eseq_respects (evX_seq x n a) n
  | .div _ _ => qEq_refl _
  | .ln _ => qEq_refl _

theorem le_a {A B m : Nat} (h : A + B + 1 ≤ m) : A ≤ m :=
  Nat.le_trans (Nat.le_trans (Nat.le_add_right A B) (Nat.le_add_right _ 1)) h
theorem le_b {A B m : Nat} (h : A + B + 1 ≤ m) : B ≤ m :=
  Nat.le_trans (Nat.le_trans (Nat.le_add_left B A) (Nat.le_add_right _ 1)) h
theorem le_1 {A B m : Nat} (h : A + B + 1 ≤ m) : 1 ≤ m := Nat.le_trans (Nat.le_add_left 1 _) h

/-- Uniformly bounded (from some index on) and uniformly Cauchy on every bounded set of ENVIRONMENTS
(rational values of the variables, all within `R`). -/
def UCo (f : Nat → (Nat → QExpr) → QExpr) : Prop :=
  ∀ R, qle qzero R → ∃ C B0 : Nat,
    (∀ n (q : Nat → QExpr), B0 ≤ n → (∀ i, qclose (q i) qzero R) → qclose (f n q) qzero (qofInt (pow2 C))) ∧
    ∀ k, ∃ N, B0 ≤ N ∧ ∀ m n (q : Nat → QExpr), N ≤ m → N ≤ n → (∀ i, qclose (q i) qzero R) →
      qclose (f m q) (f n q) (qeps k)

theorem lA {A B m : Nat} (h : A + B ≤ m) : A ≤ m := Nat.le_trans (Nat.le_add_right A B) h
theorem lB {A B m : Nat} (h : A + B ≤ m) : B ≤ m := Nat.le_trans (Nat.le_add_left B A) h

theorem close_up {x B : QExpr} {C : Nat} (h : qclose x qzero B) (hB : qclose B qzero (qofInt (pow2 C))) :
    qclose x qzero (qofInt (pow2 C)) := by
  obtain ⟨h1, h2⟩ := h; obtain ⟨b1, _⟩ := hB
  unfold qsub at h1 h2 b1
  constructor <;> (unfold qsub; rat_linarith)

theorem uc_const (c : QExpr) : UCo (fun _ _ => c) := by
  intro R _
  obtain ⟨C, hC⟩ := qexpr_bound c
  exact ⟨C, 0, fun _ _ _ _ => hC, fun k => ⟨0, Nat.le_refl _, fun _ _ _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩⟩

theorem uc_var (j : Nat) : UCo (fun _ q => q j) := by
  intro R R0
  obtain ⟨C, hC⟩ := qexpr_bound R
  exact ⟨C, 0, fun _ q _ hq => close_up (hq j) (by
      obtain ⟨c1, c2⟩ := hC; unfold qsub at c1 c2; constructor <;> (unfold qsub; rat_linarith)),
    fun k => ⟨0, Nat.le_refl _, fun _ _ _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩⟩

theorem uc_add {f g : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) (hg : UCo g) : UCo (fun n q => qadd (f n q) (g n q)) := by
  intro R R0
  obtain ⟨Cf, Bf, bf, cf⟩ := hf R R0
  obtain ⟨Cg, Bg, bg, cg⟩ := hg R R0
  obtain ⟨C, hC⟩ := qexpr_bound (qadd (qofInt (pow2 Cf)) (qofInt (pow2 Cg)))
  refine ⟨C, Bf + Bg, fun n q hn hq => ?_, fun k => ?_⟩
  · obtain ⟨f1, f2⟩ := bf n q (lA hn) hq
    obtain ⟨g1, g2⟩ := bg n q (lB hn) hq
    obtain ⟨c1, _⟩ := hC
    have p1 : qle qzero (qofInt (pow2 Cf)) := qofInt_le (pow2_nonneg Cf)
    have p2 : qle qzero (qofInt (pow2 Cg)) := qofInt_le (pow2_nonneg Cg)
    unfold qsub at f1 f2 g1 g2 c1
    show qclose (qadd (f n q) (g n q)) qzero _
    constructor <;> (unfold qsub; rat_linarith)
  · obtain ⟨N1, hN1, h1⟩ := cf (k + 1)
    obtain ⟨N2, hN2, h2⟩ := cg (k + 1)
    refine ⟨N1 + N2, Nat.add_le_add hN1 hN2, fun m n q hm hn hq => ?_⟩
    obtain ⟨a1, a2⟩ := h1 m n q (lA hm) (lA hn) hq
    obtain ⟨b1, b2⟩ := h2 m n q (lB hm) (lB hn) hq
    have e := qeps_succ_add k
    unfold qsub at a1 a2 b1 b2
    show qclose (qadd (f m q) (g m q)) (qadd (f n q) (g n q)) _
    constructor <;> (unfold qsub; rat_linarith)

theorem uc_neg {f : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) : UCo (fun n q => qneg (f n q)) := by
  intro R R0
  obtain ⟨C, Bf, bf, cf⟩ := hf R R0
  refine ⟨C, Bf, fun n q hn hq => ?_, fun k => ?_⟩
  · obtain ⟨f1, f2⟩ := bf n q hn hq
    unfold qsub at f1 f2
    show qclose (qneg (f n q)) qzero _
    constructor <;> (unfold qsub; rat_linarith)
  · obtain ⟨N, hN1, h⟩ := cf k
    refine ⟨N, hN1, fun m n q hm hn hq => ?_⟩
    obtain ⟨a1, a2⟩ := h m n q hm hn hq
    unfold qsub at a1 a2
    show qclose (qneg (f m q)) (qneg (f n q)) _
    constructor <;> (unfold qsub; rat_linarith)

theorem uc_mul {f g : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) (hg : UCo g) : UCo (fun n q => qmul (f n q) (g n q)) := by
  intro R R0
  obtain ⟨Cf, Bf, bf, cf⟩ := hf R R0
  obtain ⟨Cg, Bg, bg, cg⟩ := hg R R0
  obtain ⟨C, hC⟩ := qexpr_bound (qmul (qofInt (pow2 Cf)) (qofInt (pow2 Cg)))
  refine ⟨C, Bf + Bg, fun n q hn hq => close_up (qmul_abs_bound (bf n q (lA hn) hq) (bg n q (lB hn) hq)) hC,
    fun k => ?_⟩
  obtain ⟨N1, hN1, h1⟩ := cf (k + 1 + Cg)
  obtain ⟨N2, hN2, h2⟩ := cg (k + 1 + Cf)
  refine ⟨N1 + N2, Nat.add_le_add hN1 hN2, fun m n q hm hn hq => ?_⟩
  have hfm := bf m q (Nat.le_trans hN1 (lA hm)) hq
  have hgn := bg n q (Nat.le_trans hN2 (lB hn)) hq
  have hxc := h1 m n q (lA hm) (lA hn) hq
  have hyc := h2 m n q (lB hm) (lB hn) hq
  have p1 := qmul_abs_bound hfm (show qclose (qsub (g m q) (g n q)) qzero (qeps (k + 1 + Cf)) from by
    obtain ⟨a1, a2⟩ := hyc
    have hz : qEq (qsub (qsub (g m q) (g n q)) qzero) (qsub (g m q) (g n q)) := by unfold qsub; rat_ring
    constructor <;> rat_linarith)
  have p2 := qmul_abs_bound hgn (show qclose (qsub (f m q) (f n q)) qzero (qeps (k + 1 + Cg)) from by
    obtain ⟨a1, a2⟩ := hxc
    have hz : qEq (qsub (qsub (f m q) (f n q)) qzero) (qsub (f m q) (f n q)) := by unfold qsub; rat_ring
    constructor <;> rat_linarith)
  have q1 := qpow2_mul_eps Cf (k + 1)
  have q2 := qpow2_mul_eps Cg (k + 1)
  have he := qeps_succ_add k
  obtain ⟨p11, p12⟩ := p1
  obtain ⟨p21, p22⟩ := p2
  have hs : qEq (qsub (qmul (f m q) (g m q)) (qmul (f n q) (g n q)))
      (qadd (qmul (f m q) (qsub (g m q) (g n q))) (qmul (g n q) (qsub (f m q) (f n q)))) := by
    unfold qsub; rat_ring
  have z1 : qEq (qsub (qmul (f m q) (qsub (g m q) (g n q))) qzero) (qmul (f m q) (qsub (g m q) (g n q))) := by
    unfold qsub; rat_ring
  have z2 : qEq (qsub (qmul (g n q) (qsub (f m q) (f n q))) qzero) (qmul (g n q) (qsub (f m q) (f n q))) := by
    unfold qsub; rat_ring
  constructor <;> rat_linarith

theorem uc_pow {f : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) : ∀ k, UCo (fun n q => qpw (f n q) k)
  | 0 => uc_const qone
  | k + 1 => uc_mul hf (uc_pow hf k)

theorem uc_exp {f : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) : UCo (fun n q => eseq (f n q) n) := by
  intro R R0
  obtain ⟨Cf, Bf, bf, cf⟩ := hf R R0
  have Rf0 : qle qzero (qofInt (pow2 Cf)) := qofInt_le (pow2_nonneg Cf)
  obtain ⟨H, hH⟩ := S_bounded Rf0
  obtain ⟨Ch, hCh⟩ := qexpr_bound H
  have HC : qle H (qofInt (pow2 Ch)) := by obtain ⟨c1, _⟩ := hCh; unfold qsub at c1; rat_linarith
  refine ⟨Ch, Bf + 1, fun n q hn hq => ?_, fun k => ?_⟩
  · cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n' =>
    have b := bf (n' + 1) q (lA hn) hq
    have u := E_le_SR b n'
    have l := E_nonneg (f (n' + 1) q) n'
    have hh := hH (n' + 1)
    constructor <;> (unfold qsub; rat_linarith)
  · obtain ⟨N1, h1⟩ := E_unif Rf0 (k + 1)
    obtain ⟨N2, hN2, h2⟩ := cf (k + 1 + Ch)
    refine ⟨N1 + N2 + 1, Nat.succ_le_succ (Nat.le_trans hN2 (Nat.le_add_left _ _)), fun m n q hm hn hq => ?_⟩
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n' =>
    have am := bf m q (Nat.le_trans hN2 (le_b hm)) hq
    have an := bf (n' + 1) q (Nat.le_trans hN2 (le_b hn)) hq
    obtain ⟨u1, u2⟩ := h1 (f m q) am m (n' + 1) (le_a hm) (le_a hn)
    obtain ⟨l1, l2⟩ := E_lip am an (h2 m (n' + 1) q (le_b hm) (le_b hn) hq) n'
    have s1 := scale_l (qle_trans (hH (n' + 1)) HC) (qeps_nonneg (k + 1 + Ch))
    have e2 := qpow2_mul_eps Ch (k + 1)
    have e3 : qEq (qmul (qeps (k + 1 + Ch)) (qofInt (pow2 Ch))) (qmul (qofInt (pow2 Ch)) (qeps (k + 1 + Ch))) :=
      qmul_comm _ _
    have he := qeps_succ_add k
    unfold qsub at u1 u2 l1 l2
    constructor <;> (unfold qsub; rat_linarith)

/-- **THE ORACLE CONVERGES UNIFORMLY** on bounded sets, for every `exp`-law. -/
theorem uc_evq : ∀ e : XE, isE e = true → UCo (fun n q => evq n (q 0) e)
  | .var _, _ => uc_var 0
  | .cst c, _ => uc_const (qD c)
  | .add a b, h => uc_add (uc_evq a (and2 h).1) (uc_evq b (and2 h).2)
  | .sub a b, h => uc_add (uc_evq a (and2 h).1) (uc_neg (uc_evq b (and2 h).2))
  | .mul a b, h => uc_mul (uc_evq a (and2 h).1) (uc_evq b (and2 h).2)
  | .pow a k, h => uc_pow (uc_evq a h) k
  | .exp a, h => uc_exp (uc_evq a h)
  | .div _ _, h => by cases h
  | .ln _, h => by cases h

end Oracle

/-! ## The root -/

section Root
open VR VR.Numbers ZRealCF ZExp ZRealExp

/-- The law as a function on VR's continuum. -/
def Fx (e : XE) (x : RExpr) : RExpr := evX rCF rexpR (fun _ => x) e

/-- **THE ORACLE IS UNIFORMLY CLOSE** on the dyadics of `[a, b]`. -/
theorem orac_of (e : XE) (hE : isE e = true) (a b : D) : ∀ j, ∃ N, ∀ n, N ≤ n → ∀ t : D,
    rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
    ZKron.Bd rCF.toOH (radd (Fx e (dv rOH t)) (rneg (rofQ (evq n (qD t) e)))) (hp rOH j) := by
  intro j
  obtain ⟨Ca, hCa⟩ := qexpr_bound (qD a)
  obtain ⟨Cb, hCb⟩ := qexpr_bound (qD b)
  have pa : qle qzero (qofInt (pow2 Ca)) := qofInt_le (pow2_nonneg Ca)
  have pb : qle qzero (qofInt (pow2 Cb)) := qofInt_le (pow2_nonneg Cb)
  have p1 := qle_of_qlt qone_pos
  have R00 : qle qzero (qadd (qadd (qofInt (pow2 Ca)) (qofInt (pow2 Cb))) qone) := by rat_linarith
  obtain ⟨_, _, _, cau⟩ := uc_evq e hE _ R00
  obtain ⟨N, _, hN⟩ := cau j
  refine ⟨N, fun n hn t hat htb => ?_⟩
  have tq : qclose (qD t) qzero (qadd (qadd (qofInt (pow2 Ca)) (qofInt (pow2 Cb))) qone) := by
    obtain ⟨N1, h1⟩ := hat 0
    obtain ⟨N2, h2⟩ := htb 0
    have a1 := h1 (N1 + N2) (Nat.le_add_right _ _)
    have a2 := h2 (N1 + N2) (Nat.le_add_left _ _)
    have d1 := dv_seq a (N1 + N2)
    have d2 := dv_seq t (N1 + N2)
    have d3 := dv_seq b (N1 + N2)
    have e0 := qeps_zero
    obtain ⟨ca1, ca2⟩ := hCa
    obtain ⟨cb1, cb2⟩ := hCb
    unfold qsub at a1 a2 ca1 ca2 cb1 cb2
    constructor <;> (unfold qsub; rat_linarith)
  have key : ∀ m, N ≤ m → qclose (evq m (qD t) e) (evq n (qD t) e) (qeps j) := fun m hm => hN m n (fun _ => qD t) hm hn (fun _ => tq)
  show rle (rneg (hp rOH j)) _ ∧ rle _ (hp rOH j)
  constructor
  · refine rle_of_eventually N fun m hm => ?_
    have s1 := evX_seq (dv rOH t) m e
    have s2 := evq_respects m (dv_seq t m) e
    have s3 := hp_seq j m
    obtain ⟨k1, k2⟩ := key m hm
    change qle (qneg ((hp rOH j).seq m)) (qadd ((evX rCF rexpR (fun _ => dv rOH t) e).seq m) (qneg (evq n (qD t) e)))
    unfold qsub at k1 k2
    rat_linarith
  · refine rle_of_eventually N fun m hm => ?_
    have s1 := evX_seq (dv rOH t) m e
    have s2 := evq_respects m (dv_seq t m) e
    have s3 := hp_seq j m
    obtain ⟨k1, k2⟩ := key m hm
    change qle (qadd ((evX rCF rexpR (fun _ => dv rOH t) e).seq m) (qneg (evq n (qD t) e))) ((hp rOH j).seq m)
    unfold qsub at k1 k2
    rat_linarith

/-- An option read, then checked. -/
def optB (o : Option Iv) (f : Iv → Bool) : Bool :=
  match o with
  | some K => f K
  | none => false

theorem optB_some {o : Option Iv} {f : Iv → Bool} (h : optB o f = true) : ∃ K, o = some K ∧ f K = true := by
  cases o with
  | none => cases h
  | some K => exact ⟨K, rfl, h⟩

/-- **THE CERTIFICATE** for a root of an `exp`-law on `[a, b]`: slopes read in `[2⁻ˢ, 2ᶜ]`, `F(a) ≤ 0 ≤ F(b)`
read, width `≤ 2ᴮ`. Checked by the kernel. -/
def chkE (e : XE) (a b : D) (s C B : Nat) : Bool :=
  isE e && dle a b &&
    optB (slX (cB a b) (fun _ => ZIv.one) e) (fun K => dle ⟨⟨1, 0⟩, s⟩ K.1 && dle K.2 ⟨⟨2 ^ C, 0⟩, 0⟩) &&
    optB (ivX (cB a a) e) (fun K => dle K.2 dz0) &&
    optB (ivX (cB b b) e) (fun K => dle dz0 K.1) &&
    dle (dadd b (dneg a)) ⟨⟨2 ^ B, 0⟩, 0⟩

/-- **A CHECKED SIGN CHANGE OF AN `exp`-LAW GIVES ITS ROOT ON VR's CONTINUUM — and the only one in `[a, b]`.** -/
theorem exp_root (e : XE) (a b : D) (s C B : Nat) (h : chkE e a b s C B = true) :
    ∃ x : RExpr, (rle (dv rOH a) x ∧ rle x (dv rOH b)) ∧ rEq (Fx e x) rzero ∧
      ∀ y, rle (dv rOH a) y → rle y (dv rOH b) → rEq (Fx e y) rzero → rEq y x := by
  obtain ⟨h5, hW⟩ := and2 h
  obtain ⟨h4, hb'⟩ := and2 h5
  obtain ⟨h3, ha'⟩ := and2 h4
  obtain ⟨h2, hK'⟩ := and2 h3
  obtain ⟨hE, hab⟩ := and2 h2
  obtain ⟨K, hK, hKc⟩ := optB_some hK'
  obtain ⟨hc, hL⟩ := and2 hKc
  obtain ⟨Ka, hKa, ha⟩ := optB_some ha'
  obtain ⟨Kb, hKb, hb⟩ := optB_some hb'
  have hM : ZRootAbs.Mono rCF (Fx e) (dv rOH a) (dv rOH b) (hp rOH s) (nI rOH (2 ^ C)) :=
    mono_of_slX rExpLaws r_slope hE hK
      (rCF.le_respects (ZRootPVR.dv_hp s) (rCF.refl _) (dle_sound rOH hc))
      (rCF.le_respects (rCF.refl _) (ZRoot.dv_nat rCF (2 ^ C)) (dle_sound rOH hL))
  have H : ZRootAbs.Fam (fun _ => Fx e) (Fx e) (fun n q => evq n q e) a b s C B 0 := {
    hab := hab
    mono := fun _ _ => hM
    monoP := hM
    ends := fun _ _ => ⟨lo_end rExpLaws hE hKa ha, hi_end rExpLaws hE hKb hb⟩
    conv := fun j => ⟨0, fun _ _ x _ _ => ZKron.bd_congr rCF.toOH (rCF.symm (rCF.add_neg _)) (rCF.refl _)
      ⟨ZRootAbs.neg_le_zero rCF (hp_nonneg rOH j), hp_nonneg rOH j⟩⟩
    orac := orac_of e hE a b
    wid := hW }
  exact ⟨ZRootAbs.froot H, ZRootAbs.froot_in H, ZRootAbs.froot_is_root H,
    fun y h1 h2 hy => ZRootAbs.froot_unique H ⟨h1, h2⟩ (ZRootAbs.froot_in H) hy (ZRootAbs.froot_is_root H)⟩

end Root

/-! ## Example: the omega constant, `x·eˣ = 1` on `[0, 1]` -/

def d1 : D := ⟨⟨1, 0⟩, 0⟩
/-- `x·eˣ − 1`. -/
def omegaE : XE := .sub (.mul (.var 0) (.exp (.var 0))) (.cst d1)

/-- **THE OMEGA CONSTANT IS A VR REAL**: `x·eˣ = 1` has a root in `[0, 1]`, and only one (slopes read in `[1, 5.44]`,
`F(0) = −1`, `F(1) ∈ [1.718…]`). -/
theorem omega_exists : ∃ x : VR.Numbers.RExpr,
    (VR.Numbers.rle (dv ZRealCF.rOH dz0) x ∧ VR.Numbers.rle x (dv ZRealCF.rOH d1)) ∧
    VR.Numbers.rEq (Fx omegaE x) VR.Numbers.rzero ∧
    ∀ y, VR.Numbers.rle (dv ZRealCF.rOH dz0) y → VR.Numbers.rle y (dv ZRealCF.rOH d1) →
      VR.Numbers.rEq (Fx omegaE y) VR.Numbers.rzero → VR.Numbers.rEq y x :=
  exp_root omegaE dz0 d1 0 3 0 (by decide +kernel)

/-- The other side of the fork: on `[1, 2]` there is no sign change (`F(1) > 0`) — the certificate is refused. -/
example : chkE omegaE d1 ⟨⟨2, 0⟩, 0⟩ 0 3 0 = false := by decide +kernel

end ZRootExp

#print axioms ZRootExp.exp_chord
#print axioms ZRootExp.slX_sound
#print axioms ZRootExp.mono_of_slX
#print axioms ZRootExp.lo_end
#print axioms ZRootExp.hi_end
#print axioms ZRootExp.r_slope
#print axioms ZRootExp.uc_evq
#print axioms ZRootExp.evX_seq
#print axioms ZRootExp.orac_of
#print axioms ZRootExp.exp_root
#print axioms ZRootExp.omega_exists
