import ZExpIv
/-!
# ZSinIv — what `sin`/`cos` MEAN over any ordered field, and their interval readings. Zero axioms.

The laws (`TrigLaws`), all equalities up to the field's `r`:
  * `sin 0 = 0`, `cos 0 = 1`; congruent;
  * THE SECOND-ORDER STEP: `2·(sin y − sin x − (y − x)·cos x)` and `2·(cos y − cos x + (y − x)·sin x)` lie in
    `[−(y − x)², (y − x)²]` (classically Taylor with `|sin''|, |cos''| ≤ 1`; on VR's continuum `ZTrig13.Ev_sin2`,
    `Ev_cos2` with the reading `[−1, 1]`);
  * `|sin|, |cos| ≤ 1`; the double angle `sin 2x = 2·sin x·cos x`, `cos 2x = cos²x − sin²x`; `sin² + cos² = 1`.

The VALUE at a dyadic `d` (`scEnc`): at `h = d/2⁴⁰` the second-order step from `0` gives `sin h ∈ h ± h²/2`,
`1 − cos h ∈ ±h²/2`; then forty doublings of the pair (`sin`, `1 − cos`): `sin 2t = 2·s·(1 − v)`, `1 − cos 2t = 2s²`
(the versine keeps the rounding relative while the angle is small). MEASURED 2026-11-08 (`scratchpad/sinproto.py`,
the same arithmetic): width of `sin` `1.0e−12` at `1`, `1.3e−11` at `3`, `1.5e−8` at `100`.

The READING on `I` (`ivSin`, `ivCos`): about the midpoint `m`, radius `r`,
`sin x ∈ sin m + [−r, r]·cos m ± r²/2` (the second-order step from `m`), clamped to `[−1, 1]`; `cos` likewise.
-/

namespace ZSinIv

open VR.CSR ZNumBin ZField ZPoly ZIv ZAff ZDivIv

variable {α : Type} (S : CF α)

/-- The second-order remainders and the square of the step. -/
def Rs (sn cs : α → α) (x y : α) : α := S.add (S.add (sn y) (S.neg (sn x))) (S.neg (S.mul (S.add y (S.neg x)) (cs x)))
def Rc (sn cs : α → α) (x y : α) : α := S.add (S.add (cs y) (S.neg (cs x))) (S.mul (S.add y (S.neg x)) (sn x))
def Sq (x y : α) : α := S.mul (S.add y (S.neg x)) (S.add y (S.neg x))

/-- What `sin`, `cos` MEAN here. `ℝ`'s are; VR's (`ZTrig`'s partial sums at the argument's index) are
(`ZRootSin.r_trigLaws`). -/
structure TrigLaws (sn cs : α → α) : Prop where
  s0 : S.r (sn S.zero) S.zero
  c0 : S.r (cs S.zero) S.one
  congr_s : ∀ {a b}, S.r a b → S.r (sn a) (sn b)
  congr_c : ∀ {a b}, S.r a b → S.r (cs a) (cs b)
  s2 : ∀ x y, S.le (S.neg (Sq S x y)) (S.add (Rs S sn cs x y) (Rs S sn cs x y)) ∧
    S.le (S.add (Rs S sn cs x y) (Rs S sn cs x y)) (Sq S x y)
  c2 : ∀ x y, S.le (S.neg (Sq S x y)) (S.add (Rc S sn cs x y) (Rc S sn cs x y)) ∧
    S.le (S.add (Rc S sn cs x y) (Rc S sn cs x y)) (Sq S x y)
  bs : ∀ x, S.le (S.neg S.one) (sn x) ∧ S.le (sn x) S.one
  bc : ∀ x, S.le (S.neg S.one) (cs x) ∧ S.le (cs x) S.one
  ds : ∀ x, S.r (sn (S.add x x)) (S.add (S.mul (sn x) (cs x)) (S.mul (sn x) (cs x)))
  dc : ∀ x, S.r (cs (S.add x x)) (S.add (S.mul (cs x) (cs x)) (S.neg (S.mul (sn x) (sn x))))
  py : ∀ x, S.r (S.add (S.mul (sn x) (sn x)) (S.mul (cs x) (cs x))) S.one

/-! ## The computation -/

/-- The square of `t ∈ I`, read with its sign: `[0, max(l², h²)]` when `I` straddles `0`. Exact dyadics. -/
def ivSq (I : Iv) : Iv :=
  (cond (dle zeroD I.1) (dmul I.1 I.1) (cond (dle I.2 zeroD) (dmul I.2 I.2) zeroD), dmax (dmul I.1 I.1) (dmul I.2 I.2))


def hlf (d : D) : D := ⟨d.m, d.e + 1⟩
/-- `d²/2`. -/
def hq (d : D) : D := hlf (dmul d d)
/-- `±d²/2`. -/
def Qi (d : D) : Iv := (dneg (hq d), hq d)

/-- One doubling of the pair (`sin t`, `1 − cos t`). -/
def dblT (P : Iv × Iv) : Option (Iv × Iv) :=
  match ivSub ZIv.one P.2 with
  | none => none
  | some C => match ivMul P.1 C with
    | none => none
    | some M => match ivAdd M M with
      | none => none
      | some S' => match ivAdd (ivSq P.1) (ivSq P.1) with
        | none => none
        | some V' => some (S', V')

/-- The pair at `d` after `n` doublings from `d/2ⁿ`. -/
def encT : Nat → D → Option (Iv × Iv)
  | 0 => fun d => match ivAdd (d, d) (Qi d) with
    | none => none
    | some S0 => some (S0, Qi d)
  | n + 1 => fun d => match encT n (hlf d) with
    | none => none
    | some P => dblT P

/-- Forty doublings. -/
def trK : Nat := 40

/-- **THE VALUES OF `sin` AND `1 − cos` AT A DYADIC**, enclosed. -/
def scEnc (d : D) : Option (Iv × Iv) := encT trK d

def oneD : D := ⟨⟨1, 0⟩, 0⟩
def mOneD : D := ⟨⟨0, 1⟩, 0⟩

/-- Clamped to `[−1, 1]`. -/
def clamp1 (B : Iv) : Iv := (dmax B.1 mOneD, dmin B.2 oneD)

/-- **THE READING OF `sin`** on `I`. -/
def ivSin (I : Iv) : Option Iv :=
  match scEnc (mid I) with
  | none => none
  | some P => match ivSub ZIv.one P.2 with
    | none => none
    | some C => match ivMul (dneg (rad I), rad I) C with
      | none => none
      | some T => match ivAdd P.1 T with
        | none => none
        | some A => match ivAdd A (Qi (rad I)) with
          | none => none
          | some B => some (clamp1 B)

/-- **THE READING OF `cos`** on `I`. -/
def ivCos (I : Iv) : Option Iv :=
  match scEnc (mid I) with
  | none => none
  | some P => match ivSub ZIv.one P.2 with
    | none => none
    | some C => match ivMul (dneg (rad I), rad I) P.1 with
      | none => none
      | some T => match ivSub C T with
        | none => none
        | some A => match ivAdd A (Qi (rad I)) with
          | none => none
          | some B => some (clamp1 B)

/-! ## Soundness -/

theorem mem_sq {t : α} {I : Iv} (h : Mem S t I) : Mem S (S.mul t t) (ivSq I) := by
  obtain ⟨h1, h2⟩ := h
  have el := dv_mul S.toOH I.1 I.1
  have eh := dv_mul S.toOH I.2 I.2
  have ml := S.le_respects el (S.refl _) (dmax_l S (dmul I.1 I.1) (dmul I.2 I.2))
  have mh := S.le_respects eh (S.refl _) (dmax_r S (dmul I.1 I.1) (dmul I.2 I.2))
  have sq := sq_nonneg S (S.add (dv S.toOH I.1) (S.neg (dv S.toOH I.2)))
  have mlh : S.le (S.mul (dv S.toOH I.1) (dv S.toOH I.2)) (dv S.toOH (dmax (dmul I.1 I.1) (dmul I.2 I.2))) := by
    cr_linarith S.toOCR [ml, mh, sq]
  have mhl : S.le (S.mul (dv S.toOH I.2) (dv S.toOH I.1)) (dv S.toOH (dmax (dmul I.1 I.1) (dmul I.2 I.2))) :=
    S.le_respects (S.mul_comm _ _) (S.refl _) mlh
  refine ⟨?_, mul_upper S h1 h2 h1 h2 ml mlh mhl mh⟩
  show S.le (dv S.toOH (cond (dle zeroD I.1) (dmul I.1 I.1) (cond (dle I.2 zeroD) (dmul I.2 I.2) zeroD))) (S.mul t t)
  cases c1 : dle zeroD I.1 with
  | true =>
      have z := S.le_respects (dv_zeroD S) (S.refl _) (dle_sound S.toOH c1)
      have t0 := S.le_trans z h1
      have a := le_mul_left' S h1 z
      have b := le_mul_right S.toOH h1 t0
      exact S.le_respects (S.symm el) (S.refl _) (S.le_trans a b)
  | false =>
      cases c2 : dle I.2 zeroD with
      | true =>
          have z := S.le_respects (S.refl _) (dv_zeroD S) (dle_sound S.toOH c2)
          have n1 : S.le (S.neg (dv S.toOH I.2)) (S.neg t) := by cr_linarith S.toOCR [h2]
          have n0 : S.le S.zero (S.neg (dv S.toOH I.2)) := by cr_linarith S.toOCR [z]
          have a := le_mul_left' S n1 n0
          have b := le_mul_right S.toOH n1 (S.le_trans n0 n1)
          have e1 : S.r (S.mul (S.neg (dv S.toOH I.2)) (S.neg (dv S.toOH I.2))) (S.mul (dv S.toOH I.2) (dv S.toOH I.2)) := by
            cr_ring S.toCR
          have e2 : S.r (S.mul (S.neg t) (S.neg t)) (S.mul t t) := by cr_ring S.toCR
          exact S.le_respects (S.trans e1 (S.symm eh)) e2 (S.le_trans a b)
      | false =>
          exact S.le_respects (S.symm (dv_zeroD S)) (S.refl _) (sq_nonneg S t)

variable {S}

theorem le_of_r {a b : α} (e : S.r a b) : S.le a b := S.le_respects (S.refl _) e (S.le_refl a)
theorem ge_of_r {a b : α} (e : S.r a b) : S.le b a := S.le_respects e (S.refl _) (S.le_refl a)

/-- `−A ≤ 2R ≤ A` gives `−A/2 ≤ R ≤ A/2`. -/
theorem half_bound {R A : α} (l : S.le (S.neg A) (S.add R R)) (u : S.le (S.add R R) A) :
    S.le (S.neg (S.mul S.half A)) R ∧ S.le R (S.mul S.half A) := by
  have q1 := le_mul_right S.toOH l (half_nonneg S.toOH)
  have q2 := le_mul_right S.toOH u (half_nonneg S.toOH)
  have hs := S.half_spec
  have e : S.r (S.mul (S.add R R) S.half) R :=
    S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add S.half S.half) R)) (S.trans (S.mul_congr hs (S.refl _)) (S.one_mul _))
  have e1 := le_of_r e
  have e2 := ge_of_r e
  exact ⟨by cr_linarith S.toOCR [q1, e1, e2], by cr_linarith S.toOCR [q2, e1, e2]⟩

theorem dv_hlf (d : D) : S.r (S.add (dv S.toOH (hlf d)) (dv S.toOH (hlf d))) (dv S.toOH d) := by
  have e := dv_succ S d.m d.e
  have hs := S.half_spec
  refine S.trans (S.add_congr e e) ?_
  refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add S.half S.half) (dv S.toOH ⟨d.m, d.e⟩))) ?_
  exact S.trans (S.mul_congr hs (S.refl _)) (S.one_mul _)

theorem dv_hq (d : D) : S.r (dv S.toOH (hq d)) (S.mul S.half (S.mul (dv S.toOH d) (dv S.toOH d))) :=
  S.trans (dv_succ S (dmul d d).m (dmul d d).e) (S.mul_congr (S.refl _) (dv_mul S.toOH d d))

/-- `|x| ≤ hq d` puts `x` in `Qi d`. -/
theorem mem_Qi {x : α} {d : D} (l : S.le (S.neg (S.mul S.half (S.mul (dv S.toOH d) (dv S.toOH d)))) x)
    (u : S.le x (S.mul S.half (S.mul (dv S.toOH d) (dv S.toOH d)))) : Mem S x (Qi d) := by
  have e := dv_hq (S := S) d
  have n := dv_neg S.toOH (hq d)
  exact ⟨S.le_respects (S.trans (S.neg_congr (S.symm e)) (S.symm n)) (S.refl _) l, S.le_respects (S.refl _) (S.symm e) u⟩

theorem sq0 (t : α) : S.r (Sq S S.zero t) (S.mul t t) := by unfold Sq; cr_ring S.toCR

/-- The base: `sin t − t` and `cos t − 1` are within `t²/2`. -/
theorem base_s {sn cs : α → α} (H : TrigLaws S sn cs) (t : α) :
    S.le (S.neg (S.mul S.half (S.mul t t))) (S.add (sn t) (S.neg t)) ∧
    S.le (S.add (sn t) (S.neg t)) (S.mul S.half (S.mul t t)) := by
  obtain ⟨l, u⟩ := H.s2 S.zero t
  have e : S.r (Rs S sn cs S.zero t) (S.add (sn t) (S.neg t)) := by
    unfold Rs
    refine S.trans (S.add_congr (S.add_congr (S.refl _) (S.neg_congr H.s0))
      (S.neg_congr (S.mul_congr (S.refl _) H.c0))) ?_
    cr_ring S.toCR
  have l' := S.le_respects (S.neg_congr (sq0 t)) (S.add_congr e e) l
  have u' := S.le_respects (S.add_congr e e) (sq0 t) u
  exact half_bound l' u'

theorem base_c {sn cs : α → α} (H : TrigLaws S sn cs) (t : α) :
    S.le (S.neg (S.mul S.half (S.mul t t))) (S.add S.one (S.neg (cs t))) ∧
    S.le (S.add S.one (S.neg (cs t))) (S.mul S.half (S.mul t t)) := by
  obtain ⟨l, u⟩ := H.c2 S.zero t
  have e : S.r (Rc S sn cs S.zero t) (S.add (cs t) (S.neg S.one)) := by
    unfold Rc
    refine S.trans (S.add_congr (S.add_congr (S.refl _) (S.neg_congr H.c0))
      (S.mul_congr (S.refl _) H.s0)) ?_
    cr_ring S.toCR
  have l' := S.le_respects (S.neg_congr (sq0 t)) (S.add_congr e e) l
  have u' := S.le_respects (S.add_congr e e) (sq0 t) u
  obtain ⟨a, b⟩ := half_bound l' u'
  exact ⟨by cr_linarith S.toOCR [b], by cr_linarith S.toOCR [a]⟩

/-- The pair's meaning at `t`. -/
def PairAt (sn cs : α → α) (t : α) (P : Iv × Iv) : Prop := Mem S (sn t) P.1 ∧ Mem S (S.add S.one (S.neg (cs t))) P.2

theorem dbl_mem {sn cs : α → α} (H : TrigLaws S sn cs) {t : α} {P P' : Iv × Iv} (hP : PairAt (S := S) sn cs t P)
    (h : dblT P = some P') : PairAt (S := S) sn cs (S.add t t) P' := by
  unfold dblT at h
  cases hC : ivSub ZIv.one P.2 with
  | none => rw [hC] at h; cases h
  | some C =>
  rw [hC] at h; dsimp only at h
  cases hM : ivMul P.1 C with
  | none => rw [hM] at h; cases h
  | some M =>
  rw [hM] at h; dsimp only at h
  cases hS : ivAdd M M with
  | none => rw [hS] at h; cases h
  | some S' =>
  rw [hS] at h; dsimp only at h
  cases hV : ivAdd (ivSq P.1) (ivSq P.1) with
  | none => rw [hV] at h; cases h
  | some V' =>
  rw [hV] at h; dsimp only at h
  cases h
  have mc : Mem S (cs t) C :=
    mem_congr S (by cr_ring S.toCR : S.r (cs t) (S.add S.one (S.neg (S.add S.one (S.neg (cs t))))))
      (mem_sub S (mem_one S) hP.2 hC)
  have mm := mem_mul S hP.1 mc hM
  have ms := mem_add S mm mm hS
  have mq := mem_sq S hP.1
  have mv := mem_add S mq mq hV
  refine ⟨mem_congr S (H.ds t) ms, mem_congr S ?_ mv⟩
  refine S.trans (S.add_congr (S.refl _) (S.neg_congr (H.dc t))) ?_
  refine S.trans (S.add_congr (S.symm (H.py t)) (S.refl _)) ?_
  cr_ring S.toCR

theorem encT_mem {sn cs : α → α} (H : TrigLaws S sn cs) :
    ∀ (n : Nat) (d : D) (P : Iv × Iv), encT n d = some P → PairAt (S := S) sn cs (dv S.toOH d) P
  | 0, d, P, h => by
      unfold encT at h
      cases hA : ivAdd (d, d) (Qi d) with
      | none => rw [hA] at h; cases h
      | some S0 =>
      rw [hA] at h; dsimp only at h
      cases h
      obtain ⟨a, b⟩ := base_s H (dv S.toOH d)
      obtain ⟨c, e⟩ := base_c H (dv S.toOH d)
      have m := mem_add S (mem_cst S d) (mem_Qi a b) hA
      exact ⟨mem_congr S (by cr_ring S.toCR) m, mem_Qi c e⟩
  | n + 1, d, P, h => by
      unfold encT at h
      cases hE : encT n (hlf d) with
      | none => rw [hE] at h; cases h
      | some Q =>
      rw [hE] at h; dsimp only at h
      have ih := encT_mem H n (hlf d) Q hE
      have m := dbl_mem H ih h
      have e := dv_hlf (S := S) d
      exact ⟨mem_congr S (H.congr_s (S.symm e)) m.1,
        mem_congr S (S.add_congr (S.refl _) (S.neg_congr (H.congr_c (S.symm e)))) m.2⟩

/-- **THE ENCLOSURE OF `sin`, `1 − cos` AT A DYADIC IS SOUND.** -/
theorem scEnc_mem {sn cs : α → α} (H : TrigLaws S sn cs) {d : D} {P : Iv × Iv} (h : scEnc d = some P) :
    PairAt (S := S) sn cs (dv S.toOH d) P := encT_mem H trK d P h

/-- A point of `I` is within the radius of the midpoint. -/
theorem near_mid1 {x : α} {I : Iv} (m : Mem S x I) :
    S.le (S.neg (dv S.toOH (rad I))) (S.add x (S.neg (dv S.toOH (mid I)))) ∧
    S.le (S.add x (S.neg (dv S.toOH (mid I)))) (dv S.toOH (rad I)) := by
  have hm := S.trans (dv_succ S (dadd I.1 I.2).m (dadd I.1 I.2).e) (S.mul_congr (S.refl _) (dv_add S.toOH I.1 I.2))
  have hr := S.trans (dv_succ S (dadd I.2 (dneg I.1)).m (dadd I.2 (dneg I.1)).e)
    (S.mul_congr (S.refl _) (S.trans (dv_add S.toOH I.2 (dneg I.1)) (S.add_congr (S.refl _) (dv_neg S.toOH I.1))))
  have hs := S.half_spec
  have em : S.r (dv S.toOH (mid I)) (S.mul S.half (S.add (dv S.toOH I.1) (dv S.toOH I.2))) := hm
  have er : S.r (dv S.toOH (rad I)) (S.mul S.half (S.add (dv S.toOH I.2) (S.neg (dv S.toOH I.1)))) := hr
  have m1 := m.1
  have m2 := m.2
  have p2 : S.r (S.add (S.mul S.half x) (S.mul S.half x)) x :=
    S.trans (by cr_ring S.toCR : S.r (S.add (S.mul S.half x) (S.mul S.half x)) (S.mul (S.add S.half S.half) x))
      (S.trans (S.mul_congr hs (S.refl _)) (S.one_mul _))
  have p2a := S.le_respects (S.refl _) p2 (S.le_refl (S.add (S.mul S.half x) (S.mul S.half x)))
  have p2b := S.le_respects p2 (S.refl _) (S.le_refl (S.add (S.mul S.half x) (S.mul S.half x)))
  constructor
  · refine S.le_respects (S.neg_congr (S.symm er)) (S.add_congr (S.refl _) (S.neg_congr (S.symm em))) ?_
    have q := le_mul_right S.toOH m1 (half_nonneg S.toOH)
    cr_linarith S.toOCR [q, p2a, p2b]
  · refine S.le_respects (S.add_congr (S.refl _) (S.neg_congr (S.symm em))) (S.symm er) ?_
    have q := le_mul_right S.toOH m2 (half_nonneg S.toOH)
    cr_linarith S.toOCR [q, p2a, p2b]

/-- `|δ| ≤ r` gives `δ² ≤ r²`. -/
theorem sq_le {δ r : α} (l : S.le (S.neg r) δ) (u : S.le δ r) : S.le (S.mul δ δ) (S.mul r r) := by
  have a : S.le S.zero (S.add r (S.neg δ)) := by cr_linarith S.toOCR [u]
  have b : S.le S.zero (S.add r δ) := by cr_linarith S.toOCR [l]
  have p := S.mul_nonneg a b
  have e : S.r (S.mul (S.add r (S.neg δ)) (S.add r δ)) (S.add (S.mul r r) (S.neg (S.mul δ δ))) := by cr_ring S.toCR
  have e1 := le_of_r e
  cr_linarith S.toOCR [p, e1]

/-- A remainder bounded by `δ²/2`, `|δ| ≤ r`, is in `Qi r`. -/
theorem rem_Qi {R δ : α} {r : D} (l : S.le (S.neg (S.mul S.half (S.mul δ δ))) R) (u : S.le R (S.mul S.half (S.mul δ δ)))
    (hl : S.le (S.neg (dv S.toOH r)) δ) (hu : S.le δ (dv S.toOH r)) : Mem S R (Qi r) := by
  have s := le_mul_left' S (sq_le hl hu) (half_nonneg S.toOH)
  exact mem_Qi (by cr_linarith S.toOCR [l, s]) (by cr_linarith S.toOCR [u, s])

theorem mem_rad {δ : α} {I : Iv} (hl : S.le (S.neg (dv S.toOH (rad I))) δ) (hu : S.le δ (dv S.toOH (rad I))) :
    Mem S δ (dneg (rad I), rad I) :=
  ⟨S.le_respects (S.symm (dv_neg S.toOH (rad I))) (S.refl _) hl, hu⟩

theorem dmax_le {a b : D} {x : α} (ha : S.le (dv S.toOH a) x) (hb : S.le (dv S.toOH b) x) : S.le (dv S.toOH (dmax a b)) x := by
  unfold dmax; cases dle a b <;> assumption

theorem le_dmin {a b : D} {x : α} (ha : S.le x (dv S.toOH a)) (hb : S.le x (dv S.toOH b)) : S.le x (dv S.toOH (dmin a b)) := by
  unfold dmin; cases dle a b <;> assumption

theorem dv_oneD : S.r (dv S.toOH oneD) S.one := by
  show S.r (S.mul (zv S.toOH ⟨1, 0⟩) (hp S.toOH 0)) S.one
  show S.r (S.mul (S.add (nI S.toOH 1) (S.neg (nI S.toOH 0))) S.one) S.one
  show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) S.one
  cr_ring S.toCR

theorem dv_mOneD : S.r (dv S.toOH mOneD) (S.neg S.one) := by
  show S.r (S.mul (zv S.toOH ⟨0, 1⟩) (hp S.toOH 0)) (S.neg S.one)
  show S.r (S.mul (S.add (nI S.toOH 0) (S.neg (nI S.toOH 1))) S.one) (S.neg S.one)
  show S.r (S.mul (S.add S.zero (S.neg (S.add S.one S.zero))) S.one) (S.neg S.one)
  cr_ring S.toCR

theorem mem_clamp {x : α} {B : Iv} (h : Mem S x B) (b : S.le (S.neg S.one) x ∧ S.le x S.one) : Mem S x (clamp1 B) :=
  ⟨dmax_le h.1 (S.le_respects (S.symm dv_mOneD) (S.refl _) b.1), le_dmin h.2 (S.le_respects (S.refl _) (S.symm dv_oneD) b.2)⟩

/-- **THE READING OF `sin` IS SOUND.** -/
theorem mem_sin {sn cs : α → α} (H : TrigLaws S sn cs) {x : α} {I K : Iv} (hx : Mem S x I) (h : ivSin I = some K) :
    Mem S (sn x) K := by
  unfold ivSin at h
  cases hP : scEnc (mid I) with
  | none => rw [hP] at h; cases h
  | some P =>
  rw [hP] at h; dsimp only at h
  cases hC : ivSub ZIv.one P.2 with
  | none => rw [hC] at h; cases h
  | some C =>
  rw [hC] at h; dsimp only at h
  cases hT : ivMul (dneg (rad I), rad I) C with
  | none => rw [hT] at h; cases h
  | some T =>
  rw [hT] at h; dsimp only at h
  cases hA : ivAdd P.1 T with
  | none => rw [hA] at h; cases h
  | some A =>
  rw [hA] at h; dsimp only at h
  cases hB : ivAdd A (Qi (rad I)) with
  | none => rw [hB] at h; cases h
  | some B =>
  rw [hB] at h; dsimp only at h
  cases h
  have pm := scEnc_mem H hP
  have mc : Mem S (cs (dv S.toOH (mid I))) C :=
    mem_congr S (by cr_ring S.toCR : S.r (cs (dv S.toOH (mid I)))
      (S.add S.one (S.neg (S.add S.one (S.neg (cs (dv S.toOH (mid I)))))))) (mem_sub S (mem_one S) pm.2 hC)
  obtain ⟨n1, n2⟩ := near_mid1 hx
  have mt := mem_mul S (mem_rad n1 n2) mc hT
  have ma := mem_add S pm.1 mt hA
  obtain ⟨l, u⟩ := H.s2 (dv S.toOH (mid I)) x
  obtain ⟨r1, r2⟩ := half_bound l u
  have mr := rem_Qi (R := Rs S sn cs (dv S.toOH (mid I)) x) r1 r2 n1 n2
  have mb := mem_add S ma mr hB
  refine mem_clamp (mem_congr S ?_ mb) (H.bs x)
  unfold Rs; cr_ring S.toCR

/-- **THE READING OF `cos` IS SOUND.** -/
theorem mem_cos {sn cs : α → α} (H : TrigLaws S sn cs) {x : α} {I K : Iv} (hx : Mem S x I) (h : ivCos I = some K) :
    Mem S (cs x) K := by
  unfold ivCos at h
  cases hP : scEnc (mid I) with
  | none => rw [hP] at h; cases h
  | some P =>
  rw [hP] at h; dsimp only at h
  cases hC : ivSub ZIv.one P.2 with
  | none => rw [hC] at h; cases h
  | some C =>
  rw [hC] at h; dsimp only at h
  cases hT : ivMul (dneg (rad I), rad I) P.1 with
  | none => rw [hT] at h; cases h
  | some T =>
  rw [hT] at h; dsimp only at h
  cases hA : ivSub C T with
  | none => rw [hA] at h; cases h
  | some A =>
  rw [hA] at h; dsimp only at h
  cases hB : ivAdd A (Qi (rad I)) with
  | none => rw [hB] at h; cases h
  | some B =>
  rw [hB] at h; dsimp only at h
  cases h
  have pm := scEnc_mem H hP
  have mc : Mem S (cs (dv S.toOH (mid I))) C :=
    mem_congr S (by cr_ring S.toCR : S.r (cs (dv S.toOH (mid I)))
      (S.add S.one (S.neg (S.add S.one (S.neg (cs (dv S.toOH (mid I)))))))) (mem_sub S (mem_one S) pm.2 hC)
  obtain ⟨n1, n2⟩ := near_mid1 hx
  have mt := mem_mul S (mem_rad n1 n2) pm.1 hT
  have ma := mem_sub S mc mt hA
  obtain ⟨l, u⟩ := H.c2 (dv S.toOH (mid I)) x
  obtain ⟨r1, r2⟩ := half_bound l u
  have mr := rem_Qi (R := Rc S sn cs (dv S.toOH (mid I)) x) r1 r2 n1 n2
  have mb := mem_add S ma mr hB
  refine mem_clamp (mem_congr S ?_ mb) (H.bc x)
  unfold Rc; cr_ring S.toCR

end ZSinIv

#print axioms ZSinIv.dblT
#print axioms ZSinIv.encT
#print axioms ZSinIv.ivSin
#print axioms ZSinIv.ivCos
#print axioms ZSinIv.half_bound
#print axioms ZSinIv.dbl_mem
#print axioms ZSinIv.encT_mem
#print axioms ZSinIv.scEnc_mem
#print axioms ZSinIv.near_mid1
#print axioms ZSinIv.mem_clamp
#print axioms ZSinIv.mem_sin
#print axioms ZSinIv.mem_cos
