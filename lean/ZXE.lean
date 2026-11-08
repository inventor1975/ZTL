import ZExpIv
/-!
# ZXE — expressions with DIVISION, their values as a RELATION, and their readings. Zero axioms.

A tail of the Lean-checked `check_none` (curator, 2026-11-08: division as in ZTL; "делай как предлагаешь").
On VR's continuum the reciprocal is a PARTIAL operation: `1/x` exists given a witness that `x` is apart from 0
(`VR.Numbers.rinvPos`), and no total function can stand for it without classical axioms (it would decide
`x = 0 ∨ x # 0`; on Brouwer's reading it is even refuted — a total function on the continuum is continuous).
So the value of an expression is a RELATION `Val p e v` — "`v` is a value of `e` at `p`" — and the value of
`a / b` needs `b`'s value apart from 0 and `v_b · v = v_a`. Over ℝ the relation is the classical function.

The interval reading of `1/x` on `[l, h]` with `l > 0`: `q₁ ≈ 1/h`, `q₂ ≈ 1/l` computed by `Nat` division, then
CHECKED `0 ≤ q₁`, `q₁·h ≤ 1`, `q₂·l ≥ 1` (a negative interval through the sign). The affine reading keeps the
polynomial nodes affine and reads a quotient through its interval (a constant form, midpoint ± radius).

Part 1: the expressions, the relation, the reciprocal interval.
-/

namespace ZXE
open VR.CSR ZNumBin ZField ZPoly ZIv ZAff ZDivIv ZExpLaw ZExpIv

inductive XE where
  | var : Nat → XE
  | cst : D → XE
  | add : XE → XE → XE
  | sub : XE → XE → XE
  | mul : XE → XE → XE
  | pow : XE → Nat → XE
  | div : XE → XE → XE
  | exp : XE → XE
  | ln : XE → XE
  | atan : XE → XE

variable {α : Type} (S : CF α)

/-- What `atan` MEANS here: `atan 0 = 0`, congruent, and its chord lies between the bounds of `ψ(t) = 1/(1 + t²)` on
the chord's interval (stated without division: `L·(1 + t²) ≤ 1 ≤ U·(1 + t²)` for every `t` there). `ℝ`'s `arctan`
is one; VR's `ratan` (the grid sums of `ZAtan`) is one (`ZRootAtan.r_atanLaws`). -/
structure AtanLaws (atn : α → α) : Prop where
  zero : S.r (atn S.zero) S.zero
  congr : ∀ {a b}, S.r a b → S.r (atn a) (atn b)
  chord : ∀ x y L U, S.le x y →
    (∀ t, S.le x t → S.le t y →
      S.le (S.mul L (S.add S.one (S.mul t t))) S.one ∧ S.le S.one (S.mul U (S.add S.one (S.mul t t)))) →
    S.le (S.mul (S.add y (S.neg x)) L) (S.add (atn y) (S.neg (atn x))) ∧
    S.le (S.add (atn y) (S.neg (atn x))) (S.mul (S.add y (S.neg x)) U)

/-- `v` is a value of `e` at `p`, `ex` standing for the exponential: its nodes have values only for an `ex`
satisfying `ExpLaws` (that IS what "exp" means here; ℝ's `Real.exp` is one), and `ln a` needs `a > 0`. -/
inductive Val (ex atn : α → α) (p : Nat → α) : XE → α → Prop where
  | var {i v} : S.r v (p i) → Val ex atn p (.var i) v
  | cst {c v} : S.r v (dv S.toOH c) → Val ex atn p (.cst c) v
  | add {a b va vb v} : Val ex atn p a va → Val ex atn p b vb → S.r v (S.add va vb) → Val ex atn p (.add a b) v
  | sub {a b va vb v} : Val ex atn p a va → Val ex atn p b vb → S.r v (S.add va (S.neg vb)) → Val ex atn p (.sub a b) v
  | mul {a b va vb v} : Val ex atn p a va → Val ex atn p b vb → S.r v (S.mul va vb) → Val ex atn p (.mul a b) v
  | pow {a va v} (n : Nat) : Val ex atn p a va → S.r v (powS S.toOH va n) → Val ex atn p (.pow a n) v
  | div {a b va vb v} : Val ex atn p a va → Val ex atn p b vb → ap S vb → S.r (S.mul vb v) va → Val ex atn p (.div a b) v
  | exp {a va v} : ExpLaws S ex → Val ex atn p a va → S.r v (ex va) → Val ex atn p (.exp a) v
  | ln {a va v} : ExpLaws S ex → Val ex atn p a va → S.pos va → S.r (ex v) va → Val ex atn p (.ln a) v
  | atan {a va v} : AtanLaws S atn → Val ex atn p a va → S.r v (atn va) → Val ex atn p (.atan a) v

/-- A polynomial expression as an `XE`. -/
def ofPE : PE → XE
  | .var i => .var i
  | .cst c => .cst c
  | .add a b => .add (ofPE a) (ofPE b)
  | .sub a b => .sub (ofPE a) (ofPE b)
  | .mul a b => .mul (ofPE a) (ofPE b)
  | .pow a n => .pow (ofPE a) n

/-- An `XE` without division, as a polynomial. -/
def toPE : XE → Option PE
  | .var i => some (.var i)
  | .cst c => some (.cst c)
  | .add a b => match toPE a with
      | none => none
      | some x => match toPE b with
          | none => none
          | some y => some (.add x y)
  | .sub a b => match toPE a with
      | none => none
      | some x => match toPE b with
          | none => none
          | some y => some (.sub x y)
  | .mul a b => match toPE a with
      | none => none
      | some x => match toPE b with
          | none => none
          | some y => some (.mul x y)
  | .pow a n => match toPE a with
      | none => none
      | some x => some (.pow x n)
  | .div _ _ => none
  | .exp _ => none
  | .ln _ => none
  | .atan _ => none

theorem val_ofPE (ex atn : α → α) (p : Nat → α) : ∀ e : PE, Val S ex atn p (ofPE e) (eval S.toOH p e)
  | .var _ => .var (S.refl _)
  | .cst _ => .cst (S.refl _)
  | .add a b => .add (val_ofPE ex atn p a) (val_ofPE ex atn p b) (S.refl _)
  | .sub a b => .sub (val_ofPE ex atn p a) (val_ofPE ex atn p b) (S.refl _)
  | .mul a b => .mul (val_ofPE ex atn p a) (val_ofPE ex atn p b) (S.refl _)
  | .pow a n => .pow n (val_ofPE ex atn p a) (S.refl _)

/-- On a polynomial, the relation is the function. -/
theorem val_toPE {ex atn : α → α} {p : Nat → α} : ∀ {e : XE} {q : PE} {v : α}, toPE e = some q → Val S ex atn p e v →
    S.r v (eval S.toOH p q)
  | .var _, q, v, h, hv => by cases h; cases hv with | var e => exact e
  | .cst _, q, v, h, hv => by cases h; cases hv with | cst e => exact e
  | .add a b, q, v, h, hv => by
      unfold toPE at h
      cases ha : toPE a with
      | none => rw [ha] at h; cases h
      | some x =>
          rw [ha] at h
          cases hb : toPE b with
          | none => rw [hb] at h; cases h
          | some y =>
              rw [hb] at h; cases h
              cases hv with
              | add h1 h2 e => exact S.trans e (S.add_congr (val_toPE ha h1) (val_toPE hb h2))
  | .sub a b, q, v, h, hv => by
      unfold toPE at h
      cases ha : toPE a with
      | none => rw [ha] at h; cases h
      | some x =>
          rw [ha] at h
          cases hb : toPE b with
          | none => rw [hb] at h; cases h
          | some y =>
              rw [hb] at h; cases h
              cases hv with
              | sub h1 h2 e => exact S.trans e (S.add_congr (val_toPE ha h1) (S.neg_congr (val_toPE hb h2)))
  | .mul a b, q, v, h, hv => by
      unfold toPE at h
      cases ha : toPE a with
      | none => rw [ha] at h; cases h
      | some x =>
          rw [ha] at h
          cases hb : toPE b with
          | none => rw [hb] at h; cases h
          | some y =>
              rw [hb] at h; cases h
              cases hv with
              | mul h1 h2 e => exact S.trans e (S.mul_congr (val_toPE ha h1) (val_toPE hb h2))
  | .pow a n, q, v, h, hv => by
      unfold toPE at h
      cases ha : toPE a with
      | none => rw [ha] at h; cases h
      | some x =>
          rw [ha] at h; cases h
          cases hv with
          | pow _ h1 e => exact S.trans e (powS_congr S.toOH (val_toPE ha h1) n)
  | .div _ _, q, v, h, _ => by cases h
  | .exp _, q, v, h, _ => by cases h
  | .ln _, q, v, h, _ => by cases h
  | .atan _, q, v, h, _ => by cases h

/-! ## The interval reading with division -/

def ivDiv (I J : Iv) : Option Iv :=
  match ivInv J with
  | none => none
  | some K => ivMul I K

def ivX (B : Box) : XE → Option Iv
  | .var i => B i
  | .cst c => some (c, c)
  | .add p q => lift2 ivAdd (ivX B p) (ivX B q)
  | .sub p q => lift2 ivSub (ivX B p) (ivX B q)
  | .mul p q => lift2 ivMul (ivX B p) (ivX B q)
  | .pow p n => match ivX B p with
      | none => none
      | some I => ivPow I n
  | .div p q => lift2 ivDiv (ivX B p) (ivX B q)
  | .exp p => match ivX B p with
      | none => none
      | some I => ivExp I
  | .ln p => match ivX B p with
      | none => none
      | some I => ivLn I
  | .atan _ => none

theorem mem_div {x y v : α} {I J K : Iv} (hx : Mem S x I) (hy : Mem S y J) (hap : ap S y)
    (hv : S.r (S.mul y v) x) (h : ivDiv I J = some K) : Mem S v K := by
  unfold ivDiv at h
  cases hK : ivInv J with
  | none => rw [hK] at h; cases h
  | some L =>
      rw [hK] at h
      obtain ⟨t, ht⟩ := S.inv hap
      have mt := mem_inv S hy hK ht
      exact mem_congr S (quot_val S hap hv ht) (mem_mul S hx mt h)

/-- **THE READING ENCLOSES EVERY VALUE**, division included, in every `CF`. -/
theorem ivX_sound {ex atn : α → α} {B : Box} {p : Nat → α} (hp : InBox S B p) :
    ∀ {e : XE} {v : α}, Val S ex atn p e v → ∀ K, ivX B e = some K → Mem S v K := by
  intro e v hv
  induction hv with
  | var e => intro K h; exact mem_congr S e (hp _ K h)
  | cst e => intro K h; cases h; exact mem_congr S e (mem_cst S _)
  | add _ _ e ih1 ih2 =>
      intro K h
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      exact mem_congr S e (mem_add S (ih1 x ex) (ih2 y ey) hk)
  | sub _ _ e ih1 ih2 =>
      intro K h
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      exact mem_congr S e (mem_sub S (ih1 x ex) (ih2 y ey) hk)
  | mul _ _ e ih1 ih2 =>
      intro K h
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      exact mem_congr S e (mem_mul S (ih1 x ex) (ih2 y ey) hk)
  | @pow a va v n _ e ih =>
      intro K h
      unfold ivX at h
      cases ha : ivX B a with
      | none => rw [ha] at h; cases h
      | some I => rw [ha] at h; exact mem_congr S e (mem_pow S (ih I ha) n K h)
  | div _ _ hap e ih1 ih2 =>
      intro K h
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      exact mem_div S (ih1 x ex) (ih2 y ey) hap e hk
  | @exp a va v H _ e ih =>
      intro K h
      unfold ivX at h
      cases ha : ivX B a with
      | none => rw [ha] at h; cases h
      | some I => rw [ha] at h; exact mem_congr S e (mem_exp S H (ih I ha) h)
  | @ln a va v H _ _ e ih =>
      intro K h
      unfold ivX at h
      cases ha : ivX B a with
      | none => rw [ha] at h; cases h
      | some I => rw [ha] at h; exact mem_ln S H (ih I ha) e h
  | atan _ _ _ _ => intro K h; cases h

/-! ## The affine reading with division -/

def toForm (K : Iv) : AF := ⟨mid K, [], rad K⟩

def afDiv (B : Box) (A F : AF) : Option AF :=
  match afIv B A with
  | none => none
  | some I => match afIv B F with
      | none => none
      | some J => (ivDiv I J).map toForm

def afX (B : Box) : XE → Option AF
  | .var i => afVar B i
  | .cst c => some (afCst c)
  | .add p q => bind2 (fun a b => some (afAdd a b)) (afX B p) (afX B q)
  | .sub p q => bind2 (fun a b => some (afSub a b)) (afX B p) (afX B q)
  | .mul p q => (bind2 (afMul B) (afX B p) (afX B q)).map afRnd
  | .pow p n => match afX B p with
      | none => none
      | some F => afPow B F n
  | .div p q => bind2 (afDiv B) (afX B p) (afX B q)
  | .exp p => match afX B p with
      | none => none
      | some F => match afIv B F with
          | none => none
          | some I => (ivExp I).map toForm
  | .ln p => match afX B p with
      | none => none
      | some F => match afIv B F with
          | none => none
          | some I => (ivLn I).map toForm
  | .atan _ => none

theorem enc_congr {B : Box} {p : Nat → α} {v w : α} {F : AF} (e : S.r v w) (h : Enc S B p w F) : Enc S B p v F :=
  ⟨S.le_respects (S.refl _) (S.add_congr (S.symm e) (S.refl _)) h.1,
   S.le_respects (S.add_congr (S.symm e) (S.refl _)) (S.refl _) h.2⟩

/-- A value in an interval is within its radius of its midpoint: a constant form. -/
theorem enc_of_mem {B : Box} {p : Nat → α} {v : α} {K : Iv} (hv : Mem S v K) : Enc S B p v (toForm K) := by
  have hm := S.trans (dv_succ S (dadd K.1 K.2).m (dadd K.1 K.2).e) (S.mul_congr (S.refl _) (dv_add S.toOH K.1 K.2))
  have hr := S.trans (dv_succ S (dadd K.2 (dneg K.1)).m (dadd K.2 (dneg K.1)).e)
    (S.mul_congr (S.refl _) (S.trans (dv_add S.toOH K.2 (dneg K.1)) (S.add_congr (S.refl _) (dv_neg S.toOH K.1))))
  have em : S.r (dv S.toOH (mid K)) (S.mul S.half (S.add (dv S.toOH K.1) (dv S.toOH K.2))) := hm
  have er : S.r (dv S.toOH (rad K)) (S.mul S.half (S.add (dv S.toOH K.2) (S.neg (dv S.toOH K.1)))) := hr
  have hs := S.half_spec
  have p2 : S.r (S.add (S.mul S.half v) (S.mul S.half v)) v :=
    S.trans (by cr_ring S.toCR : S.r (S.add (S.mul S.half v) (S.mul S.half v)) (S.mul (S.add S.half S.half) v))
      (S.trans (S.mul_congr hs (S.refl _)) (S.one_mul _))
  have p2a := S.le_respects (S.refl _) p2 (S.le_refl (S.add (S.mul S.half v) (S.mul S.half v)))
  have p2b := S.le_respects p2 (S.refl _) (S.le_refl (S.add (S.mul S.half v) (S.mul S.half v)))
  have q1 := le_mul_right S.toOH hv.1 (half_nonneg S.toOH)
  have q2 := le_mul_right S.toOH hv.2 (half_nonneg S.toOH)
  unfold Enc toForm
  show S.le (S.neg (dv S.toOH (rad K))) (S.add v (S.neg (S.add (dv S.toOH (mid K)) S.zero))) ∧
    S.le (S.add v (S.neg (S.add (dv S.toOH (mid K)) S.zero))) (dv S.toOH (rad K))
  constructor
  · refine S.le_respects (S.neg_congr (S.symm er)) (S.add_congr (S.refl _) (S.neg_congr (S.add_congr (S.symm em) (S.refl _)))) ?_
    cr_linarith S.toOCR [q1, p2a, p2b]
  · refine S.le_respects (S.add_congr (S.refl _) (S.neg_congr (S.add_congr (S.symm em) (S.refl _)))) (S.symm er) ?_
    cr_linarith S.toOCR [q2, p2a, p2b]

/-- **THE AFFINE READING ENCLOSES EVERY VALUE**, division included, in every `CF`. -/
theorem afX_sound {ex atn : α → α} {B : Box} {p : Nat → α} (hp : InBox S B p) :
    ∀ {e : XE} {v : α}, Val S ex atn p e v → ∀ F, afX B e = some F → Enc S B p v F := by
  intro e v hv
  induction hv with
  | @var i v e =>
      intro F h
      unfold afX afVar at h
      cases hB : B i with
      | none => rw [hB] at h; cases h
      | some I => rw [hB] at h; cases h; exact enc_congr S e (enc_var S hB)
  | cst e => intro F h; cases h; exact enc_congr S e (enc_cst S B p _)
  | add _ _ e ih1 ih2 =>
      intro F h
      obtain ⟨x, y, ex, ey, hk⟩ := bind2_some h
      cases hk; exact enc_congr S e (enc_add S (ih1 x ex) (ih2 y ey))
  | sub _ _ e ih1 ih2 =>
      intro F h
      obtain ⟨x, y, ex, ey, hk⟩ := bind2_some h
      cases hk; exact enc_congr S e (enc_sub S (ih1 x ex) (ih2 y ey))
  | mul _ _ e ih1 ih2 =>
      intro F h
      obtain ⟨M, hM, hr⟩ := map_some h
      obtain ⟨x, y, ex, ey, hk⟩ := bind2_some hM
      cases hr
      exact enc_congr S e (enc_rnd S (enc_mul S hp (ih1 x ex) (ih2 y ey) hk))
  | @pow a va v n _ e ih =>
      intro F h
      unfold afX at h
      cases ha : afX B a with
      | none => rw [ha] at h; cases h
      | some G => rw [ha] at h; exact enc_congr S e (afPow_sound S hp (ih G ha) n F h)
  | div _ _ hap e ih1 ih2 =>
      intro F h
      obtain ⟨x, y, ex, ey, hk⟩ := bind2_some h
      unfold afDiv at hk
      cases h1 : afIv B x with
      | none => rw [h1] at hk; cases hk
      | some I =>
          rw [h1] at hk
          dsimp only at hk
          cases h2 : afIv B y with
          | none => rw [h2] at hk; cases hk
          | some J =>
              rw [h2] at hk
              dsimp only at hk
              cases hq : ivDiv I J with
              | none => rw [hq] at hk; cases hk
              | some K =>
                  rw [hq] at hk
                  cases hk
                  exact enc_of_mem S (mem_div S (afIv_sound S hp (ih1 x ex) h1) (afIv_sound S hp (ih2 y ey) h2) hap e hq)
  | @exp a va v H _ e ih =>
      intro F h
      unfold afX at h
      cases ha : afX B a with
      | none => rw [ha] at h; cases h
      | some G =>
          rw [ha] at h
          dsimp only at h
          cases hI : afIv B G with
          | none => rw [hI] at h; cases h
          | some I =>
              rw [hI] at h
              dsimp only at h
              cases hq : ivExp I with
              | none => rw [hq] at h; cases h
              | some K =>
                  rw [hq] at h
                  cases h
                  exact enc_of_mem S (mem_congr S e (mem_exp S H (afIv_sound S hp (ih G ha) hI) hq))
  | @ln a va v H _ _ e ih =>
      intro F h
      unfold afX at h
      cases ha : afX B a with
      | none => rw [ha] at h; cases h
      | some G =>
          rw [ha] at h
          dsimp only at h
          cases hI : afIv B G with
          | none => rw [hI] at h; cases h
          | some I =>
              rw [hI] at h
              dsimp only at h
              cases hq : ivLn I with
              | none => rw [hq] at h; cases h
              | some K =>
                  rw [hq] at h
                  cases h
                  exact enc_of_mem S (mem_ln S H (afIv_sound S hp (ih G ha) hI) e hq)
  | atan _ _ _ _ => intro F h; cases h

/-- The affine reading as an interval. -/
def afIvX (B : Box) (e : XE) : Option Iv :=
  match afX B e with
  | none => none
  | some F => afIv B F

theorem afIvX_sound {ex atn : α → α} {B : Box} {p : Nat → α} (hp : InBox S B p) {e : XE} {v : α} (hv : Val S ex atn p e v) (K : Iv)
    (h : afIvX B e = some K) : Mem S v K := by
  unfold afIvX at h
  cases hF : afX B e with
  | none => rw [hF] at h; cases h
  | some F => rw [hF] at h; exact afIv_sound S hp (afX_sound S hp hv F hF) h

end ZXE
