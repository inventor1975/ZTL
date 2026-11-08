import ZSinIv
import ZMinIv
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
open VR.CSR ZNumBin ZField ZPoly ZIv ZAff ZDivIv ZExpLaw ZExpIv ZSinIv ZMinIv

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
  | sin : XE → XE
  | cos : XE → XE
  | min : XE → XE → XE

variable {α : Type} (S : CF α)

/-- The reading of `ψ(t) = 1/(1 + t²)` for `t ∈ I`. -/
def psiI (I : Iv) : Option Iv :=
  match ivAdd ZIv.one (ivSq I) with
  | none => none
  | some J => ivInvPos J

/-- The trapezoid defect `4(atan y − atan x) − 2(y − x)(w_x + w_y)` and the cube `(y − x)³`. -/
def trapR (atn : α → α) (x y wx wy : α) : α :=
  S.add (S.mul (S.add (S.add S.one S.one) (S.add S.one S.one)) (S.add (atn y) (S.neg (atn x))))
    (S.neg (S.mul (S.mul (S.add S.one S.one) (S.add y (S.neg x))) (S.add wx wy)))
def cub (x y : α) : α := S.mul (S.mul (S.add y (S.neg x)) (S.add y (S.neg x))) (S.add y (S.neg x))

/-- What `atan` MEANS here: `atan 0 = 0`, congruent, and its chord over two points of a dyadic interval `I` lies
between the bounds of the reading of `ψ(t) = 1/(1 + t²)` on `I` (the derivative). `ℝ`'s `arctan` is one (the mean
value theorem); VR's `ratan` (the grid sums of `ZAtan`) is one (`ZRootAtan.r_atanLaws`). -/
structure AtanLaws (atn : α → α) : Prop where
  zero : S.r (atn S.zero) S.zero
  congr : ∀ {a b}, S.r a b → S.r (atn a) (atn b)
  chord : ∀ (I W : Iv), psiI I = some W → ∀ x y, Mem S x I → Mem S y I → S.le x y →
    S.le (S.mul (S.add y (S.neg x)) (dv S.toOH W.1)) (S.add (atn y) (S.neg (atn x))) ∧
    S.le (S.add (atn y) (S.neg (atn x))) (S.mul (S.add y (S.neg x)) (dv S.toOH W.2))
  /-- THE TRAPEZOID (2026-11-08): `|4(atan y − atan x) − 2h(ψ(x) + ψ(y))| ≤ h³` for `x ≤ y`, `w` the reciprocals of
  `1 + t²` (`ZAtanTrap.trap_seq` on VR). -/
  trap : ∀ x y wx wy, S.le x y → S.r (S.mul (S.add S.one (S.mul x x)) wx) S.one →
    S.r (S.mul (S.add S.one (S.mul y y)) wy) S.one →
    S.le (S.neg (cub S x y)) (trapR S atn x y wx wy) ∧ S.le (trapR S atn x y wx wy) (cub S x y)

inductive Val (ex atn sn cs : α → α) (mn : α → α → α) (p : Nat → α) : XE → α → Prop where
  | var {i v} : S.r v (p i) → Val ex atn sn cs mn p (.var i) v
  | cst {c v} : S.r v (dv S.toOH c) → Val ex atn sn cs mn p (.cst c) v
  | add {a b va vb v} : Val ex atn sn cs mn p a va → Val ex atn sn cs mn p b vb → S.r v (S.add va vb) → Val ex atn sn cs mn p (.add a b) v
  | sub {a b va vb v} : Val ex atn sn cs mn p a va → Val ex atn sn cs mn p b vb → S.r v (S.add va (S.neg vb)) → Val ex atn sn cs mn p (.sub a b) v
  | mul {a b va vb v} : Val ex atn sn cs mn p a va → Val ex atn sn cs mn p b vb → S.r v (S.mul va vb) → Val ex atn sn cs mn p (.mul a b) v
  | pow {a va v} (n : Nat) : Val ex atn sn cs mn p a va → S.r v (powS S.toOH va n) → Val ex atn sn cs mn p (.pow a n) v
  | div {a b va vb v} : Val ex atn sn cs mn p a va → Val ex atn sn cs mn p b vb → ap S vb → S.r (S.mul vb v) va → Val ex atn sn cs mn p (.div a b) v
  | exp {a va v} : ExpLaws S ex → Val ex atn sn cs mn p a va → S.r v (ex va) → Val ex atn sn cs mn p (.exp a) v
  | ln {a va v} : ExpLaws S ex → Val ex atn sn cs mn p a va → S.pos va → S.r (ex v) va → Val ex atn sn cs mn p (.ln a) v
  | atan {a va v} : AtanLaws S atn → Val ex atn sn cs mn p a va → S.r v (atn va) → Val ex atn sn cs mn p (.atan a) v
  | sin {a va v} : TrigLaws S sn cs → Val ex atn sn cs mn p a va → S.r v (sn va) → Val ex atn sn cs mn p (.sin a) v
  | cos {a va v} : TrigLaws S sn cs → Val ex atn sn cs mn p a va → S.r v (cs va) → Val ex atn sn cs mn p (.cos a) v
  | min {a b va vb v} : MinLaws S mn → Val ex atn sn cs mn p a va → Val ex atn sn cs mn p b vb → S.r v (mn va vb) →
      Val ex atn sn cs mn p (.min a b) v

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
  | .sin _ => none
  | .cos _ => none
  | .min _ _ => none

theorem val_ofPE (ex atn sn cs : α → α) (mn : α → α → α) (p : Nat → α) : ∀ e : PE, Val S ex atn sn cs mn p (ofPE e) (eval S.toOH p e)
  | .var _ => .var (S.refl _)
  | .cst _ => .cst (S.refl _)
  | .add a b => .add (val_ofPE ex atn sn cs mn p a) (val_ofPE ex atn sn cs mn p b) (S.refl _)
  | .sub a b => .sub (val_ofPE ex atn sn cs mn p a) (val_ofPE ex atn sn cs mn p b) (S.refl _)
  | .mul a b => .mul (val_ofPE ex atn sn cs mn p a) (val_ofPE ex atn sn cs mn p b) (S.refl _)
  | .pow a n => .pow n (val_ofPE ex atn sn cs mn p a) (S.refl _)

/-- On a polynomial, the relation is the function. -/
theorem val_toPE {ex atn sn cs : α → α} {mn : α → α → α} {p : Nat → α} : ∀ {e : XE} {q : PE} {v : α}, toPE e = some q → Val S ex atn sn cs mn p e v →
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
  | .sin _, q, v, h, _ => by cases h
  | .cos _, q, v, h, _ => by cases h
  | .min _ _, q, v, h, _ => by cases h

/-! ## The reading of `atan`: `ψ` on an interval, and the values at dyadic points by a Riemann enclosure from `0` -/

/-- **THE READING OF `ψ`**: for `t ∈ I`, `1/(1 + t²)` is in `psiI I`. -/
theorem psi_mem {t w : α} {I W : Iv} (h : Mem S t I) (hW : psiI I = some W)
    (hw : S.r (S.mul (S.add S.one (S.mul t t)) w) S.one) : Mem S w W := by
  unfold psiI at hW
  cases hJ : ivAdd ZIv.one (ivSq I) with
  | none => rw [hJ] at hW; cases hW
  | some J =>
      rw [hJ] at hW
      exact mem_inv_pos S (mem_add S (mem_one S) (mem_sq S h) hJ) hW hw

theorem psi_lo_nonneg {I W : Iv} (hW : psiI I = some W) : S.le S.zero (dv S.toOH W.1) := by
  unfold psiI at hW
  cases hJ : ivAdd ZIv.one (ivSq I) with
  | none => rw [hJ] at hW; cases hW
  | some J =>
      rw [hJ] at hW
      unfold ivInvPos at hW
      obtain ⟨hb, hK⟩ := cond_some hW
      cases hK
      obtain ⟨_, c2, _, _, _⟩ := and5 hb
      exact S.le_respects (dv_zeroD S) (S.refl _) (dle_sound S.toOH c2)

/-- The grid `d·i/2ᵏ`. -/
def gridA (d : D) (k i : Nat) : D := dmul d ⟨⟨i, 0⟩, k⟩

/-- `|h|³/4`. -/
def qcube (h : D) : D := ZSinIv.hlf (ZSinIv.hlf (dabs (dmul h (dmul h h))))

/-- One segment by THE TRAPEZOID: `atan(aᵢ₊₁) − atan(aᵢ) ∈ (h/2)·(ψ(aᵢ) + ψ(aᵢ₊₁)) ± |h|³/4`, `h = aᵢ₊₁ − aᵢ`
(until 2026-11-08 the chord `h·ψ([aᵢ, aᵢ₊₁])`: width `~h²` per segment, now `~h³`). -/
def segC (d : D) (k i : Nat) : Option Iv :=
  match psiI (gridA d k i, gridA d k i) with
  | none => none
  | some Wa => match psiI (gridA d k (i + 1), gridA d k (i + 1)) with
    | none => none
    | some Wb => match ivAdd Wa Wb with
      | none => none
      | some Wab => match ivMul (ZSinIv.hlf (dadd (gridA d k (i + 1)) (dneg (gridA d k i))),
            ZSinIv.hlf (dadd (gridA d k (i + 1)) (dneg (gridA d k i)))) Wab with
        | none => none
        | some M => ivAdd M (dneg (qcube (dadd (gridA d k (i + 1)) (dneg (gridA d k i)))),
            qcube (dadd (gridA d k (i + 1)) (dneg (gridA d k i))))

def encS (d : D) (k : Nat) : Nat → Option Iv
  | 0 => some (zeroD, zeroD)
  | i + 1 => match encS d k i with
    | none => none
    | some E => match segC d k i with
      | none => none
      | some C => ivAdd E C

/-- The number of grid steps' exponent for the value of `atan`: `2⁸` trapezoids. MEASURED 2026-11-08: `atan 1` within
`8e−6` (the Riemann chords before: `2e−3`), `atan 3` within `2e−4`; the system `y = atan x, x + y = 1` is now a theorem
at the cube `2⁻²⁰` (before: only at `2⁻¹²`). `2¹⁰` gives `atan 1` within `1e−6`, but the kernel's `decide` on a
system's checks then did not finish (refused at every radius, 81 s) — kept at `2⁸`. -/
def atK : Nat := 8

/-- **THE VALUE OF `atan` AT A DYADIC**, enclosed. -/
def atEnc (d : D) : Option Iv := encS d atK (2 ^ atK)

/-- **THE READING OF `atan`** on `I`: monotone, so the enclosures of the values at the ends. -/
def ivAtan (I : Iv) : Option Iv :=
  match psiI I with
  | none => none
  | some _ => match atEnc I.1 with
    | none => none
    | some E1 => match atEnc I.2 with
      | none => none
      | some E2 => some (E1.1, E2.2)

variable {S}

/-- `−A ≤ 4R ≤ A` gives `−A/4 ≤ R ≤ A/4`. -/
theorem quarter_bound {R A : α} (l : S.le (S.neg A) (S.add (S.add R R) (S.add R R)))
    (u : S.le (S.add (S.add R R) (S.add R R)) A) :
    S.le (S.neg (S.mul S.half (S.mul S.half A))) R ∧ S.le R (S.mul S.half (S.mul S.half A)) := by
  obtain ⟨a, b⟩ := ZSinIv.half_bound l u
  exact ZSinIv.half_bound a b

/-- The reciprocal of `1 + t²` exists (it is positive). -/
theorem psi_exists (t : α) : ∃ w, S.r (S.mul (S.add S.one (S.mul t t)) w) S.one := by
  have p1 : S.pos (S.add S.one (S.mul t t)) :=
    S.pos_mono (pos_one S) (by have := sq_nonneg S t; cr_linarith S.toOCR [this])
  exact S.inv (Or.inl p1)

/-- `4·(Δ − (h/2)·w) = 4Δ − 2h·w`, through `half + half = 1`. -/
theorem four_half {atn : α → α} (a b wa wb : α) :
    S.r (S.add (S.add (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb))))
        (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb)))))
      (S.add (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb))))
        (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb))))))
      (trapR S atn a b wa wb) := by
  have hs := S.half_spec
  unfold trapR
  refine S.trans (by cr_ring S.toCR : S.r _ (S.add (S.mul (S.add (S.add S.one S.one) (S.add S.one S.one))
    (S.add (atn b) (S.neg (atn a)))) (S.neg (S.mul (S.mul (S.add S.one S.one) (S.add S.half S.half))
      (S.mul (S.add b (S.neg a)) (S.add wa wb)))))) ?_
  refine S.trans (S.add_congr (S.refl _) (S.neg_congr (S.mul_congr (S.mul_congr (S.refl _) hs) (S.refl _)))) ?_
  cr_ring S.toCR

/-- The trapezoid upward (`a ≤ b`): the remainder `R = Δ − (h/2)·w` within `cub/4`. -/
theorem trap_up {atn : α → α} (H : AtanLaws S atn) {a b wa wb : α} (hab : S.le a b)
    (hwa : S.r (S.mul (S.add S.one (S.mul a a)) wa) S.one) (hwb : S.r (S.mul (S.add S.one (S.mul b b)) wb) S.one) :
    S.le (S.neg (S.mul S.half (S.mul S.half (cub S a b))))
        (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb)))) ∧
    S.le (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb))))
        (S.mul S.half (S.mul S.half (cub S a b))) := by
  obtain ⟨l, u⟩ := H.trap a b wa wb hab hwa hwb
  have e := four_half (S := S) (atn := atn) a b wa wb
  exact quarter_bound (S.le_respects (S.refl _) (S.symm e) l) (S.le_respects (S.symm e) (S.refl _) u)

/-- The trapezoid downward (`b ≤ a`): the same remainder within `cub(b, a)/4`. -/
theorem trap_down {atn : α → α} (H : AtanLaws S atn) {a b wa wb : α} (hba : S.le b a)
    (hwa : S.r (S.mul (S.add S.one (S.mul a a)) wa) S.one) (hwb : S.r (S.mul (S.add S.one (S.mul b b)) wb) S.one) :
    S.le (S.neg (S.mul S.half (S.mul S.half (cub S b a))))
        (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb)))) ∧
    S.le (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb))))
        (S.mul S.half (S.mul S.half (cub S b a))) := by
  obtain ⟨l, u⟩ := H.trap b a wb wa hba hwb hwa
  have e := four_half (S := S) (atn := atn) b a wb wa
  obtain ⟨q1, q2⟩ := quarter_bound (S.le_respects (S.refl _) (S.symm e) l) (S.le_respects (S.symm e) (S.refl _) u)
  -- the remainder downward is minus the remainder upward from b
  have r : S.r (S.add (S.add (atn b) (S.neg (atn a))) (S.neg (S.mul (S.mul S.half (S.add b (S.neg a))) (S.add wa wb))))
      (S.neg (S.add (S.add (atn a) (S.neg (atn b))) (S.neg (S.mul (S.mul S.half (S.add a (S.neg b))) (S.add wb wa))))) := by
    cr_ring S.toCR
  constructor
  · exact S.le_respects (S.refl _) (S.symm r) (by cr_linarith S.toOCR [q2])
  · exact S.le_respects (S.symm r) (S.refl _) (by cr_linarith S.toOCR [q1])

theorem seg_mem {atn : α → α} (H : AtanLaws S atn) (d : D) (k i : Nat) {C : Iv} (h : segC d k i = some C) :
    Mem S (S.add (atn (dv S.toOH (gridA d k (i + 1)))) (S.neg (atn (dv S.toOH (gridA d k i))))) C := by
  unfold segC at h
  cases hWa : psiI (gridA d k i, gridA d k i) with
  | none => rw [hWa] at h; cases h
  | some Wa =>
  rw [hWa] at h; dsimp only at h
  cases hWb : psiI (gridA d k (i + 1), gridA d k (i + 1)) with
  | none => rw [hWb] at h; cases h
  | some Wb =>
  rw [hWb] at h; dsimp only at h
  cases hWab : ivAdd Wa Wb with
  | none => rw [hWab] at h; cases h
  | some Wab =>
  rw [hWab] at h; dsimp only at h
  generalize hhd : dadd (gridA d k (i + 1)) (dneg (gridA d k i)) = hd at h
  cases hM : ivMul (ZSinIv.hlf hd, ZSinIv.hlf hd) Wab with
  | none => rw [hM] at h; cases h
  | some M =>
  rw [hM] at h; dsimp only at h
  obtain ⟨wa, hwa⟩ := psi_exists (S := S) (dv S.toOH (gridA d k i))
  obtain ⟨wb, hwb⟩ := psi_exists (S := S) (dv S.toOH (gridA d k (i + 1)))
  have mwa := psi_mem S (mem_cst S (gridA d k i)) hWa hwa
  have mwb := psi_mem S (mem_cst S (gridA d k (i + 1))) hWb hwb
  have mw := mem_add S mwa mwb hWab
  have mM := mem_mul S (mem_cst S (ZSinIv.hlf hd)) mw hM
  have eh : S.r (dv S.toOH hd) (S.add (dv S.toOH (gridA d k (i + 1))) (S.neg (dv S.toOH (gridA d k i)))) := by
    rw [← hhd]; exact S.trans (dv_add S.toOH _ _) (S.add_congr (S.refl _) (dv_neg S.toOH _))
  have eh2 : S.r (dv S.toOH (ZSinIv.hlf hd))
      (S.mul S.half (S.add (dv S.toOH (gridA d k (i + 1))) (S.neg (dv S.toOH (gridA d k i))))) :=
    S.trans (ZAff.dv_succ S hd.m hd.e) (S.mul_congr (S.refl _) eh)
  -- |h|³/4
  have eX : S.r (dv S.toOH (dmul hd (dmul hd hd))) (cub S (dv S.toOH (gridA d k i)) (dv S.toOH (gridA d k (i + 1)))) := by
    refine S.trans (dv_mul S.toOH _ _) (S.trans (S.mul_congr (S.refl _) (dv_mul S.toOH _ _)) ?_)
    refine S.trans (S.mul_congr eh (S.mul_congr eh eh)) ?_
    unfold cub; cr_ring S.toCR
  have eq : S.r (dv S.toOH (qcube hd)) (S.mul S.half (S.mul S.half (dv S.toOH (dabs (dmul hd (dmul hd hd)))))) :=
    S.trans (ZAff.dv_succ S _ _) (S.mul_congr (S.refl _) (ZAff.dv_succ S _ _))
  obtain ⟨_, ab1, ab2⟩ := ZAff.dabs_sound S (dmul hd (dmul hd hd))
  have hh0 := half_nonneg S.toOH
  have cubs : S.r (cub S (dv S.toOH (gridA d k (i + 1))) (dv S.toOH (gridA d k i)))
      (S.neg (cub S (dv S.toOH (gridA d k i)) (dv S.toOH (gridA d k (i + 1))))) := by unfold cub; cr_ring S.toCR
  -- the remainder within ±|h|³/4, whichever way the grid runs
  have hR : S.le (S.neg (S.mul S.half (S.mul S.half (dv S.toOH (dabs (dmul hd (dmul hd hd)))))))
        (S.add (S.add (atn (dv S.toOH (gridA d k (i + 1)))) (S.neg (atn (dv S.toOH (gridA d k i)))))
          (S.neg (S.mul (S.mul S.half (S.add (dv S.toOH (gridA d k (i + 1))) (S.neg (dv S.toOH (gridA d k i)))))
            (S.add wa wb)))) ∧
      S.le (S.add (S.add (atn (dv S.toOH (gridA d k (i + 1)))) (S.neg (atn (dv S.toOH (gridA d k i)))))
          (S.neg (S.mul (S.mul S.half (S.add (dv S.toOH (gridA d k (i + 1))) (S.neg (dv S.toOH (gridA d k i)))))
            (S.add wa wb))))
        (S.mul S.half (S.mul S.half (dv S.toOH (dabs (dmul hd (dmul hd hd)))))) := by
    cases hb : dle (gridA d k i) (gridA d k (i + 1)) with
    | true =>
        obtain ⟨r1, r2⟩ := trap_up H (dle_sound S.toOH hb) hwa hwb
        have c1 := S.le_respects eX (S.refl _) ab2
        have s := le_mul_left' S (le_mul_left' S c1 hh0) hh0
        exact ⟨by cr_linarith S.toOCR [r1, s], by cr_linarith S.toOCR [r2, s]⟩
    | false =>
        obtain ⟨r1, r2⟩ := trap_down H (dle_sound S.toOH (dle_swap hb)) hwa hwb
        have c1 : S.le (cub S (dv S.toOH (gridA d k (i + 1))) (dv S.toOH (gridA d k i)))
            (dv S.toOH (dabs (dmul hd (dmul hd hd)))) := by
          have := S.le_respects (S.refl _) eX ab1
          exact S.le_respects (S.symm cubs) (S.refl _) (by cr_linarith S.toOCR [this])
        have s := le_mul_left' S (le_mul_left' S c1 hh0) hh0
        exact ⟨by cr_linarith S.toOCR [r1, s], by cr_linarith S.toOCR [r2, s]⟩
  have mR : Mem S (S.add (S.add (atn (dv S.toOH (gridA d k (i + 1)))) (S.neg (atn (dv S.toOH (gridA d k i)))))
      (S.neg (S.mul (S.mul S.half (S.add (dv S.toOH (gridA d k (i + 1))) (S.neg (dv S.toOH (gridA d k i)))))
        (S.add wa wb)))) (dneg (qcube hd), qcube hd) :=
    ⟨S.le_respects (S.trans (S.neg_congr (S.symm eq)) (S.symm (dv_neg S.toOH _))) (S.refl _) hR.1,
     S.le_respects (S.refl _) (S.symm eq) hR.2⟩
  have m := mem_add S mM mR h
  refine mem_congr S ?_ m
  refine S.symm (S.trans (S.add_congr (S.mul_congr eh2 (S.refl _)) (S.refl _)) ?_)
  cr_ring S.toCR

theorem dv_grid0 (d : D) (k : Nat) : S.r (dv S.toOH (gridA d k 0)) S.zero :=
  S.trans (dv_mul S.toOH _ _) (S.trans (S.mul_congr (S.refl _) (zv_isZ S.toOH (c := ⟨⟨0, 0⟩, k⟩) rfl))
    (by cr_ring S.toCR))

theorem enc_mem {atn : α → α} (H : AtanLaws S atn) (d : D) (k : Nat) :
    ∀ i E, encS d k i = some E → Mem S (atn (dv S.toOH (gridA d k i))) E
  | 0, E, h => by
      cases h
      have e := S.trans (H.congr (dv_grid0 d k)) H.zero
      exact ⟨S.le_respects (S.symm (dv_zeroD S)) (S.symm e) (S.le_refl S.zero),
        S.le_respects (S.symm e) (S.symm (dv_zeroD S)) (S.le_refl S.zero)⟩
  | i + 1, E, h => by
      unfold encS at h
      cases h1 : encS d k i with
      | none => rw [h1] at h; cases h
      | some E0 =>
      rw [h1] at h; dsimp only at h
      cases h2 : segC d k i with
      | none => rw [h2] at h; cases h
      | some C =>
      rw [h2] at h; dsimp only at h
      have m := mem_add S (enc_mem H d k i E0 h1) (seg_mem H d k i h2) h
      exact mem_congr S (by cr_ring S.toCR) m

theorem dv_gridN (d : D) (k : Nat) : S.r (dv S.toOH (gridA d k (2 ^ k))) (dv S.toOH d) := by
  refine S.trans (dv_mul S.toOH _ _) ?_
  have e : S.r (dv S.toOH (⟨⟨2 ^ k, 0⟩, k⟩ : D)) S.one := by
    show S.r (S.mul (S.add (nI S.toOH (2 ^ k)) (S.neg (nI S.toOH 0))) (hp S.toOH k)) S.one
    have z := nI_zero S.toOH
    refine S.trans (S.mul_congr (S.trans (S.add_congr (S.refl _) (S.neg_congr z))
      (by cr_ring S.toCR : S.r (S.add (nI S.toOH (2 ^ k)) (S.neg S.zero)) (nI S.toOH (2 ^ k)))) (S.refl _)) ?_
    exact two_hp S.toOH k
  exact S.trans (S.mul_congr (S.refl _) e) (by cr_ring S.toCR)

/-- **THE ENCLOSURE OF `atan` AT A DYADIC IS SOUND.** -/
theorem atEnc_mem {atn : α → α} (H : AtanLaws S atn) {d : D} {E : Iv} (h : atEnc d = some E) :
    Mem S (atn (dv S.toOH d)) E :=
  mem_congr S (H.congr (S.symm (dv_gridN d atK))) (enc_mem H d atK (2 ^ atK) E h)

/-- **THE READING OF `atan` IS SOUND.** -/
theorem mem_atan {atn : α → α} (H : AtanLaws S atn) {x : α} {I K : Iv} (hx : Mem S x I) (h : ivAtan I = some K) :
    Mem S (atn x) K := by
  unfold ivAtan at h
  cases hW : psiI I with
  | none => rw [hW] at h; cases h
  | some W =>
  rw [hW] at h; dsimp only at h
  cases h1 : atEnc I.1 with
  | none => rw [h1] at h; cases h
  | some E1 =>
  rw [h1] at h; dsimp only at h
  cases h2 : atEnc I.2 with
  | none => rw [h2] at h; cases h
  | some E2 =>
  rw [h2] at h; dsimp only at h
  cases h
  have lo : Mem S (dv S.toOH I.1) I := ⟨S.le_refl _, S.le_trans hx.1 hx.2⟩
  have hi : Mem S (dv S.toOH I.2) I := ⟨S.le_trans hx.1 hx.2, S.le_refl _⟩
  have w0 := psi_lo_nonneg S hW
  obtain ⟨a1, _⟩ := H.chord I W hW _ _ lo hx hx.1
  obtain ⟨b1, _⟩ := H.chord I W hW _ _ hx hi hx.2
  have p1 := S.mul_nonneg (by cr_linarith S.toOCR [hx.1] : S.le S.zero (S.add x (S.neg (dv S.toOH I.1)))) w0
  have p2 := S.mul_nonneg (by cr_linarith S.toOCR [hx.2] : S.le S.zero (S.add (dv S.toOH I.2) (S.neg x))) w0
  have e1 := atEnc_mem H h1
  have e2 := atEnc_mem H h2
  exact ⟨by cr_linarith S.toOCR [a1, p1, e1.1], by cr_linarith S.toOCR [b1, p2, e2.2]⟩

variable (S)

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
  | .atan p => match ivX B p with
      | none => none
      | some I => ivAtan I
  | .sin p => match ivX B p with
      | none => none
      | some I => ivSin I
  | .cos p => match ivX B p with
      | none => none
      | some I => ivCos I
  | .min p q => lift2 (fun I J => some (ivMin I J)) (ivX B p) (ivX B q)

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
theorem ivX_sound {ex atn sn cs : α → α} {mn : α → α → α} {B : Box} {p : Nat → α} (hp : InBox S B p) :
    ∀ {e : XE} {v : α}, Val S ex atn sn cs mn p e v → ∀ K, ivX B e = some K → Mem S v K := by
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
  | @atan a va v H _ e ih =>
      intro K h
      unfold ivX at h
      cases ha : ivX B a with
      | none => rw [ha] at h; cases h
      | some I => rw [ha] at h; exact mem_congr S e (mem_atan H (ih I ha) h)
  | @sin a va v H _ e ih =>
      intro K h
      unfold ivX at h
      cases ha : ivX B a with
      | none => rw [ha] at h; cases h
      | some I => rw [ha] at h; exact mem_congr S e (mem_sin H (ih I ha) h)
  | @cos a va v H _ e ih =>
      intro K h
      unfold ivX at h
      cases ha : ivX B a with
      | none => rw [ha] at h; cases h
      | some I => rw [ha] at h; exact mem_congr S e (mem_cos H (ih I ha) h)
  | @min a b va vb v H _ _ e ih1 ih2 =>
      intro K h
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      cases hk
      exact mem_congr S e (mem_min H (ih1 x ex) (ih2 y ey))

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
  | .sin p => match afX B p with
      | none => none
      | some F => match afIv B F with
          | none => none
          | some I => (ivSin I).map toForm
  | .cos p => match afX B p with
      | none => none
      | some F => match afIv B F with
          | none => none
          | some I => (ivCos I).map toForm
  | .min p q => match afX B p with
      | none => none
      | some F => match afX B q with
        | none => none
        | some G => match afIv B F with
          | none => none
          | some I => match afIv B G with
            | none => none
            | some J => some (toForm (ivMin I J))

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
theorem afX_sound {ex atn sn cs : α → α} {mn : α → α → α} {B : Box} {p : Nat → α} (hp : InBox S B p) :
    ∀ {e : XE} {v : α}, Val S ex atn sn cs mn p e v → ∀ F, afX B e = some F → Enc S B p v F := by
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
  | @sin a va v H _ e ih =>
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
              cases hq : ivSin I with
              | none => rw [hq] at h; cases h
              | some K =>
                  rw [hq] at h
                  cases h
                  exact enc_of_mem S (mem_congr S e (mem_sin H (afIv_sound S hp (ih G ha) hI) hq))
  | @cos a va v H _ e ih =>
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
              cases hq : ivCos I with
              | none => rw [hq] at h; cases h
              | some K =>
                  rw [hq] at h
                  cases h
                  exact enc_of_mem S (mem_congr S e (mem_cos H (afIv_sound S hp (ih G ha) hI) hq))
  | @min a b va vb v H _ _ e ih1 ih2 =>
      intro F h
      unfold afX at h
      cases ha : afX B a with
      | none => rw [ha] at h; cases h
      | some G =>
      rw [ha] at h; dsimp only at h
      cases hb : afX B b with
      | none => rw [hb] at h; cases h
      | some G' =>
      rw [hb] at h; dsimp only at h
      cases hI : afIv B G with
      | none => rw [hI] at h; cases h
      | some I =>
      rw [hI] at h; dsimp only at h
      cases hJ : afIv B G' with
      | none => rw [hJ] at h; cases h
      | some J =>
      rw [hJ] at h; dsimp only at h
      cases h
      exact enc_of_mem S (mem_congr S e (mem_min H (afIv_sound S hp (ih1 G ha) hI) (afIv_sound S hp (ih2 G' hb) hJ)))

/-- The affine reading as an interval. -/
def afIvX (B : Box) (e : XE) : Option Iv :=
  match afX B e with
  | none => none
  | some F => afIv B F

theorem afIvX_sound {ex atn sn cs : α → α} {mn : α → α → α} {B : Box} {p : Nat → α} (hp : InBox S B p) {e : XE} {v : α} (hv : Val S ex atn sn cs mn p e v) (K : Iv)
    (h : afIvX B e = some K) : Mem S v K := by
  unfold afIvX at h
  cases hF : afX B e with
  | none => rw [hF] at h; cases h
  | some F => rw [hF] at h; exact afIv_sound S hp (afX_sound S hp hv F hF) h

end ZXE
#print axioms ZSinIv.mem_sq
#print axioms ZXE.psi_mem
#print axioms ZXE.atEnc_mem
#print axioms ZXE.mem_atan
