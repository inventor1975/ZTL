import ZSlope
import ZExp

/-!
# ZSlopeExp — `ZSlope` with `exp`, on VR's operational reals. Zero axioms.

(B) of the curator's "сделай и А, и Б" (2026-10-10). Values are operational reals now (`exp` of a rational is
not rational), built as sequences of rationals (`evalN n`, `evalR`), and every statement is "for every precision,
from some index on" (`Ev`) — the comparison `rle` asks for. The kernel's readings stay rational relations; an
`exp` reading carries its brackets certified at the argument's two ends (`ExpCert`).

  * `value_sound` — the value reading encloses the value (products by approximate corners, `exp` by
    monotonicity, the Lipschitz bound and `ZExp.bracket_sound`);
  * `slope_sound` — a derivative reading `[l, h]` in quantity `i` bounds the difference between two points of
    the piece by `[l·d, h·d]`; the `exp` step writes `E(b) − E(a)` between `σ·(b − a)` for slopes `σ` near the
    `exp` interval (`ZExp.E_slope`) — no point between `a` and `b` is chosen, no mean value theorem;
  * `mono_up`, `mono_down`, `certificate_sound` — the kernel's certificate rule, premise-free, as the real order
    `rle` (not total — `ZCertify.corner_bound` is re-proved for it with reflexivity and transitivity only).

Not covered here: division (`ZSlopeDiv`), `ln`; the affine reading the kernel intersects with the interval one (`zaffine`).
-/

namespace ZSlopeExp

open VR.Numbers ZCertify ZSlope ZExp

/-! ## Approximate corners -/

/-- Moving both factors by at most `e ≤ 1` moves the product by at most `e·(2M + 1)` (`|x|, |y| ≤ M`). -/
theorem shift_prod {x y u v M e : QExpr} (hx : qclose x qzero M) (hy : qclose y qzero M)
    (hu : qclose u qzero e) (hv : qclose v qzero e) (he1 : qle e qone) :
    qclose (qmul (qadd x u) (qadd y v)) (qmul x y) (qmul e (qadd (qadd M M) qone)) := by
  have p1 := qmul_abs_bound hx hv
  have p2 := qmul_abs_bound hu hy
  have p3 := qmul_abs_bound hu hv
  have he : qle qzero e := by obtain ⟨h1, h2⟩ := hu; unfold qsub at h1 h2; rat_linarith
  have hM : qle qzero M := by obtain ⟨h1, h2⟩ := hx; unfold qsub at h1 h2; rat_linarith
  have f := scale_l he1 he
  have e1 := qmul_one e
  have r1 : qEq (qmul M e) (qmul e M) := qmul_comm _ _
  have r2 : qEq (qmul e (qadd (qadd M M) qone)) (qadd (qadd (qmul e M) (qmul e M)) e) := by rat_ring
  have r3 : qEq (qsub (qmul (qadd x u) (qadd y v)) (qmul x y))
      (qadd (qadd (qmul x v) (qmul u y)) (qmul u v)) := by unfold qsub; rat_ring
  obtain ⟨a1, a2⟩ := p1
  obtain ⟨b1, b2⟩ := p2
  obtain ⟨c1, c2⟩ := p3
  have s1 : qEq (qsub (qmul x v) qzero) (qmul x v) := by unfold qsub; rat_ring
  have s2 : qEq (qsub (qmul u y) qzero) (qmul u y) := by unfold qsub; rat_ring
  have s3 : qEq (qsub (qmul u v) qzero) (qmul u v) := by unfold qsub; rat_ring
  constructor <;> rat_linarith

/-- Corners of `[a1, a2] × [b1, b2]`, between `l` and `h`; factors within `e` of their intervals, the interval
ends within `M`: the product lies in `[l − e(2M+1), h + e(2M+1)]`. -/
theorem approx_corner {a1 a2 b1 b2 l h e M a b : QExpr} (hc : Corners l h a1 a2 b1 b2)
    (m1 : qclose a1 qzero M) (m2 : qclose a2 qzero M) (m3 : qclose b1 qzero M) (m4 : qclose b2 qzero M)
    (he : qle qzero e) (he1 : qle e qone)
    (ha1 : qle (qsub a1 e) a) (ha2 : qle a (qadd a2 e)) (hb1 : qle (qsub b1 e) b) (hb2 : qle b (qadd b2 e)) :
    qle (qsub l (qmul e (qadd (qadd M M) qone))) (qmul a b) ∧
    qle (qmul a b) (qadd h (qmul e (qadd (qadd M M) qone))) := by
  obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hc
  have en : qclose (qneg e) qzero e := by constructor <;> (unfold qsub; rat_linarith)
  have ep : qclose e qzero e := by constructor <;> (unfold qsub; rat_linarith)
  have c11 := shift_prod m1 m3 en en he1
  have c12 := shift_prod m1 m4 en ep he1
  have c21 := shift_prod m2 m3 ep en he1
  have c22 := shift_prod m2 m4 ep ep he1
  obtain ⟨c11a, c11b⟩ := c11
  obtain ⟨c12a, c12b⟩ := c12
  obtain ⟨c21a, c21b⟩ := c21
  obtain ⟨c22a, c22b⟩ := c22
  unfold qsub at *
  exact ⟨mul_lo ha1 ha2 hb1 hb2 (by rat_linarith) (by rat_linarith) (by rat_linarith) (by rat_linarith),
         mul_hi ha1 ha2 hb1 hb2 (by rat_linarith) (by rat_linarith) (by rat_linarith) (by rat_linarith)⟩

/-! ## "Eventually in `[l, h]`, to every precision" -/

def Ev (x : Nat → QExpr) (l h : QExpr) : Prop :=
  ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub l (qeps k)) (x n) ∧ qle (x n) (qadd h (qeps k))

theorem Ev_of_exact {x : Nat → QExpr} {l h : QExpr} (N0 : Nat) (hx : ∀ n, N0 ≤ n → qle l (x n) ∧ qle (x n) h) :
    Ev x l h := fun k => ⟨N0, fun n hn => by
  obtain ⟨a, b⟩ := hx n hn; have := qeps_nonneg k
  exact ⟨by unfold qsub; rat_linarith, by rat_linarith⟩⟩

theorem Ev_widen {x : Nat → QExpr} {l h l' h' : QExpr} (hv : Ev x l h) (hl : qle l' l) (hh : qle h h') :
    Ev x l' h' := fun k => by
  obtain ⟨N, hN⟩ := hv k
  exact ⟨N, fun n hn => by obtain ⟨a, b⟩ := hN n hn; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩

theorem Ev_add {x y : Nat → QExpr} {l1 h1 l2 h2 : QExpr} (hx : Ev x l1 h1) (hy : Ev y l2 h2) :
    Ev (fun n => qadd (x n) (y n)) (qadd l1 l2) (qadd h1 h2) := fun k => by
  obtain ⟨N1, h1'⟩ := hx (k + 1)
  obtain ⟨N2, h2'⟩ := hy (k + 1)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := h1' n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  obtain ⟨b1, b2⟩ := h2' n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  have e := qeps_succ_add k
  show qle _ (qadd (x n) (y n)) ∧ qle (qadd (x n) (y n)) _
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem Ev_sub {x y : Nat → QExpr} {l1 h1 l2 h2 : QExpr} (hx : Ev x l1 h1) (hy : Ev y l2 h2) :
    Ev (fun n => qsub (x n) (y n)) (qsub l1 h2) (qsub h1 l2) := fun k => by
  obtain ⟨N1, h1'⟩ := hx (k + 1)
  obtain ⟨N2, h2'⟩ := hy (k + 1)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := h1' n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  obtain ⟨b1, b2⟩ := h2' n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  have e := qeps_succ_add k
  show qle _ (qsub (x n) (y n)) ∧ qle (qsub (x n) (y n)) _
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem eps_le_one (k : Nat) : qle (qeps k) qone := by
  have h := qeps_le_add 0 k
  rw [Nat.zero_add] at h
  exact qle_trans h (qle_of_qEq qeps_zero)

/-- `ε_{k+B+2}·(2M + 1) ≤ ε_k` when `0 ≤ M ≤ 2^B`. -/
theorem eps_scale {M : QExpr} {B : Nat} (hM0 : qle qzero M) (hM : qle M (qofInt (pow2 B))) (k : Nat) :
    qle (qmul (qeps (k + (B + 2))) (qadd (qadd M M) qone)) (qeps k) := by
  have p1 : qEq (qofInt (pow2 (B + 1))) (qadd (qofInt (pow2 B)) (qofInt (pow2 B))) :=
    qEq_trans (qofInt_respects (pow2_succ B)) (qofInt_add _ _)
  have p2 : qEq (qofInt (pow2 (B + 2))) (qadd (qofInt (pow2 (B + 1))) (qofInt (pow2 (B + 1)))) :=
    qEq_trans (qofInt_respects (pow2_succ (B + 1))) (qofInt_add _ _)
  have one : qle qone (qofInt (pow2 B)) := qofInt_le (one_le_pow2 B)
  have hle : qle (qadd (qadd M M) qone) (qofInt (pow2 (B + 2))) := by rat_linarith
  have f := scale_l hle (qeps_nonneg (k + (B + 2)))
  have e := qpow2_mul_eps (B + 2) k
  have c : qEq (qmul (qeps (k + (B + 2))) (qofInt (pow2 (B + 2))))
      (qmul (qofInt (pow2 (B + 2))) (qeps (k + (B + 2)))) := qmul_comm _ _
  rat_linarith

/-- A pre-rational bound common to finitely many: `|x| ≤ 2^B`. -/
theorem bound4 (a b c d : QExpr) : ∃ M B, qle qzero M ∧ qle M (qofInt (pow2 B)) ∧
    qclose a qzero M ∧ qclose b qzero M ∧ qclose c qzero M ∧ qclose d qzero M := by
  obtain ⟨B1, a1, a2⟩ := qexpr_bound a
  obtain ⟨B2, b1, b2⟩ := qexpr_bound b
  obtain ⟨B3, c1, c2⟩ := qexpr_bound c
  obtain ⟨B4, d1, d2⟩ := qexpr_bound d
  have p1 := qofInt_le (pow2_nonneg B1)
  have p2 := qofInt_le (pow2_nonneg B2)
  have p3 := qofInt_le (pow2_nonneg B3)
  have p4 := qofInt_le (pow2_nonneg B4)
  obtain ⟨B, hB, _⟩ := qexpr_bound
    (qadd (qadd (qofInt (pow2 B1)) (qofInt (pow2 B2))) (qadd (qofInt (pow2 B3)) (qofInt (pow2 B4))))
  unfold qsub at *
  refine ⟨qadd (qadd (qofInt (pow2 B1)) (qofInt (pow2 B2))) (qadd (qofInt (pow2 B3)) (qofInt (pow2 B4))), B,
    by rat_linarith, by rat_linarith, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> (unfold qsub; rat_linarith)

/-- PRODUCTS: factors eventually in their intervals, the corners bracketed: the product eventually in
`[l, h]`. -/
theorem Ev_mul {x y : Nat → QExpr} {a1 a2 b1 b2 l h : QExpr} (hx : Ev x a1 a2) (hy : Ev y b1 b2)
    (hc : Corners l h a1 a2 b1 b2) : Ev (fun n => qmul (x n) (y n)) l h := fun k => by
  obtain ⟨M, B, hM0, hMB, m1, m2, m3, m4⟩ := bound4 a1 a2 b1 b2
  obtain ⟨N1, h1⟩ := hx (k + (B + 2))
  obtain ⟨N2, h2⟩ := hy (k + (B + 2))
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨xa, xb⟩ := h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  obtain ⟨ya, yb⟩ := h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  have he := qeps_nonneg (k + (B + 2))
  have he1 := eps_le_one (k + (B + 2))
  obtain ⟨c1, c2⟩ := approx_corner hc m1 m2 m3 m4 he he1 xa xb ya yb
  have es := eps_scale hM0 hMB k
  show qle _ (qmul (x n) (y n)) ∧ qle (qmul (x n) (y n)) _
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `exp` of an argument eventually in `[lu, hu]`, with the kernel's brackets certified at the ends: eventually
in `[El, Eh]`. Monotone, Lipschitz on a bounded range, and the bracket theorem (A) at `lu` and at `hu`. -/
theorem Ev_exp {x : Nat → QExpr} {lu hu El Eh : QExpr} (hx : Ev x lu hu)
    (cl : ∃ z, ExpCert lu El z) (ch : ∃ z, ExpCert hu z Eh) : Ev (fun n => eseq (x n) n) El Eh := fun k => by
  obtain ⟨zl, cl⟩ := cl
  obtain ⟨zh, ch⟩ := ch
  have bl := (bracket_sound cl).1
  have bh := (bracket_sound ch).2
  obtain ⟨M, _, hM0, _, ml, mh, _, _⟩ := bound4 lu hu lu hu
  -- R = M + 1 covers [lu − 1, hu + 1]
  have hR0 : qle qzero (qadd M qone) := by have := qle_of_qlt qone_pos; rat_linarith
  obtain ⟨H, hH⟩ := S_bounded hR0
  obtain ⟨C, hC0, _⟩ := qexpr_bound H
  have hC : qle H (qofInt (pow2 C)) := by unfold qsub at hC0; rat_linarith
  obtain ⟨N1, h1⟩ := hx ((k + 1) + C)
  obtain ⟨N2, h2⟩ := bl (k + 1)
  obtain ⟨N3, h3⟩ := bh (k + 1)
  refine ⟨N1 + N2 + N3 + 1, fun n hn => ?_⟩
  have n1 : N1 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N3))
    (Nat.le_trans (Nat.le_add_right _ 1) hn)
  have n2 : N2 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N3))
    (Nat.le_trans (Nat.le_add_right _ 1) hn)
  have n3 : N3 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N3 (N1 + N2)) (Nat.le_add_right _ 1)) hn
  obtain ⟨xa, xb⟩ := h1 n n1
  have g2 : qle (qsub El (eseq lu n)) (qeps (k + 1)) := h2 n n2
  have g3 : qle (qsub (eseq hu n) Eh) (qeps (k + 1)) := h3 n n3
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n' => exact ⟨n', rfl⟩
  have δ0 := qeps_nonneg ((k + 1) + C)
  have δ1 := eps_le_one ((k + 1) + C)
  obtain ⟨ml1, ml2⟩ := ml
  obtain ⟨mh1, mh2⟩ := mh
  unfold qsub at ml1 ml2 mh1 mh2
  -- the moved ends stay within R
  have rl : qclose (qsub lu (qeps ((k + 1) + C))) qzero (qadd M qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have rl' : qclose lu qzero (qadd M qone) := by constructor <;> (unfold qsub; rat_linarith)
  have rh : qclose (qadd hu (qeps ((k + 1) + C))) qzero (qadd M qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have rh' : qclose hu qzero (qadd M qone) := by constructor <;> (unfold qsub; rat_linarith)
  have dl : qclose (qsub lu (qeps ((k + 1) + C))) lu (qeps ((k + 1) + C)) := by
    constructor <;> (unfold qsub; rat_linarith)
  have dh : qclose (qadd hu (qeps ((k + 1) + C))) hu (qeps ((k + 1) + C)) := by
    constructor <;> (unfold qsub; rat_linarith)
  have m1 := E_mono xa n'
  have m2 := E_mono xb n'
  obtain ⟨L1, _⟩ := E_lip rl rl' dl n'
  obtain ⟨_, L2⟩ := E_lip rh rh' dh n'
  have hHn := hH (n' + 1)
  have s1 := scale_l (qle_trans hHn hC) δ0
  have s2 := scale_l hHn δ0
  have e1 : qEq (qmul (qeps ((k + 1) + C)) (qofInt (pow2 C))) (qmul (qofInt (pow2 C)) (qeps ((k + 1) + C))) :=
    qmul_comm _ _
  have e2 := qpow2_mul_eps C (k + 1)
  have e3 := qeps_succ_add k
  show qle _ (eseq (x (n' + 1)) (n' + 1)) ∧ qle (eseq (x (n' + 1)) (n' + 1)) _
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The grammar with `exp`, its value as an operational real -/

inductive F where
  | const : QExpr → F
  | var   : Nat → F
  | add   : F → F → F
  | sub   : F → F → F
  | mul   : F → F → F
  | exp   : F → F

/-- The `n`-th rational approximant of the value. -/
def evalN (n : Nat) (p : Point QExpr) : F → QExpr
  | .const c => c
  | .var i => p i
  | .add u v => qadd (evalN n p u) (evalN n p v)
  | .sub u v => qsub (evalN n p u) (evalN n p v)
  | .mul u v => qmul (evalN n p u) (evalN n p v)
  | .exp u => eseq (evalN n p u) n

/-- The value, an operational real (each constructor's sequence is `evalN`'s). -/
def evalR (p : Point QExpr) : F → RExpr
  | .const c => rofQ c
  | .var i => rofQ (p i)
  | .add u v => radd (evalR p u) (evalR p v)
  | .sub u v => radd (evalR p u) (rneg (evalR p v))
  | .mul u v => rmul (evalR p u) (evalR p v)
  | .exp u => rexpR (evalR p u)

theorem evalR_seq (p : Point QExpr) (n : Nat) : ∀ e : F, (evalR p e).seq n = evalN n p e
  | .const _ => rfl
  | .var _ => rfl
  | .add u v => by
      show qadd ((evalR p u).seq n) ((evalR p v).seq n) = _
      rw [evalR_seq p n u, evalR_seq p n v]; rfl
  | .sub u v => by
      show qadd ((evalR p u).seq n) (qneg ((evalR p v).seq n)) = _
      rw [evalR_seq p n u, evalR_seq p n v]; rfl
  | .mul u v => by
      show qmul ((evalR p u).seq n) ((evalR p v).seq n) = _
      rw [evalR_seq p n u, evalR_seq p n v]; rfl
  | .exp u => by
      show eseq ((evalR p u).seq n) n = _
      rw [evalR_seq p n u]; rfl

/-- What the kernel checks of a value reading, now with `exp`: the argument's reading `[lu, hu]`, and its
own `exp` brackets certified at the two ends (`ExpCert`, the rule `zexpcert.py` applies). -/
inductive VRead (B : Box QExpr) : F → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l c → qle c h → VRead B (.const c) l h
  | var {i : Nat} {l h : QExpr} : qle l (B i).1 → qle (B i).2 h → VRead B (.var i) l h
  | add {u v : F} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → VRead B (.add u v) l h
  | sub {u v : F} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → VRead B (.sub u v) l h
  | mul {u v : F} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      Corners l h l1 h1 l2 h2 → VRead B (.mul u v) l h
  | exp {u : F} {lu hu El Eh : QExpr} : VRead B u lu hu →
      (∃ z, ExpCert lu El z) → (∃ z, ExpCert hu z Eh) → VRead B (.exp u) El Eh

/-- THE VALUE READING IS SOUND: eventually in `[l, h]`, to every precision. -/
theorem value_sound {B : Box QExpr} {p : Point QExpr} (hp : InBox qOrd B p) :
    ∀ {e : F} {l h : QExpr}, VRead B e l h → Ev (fun n => evalN n p e) l h := by
  intro e l h r
  induction r with
  | const h1 h2 => exact Ev_of_exact 0 (fun _ _ => ⟨h1, h2⟩)
  | var h1 h2 => exact Ev_of_exact 0 (fun _ _ => ⟨qle_trans h1 (hp _).1, qle_trans (hp _).2 h2⟩)
  | add _ _ hl hh ih1 ih2 => exact Ev_widen (Ev_add ih1 ih2) hl hh
  | sub _ _ hl hh ih1 ih2 => exact Ev_widen (Ev_sub ih1 ih2) hl hh
  | mul _ _ hc ih1 ih2 => exact Ev_mul ih1 ih2 hc
  | exp _ cl ch ih => exact Ev_exp ih cl ch

/-! ## The slope with `exp` -/

theorem Ev_congr {x y : Nat → QExpr} {l h : QExpr} (e : ∀ n, qEq (x n) (y n)) (hx : Ev x l h) : Ev y l h :=
  fun k => by
    obtain ⟨N, hN⟩ := hx k
    exact ⟨N, fun n hn => by obtain ⟨a, b⟩ := hN n hn; have := e n; exact ⟨by rat_linarith, by rat_linarith⟩⟩

/-- Corners scaled by `d ≥ 0` in the second factor. -/
theorem corners_scale {m M a1 a2 b1 b2 d : QExpr} (hc : Corners m M a1 a2 b1 b2) (hd : qle qzero d) :
    Corners (qmul m d) (qmul M d) a1 a2 (qmul b1 d) (qmul b2 d) := by
  obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hc
  have r : ∀ x y : QExpr, qEq (qmul (qmul x y) d) (qmul x (qmul y d)) := fun x y => by rat_ring
  exact ⟨⟨qle_respects (qEq_refl _) (r _ _) (ZExp.scale l11 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l12 hd),
          qle_respects (qEq_refl _) (r _ _) (ZExp.scale l21 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l22 hd)⟩,
         ⟨qle_respects (r _ _) (qEq_refl _) (ZExp.scale h11 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h12 hd),
          qle_respects (r _ _) (qEq_refl _) (ZExp.scale h21 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h22 hd)⟩⟩

theorem le_add_l {x y : Nat} (z : Nat) (h : x ≤ y) : x ≤ y + z := Nat.le_trans h (Nat.le_add_right y z)

/-- Each of six summands is below the sum (`omega` would bring `propext`). -/
theorem le6 (a b c d e f : Nat) :
    a ≤ a + b + c + d + e + f ∧ b ≤ a + b + c + d + e + f ∧ c ≤ a + b + c + d + e + f ∧
    d ≤ a + b + c + d + e + f ∧ e ≤ a + b + c + d + e + f ∧ f ≤ a + b + c + d + e + f :=
  ⟨le_add_l f (le_add_l e (le_add_l d (le_add_l c (Nat.le_add_right a b)))),
   le_add_l f (le_add_l e (le_add_l d (le_add_l c (Nat.le_add_left b a)))),
   le_add_l f (le_add_l e (le_add_l d (Nat.le_add_left c (a + b)))),
   le_add_l f (le_add_l e (Nat.le_add_left d (a + b + c))),
   le_add_l f (Nat.le_add_left e (a + b + c + d)),
   Nat.le_add_left f (a + b + c + d + e)⟩

/-- THE `exp` STEP. The argument's approximants at the two points, `a_n` and `b_n`, eventually in `[lu, hu]`;
the `exp` values eventually in `[El, Eh]`; the argument's difference eventually in `[t1, t2]`; the corners of
`[El, Eh] × [t1, t2]` between `m` and `M`. Then the difference of the `exp` values is eventually in `[m, M]`.
At each index, `E_slope` writes it between `σ·(b − a)` for two slopes `σ` near `[El, Eh]` — no point between
`a` and `b` is chosen. -/
theorem Ev_exp_slope {a b : Nat → QExpr} {lu hu El Eh t1 t2 m M : QExpr}
    (ha : Ev a lu hu) (hb : Ev b lu hu)
    (Ea : Ev (fun n => eseq (a n) n) El Eh) (Eb : Ev (fun n => eseq (b n) n) El Eh)
    (hΔ : Ev (fun n => qsub (b n) (a n)) t1 t2) (hc : Corners m M El Eh t1 t2) :
    Ev (fun n => qsub (eseq (b n) n) (eseq (a n) n)) m M := fun k => by
  obtain ⟨Mc, B, hM0, hMB, c1, c2, c3, c4⟩ := bound4 El Eh t1 t2
  -- R covers the argument's eventual range [lu − 1, hu + 1]
  obtain ⟨Mu, _, hMu0, _, mlu, mhu, _, _⟩ := bound4 lu hu lu hu
  have hR0 : qle qzero (qadd Mu qone) := by have := qle_of_qlt qone_pos; rat_linarith
  obtain ⟨K, hg⟩ := good_exists (qadd Mu qone)
  obtain ⟨Nt, _, hNt⟩ := tm_small hR0 hg (k + (B + 2) + 1)
  obtain ⟨Na, hNa⟩ := ha 0
  obtain ⟨Nb, hNb⟩ := hb 0
  obtain ⟨Nea, hNea⟩ := Ea (k + (B + 2) + 1)
  obtain ⟨Neb, hNeb⟩ := Eb (k + (B + 2) + 1)
  obtain ⟨Nd, hNd⟩ := hΔ (k + (B + 2))
  refine ⟨Nt + Na + Nb + Nea + Neb + Nd + 1, fun n hn => ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n' => exact ⟨n', rfl⟩
  have hn' : Nt + Na + Nb + Nea + Neb + Nd ≤ n' := Nat.le_of_succ_le_succ hn
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := le6 Nt Na Nb Nea Neb Nd
  have up : ∀ X, X ≤ Nt + Na + Nb + Nea + Neb + Nd → X ≤ n' + 1 :=
    fun X h => Nat.le_succ_of_le (Nat.le_trans h hn')
  obtain ⟨a1, a2⟩ := hNa (n' + 1) (up Na q2)
  obtain ⟨b1, b2⟩ := hNb (n' + 1) (up Nb q3)
  obtain ⟨ea1, ea2⟩ := hNea (n' + 1) (up Nea q4)
  obtain ⟨eb1, eb2⟩ := hNeb (n' + 1) (up Neb q5)
  obtain ⟨d1, d2⟩ := hNd (n' + 1) (up Nd q6)
  have tt := hNt n' (Nat.le_trans q1 hn')
  have t0 := tm_nonneg hR0 n'
  have e0 := qeps_nonneg (k + (B + 2) + 1)
  have ee := qeps_succ_add (k + (B + 2))
  have e1 := eps_le_one (k + (B + 2))
  have eE := qeps_nonneg (k + (B + 2))
  obtain ⟨u1, u2⟩ := mlu
  obtain ⟨w1, w2⟩ := mhu
  unfold qsub at u1 u2 w1 w2 a1 b1
  have e00 : qEq (qeps 0) qone := qeps_zero
  have aR : qclose (a (n' + 1)) qzero (qadd Mu qone) := by constructor <;> (unfold qsub; rat_linarith)
  have bR : qclose (b (n' + 1)) qzero (qadd Mu qone) := by constructor <;> (unfold qsub; rat_linarith)
  have es := eps_scale hM0 hMB k
  show qle _ (qsub (eseq (b (n' + 1)) (n' + 1)) (eseq (a (n' + 1)) (n' + 1))) ∧
    qle (qsub (eseq (b (n' + 1)) (n' + 1)) (eseq (a (n' + 1)) (n' + 1))) _
  cases qle_total (a (n' + 1)) (b (n' + 1)) with
  | inl hab =>
      obtain ⟨L, U⟩ := E_slope hab aR bR n'
      -- σ1 = E(a) − t, σ2 = E(b), both within e of [El, Eh]
      obtain ⟨p1, _⟩ := approx_corner hc c1 c2 c3 c4 eE e1
        (a := qsub (eseq (a (n' + 1)) (n' + 1)) (tm (qadd Mu qone) n')) (b := qsub (b (n' + 1)) (a (n' + 1)))
        (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith) d1 d2
      obtain ⟨_, p2⟩ := approx_corner hc c1 c2 c3 c4 eE e1
        (a := eseq (b (n' + 1)) (n' + 1)) (b := qsub (b (n' + 1)) (a (n' + 1)))
        (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith) d1 d2
      have r1 := qmul_comm (qsub (b (n' + 1)) (a (n' + 1))) (qsub (eseq (a (n' + 1)) (n' + 1)) (tm (qadd Mu qone) n'))
      have r2 := qmul_comm (qsub (b (n' + 1)) (a (n' + 1))) (eseq (b (n' + 1)) (n' + 1))
      unfold qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | inr hba =>
      obtain ⟨L, U⟩ := E_slope hba bR aR n'
      -- Δ = −(E(a) − E(b)): σ1 = E(a), σ2 = E(b) − t
      obtain ⟨p1, _⟩ := approx_corner hc c1 c2 c3 c4 eE e1
        (a := eseq (a (n' + 1)) (n' + 1)) (b := qsub (b (n' + 1)) (a (n' + 1)))
        (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith) d1 d2
      obtain ⟨_, p2⟩ := approx_corner hc c1 c2 c3 c4 eE e1
        (a := qsub (eseq (b (n' + 1)) (n' + 1)) (tm (qadd Mu qone) n')) (b := qsub (b (n' + 1)) (a (n' + 1)))
        (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith) d1 d2
      have r1 : qEq (qmul (eseq (a (n' + 1)) (n' + 1)) (qsub (b (n' + 1)) (a (n' + 1))))
          (qneg (qmul (qsub (a (n' + 1)) (b (n' + 1))) (eseq (a (n' + 1)) (n' + 1)))) := by unfold qsub; rat_ring
      have r2 : qEq (qmul (qsub (eseq (b (n' + 1)) (n' + 1)) (tm (qadd Mu qone) n')) (qsub (b (n' + 1)) (a (n' + 1))))
          (qneg (qmul (qsub (a (n' + 1)) (b (n' + 1))) (qsub (eseq (b (n' + 1)) (n' + 1)) (tm (qadd Mu qone) n')))) := by
        unfold qsub; rat_ring
      have r3 : qEq (qsub (eseq (b (n' + 1)) (n' + 1)) (eseq (a (n' + 1)) (n' + 1)))
          (qneg (qsub (eseq (a (n' + 1)) (n' + 1)) (eseq (b (n' + 1)) (n' + 1)))) := by unfold qsub; rat_ring
      unfold qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- What the kernel checks of a derivative reading in quantity `i`, now with `exp`: `(e^u)' = e^u · u'`, the
`exp` interval being the value reading's (brackets certified at the argument's ends). -/
inductive DRead (B : Box QExpr) (i : Nat) : F → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l qzero → qle qzero h → DRead B i (.const c) l h
  | self {l h : QExpr} : qle l qone → qle qone h → DRead B i (.var i) l h
  | other {j : Nat} {l h : QExpr} : j ≠ i → qle l qzero → qle qzero h → DRead B i (.var j) l h
  | add {u v : F} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → DRead B i (.add u v) l h
  | sub {u v : F} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → DRead B i (.sub u v) l h
  | mul {u v : F} {lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h : QExpr} :
      VRead B u lu hu → VRead B v lv hv → DRead B i u du1 du2 → DRead B i v dv1 dv2 →
      Corners m1 M1 lu hu dv1 dv2 → Corners m2 M2 lv hv du1 du2 →
      qle l (qadd m1 m2) → qle (qadd M1 M2) h → DRead B i (.mul u v) l h
  | exp {u : F} {lu hu El Eh du1 du2 m M l h : QExpr} :
      VRead B u lu hu → (∃ z, ExpCert lu El z) → (∃ z, ExpCert hu z Eh) → DRead B i u du1 du2 →
      Corners m M El Eh du1 du2 → qle l m → qle M h → DRead B i (.exp u) l h

/-- THE SLOPE, WITH `exp`. Two points of the piece differing only in `i` by `d ≥ 0`: the difference of the
values is eventually in `[l·d, h·d]`, to every precision. -/
theorem slope_sound {B : Box QExpr} {i : Nat} {p p' : Point QExpr} (hp : InBox qOrd B p)
    (hp' : InBox qOrd B p') (hfix : ∀ j, j ≠ i → p' j = p j) (hd : qle qzero (qsub (p' i) (p i))) :
    ∀ {e : F} {l h : QExpr}, DRead B i e l h →
      Ev (fun n => qsub (evalN n p' e) (evalN n p e)) (qmul l (qsub (p' i) (p i))) (qmul h (qsub (p' i) (p i))) := by
  intro e l h r
  induction r with
  | @const c l h hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub c c) qzero := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub c c); rat_linarith, by show qle (qsub c c) _; rat_linarith⟩)
  | @self l h hl hh =>
      have f1 : qle qzero (qmul (qsub qone l) (qsub (p' i) (p i))) := qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e1 : qEq (qmul (qsub qone l) (qsub (p' i) (p i)))
          (qadd (qsub (p' i) (p i)) (qneg (qmul l (qsub (p' i) (p i))))) := by unfold qsub; rat_ring
      have f2 : qle qzero (qmul (qsub h qone) (qsub (p' i) (p i))) := qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e2 : qEq (qmul (qsub h qone) (qsub (p' i) (p i)))
          (qadd (qmul h (qsub (p' i) (p i))) (qneg (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub (p' i) (p i)); rat_linarith,
                                       by show qle (qsub (p' i) (p i)) _; rat_linarith⟩)
  | @other j l h hj hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub (p j) (p j)) qzero := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => by
        show qle _ (qsub (p' j) (p j)) ∧ qle (qsub (p' j) (p j)) _
        rw [hfix j hj]; exact ⟨by rat_linarith, by rat_linarith⟩)
  | @add u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd l1 l2) (qsub (p' i) (p i)))
          (qadd (qmul l1 (qsub (p' i) (p i))) (qmul l2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd h1 h2) (qsub (p' i) (p i)))
          (qadd (qmul h1 (qsub (p' i) (p i))) (qmul h2 (qsub (p' i) (p i)))) := by rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_add ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qadd (evalN n p' u) (evalN n p' v)) (qadd (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @sub u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qsub l1 h2) (qsub (p' i) (p i)))
          (qsub (qmul l1 (qsub (p' i) (p i))) (qmul h2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      have r2 : qEq (qmul (qsub h1 l2) (qsub (p' i) (p i)))
          (qsub (qmul h1 (qsub (p' i) (p i))) (qmul l2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_sub ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qsub (evalN n p' u) (evalN n p' v)) (qsub (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @mul u v lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h ru rv _ _ c1 c2 hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd m1 m2) (qsub (p' i) (p i)))
          (qadd (qmul m1 (qsub (p' i) (p i))) (qmul m2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd M1 M2) (qsub (p' i) (p i)))
          (qadd (qmul M1 (qsub (p' i) (p i))) (qmul M2 (qsub (p' i) (p i)))) := by rat_ring
      have A := Ev_mul (value_sound hp' ru) ih2 (corners_scale c1 hd)
      have Bv := Ev_mul (value_sound hp rv) ih1 (corners_scale c2 hd)
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_add A Bv)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qmul (evalN n p' u) (evalN n p' v)) (qmul (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @exp u lu hu El Eh du1 du2 m M l h ru cl ch _ hc hl hh ih =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      exact Ev_widen (Ev_exp_slope (value_sound hp ru) (value_sound hp' ru)
        (Ev_exp (value_sound hp ru) cl ch) (Ev_exp (value_sound hp' ru) cl ch) ih (corners_scale hc hd)) s1 s2

/-! ## Monotone, and the certificate rule — on the operational reals -/

/-- A derivative read non-negative: moving `i` to the top never lowers the (real) value. -/
theorem mono_up {B : Box QExpr} {i : Nat} {e : F} {l h : QExpr} (r : DRead B i e l h) (hl : qle qzero l) :
    ∀ p, InBox qOrd B p → rle (evalR p e) (evalR (upd p i (endOf B true i)) e) := by
  intro p hp k
  have hp' := upd_end_inbox qOrd i true hp
  have hu : upd p i (endOf B true i) i = (B i).2 := upd_self p i _
  have hd : qle qzero (qsub (upd p i (endOf B true i) i) (p i)) := by
    have h2 : qle (p i) (B i).2 := (hp i).2
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨N, hN⟩ := slope_sound hp hp' (upd_other p i _) hd r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s0, _⟩ := hN n hn
  have s : qle (qsub (qmul l (qsub (upd p i (endOf B true i) i) (p i))) (qeps k))
      (qsub (evalN n (upd p i (endOf B true i)) e) (evalN n p e)) := s0
  have f := qmul_nonneg hl hd
  rw [evalR_seq, evalR_seq]
  unfold qsub at *
  rat_linarith

/-- A derivative read non-positive: moving `i` to the bottom never lowers the value. -/
theorem mono_down {B : Box QExpr} {i : Nat} {e : F} {l h : QExpr} (r : DRead B i e l h) (hh : qle h qzero) :
    ∀ p, InBox qOrd B p → rle (evalR p e) (evalR (upd p i (endOf B false i)) e) := by
  intro p hp k
  have hp' := upd_end_inbox qOrd i false hp
  have hu : upd p i (endOf B false i) i = (B i).1 := upd_self p i _
  have hfix : ∀ j, j ≠ i → p j = upd p i (endOf B false i) j := fun j hj => (upd_other p i _ j hj).symm
  have hd : qle qzero (qsub (p i) (upd p i (endOf B false i) i)) := by
    have h1 : qle (B i).1 (p i) := (hp i).1
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨N, hN⟩ := slope_sound hp' hp hfix hd r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, s0⟩ := hN n hn
  have s : qle (qsub (evalN n p e) (evalN n (upd p i (endOf B false i)) e))
      (qadd (qmul h (qsub (p i) (upd p i (endOf B false i) i))) (qeps k)) := s0
  have f : qle qzero (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i))) := qmul_nonneg (by rat_linarith) hd
  have e1 : qEq (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i)))
      (qneg (qmul h (qsub (p i) (upd p i (endOf B false i) i)))) := by rat_ring
  rw [evalR_seq, evalR_seq]
  unfold qsub at *
  rat_linarith

/-- The quantities an expression reads. -/
def Uses : F → Nat → Prop
  | .const _, _ => False
  | .var i, j => j = i
  | .add u v, j => Uses u j ∨ Uses v j
  | .sub u v, j => Uses u j ∨ Uses v j
  | .mul u v, j => Uses u j ∨ Uses v j
  | .exp u, j => Uses u j

theorem evalN_dep (n : Nat) (p q : Point QExpr) : ∀ e : F, (∀ j, Uses e j → p j = q j) → evalN n p e = evalN n q e
  | .const _, _ => rfl
  | .var i, h => h i rfl
  | .add u v, h => by
      show qadd _ _ = qadd _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .sub u v, h => by
      show qsub _ _ = qsub _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .mul u v, h => by
      show qmul _ _ = qmul _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .exp u, h => by
      show eseq _ n = eseq _ n
      rw [evalN_dep n p q u h]

/-- Every point is below the corner its signs point to (`ZCertify.corner_bound`, for the real order `rle`,
which is not total — only reflexivity and transitivity are used). -/
theorem corner_bound_R (e : F) (B : Box QExpr) (sg : Nat → Bool) :
    ∀ (ns : List Nat), (∀ i, List.Mem i ns → ∀ p, InBox qOrd B p →
        rle (evalR p e) (evalR (upd p i (endOf B (sg i) i)) e)) →
      ∀ p, InBox qOrd B p → rle (evalR p e) (evalR (cornerOn B sg ns p) e) := by
  intro ns
  induction ns with
  | nil => intro _ p _; exact rle_refl _
  | cons i ns ih =>
      intro hm p hp
      exact rle_trans (hm i (List.Mem.head ns) p hp)
        (ih (fun j hj => hm j (List.Mem.tail i hj)) _ (upd_end_inbox qOrd i (sg i) hp))

/-- The one-point box at a corner — where the kernel reads the value. -/
def cornerBox (B : Box QExpr) (sg : Nat → Bool) : Box QExpr := fun j => (corner B sg j, corner B sg j)

def IvOK (e : F) (c : QExpr) (B : Box QExpr) : Prop := ∃ l h, VRead B e l h ∧ qle h c

def DerivOK (e : F) (B : Box QExpr) (i : Nat) : Bool → Prop
  | true => ∃ l h, DRead B i e l h ∧ qle qzero l
  | false => ∃ l h, DRead B i e l h ∧ qle h qzero

def LeafOK (e : F) (ns : List Nat) (c : QExpr) : Box QExpr → Leaf → Prop
  | B, .interval => IvOK e c B
  | B, .monotone sg => (∀ i, List.Mem i ns → DerivOK e B i (sg i)) ∧ IvOK e c (cornerBox B sg)

/-- An interval reading under the bound: the real value is below it. -/
theorem iv_le {B : Box QExpr} {e : F} {c : QExpr} (h : IvOK e c B) :
    ∀ p, InBox qOrd B p → rle (evalR p e) (rofQ c) := by
  intro p hp k
  obtain ⟨l, h', r, hc⟩ := h
  obtain ⟨N, hN⟩ := value_sound hp r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, b⟩ := hN n hn
  rw [evalR_seq]
  show qle (qsub (evalN n p e) c) (qeps k)
  unfold qsub; rat_linarith

theorem rle_of_seq_eq {x y : RExpr} (h : ∀ n, x.seq n = y.seq n) : rle x y :=
  rle_of_rEq (rEq_of_seq (fun n => by rw [h n]; exact qEq_refl _))

/-- THE CERTIFICATE RULE IS SOUND, WITH `exp`, ON VR'S OPERATIONAL REALS, premise-free: every quantity the
expression reads listed, an accepted certificate shows `e ≤ c` — as the real order `rle` — on the whole box. -/
theorem certificate_sound (e : F) (ns : List Nat) (c : QExpr) (hns : ∀ j, Uses e j → List.Mem j ns) :
    ∀ (t : Tree QExpr Leaf) (B : Box QExpr), Accepts (LeafOK e ns c) B t →
      ∀ p, InBox qOrd B p → rle (evalR p e) (rofQ c) := by
  apply accepts_sound qOrd (LeafOK e ns c) (fun p => rle (evalR p e) (rofQ c))
  intro B lf hok p hp
  cases lf with
  | interval => exact iv_le hok p hp
  | monotone sg =>
      obtain ⟨hd, hcorner⟩ := hok
      have step := corner_bound_R e B sg ns (fun i hi => by
        have := hd i hi
        cases hs : sg i with
        | true => rw [hs] at this; obtain ⟨_, _, r, hl⟩ := this; rw [← hs]; exact hs ▸ mono_up r hl
        | false => rw [hs] at this; obtain ⟨_, _, r, hh⟩ := this; rw [← hs]; exact hs ▸ mono_down r hh) p hp
      have same : rle (evalR (cornerOn B sg ns p) e) (evalR (corner B sg) e) :=
        rle_of_seq_eq (fun n => by
          rw [evalR_seq, evalR_seq]
          exact evalN_dep n _ _ e (fun j hj => cornerOn_agrees B sg ns p j (hns j hj)))
      have atc : InBox qOrd (cornerBox B sg) (corner B sg) := fun j => ⟨qle_refl _, qle_refl _⟩
      exact rle_trans step (rle_trans same (iv_le hcorner _ atc))

set_option maxRecDepth 200000 in
/-- Nonvacuity: `exp x` on `[0, 1]` rises. The kernel's readings: the argument `[0, 1]`, `exp` bracketed
`[1, 3]` (certified at `0` and at `1`), the derivative `[1, 3]·[1, 1]` — non-negative. -/
example : ∀ p, InBox qOrd (fun _ => (qzero, qnat 1)) p →
    rle (evalR p (.exp (.var 0))) (evalR (upd p 0 (endOf (fun _ => (qzero, qnat 1)) true 0)) (.exp (.var 0))) :=
  mono_up (l := qone) (h := qnat 3)
    (DRead.exp (lu := qzero) (hu := qnat 1) (El := qone) (Eh := qnat 3) (du1 := qone) (du2 := qone)
      (m := qone) (M := qnat 3)
      (VRead.var (by decide) (by decide))
      ⟨qone, Or.inl ⟨by decide, 1, by unfold Good; decide, by decide, by decide⟩⟩
      ⟨qnat 2, Or.inl ⟨by decide, 3, by unfold Good; decide, by decide, by decide⟩⟩
      (DRead.self (by decide) (by decide))
      (by unfold Corners; decide) (by decide) (by decide))
    (by decide)

end ZSlopeExp

#print axioms ZSlopeExp.shift_prod
#print axioms ZSlopeExp.approx_corner
#print axioms ZSlopeExp.Ev_add
#print axioms ZSlopeExp.Ev_sub
#print axioms ZSlopeExp.eps_scale
#print axioms ZSlopeExp.bound4
#print axioms ZSlopeExp.Ev_mul
#print axioms ZSlopeExp.Ev_exp
#print axioms ZSlopeExp.evalR_seq
#print axioms ZSlopeExp.value_sound
#print axioms ZSlopeExp.corners_scale
#print axioms ZSlopeExp.Ev_exp_slope
#print axioms ZSlopeExp.slope_sound
#print axioms ZSlopeExp.mono_up
#print axioms ZSlopeExp.mono_down
#print axioms ZSlopeExp.evalN_dep
#print axioms ZSlopeExp.corner_bound_R
#print axioms ZSlopeExp.iv_le
#print axioms ZSlopeExp.certificate_sound
