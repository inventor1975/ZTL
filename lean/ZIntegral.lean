
/-!
# ZIntegral — the rule `zintegral.py` encloses a definite integral by. Zero axioms.

`zintegral.py` (2026-10-16) checks a certificate: a partition `a = x_0 < … < x_n = b` and a leaf per piece. For an
INTERVAL leaf the kernel reads `f` over the piece, `lo ≤ f(t) ≤ hi`; for a MONOTONE leaf it reads the sign of
`f'` there and the values at the two ends. It then adds `L = Σ lo_k · (x_{k+1} − x_k)` and
`U = Σ hi_k · (x_{k+1} − x_k)`. This module proves what that sum means, with no limit taken:

    every tagged sum over a refinement of the partition lies in [L, U]        (`enclosure_sound`)

A refinement splits each piece `[a, b]` into sub-pieces with weights `w_j ≥ 0` adding up to `b − a` and tags
`t_j ∈ [a, b]`; the sum is `Σ w_j · f(t_j)`. The proof is local: on one piece `Σ w_j f(t_j) ≥ Σ w_j lo =
lo · (b − a)` (`piece_lower`, distributivity), then the pieces add. A monotone leaf is an
interval leaf with the end values as its bounds (`monotone_leaf`, `antitone_leaf`).

What is NOT proved here, said rather than hidden:
* the readings: that the kernel's interval encloses `f` on the piece, and that a derivative sign makes `f`
  monotone — `ZSlope` discharges both for `+ − ×` (and `ZSlopeExp` for `exp`) over VR's operational numbers;
  the other functions of `zcertify` stay premises;
* the TAYLOR leaf. Its claim is about the LIMIT of Riemann sums (a single tagged sum can leave its enclosure —
  corrected 2026-10-16, ZTL 331d126), and the Lagrange remainder is classical analysis. It stays a premise;
* that the pieces tile `[a, b]` (points strictly increasing from `a` to `b`) is the Python check; the bound
  itself does not use it. A Riemann sum whose sub-piece straddles a partition point is not a refinement; such
  sums enter only the limit claim.

The order laws are parameters (`OSum`), nothing borrowed — as in `ZLP`, and for the same reason: `Int`/`Rat` laws
from core carry `propext`. They are stated as inequalities only (an equation is `≤` both ways), so the same theorem
holds where equality is a setoid: `ZIntegralR` instantiates it on VR's pre-rationals and discharges the leaves for
the grammar `+ − × / exp ln` with `ZSlopeDiv`'s proved readings. The leaf is asked at the TAGS only
(`enclosure_sound`); a leaf on the whole piece gives it (`enclosure_sound_leaf`).
-/

namespace ZIntegral

variable {α : Type}

/-- The laws a tagged sum's bounds need, as inequalities (an equation is `≤` both ways): order, sums keep it,
non-negative factors keep it, products commute, distribute, vanish at zero, respect `≤`-both-ways. -/
structure OSum (α : Type) where
  zero : α
  add  : α → α → α
  neg  : α → α
  mul  : α → α → α
  le   : α → α → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  add_le_add : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d)
  mul_le_mul_nonneg : ∀ {c a b}, le zero c → le a b → le (mul c a) (mul c b)
  mul_comm_le : ∀ a b, le (mul a b) (mul b a)
  mul_add_le  : ∀ a b c, le (mul a (add b c)) (add (mul a b) (mul a c))
  mul_add_ge  : ∀ a b c, le (add (mul a b) (mul a c)) (mul a (add b c))
  mul_zero_le : ∀ a, le (mul a zero) zero
  mul_zero_ge : ∀ a, le zero (mul a zero)
  mul_congr   : ∀ {a b} (c : α), le a b → le b a → le (mul c a) (mul c b)

/-- The tagged sum `Σ w · f(t)` over (weight, tag) pairs. -/
def rsum (R : OSum α) (f : α → α) : List (α × α) → α
  | [] => R.zero
  | (w, t) :: rest => R.add (R.mul w (f t)) (rsum R f rest)

/-- The total weight `Σ w`. -/
def wtotal (R : OSum α) : List (α × α) → α
  | [] => R.zero
  | (w, _) :: rest => R.add w (wtotal R rest)

/-- ONE PIECE, FROM BELOW: non-negative weights, `lo ≤ f` at every tag — then `lo · Σ w ≤ Σ w · f(t)`. -/
theorem piece_lower (R : OSum α) (f : α → α) (lo : α) :
    ∀ l : List (α × α), (∀ wt, List.Mem wt l → R.le R.zero wt.1 ∧ R.le lo (f wt.2)) →
      R.le (R.mul lo (wtotal R l)) (rsum R f l) := by
  intro l
  induction l with
  | nil => intro _; exact R.mul_zero_le lo
  | cons wt rest ih =>
      intro h
      obtain ⟨w, t⟩ := wt
      have h0 := h (w, t) (List.Mem.head rest)
      have hw : R.le (R.mul lo w) (R.mul w (f t)) :=
        R.le_trans (R.mul_comm_le lo w) (R.mul_le_mul_nonneg h0.1 h0.2)
      have hr := ih (fun z hz => h z (List.Mem.tail _ hz))
      exact R.le_trans (R.mul_add_le lo w (wtotal R rest)) (R.add_le_add hw hr)

/-- ONE PIECE, FROM ABOVE: `f ≤ hi` at every tag — then `Σ w · f(t) ≤ hi · Σ w`. -/
theorem piece_upper (R : OSum α) (f : α → α) (hi : α) :
    ∀ l : List (α × α), (∀ wt, List.Mem wt l → R.le R.zero wt.1 ∧ R.le (f wt.2) hi) →
      R.le (rsum R f l) (R.mul hi (wtotal R l)) := by
  intro l
  induction l with
  | nil => intro _; exact R.mul_zero_ge hi
  | cons wt rest ih =>
      intro h
      obtain ⟨w, t⟩ := wt
      have h0 := h (w, t) (List.Mem.head rest)
      have hw : R.le (R.mul w (f t)) (R.mul hi w) :=
        R.le_trans (R.mul_le_mul_nonneg h0.1 h0.2) (R.mul_comm_le w hi)
      have hr := ih (fun z hz => h z (List.Mem.tail _ hz))
      exact R.le_trans (R.add_le_add hw hr) (R.mul_add_ge hi w (wtotal R rest))

/-- A piece `[a, b]` of the certificate: the leaf's bounds `lo`, `hi`, and a refinement of it. -/
structure Piece (α : Type) where
  a : α
  b : α
  lo : α
  hi : α
  fine : List (α × α)

/-- The refinement's weights are non-negative and add up to `b − a`. -/
def WeightsOK (R : OSum α) (p : Piece α) : Prop :=
  (∀ wt, List.Mem wt p.fine → R.le R.zero wt.1)
  ∧ R.le (wtotal R p.fine) (R.add p.b (R.neg p.a)) ∧ R.le (R.add p.b (R.neg p.a)) (wtotal R p.fine)

/-- What one piece must satisfy at its TAGS: the weights, and `lo ≤ f(t) ≤ hi` at every tag. -/
def TagsOK (R : OSum α) (f : α → α) (p : Piece α) : Prop :=
  WeightsOK R p ∧ (∀ wt, List.Mem wt p.fine → R.le p.lo (f wt.2) ∧ R.le (f wt.2) p.hi)

/-- The kernel's lower end `L = Σ lo_k · (b_k − a_k)`. -/
def lower (R : OSum α) : List (Piece α) → α
  | [] => R.zero
  | p :: ps => R.add (R.mul p.lo (R.add p.b (R.neg p.a))) (lower R ps)

/-- The kernel's upper end `U = Σ hi_k · (b_k − a_k)`. -/
def upper (R : OSum α) : List (Piece α) → α
  | [] => R.zero
  | p :: ps => R.add (R.mul p.hi (R.add p.b (R.neg p.a))) (upper R ps)

/-- The tagged sum over the whole refinement. -/
def total (R : OSum α) (f : α → α) : List (Piece α) → α
  | [] => R.zero
  | p :: ps => R.add (rsum R f p.fine) (total R f ps)

/-- THE ENCLOSURE IS SOUND: every tagged sum over a refinement of the certificate's partition, with the leaf's
bounds holding at its tags, lies in `[L, U]`. -/
theorem enclosure_sound (R : OSum α) (f : α → α) :
    ∀ ps : List (Piece α), (∀ p, List.Mem p ps → TagsOK R f p) →
      R.le (lower R ps) (total R f ps) ∧ R.le (total R f ps) (upper R ps) := by
  intro ps
  induction ps with
  | nil => intro _; exact ⟨R.le_refl _, R.le_refl _⟩
  | cons p rest ih =>
      intro h
      have ⟨⟨hw0, hwle, hwge⟩, htag⟩ := h p (List.Mem.head rest)
      have hr := ih (fun z hz => h z (List.Mem.tail _ hz))
      have hlo : R.le (R.mul p.lo (R.add p.b (R.neg p.a))) (rsum R f p.fine) :=
        R.le_trans (R.mul_congr p.lo hwge hwle)
          (piece_lower R f p.lo p.fine (fun wt hm => ⟨hw0 wt hm, (htag wt hm).1⟩))
      have hhi : R.le (rsum R f p.fine) (R.mul p.hi (R.add p.b (R.neg p.a))) :=
        R.le_trans (piece_upper R f p.hi p.fine (fun wt hm => ⟨hw0 wt hm, (htag wt hm).2⟩))
          (R.mul_congr p.hi hwle hwge)
      exact ⟨R.add_le_add hlo hr.1, R.add_le_add hhi hr.2⟩

/-- What one piece must satisfy with the leaf on the whole piece: the leaf holds on `[a, b]`, the weights, and the
tags lie in `[a, b]`. -/
def PieceOK (R : OSum α) (f : α → α) (p : Piece α) : Prop :=
  (∀ t, R.le p.a t → R.le t p.b → R.le p.lo (f t) ∧ R.le (f t) p.hi)
  ∧ WeightsOK R p ∧ (∀ wt, List.Mem wt p.fine → R.le p.a wt.2 ∧ R.le wt.2 p.b)

theorem tags_of_piece (R : OSum α) (f : α → α) (p : Piece α) (h : PieceOK R f p) : TagsOK R f p :=
  ⟨h.2.1, fun wt hm => h.1 wt.2 (h.2.2 wt hm).1 (h.2.2 wt hm).2⟩

/-- The same, the leaf read on the whole piece. -/
theorem enclosure_sound_leaf (R : OSum α) (f : α → α) (ps : List (Piece α))
    (h : ∀ p, List.Mem p ps → PieceOK R f p) :
    R.le (lower R ps) (total R f ps) ∧ R.le (total R f ps) (upper R ps) :=
  enclosure_sound R f ps (fun p hp => tags_of_piece R f p (h p hp))

/-- A MONOTONE LEAF IS AN INTERVAL LEAF: `f` non-decreasing on `[a, b]`, `lo ≤ f(a)`, `f(b) ≤ hi` — then
`lo ≤ f(t) ≤ hi` on the whole piece. (On VR's numbers, from a derivative sign: `ZIntegralR`.) -/
theorem monotone_leaf (R : OSum α) (f : α → α) {a b lo hi : α}
    (mono : ∀ s t, R.le a s → R.le s t → R.le t b → R.le (f s) (f t))
    (hlo : R.le lo (f a)) (hhi : R.le (f b) hi) :
    ∀ t, R.le a t → R.le t b → R.le lo (f t) ∧ R.le (f t) hi :=
  fun t hat htb =>
    ⟨R.le_trans hlo (mono a t (R.le_refl a) hat htb), R.le_trans (mono t b hat htb (R.le_refl b)) hhi⟩

/-- The non-increasing leaf: the ends trade places, `lo ≤ f(b)`, `f(a) ≤ hi`. -/
theorem antitone_leaf (R : OSum α) (f : α → α) {a b lo hi : α}
    (anti : ∀ s t, R.le a s → R.le s t → R.le t b → R.le (f t) (f s))
    (hlo : R.le lo (f b)) (hhi : R.le (f a) hi) :
    ∀ t, R.le a t → R.le t b → R.le lo (f t) ∧ R.le (f t) hi :=
  fun t hat htb =>
    ⟨R.le_trans hlo (anti t b hat htb (R.le_refl b)), R.le_trans (anti a t (R.le_refl a) hat htb) hhi⟩

/-- On ℤ (the laws from core; the example is not on the axiom list). -/
def intOSum : OSum Int where
  zero := 0
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  le := (· ≤ ·)
  le_refl := Int.le_refl
  le_trans := Int.le_trans
  add_le_add := Int.add_le_add
  mul_le_mul_nonneg := fun hc h => Int.mul_le_mul_of_nonneg_left h hc
  mul_comm_le := fun a b => Int.le_of_eq (Int.mul_comm a b)
  mul_add_le := fun a b c => Int.le_of_eq (Int.mul_add a b c)
  mul_add_ge := fun a b c => Int.le_of_eq (Int.mul_add a b c).symm
  mul_zero_le := fun a => Int.le_of_eq (Int.mul_zero a)
  mul_zero_ge := fun a => Int.le_of_eq (Int.mul_zero a).symm
  mul_congr := fun c h1 h2 => Int.le_of_eq (congrArg (c * ·) (Int.le_antisymm h1 h2))

/-- `decide` through `intOSum.le`: state the goal as an `Int` order first. -/
local macro "idec" : tactic => `(tactic| (show (_ : Int) ≤ _; decide))

/-- At work: `f(t) = t²` on `[0, 4]`, certificate pieces `[0, 2]` and `[2, 4]` with monotone leaves
(`L = 0·2 + 4·2 = 8`, `U = 4·2 + 16·2 = 40`), a refinement with unit weights and tags 0, 2, 3, 4: the sum
`0 + 4 + 9 + 16 = 29` lies in `[8, 40]`. -/
example : intOSum.le 8 29 ∧ intOSum.le 29 40 := by
  have := enclosure_sound_leaf intOSum (fun t => t * t)
    [⟨0, 2, 0, 4, [(1, 0), (1, 2)]⟩, ⟨2, 4, 4, 16, [(1, 3), (1, 4)]⟩] (by
      intro p hp
      cases hp with
      | head =>
          refine ⟨monotone_leaf intOSum (fun t => t * t) (a := 0) (b := 2) ?_ (by idec) (by idec),
            ⟨?_, by idec, by idec⟩, ?_⟩
          · intro s t h0 hst _
            exact Int.mul_le_mul hst hst h0 (Int.le_trans h0 hst)
          · intro wt hm
            cases hm with
            | head => idec
            | tail _ hm => cases hm with
              | head => idec
              | tail _ hm => cases hm
          · intro wt hm
            cases hm with
            | head => exact ⟨by idec, by idec⟩
            | tail _ hm => cases hm with
              | head => exact ⟨by idec, by idec⟩
              | tail _ hm => cases hm
      | tail _ hp => cases hp with
        | head =>
            refine ⟨monotone_leaf intOSum (fun t => t * t) (a := 2) (b := 4) ?_ (by idec) (by idec),
              ⟨?_, by idec, by idec⟩, ?_⟩
            · intro s t h2 hst _
              have h0 : (0 : Int) ≤ s := Int.le_trans (by decide) h2
              exact Int.mul_le_mul hst hst h0 (Int.le_trans h0 hst)
            · intro wt hm
              cases hm with
              | head => idec
              | tail _ hm => cases hm with
                | head => idec
                | tail _ hm => cases hm
            · intro wt hm
              cases hm with
              | head => exact ⟨by idec, by idec⟩
              | tail _ hm => cases hm with
                | head => exact ⟨by idec, by idec⟩
                | tail _ hm => cases hm
        | tail _ hp => cases hp)
  exact this

end ZIntegral

#print axioms ZIntegral.piece_lower
#print axioms ZIntegral.piece_upper
#print axioms ZIntegral.enclosure_sound
#print axioms ZIntegral.tags_of_piece
#print axioms ZIntegral.enclosure_sound_leaf
#print axioms ZIntegral.monotone_leaf
#print axioms ZIntegral.antitone_leaf
