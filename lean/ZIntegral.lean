import ZLP

/-!
# ZIntegral — the rule `zintegral.py` encloses a definite integral by. Zero axioms.

`zintegral.py` (2026-10-16) checks a certificate: a partition `a = x_0 < … < x_n = b` and a leaf per piece. For an
INTERVAL leaf the kernel reads `f` over the piece, `lo ≤ f(t) ≤ hi`; for a MONOTONE leaf it reads the sign of
`f'` there and the values at the two ends. It then adds `L = Σ lo_k · (x_{k+1} − x_k)` and
`U = Σ hi_k · (x_{k+1} − x_k)`. This module proves what that sum means, with no limit taken:

    every tagged sum over a refinement of the partition lies in [L, U]        (`enclosure_sound`)

A refinement splits each piece `[a, b]` into sub-pieces with weights `w_j ≥ 0` adding up to `b − a` and tags
`t_j ∈ [a, b]`; the sum is `Σ w_j · f(t_j)`. The proof is local: on one piece `Σ w_j f(t_j) ≥ Σ w_j lo =
lo · (b − a)` (`piece_lower`, distributivity), then the pieces add (`ZLP.add_le_add`). A monotone leaf is an
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

The order laws are parameters (`ZLP.OMul` plus distributivity), nothing borrowed — as in `ZLP`, and for the
same reason: `Int`/`Rat` laws from core carry `propext`.
-/

namespace ZIntegral

open ZLP

variable {α : Type}

/-- An ordered commutative ring with the distributive law (the one law weights need: lengths add). -/
structure ODist (α : Type) extends OMul α where
  mul_add  : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_zero : ∀ a, mul a zero = zero

/-- The tagged sum `Σ w · f(t)` over (weight, tag) pairs. -/
def rsum (R : ODist α) (f : α → α) : List (α × α) → α
  | [] => R.zero
  | (w, t) :: rest => R.add (R.mul w (f t)) (rsum R f rest)

/-- The total weight `Σ w`. -/
def wtotal (R : ODist α) : List (α × α) → α
  | [] => R.zero
  | (w, _) :: rest => R.add w (wtotal R rest)

/-- ONE PIECE, FROM BELOW: non-negative weights, `lo ≤ f` at every tag — then `lo · Σ w ≤ Σ w · f(t)`. -/
theorem piece_lower (R : ODist α) (f : α → α) (lo : α) :
    ∀ l : List (α × α), (∀ wt, List.Mem wt l → R.le R.zero wt.1 ∧ R.le lo (f wt.2)) →
      R.le (R.mul lo (wtotal R l)) (rsum R f l) := by
  intro l
  induction l with
  | nil =>
      intro _
      show R.le (R.mul lo R.zero) R.zero
      rw [R.mul_zero]
      exact R.le_refl _
  | cons wt rest ih =>
      intro h
      obtain ⟨w, t⟩ := wt
      have h0 := h (w, t) (List.Mem.head rest)
      have hw : R.le (R.mul lo w) (R.mul w (f t)) := by
        rw [R.mul_comm lo w]
        exact R.mul_le_mul_nonneg h0.1 h0.2
      have hr := ih (fun z hz => h z (List.Mem.tail _ hz))
      show R.le (R.mul lo (R.add w (wtotal R rest))) (R.add (R.mul w (f t)) (rsum R f rest))
      rw [R.mul_add]
      exact add_le_add R.toOMul hw hr

/-- ONE PIECE, FROM ABOVE: `f ≤ hi` at every tag — then `Σ w · f(t) ≤ hi · Σ w`. -/
theorem piece_upper (R : ODist α) (f : α → α) (hi : α) :
    ∀ l : List (α × α), (∀ wt, List.Mem wt l → R.le R.zero wt.1 ∧ R.le (f wt.2) hi) →
      R.le (rsum R f l) (R.mul hi (wtotal R l)) := by
  intro l
  induction l with
  | nil =>
      intro _
      show R.le R.zero (R.mul hi R.zero)
      rw [R.mul_zero]
      exact R.le_refl _
  | cons wt rest ih =>
      intro h
      obtain ⟨w, t⟩ := wt
      have h0 := h (w, t) (List.Mem.head rest)
      have hw : R.le (R.mul w (f t)) (R.mul hi w) := by
        rw [R.mul_comm hi w]
        exact R.mul_le_mul_nonneg h0.1 h0.2
      have hr := ih (fun z hz => h z (List.Mem.tail _ hz))
      show R.le (R.add (R.mul w (f t)) (rsum R f rest)) (R.mul hi (R.add w (wtotal R rest)))
      rw [R.mul_add]
      exact add_le_add R.toOMul hw hr

/-- A piece `[a, b]` of the certificate: the leaf's bounds `lo`, `hi`, and a refinement of it. -/
structure Piece (α : Type) where
  a : α
  b : α
  lo : α
  hi : α
  fine : List (α × α)

/-- What one piece must satisfy: the leaf holds on `[a, b]`, the refinement's weights are non-negative, add up
to `b − a`, and its tags lie in `[a, b]`. -/
def PieceOK (R : ODist α) (f : α → α) (p : Piece α) : Prop :=
  (∀ t, R.le p.a t → R.le t p.b → R.le p.lo (f t) ∧ R.le (f t) p.hi)
  ∧ (∀ wt, List.Mem wt p.fine → R.le R.zero wt.1 ∧ R.le p.a wt.2 ∧ R.le wt.2 p.b)
  ∧ wtotal R p.fine = R.add p.b (R.neg p.a)

/-- The kernel's lower end `L = Σ lo_k · (b_k − a_k)`. -/
def lower (R : ODist α) : List (Piece α) → α
  | [] => R.zero
  | p :: ps => R.add (R.mul p.lo (R.add p.b (R.neg p.a))) (lower R ps)

/-- The kernel's upper end `U = Σ hi_k · (b_k − a_k)`. -/
def upper (R : ODist α) : List (Piece α) → α
  | [] => R.zero
  | p :: ps => R.add (R.mul p.hi (R.add p.b (R.neg p.a))) (upper R ps)

/-- The tagged sum over the whole refinement. -/
def total (R : ODist α) (f : α → α) : List (Piece α) → α
  | [] => R.zero
  | p :: ps => R.add (rsum R f p.fine) (total R f ps)

/-- THE ENCLOSURE IS SOUND: every tagged sum over a refinement of the certificate's partition lies in `[L, U]`. -/
theorem enclosure_sound (R : ODist α) (f : α → α) :
    ∀ ps : List (Piece α), (∀ p, List.Mem p ps → PieceOK R f p) →
      R.le (lower R ps) (total R f ps) ∧ R.le (total R f ps) (upper R ps) := by
  intro ps
  induction ps with
  | nil => intro _; exact ⟨R.le_refl _, R.le_refl _⟩
  | cons p rest ih =>
      intro h
      have ⟨hleaf, htags, hw⟩ := h p (List.Mem.head rest)
      have hr := ih (fun z hz => h z (List.Mem.tail _ hz))
      have hlo : R.le (R.mul p.lo (R.add p.b (R.neg p.a))) (rsum R f p.fine) := by
        rw [← hw]
        exact piece_lower R f p.lo p.fine (fun wt hm =>
          ⟨(htags wt hm).1, (hleaf wt.2 (htags wt hm).2.1 (htags wt hm).2.2).1⟩)
      have hhi : R.le (rsum R f p.fine) (R.mul p.hi (R.add p.b (R.neg p.a))) := by
        rw [← hw]
        exact piece_upper R f p.hi p.fine (fun wt hm =>
          ⟨(htags wt hm).1, (hleaf wt.2 (htags wt hm).2.1 (htags wt hm).2.2).2⟩)
      exact ⟨add_le_add R.toOMul hlo hr.1, add_le_add R.toOMul hhi hr.2⟩

/-- A MONOTONE LEAF IS AN INTERVAL LEAF: `f` non-decreasing on `[a, b]`, `lo ≤ f(a)`, `f(b) ≤ hi` — then
`lo ≤ f(t) ≤ hi` on the whole piece. (The sign of `f'` making `f` monotone is `ZSlope.mono_up`.) -/
theorem monotone_leaf (R : ODist α) (f : α → α) {a b lo hi : α}
    (mono : ∀ s t, R.le a s → R.le s t → R.le t b → R.le (f s) (f t))
    (hlo : R.le lo (f a)) (hhi : R.le (f b) hi) :
    ∀ t, R.le a t → R.le t b → R.le lo (f t) ∧ R.le (f t) hi :=
  fun t hat htb =>
    ⟨R.le_trans hlo (mono a t (R.le_refl a) hat htb), R.le_trans (mono t b hat htb (R.le_refl b)) hhi⟩

/-- The non-increasing leaf: the ends trade places, `lo ≤ f(b)`, `f(a) ≤ hi`. -/
theorem antitone_leaf (R : ODist α) (f : α → α) {a b lo hi : α}
    (anti : ∀ s t, R.le a s → R.le s t → R.le t b → R.le (f t) (f s))
    (hlo : R.le lo (f b)) (hhi : R.le (f a) hi) :
    ∀ t, R.le a t → R.le t b → R.le lo (f t) ∧ R.le (f t) hi :=
  fun t hat htb =>
    ⟨R.le_trans hlo (anti t b hat htb (R.le_refl b)), R.le_trans (anti a t (R.le_refl a) hat htb) hhi⟩

/-- On ℤ (the laws from core; the example is not on the axiom list). -/
def intODist : ODist Int :=
  { intOMul with mul_add := Int.mul_add, mul_zero := Int.mul_zero }

/-- `decide` through `intODist.le`: state the goal as an `Int` order first. -/
local macro "idec" : tactic => `(tactic| (show (_ : Int) ≤ _; decide))

/-- At work: `f(t) = t²` on `[0, 4]`, certificate pieces `[0, 2]` and `[2, 4]` with monotone leaves
(`L = 0·2 + 4·2 = 8`, `U = 4·2 + 16·2 = 40`), a refinement with unit weights and tags 0, 2, 3, 4: the sum
`0 + 4 + 9 + 16 = 29` lies in `[8, 40]`. -/
example : intODist.le 8 29 ∧ intODist.le 29 40 := by
  have := enclosure_sound intODist (fun t => t * t)
    [⟨0, 2, 0, 4, [(1, 0), (1, 2)]⟩, ⟨2, 4, 4, 16, [(1, 3), (1, 4)]⟩] (by
      intro p hp
      cases hp with
      | head =>
          refine ⟨monotone_leaf intODist (fun t => t * t) (a := 0) (b := 2) ?_ (by idec) (by idec), ?_, by decide⟩
          · intro s t h0 hst _
            exact Int.mul_le_mul hst hst h0 (Int.le_trans h0 hst)
          · intro wt hm
            cases hm with
            | head => exact ⟨by idec, by idec, by idec⟩
            | tail _ hm => cases hm with
              | head => exact ⟨by idec, by idec, by idec⟩
              | tail _ hm => cases hm
      | tail _ hp => cases hp with
        | head =>
            refine ⟨monotone_leaf intODist (fun t => t * t) (a := 2) (b := 4) ?_ (by idec) (by idec), ?_, by decide⟩
            · intro s t h2 hst _
              have h0 : (0 : Int) ≤ s := Int.le_trans (by idec) h2
              exact Int.mul_le_mul hst hst h0 (Int.le_trans h0 hst)
            · intro wt hm
              cases hm with
              | head => exact ⟨by idec, by idec, by idec⟩
              | tail _ hm => cases hm with
                | head => exact ⟨by idec, by idec, by idec⟩
                | tail _ hm => cases hm
        | tail _ hp => cases hp)
  exact this

end ZIntegral

#print axioms ZIntegral.piece_lower
#print axioms ZIntegral.piece_upper
#print axioms ZIntegral.enclosure_sound
#print axioms ZIntegral.monotone_leaf
#print axioms ZIntegral.antitone_leaf
