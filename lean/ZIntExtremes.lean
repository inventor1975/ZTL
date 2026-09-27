import ZParabola

/-!
# Where an integer quadratic takes its extremes on a box. Zero axioms. (2026-09-27)

The numeric judge decides a claim over INTEGER quantities without listing the box
(`znum._int_refine`, 2026-09-25, ZTL c730fb2 / 4cc5504): for f = a·m² + b·m + c on the
integers of [lo, hi] it reads the maximum and the minimum from the two ends and the two
integers next to the vertex, and for two names it reads a maximum on the edges of the box
where f is convex in the other name. This module is why those few points suffice.

Index the box from its left end, m = lo + k, k = 0 … n. What is kernel-checked here:

    Convex f          :  f(k+1) + f(k+1) ≤ f k + f(k+2)          (midpoint, no subtraction)
    max_at_ends       :  Convex f → k ≤ n → f k ≤ f 0 ∨ f k ≤ f n
    min_at_turn       :  Convex f → f t ≤ f (t+1) → (∀ s, s+1 = t → f t ≤ f s) → f t ≤ f k
    convex_of_linear_shift : a linear shift (M k + M (k+2) = 2·M (k+1)) keeps convexity
    quad_mid          :  P k + P (k+2) = P (k+1) + P (k+1) + 2a   for P = a·k² + b·k + c
    quad_convex       :  P is Convex
    sum_multiple      :  a sum of multiples of s is a multiple of s

`max_at_ends` is the edge rule and the maximum of a convex parabola: the ends suffice.
`min_at_turn` is the minimum: once f stops falling it never falls again (`rise_le`), and
before the turn it only fell (`fall_le`), so the turn is the minimum over the whole range.
`sum_multiple` is the only direction a lattice may be inherited by a sum; the red team's
LIE-1 (2026-09-26) was the other, a sum given the lattice of its LAST stepped term.

SIGNED VALUES WITHOUT `Int`. The core's `Int` order and ring laws carry `propext` in this
toolchain (MEASURED 2026-09-27: `Int.le_trans`, `Int.le_refl`, `Int.add_le_add`,
`Int.add_comm`, `Int.add_mul`, `Int.sub_add_cancel` among them; `Nat.le_of_add_le_add_left`
too, hence `cancel_left`). So a signed value is what `Int` is by definition, a difference of
two naturals, f k = P k − N k, and f i ≤ f j is written `P i + N j ≤ P j + N i` (`PLe`).
Every signed statement below is proved on `Nat` alone:

    pquad_convex        (aP − aN)·k² + (bP − bN)·k + (cP − cN) with aN ≤ aP is convex
    pmax_at_ends        its maximum on 0 … n is at an end
    pmin_at_ends_concave  the mirror: a concave f has its minimum at an end
    pmin_at_turn        a convex f is least where it stops falling
    pmin_at_vertex      if 2a·t + b ≤ 0 ≤ 2a·(t+1) + b (t = ⌊−b/2a⌋), the minimum is at t or t+1

Indexing from the box's left end (m = lo + k) keeps the leading coefficient and changes only
b and c, which are arbitrary here. What is NOT kernel-checked is only notation: that an
integer is a difference of two naturals (the definition of `Int`), and that Python's `//`
is the floor (`pmin_at_vertex` takes the floor's defining inequalities as hypotheses).
-/

namespace ZIntExtremes

/-- `Nat.le_of_add_le_add_left`, by induction: core's carries `propext` here (measured). -/
theorem cancel_left : ∀ (a b c : Nat), a + b ≤ a + c → b ≤ c
  | 0, b, c, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | a + 1, b, c, h => by
      rw [Nat.succ_add, Nat.succ_add] at h
      exact cancel_left a b c (Nat.le_of_succ_le_succ h)

/-- Midpoint convexity on the integer points, in additive form. -/
def Convex (f : Nat → Nat) : Prop := ∀ k, f (k + 1) + f (k + 1) ≤ f k + f (k + 2)

/-- Once f stops falling, the next step does not fall either. -/
theorem step_up {f : Nat → Nat} (hc : Convex f) (k : Nat) (h : f k ≤ f (k + 1)) :
    f (k + 1) ≤ f (k + 2) :=
  cancel_left _ _ _ (Nat.le_trans (hc k) (Nat.add_le_add_right h _))

/-- If f does not rise into k+2, it did not rise into k+1 either. -/
theorem step_down {f : Nat → Nat} (hc : Convex f) (k : Nat) (h : f (k + 2) ≤ f (k + 1)) :
    f (k + 1) ≤ f k := by
  have h1 : f (k + 1) + f (k + 1) ≤ f (k + 1) + f k := by
    rw [Nat.add_comm (f (k + 1)) (f k)]
    exact Nat.le_trans (hc k) (Nat.add_le_add_left h _)
  exact cancel_left _ _ _ h1

theorem rising {f : Nat → Nat} (hc : Convex f) {k : Nat} (h : f k ≤ f (k + 1)) :
    ∀ j, f (k + j) ≤ f (k + j + 1)
  | 0 => h
  | j + 1 => step_up hc (k + j) (rising hc h j)

/-- After the turn, f only rises: f k ≤ f (k + j). -/
theorem rise_le {f : Nat → Nat} (hc : Convex f) {k : Nat} (h : f k ≤ f (k + 1)) :
    ∀ j, f k ≤ f (k + j)
  | 0 => Nat.le_refl _
  | j + 1 => Nat.le_trans (rise_le hc h j) (rising hc h j)

/-- Before a fall, f only fell: if f (k+1) ≤ f k then f k ≤ f i for every i ≤ k. -/
theorem fall_le {f : Nat → Nat} (hc : Convex f) :
    ∀ k, f (k + 1) ≤ f k → ∀ i, i ≤ k → f k ≤ f i
  | 0, _, i, hi => by
      cases Nat.eq_or_lt_of_le hi with
      | inl e => rw [e]; exact Nat.le_refl _
      | inr l => exact absurd l (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
      have hk : f (k + 1) ≤ f k := step_down hc k h
      cases Nat.eq_or_lt_of_le hi with
      | inl e => rw [e]; exact Nat.le_refl _
      | inr l => exact Nat.le_trans hk (fall_le hc k hk i (Nat.le_of_lt_succ l))

/-- THE MAXIMUM LIES AT AN END: on 0 … n a convex f never exceeds both f 0 and f n. -/
theorem max_at_ends {f : Nat → Nat} (hc : Convex f) {k n : Nat} (hk : k ≤ n) :
    f k ≤ f 0 ∨ f k ≤ f n := by
  cases Nat.le_total (f k) (f (k + 1)) with
  | inl up =>
      match Nat.le.dest hk with
      | ⟨j, hj⟩ => exact Or.inr (hj ▸ rise_le hc up j)
  | inr down => exact Or.inl (fall_le hc k down 0 (Nat.zero_le k))

/-- THE MINIMUM IS THE TURN: where f stops falling, it is least over the whole range. -/
theorem min_at_turn {f : Nat → Nat} (hc : Convex f) {t : Nat}
    (hup : f t ≤ f (t + 1)) (hin : ∀ s, s + 1 = t → f t ≤ f s) (k : Nat) : f t ≤ f k := by
  cases Nat.le_total t k with
  | inl h =>
      match Nat.le.dest h with
      | ⟨j, hj⟩ => exact hj ▸ rise_le hc hup j
  | inr h =>
      cases t with
      | zero =>
          cases Nat.eq_or_lt_of_le h with
          | inl e => rw [e]; exact Nat.le_refl _
          | inr l => exact absurd l (Nat.not_lt_zero k)
      | succ s =>
          have hs : f (s + 1) ≤ f s := hin s rfl
          cases Nat.eq_or_lt_of_le h with
          | inl e => rw [e]; exact Nat.le_refl _
          | inr l => exact Nat.le_trans hs (fall_le hc s hs k (Nat.le_of_lt_succ l))

/-- A linear shift keeps convexity: if g k + M k = P k with P convex and M linear, g is convex. -/
theorem convex_of_linear_shift {g M P : Nat → Nat} (hP : Convex P)
    (hM : ∀ k, M k + M (k + 2) = M (k + 1) + M (k + 1)) (hg : ∀ k, g k + M k = P k) :
    Convex g := by
  intro k
  have h := hP k
  rw [← hg (k + 1), ← hg k, ← hg (k + 2)] at h
  -- (g1 + M1) + (g1 + M1) ≤ (g0 + M0) + (g2 + M2), and M0 + M2 = M1 + M1
  have e1 : g (k + 1) + M (k + 1) + (g (k + 1) + M (k + 1))
      = (M (k + 1) + M (k + 1)) + (g (k + 1) + g (k + 1)) := by
    rw [Nat.add_assoc, Nat.add_left_comm (M (k + 1)) (g (k + 1)) (M (k + 1)),
        ← Nat.add_assoc, Nat.add_comm (g (k + 1) + g (k + 1))]
  have e2 : g k + M k + (g (k + 2) + M (k + 2)) = (M k + M (k + 2)) + (g k + g (k + 2)) := by
    rw [Nat.add_assoc, Nat.add_left_comm (M k) (g (k + 2)) (M (k + 2)),
        ← Nat.add_assoc, Nat.add_comm (g k + g (k + 2))]
  rw [e1, e2, hM k] at h
  exact cancel_left _ _ _ h

/-- Additive rearrangements the steps below need; `simp`/`ac_rfl` would bring `propext`. -/
theorem lin4 (X Y B b c : Nat) : X + Y + (B + b) + c = X + B + c + (Y + b) := by
  rw [Nat.add_assoc X Y (B + b), Nat.add_assoc X B c, Nat.add_assoc X (B + c) (Y + b),
      Nat.add_assoc X (Y + (B + b)) c]
  congr 1
  rw [Nat.add_comm B b, ← Nat.add_assoc Y b B, Nat.add_assoc (Y + b) B c, Nat.add_comm (Y + b) (B + c)]

theorem odd_step (k : Nat) : k + 1 + (k + 1) + 1 = k + k + 1 + (1 + 1) := by
  show k + 1 + k + 1 + 1 = k + k + 1 + 1 + 1
  rw [Nat.add_right_comm k 1 k]

theorem mid_lin (p d a : Nat) : p + (p + d + (d + (a + a))) = p + d + (p + d) + (a + a) := by
  rw [← Nat.add_assoc (p + d) d (a + a), ← Nat.add_assoc p (p + d + d) (a + a)]
  congr 1
  rw [Nat.add_assoc p d d, ← Nat.add_assoc p p (d + d), Nat.add_assoc p d (p + d),
      Nat.add_left_comm d p d, ← Nat.add_assoc p p (d + d)]

/-- The quadratic, indexed from the box's left end. -/
def quad (a b c k : Nat) : Nat := a * (k * k) + b * k + c

/-- Its step: P (k+1) = P k + (a·(k+k+1) + b). -/
theorem quad_step (a b c k : Nat) : quad a b c (k + 1) = quad a b c k + (a * (k + k + 1) + b) := by
  unfold quad
  have sq : (k + 1) * (k + 1) = k * k + (k + k + 1) := by
    rw [Nat.mul_succ, Nat.succ_mul, Nat.add_assoc (k * k) k (k + 1), ← Nat.add_assoc k k 1]
  rw [sq, Nat.mul_add, Nat.mul_succ b k]
  exact lin4 _ _ _ _ _

/-- The step grows by 2a: a·((k+1)+(k+1)+1) + b = (a·(k+k+1) + b) + 2a. -/
theorem quad_step_grows (a b k : Nat) :
    a * ((k + 1) + (k + 1) + 1) + b = (a * (k + k + 1) + b) + (a + a) := by
  have e : (k + 1) + (k + 1) + 1 = (k + k + 1) + (1 + 1) := odd_step k
  rw [e, Nat.mul_add a (k + k + 1) (1 + 1), Nat.mul_add a 1 1, Nat.mul_one,
      Nat.add_right_comm (a * (k + k + 1)) (a + a) b]

/-- P k + P (k+2) = P (k+1) + P (k+1) + 2a. -/
theorem quad_mid (a b c k : Nat) :
    quad a b c k + quad a b c (k + 2)
      = quad a b c (k + 1) + quad a b c (k + 1) + (a + a) := by
  have s1 := quad_step a b c k
  have s2 := quad_step a b c (k + 1)
  rw [quad_step_grows] at s2
  show quad a b c k + quad a b c (k + 1 + 1) = _
  rw [s2, s1]
  generalize quad a b c k = p
  generalize a * (k + k + 1) + b = d
  exact mid_lin p d a

/-- A quadratic with a ≥ 0 (all coefficients `Nat`) is convex on the integer points. -/
theorem quad_convex (a b c : Nat) : Convex (quad a b c) := by
  intro k
  rw [quad_mid]
  exact Nat.le_add_right _ _

/-- The only way a lattice passes to a sum: every term on it. -/
theorem sum_multiple (s : Nat) : ∀ (xs : List Nat), (∀ x, x ∈ xs → ∃ q, x = s * q) →
    ∃ q, xs.foldr (· + ·) 0 = s * q
  | [], _ => ⟨0, (Nat.mul_zero s).symm⟩
  | x :: xs, h => by
      match h x (List.Mem.head xs), sum_multiple s xs (fun y hy => h y (List.Mem.tail x hy)) with
      | ⟨q1, e1⟩, ⟨q2, e2⟩ =>
          exact ⟨q1 + q2, by show x + xs.foldr (· + ·) 0 = _; rw [e1, e2, Nat.mul_add]⟩


/-- (a+b)+(c+d) = (c+b)+(a+d) -/
theorem sw1 (a b c d : Nat) : a + b + (c + d) = c + b + (a + d) := by
  rw [Nat.add_assoc, Nat.add_left_comm b c d, ← Nat.add_assoc a c (b + d), Nat.add_comm a c,
      Nat.add_assoc c a (b + d), Nat.add_left_comm a b d, ← Nat.add_assoc c b (a + d)]

/-- (a+b)+(c+d) = (a+d)+(c+b) -/
theorem sw2 (a b c d : Nat) : a + b + (c + d) = a + d + (c + b) := by
  rw [Nat.add_assoc, Nat.add_left_comm b c d, Nat.add_comm b d, Nat.add_left_comm c d b,
      ← Nat.add_assoc a d (c + b)]

/-- a+a'+(b+c) = (a+c)+(a'+b) -/
theorem sw3 (a a' b c : Nat) : a + a' + (b + c) = a + c + (a' + b) := by
  rw [Nat.add_assoc, Nat.add_comm b c, Nat.add_left_comm a' c b, ← Nat.add_assoc a c (a' + b)]

theorem cancel_right (a b c : Nat) (h : b + a ≤ c + a) : b ≤ c := by
  rw [Nat.add_comm b a, Nat.add_comm c a] at h
  exact cancel_left a b c h

/-! ## Signed values, as a difference of two naturals: f k = P k − N k. -/

/-- f i ≤ f j, written without subtraction. -/
def PLe (P N : Nat → Nat) (i j : Nat) : Prop := P i + N j ≤ P j + N i

theorem ple_refl (P N : Nat → Nat) (i : Nat) : PLe P N i i := Nat.le_refl _

theorem ple_total (P N : Nat → Nat) (i j : Nat) : PLe P N i j ∨ PLe P N j i :=
  Nat.le_total _ _

theorem ple_trans {P N : Nat → Nat} {i j k : Nat} (h1 : PLe P N i j) (h2 : PLe P N j k) :
    PLe P N i k := by
  unfold PLe at *
  have h := Nat.add_le_add h1 h2
  rw [sw1 (P i) (N j) (P j) (N k), sw2 (P j) (N i) (P k) (N j)] at h
  exact cancel_left _ _ _ h

/-- Midpoint convexity of f = P − N. -/
def PConvex (P N : Nat → Nat) : Prop :=
  ∀ k, P (k + 1) + P (k + 1) + (N k + N (k + 2)) ≤ P k + P (k + 2) + (N (k + 1) + N (k + 1))

/-- a+b+(c+c) = (b+c)+(a+c) -/
theorem sw4 (a b c : Nat) : a + b + (c + c) = b + c + (a + c) := by
  rw [Nat.add_comm a b, Nat.add_assoc, Nat.add_left_comm a c c, ← Nat.add_assoc b c (a + c)]

theorem pstep_up {P N : Nat → Nat} (hc : PConvex P N) (k : Nat) (h : PLe P N k (k + 1)) :
    PLe P N (k + 1) (k + 2) := by
  unfold PLe at *
  have c := hc k
  rw [sw3 (P (k + 1)) (P (k + 1)) (N k) (N (k + 2)), sw4 (P k) (P (k + 2)) (N (k + 1))] at c
  exact cancel_right _ _ _ (Nat.le_trans c (Nat.add_le_add_left h _))

theorem pstep_down {P N : Nat → Nat} (hc : PConvex P N) (k : Nat) (h : PLe P N (k + 2) (k + 1)) :
    PLe P N (k + 1) k := by
  unfold PLe at *
  have c := hc k
  rw [sw3 (P (k + 1)) (P (k + 1)) (N k) (N (k + 2)), sw4 (P k) (P (k + 2)) (N (k + 1))] at c
  exact cancel_left _ _ _ (Nat.le_trans c (Nat.add_le_add_right h _))

theorem prising {P N : Nat → Nat} (hc : PConvex P N) {k : Nat} (h : PLe P N k (k + 1)) :
    ∀ j, PLe P N (k + j) (k + j + 1)
  | 0 => h
  | j + 1 => pstep_up hc (k + j) (prising hc h j)

theorem prise_le {P N : Nat → Nat} (hc : PConvex P N) {k : Nat} (h : PLe P N k (k + 1)) :
    ∀ j, PLe P N k (k + j)
  | 0 => ple_refl P N k
  | j + 1 => ple_trans (prise_le hc h j) (prising hc h j)

theorem pfall_le {P N : Nat → Nat} (hc : PConvex P N) :
    ∀ k, PLe P N (k + 1) k → ∀ i, i ≤ k → PLe P N k i
  | 0, _, i, hi => by
      cases Nat.eq_or_lt_of_le hi with
      | inl e => rw [e]; exact ple_refl P N _
      | inr l => exact absurd l (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
      have hk : PLe P N (k + 1) k := pstep_down hc k h
      cases Nat.eq_or_lt_of_le hi with
      | inl e => rw [e]; exact ple_refl P N _
      | inr l => exact ple_trans hk (pfall_le hc k hk i (Nat.le_of_lt_succ l))

/-- SIGNED: the maximum of a convex f = P − N on 0 … n lies at an end. -/
theorem pmax_at_ends {P N : Nat → Nat} (hc : PConvex P N) {k n : Nat} (hk : k ≤ n) :
    PLe P N k 0 ∨ PLe P N k n := by
  cases ple_total P N k (k + 1) with
  | inl up =>
      match Nat.le.dest hk with
      | ⟨j, hj⟩ => exact Or.inr (hj ▸ prise_le hc up j)
  | inr down => exact Or.inl (pfall_le hc k down 0 (Nat.zero_le k))

/-- SIGNED: where a convex f = P − N stops falling, it is least over the whole range. -/
theorem pmin_at_turn {P N : Nat → Nat} (hc : PConvex P N) {t : Nat}
    (hup : PLe P N t (t + 1)) (hin : ∀ s, s + 1 = t → PLe P N t s) (k : Nat) : PLe P N t k := by
  cases Nat.le_total t k with
  | inl h =>
      match Nat.le.dest h with
      | ⟨j, hj⟩ => exact hj ▸ prise_le hc hup j
  | inr h =>
      cases t with
      | zero =>
          cases Nat.eq_or_lt_of_le h with
          | inl e => rw [e]; exact ple_refl P N _
          | inr l => exact absurd l (Nat.not_lt_zero k)
      | succ s =>
          have hs : PLe P N (s + 1) s := hin s rfl
          cases Nat.eq_or_lt_of_le h with
          | inl e => rw [e]; exact ple_refl P N _
          | inr l => exact ple_trans hs (pfall_le hc s hs k (Nat.le_of_lt_succ l))

/-- A signed quadratic (aP − aN)·k² + (bP − bN)·k + (cP − cN) with aN ≤ aP is convex. -/
theorem pquad_convex (aP bP cP aN bN cN : Nat) (ha : aN ≤ aP) :
    PConvex (quad aP bP cP) (quad aN bN cN) := by
  intro k
  have mp := quad_mid aP bP cP k
  have mn := quad_mid aN bN cN k
  show quad aP bP cP (k + 1) + quad aP bP cP (k + 1) + (quad aN bN cN k + quad aN bN cN (k + 2))
      ≤ quad aP bP cP k + quad aP bP cP (k + 2) + (quad aN bN cN (k + 1) + quad aN bN cN (k + 1))
  rw [mn, mp]
  generalize quad aP bP cP (k + 1) = p
  generalize quad aN bN cN (k + 1) = q
  -- p + p + (q + q + 2aN) ≤ p + p + 2aP + (q + q)
  rw [← Nat.add_assoc (p + p) (q + q) (aN + aN), Nat.add_right_comm (p + p) (aP + aP) (q + q)]
  exact Nat.add_le_add_left (Nat.add_le_add ha ha) _

/-- The mirror: f = P − N is concave when −f = N − P is convex, and then the MINIMUM lies at an end. -/
theorem pmin_at_ends_concave {P N : Nat → Nat} (hc : PConvex N P) {k n : Nat} (hk : k ≤ n) :
    PLe P N 0 k ∨ PLe P N n k := by
  cases pmax_at_ends hc hk with
  | inl h => exact Or.inl (by unfold PLe at *; rw [Nat.add_comm (P 0), Nat.add_comm (P k)]; exact h)
  | inr h => exact Or.inr (by unfold PLe at *; rw [Nat.add_comm (P n), Nat.add_comm (P k)]; exact h)

/-- The step of f = quadP − quadN is ≥ 0 at k when a(2k+1)+b ≥ 0, in pair form. -/
theorem up_of_d (aP bP cP aN bN cN k : Nat)
    (h : aN * (k + k + 1) + bN ≤ aP * (k + k + 1) + bP) :
    PLe (quad aP bP cP) (quad aN bN cN) k (k + 1) := by
  unfold PLe
  rw [quad_step aP bP cP k, quad_step aN bN cN k]
  generalize quad aP bP cP k = p
  generalize quad aN bN cN k = q
  rw [Nat.add_right_comm p _ q, ← Nat.add_assoc p q _]
  exact Nat.add_le_add_left h _

theorem down_of_d (aP bP cP aN bN cN k : Nat)
    (h : aP * (k + k + 1) + bP ≤ aN * (k + k + 1) + bN) :
    PLe (quad aP bP cP) (quad aN bN cN) (k + 1) k := by
  unfold PLe
  rw [quad_step aP bP cP k, quad_step aN bN cN k]
  generalize quad aP bP cP k = p
  generalize quad aN bN cN k = q
  rw [Nat.add_right_comm p _ q, ← Nat.add_assoc p q _]
  exact Nat.add_le_add_left h _

theorem two_s (s : Nat) : (s + 1) + (s + 1) = (s + s + 1) + 1 := by
  show s + 1 + s + 1 = s + s + 1 + 1
  rw [Nat.add_right_comm s 1 s]

/-- THE MINIMUM IS AT THE VERTEX'S FLOOR OR CEILING. If the vertex −b/2a lies between the
indices t and t+1 — 2a·t + b ≤ 0 ≤ 2a·(t+1) + b, which is what ⌊−b/2a⌋ = t means — then over
the whole range f is least at t or at t+1. -/
theorem pmin_at_vertex (aP bP cP aN bN cN t : Nat) (ha : aN ≤ aP)
    (hv1 : aP * (t + t) + bP ≤ aN * (t + t) + bN)
    (hv2 : aN * ((t + 1) + (t + 1)) + bN ≤ aP * ((t + 1) + (t + 1)) + bP) (k : Nat) :
    PLe (quad aP bP cP) (quad aN bN cN) t k ∨ PLe (quad aP bP cP) (quad aN bN cN) (t + 1) k := by
  have hc := pquad_convex aP bP cP aN bN cN ha
  cases ple_total (quad aP bP cP) (quad aN bN cN) t (t + 1) with
  | inl up =>
      refine Or.inl (pmin_at_turn hc up ?_ k)
      intro s hs
      subst hs
      apply down_of_d
      -- aP(s+s+1)+bP ≤ aN(s+s+1)+bN, from hv1 at t = s+1 and aN ≤ aP
      rw [two_s, Nat.mul_succ aP, Nat.mul_succ aN, Nat.add_right_comm (aP * (s + s + 1)) aP bP,
          Nat.add_right_comm (aN * (s + s + 1)) aN bN] at hv1
      exact cancel_right aN _ _ (Nat.le_trans (Nat.add_le_add_left ha _) hv1)
  | inr down =>
      refine Or.inr (pmin_at_turn hc (up_of_d aP bP cP aN bN cN (t + 1) ?_) (fun s hs => ?_) k)
      · -- aN(2t+3)+bN ≤ aP(2t+3)+bP, from hv2 and aN ≤ aP
        rw [Nat.mul_succ aN, Nat.mul_succ aP, Nat.add_right_comm (aN * (t + 1 + (t + 1))) aN bN,
            Nat.add_right_comm (aP * (t + 1 + (t + 1))) aP bP]
        exact Nat.add_le_add hv2 ha
      · have e : s = t := Nat.succ.inj hs
        subst e
        exact down

end ZIntExtremes
