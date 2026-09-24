/-!
# The parabola the solver refutes by: a negative discriminant leaves no root.
Zero axioms. (2026-09-24)

The numeric solver (`znumsolve._parabola_pieces`) refutes `a·x² + b·x + c = 0`
outright when D = b² − 4ac < 0: no x satisfies it, and the claim is REFUTED
without trying a single value (the curator's `X*X-2X+5=0`, D = −16). The stand
`test_quadratic.py` measures the rule on a pool; this module is why it holds
for every x.

`form_pos` is the one case with content. For a > 0 (else negate the equation)
D < 0 forces c > 0, and at a rational x = p/q, f(x)·q² = a p² + b p q + c q².
When b·p·q ≥ 0 that sum is plainly positive; when b·p·q < 0, write A = a,
B = |b|, C = c, P = |p|, Q = |q|, and the sum is A P² − B P Q + C Q², positive
by `form_pos`. `no_root_line` is its integer case, Q = 1, the one the floor's
integer readings (`ZNum`) meet.

What is kernel-checked here is `form_pos` and its lemmas over `Nat`. The
passage from signed coefficients to those cases is the two lines above,
argued, not checked: in this toolchain the core's `Int` multiplication laws
carry `propext` (MEASURED 2026-09-24: `Int.mul_comm`, `Int.mul_assoc`,
`Int.mul_add`, `Int.add_mul`, `Int.mul_one`, `Int.neg_mul`, `Int.mul_pos`,
`Int.lt_irrefl` among them), and so do `Nat.mul_assoc`, `Nat.add_mul` and
`Nat.lt_of_mul_lt_mul_left` (the last the full classical set). The clean
replacements below are proved from the clean `Nat.mul_comm`,
`Nat.left_distrib` (`Nat.mul_add`), `Nat.mul_le_mul_left` and the additive
laws; `simp` and `ac_rfl` are not used, both measured to bring `propext`.

    am_gm     :  2·u·v ≤ u² + v²
    form_pos  :  B² < 4AC → 0 < P ∨ 0 < Q → B·P·Q < A·P² + C·Q²
    no_root_line : B² < 4AC → B·X < A·X² + C

The range of a parabola over a box (its ends and its vertex), which the judge
uses when x is measured, is measured (`test_quadratic.py`), not a theorem here.
-/

namespace ZParabola

/-- `Nat.mul_assoc`, by induction: core's carries `propext` here (measured). -/
theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ k ih =>
      show a * b * k + a * b = a * (b * k + b)
      rw [ih, Nat.mul_add]

/-- Right distributivity from `Nat.mul_add` and `Nat.mul_comm`, both clean. -/
theorem nat_add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

theorem nat_mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← nat_mul_assoc, Nat.mul_comm a b, nat_mul_assoc]

/-- Cancel a factor from a strict inequality, contrapositively from `Nat.mul_le_mul_left`. -/
theorem lt_of_mul_lt_mul_left' {k u v : Nat} (h : k * u < k * v) : u < v := by
  cases Nat.lt_or_ge u v with
  | inl hlt => exact hlt
  | inr hge => exact absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left k hge)) (Nat.lt_irrefl _)

theorem sq_add (u d : Nat) : (u + d) * (u + d) = u * u + 2 * u * d + d * d := by
  rw [nat_add_mul, Nat.mul_add, Nat.mul_add, Nat.two_mul, nat_add_mul, Nat.mul_comm d u,
      Nat.add_assoc (u * u) (u * d) (u * d + d * d), ← Nat.add_assoc (u * d) (u * d) (d * d),
      Nat.add_assoc (u * u) (u * d + u * d) (d * d)]

theorem am_gm_le (u d : Nat) : 2 * u * (u + d) ≤ u * u + (u + d) * (u + d) := by
  rw [sq_add, Nat.mul_add, nat_mul_assoc 2 u u, Nat.two_mul (u * u),
      ← Nat.add_assoc (u * u) (u * u + 2 * u * d) (d * d), ← Nat.add_assoc (u * u) (u * u) (2 * u * d)]
  exact Nat.le_add_right _ _

/-- The arithmetic–geometric mean inequality on `Nat`: 2uv ≤ u² + v². -/
theorem am_gm (u v : Nat) : 2 * u * v ≤ u * u + v * v := by
  cases Nat.le_total u v with
  | inl h =>
      match Nat.le.dest h with
      | ⟨d, hd⟩ => subst hd; exact am_gm_le u d
  | inr h =>
      match Nat.le.dest h with
      | ⟨d, hd⟩ =>
          subst hd
          have e : 2 * (v + d) * v = 2 * v * (v + d) := by
            rw [nat_mul_assoc, Nat.mul_comm (v + d) v, ← nat_mul_assoc]
          rw [e, Nat.add_comm ((v + d) * (v + d)) (v * v)]
          exact am_gm_le v d

theorem sq_prod (b q : Nat) : (b * q) * (b * q) = (b * b) * (q * q) := by
  rw [nat_mul_assoc b q (b * q), nat_mul_left_comm q b q, ← nat_mul_assoc b b (q * q)]

theorem two_two (n : Nat) : 2 * (2 * n) = 4 * n := by
  rw [← nat_mul_assoc]

theorem id_left (A B P Q : Nat) : 2 * (2 * A * P) * (B * Q) = 4 * A * (B * P * Q) := by
  rw [nat_mul_assoc 2 A P, two_two, nat_mul_assoc 4 (A * P) (B * Q), nat_mul_assoc A P (B * Q),
      nat_mul_left_comm P B Q, nat_mul_assoc 4 A (B * P * Q), nat_mul_assoc B P Q]

theorem id_right (A C P Q : Nat) :
    (2 * A * P) * (2 * A * P) + (4 * A * C) * (Q * Q) = 4 * A * (A * P * P + C * Q * Q) := by
  rw [Nat.mul_add, sq_prod (2 * A) P, nat_mul_assoc 2 A (2 * A), nat_mul_left_comm A 2 A, two_two,
      nat_mul_assoc 4 A (A * P * P), nat_mul_assoc A P P, ← nat_mul_assoc A A (P * P),
      nat_mul_assoc 4 (A * A) (P * P), nat_mul_assoc (4 * A) C (Q * Q), nat_mul_assoc C Q Q]

/-- A negative discriminant forces a positive leading coefficient. -/
theorem a_pos {A B C : Nat} (hD : B * B < 4 * A * C) : 0 < A := by
  cases Nat.eq_or_lt_of_le (Nat.zero_le A) with
  | inl h => subst h; rw [Nat.mul_zero, Nat.zero_mul] at hD; exact absurd hD (Nat.not_lt_zero _)
  | inr h => exact h

/-- THE FORM IS POSITIVE DEFINITE when B² < 4AC: at every (P, Q) ≠ (0, 0),
B·P·Q < A·P² + C·Q². The case the solver's refusal at D < 0 rests on. -/
theorem form_pos (A B C P Q : Nat) (hD : B * B < 4 * A * C) (hPQ : 0 < P ∨ 0 < Q) :
    B * P * Q < A * P * P + C * Q * Q := by
  cases Nat.eq_or_lt_of_le (Nat.zero_le Q) with
  | inl hQ =>
      subst hQ
      have hP : 0 < P := by
        cases hPQ with
        | inl h => exact h
        | inr h => exact absurd h (Nat.lt_irrefl 0)
      rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      exact Nat.mul_pos (Nat.mul_pos (a_pos hD) hP) hP
  | inr hQ =>
      have h1 := am_gm (2 * A * P) (B * Q)
      have h2 : (B * Q) * (B * Q) < (4 * A * C) * (Q * Q) := by
        rw [sq_prod B Q]
        exact Nat.mul_lt_mul_of_lt_of_le hD (Nat.le_refl _) (Nat.mul_pos hQ hQ)
      have h3 : 2 * (2 * A * P) * (B * Q) < (2 * A * P) * (2 * A * P) + (4 * A * C) * (Q * Q) :=
        Nat.lt_of_le_of_lt h1 (Nat.add_lt_add_left h2 _)
      rw [id_left A B P Q, id_right A C P Q] at h3
      exact lt_of_mul_lt_mul_left' h3

/-- The integer case (Q = 1): B·X < A·X² + C, so A·X² − B·X + C has no root. -/
theorem no_root_line (A B C X : Nat) (hD : B * B < 4 * A * C) : B * X < A * X * X + C := by
  have h := form_pos A B C X 1 hD (Or.inr (Nat.succ_pos 0))
  rw [Nat.mul_one, Nat.mul_one, Nat.mul_one] at h
  exact h

end ZParabola
