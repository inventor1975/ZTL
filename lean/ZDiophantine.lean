/-
  ZDiophantine.lean — "has a root" and "has no root" are earned on different grounds. Zero axioms.

  A polynomial equation over the naturals, three kinds of claim (2026-11-06, the curator: "Да"; the MRDP thread):
  * "it HAS a root" is earned by one finite witness, checked by substitution — `pell61_witness`: x² − 61·y² = 1 at
    x = 1 766 319 049, y = 226 153 980, the kernel multiplies the numbers out;
  * "it has NO root" is never earned by a search — a search up to any bound leaves the claim open (Pell 61 has no root
    with y ≤ 10⁶, measured in `dilemmas/diophantine.py`, and still has one) — it is earned only by a PROOF: here
    `no_root_three`, x·x ≠ 3·y + 2 for all x, y, by the residues of squares modulo 3;
  * and for some polynomials neither a witness nor a proof in a given theory exists: MRDP gives one whose having no
    root is equivalent to that theory's consistency (not formalised here; see the stand).

  FORM. Core's modular lemmas (`Nat.mul_mod`, `Nat.add_mod`, `Nat.mod_mod`, `Nat.add_mul_mod_self_left`) carry propext
  (probed), and so do `Nat.add_mul` and `Nat.mul_assoc`: the residue here is a function by recursion, and right
  distributivity and associativity are re-derived from the clean `Nat.mul_add` and `Nat.mul_comm`.
-/
namespace ZDiophantine

/-! ### A witness -/

/-- Pell's equation x² − 61y² = 1 has a root; the smallest has ten digits. -/
theorem pell61_witness : 1766319049 * 1766319049 = 61 * 226153980 * 226153980 + 1 := by decide

/-! ### A proof of "no root" -/

/-- The residue modulo 3, by recursion (no `%`). -/
def r3 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => r3 n

theorem add_mul' (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

theorem mul_assoc' (a b : Nat) : ∀ c : Nat, a * b * c = a * (b * c)
  | 0 => rfl
  | c + 1 => by
      show a * b * c + a * b = a * (b * c + b)
      rw [Nat.mul_add, mul_assoc' a b c]

/-- Adding a multiple of 3 does not change the residue. -/
theorem r3_add (a : Nat) : ∀ k : Nat, r3 (a + 3 * k) = r3 a
  | 0 => rfl
  | k + 1 => by
      show r3 (a + (3 * k + 3)) = r3 a
      rw [← Nat.add_assoc]
      exact r3_add a k

/-- Every number is s + 3q with s < 3 (s given by cases, no `%`). -/
theorem split3 : ∀ x : Nat, ∃ q s, (s = 0 ∨ s = 1 ∨ s = 2) ∧ x = s + 3 * q
  | 0 => ⟨0, 0, Or.inl rfl, rfl⟩
  | x + 1 => by
      obtain ⟨q, s, hs, hx⟩ := split3 x
      rcases hs with h | h | h
      · exact ⟨q, 1, Or.inr (Or.inl rfl), by rw [hx, h, Nat.zero_add, Nat.add_comm]⟩
      · exact ⟨q, 2, Or.inr (Or.inr rfl), by
          rw [hx, h, Nat.add_comm 1 (3 * q), Nat.add_assoc]; exact Nat.add_comm (3 * q) 2⟩
      · refine ⟨q + 1, 0, Or.inl rfl, ?_⟩
        rw [hx, h, Nat.zero_add, Nat.mul_add, Nat.mul_one, Nat.add_comm 2 (3 * q), Nat.add_assoc]

/-- (s + 3q)² = s·s + 3·(stuff): the square's residue is the residue of s·s. -/
theorem sq_form (s q : Nat) : (s + 3 * q) * (s + 3 * q) = s * s + 3 * (s * q + q * (s + 3 * q)) := by
  rw [add_mul' s (3 * q) (s + 3 * q), Nat.mul_add s s (3 * q), mul_assoc' 3 q (s + 3 * q),
    Nat.mul_add 3 (s * q) (q * (s + 3 * q)), Nat.add_assoc]
  have h : s * (3 * q) = 3 * (s * q) := by
    rw [← mul_assoc' s 3 q, Nat.mul_comm s 3, mul_assoc' 3 s q]
  rw [h]

theorem r3_sq (x : Nat) : r3 (x * x) = 0 ∨ r3 (x * x) = 1 := by
  obtain ⟨q, s, hs, hx⟩ := split3 x
  rw [hx, sq_form, r3_add]
  rcases hs with h | h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

theorem r3_target (y : Nat) : r3 (3 * y + 2) = 2 := by
  rw [Nat.add_comm, r3_add]
  rfl

/-- "x·x = 3·y + 2 has no root" — earned by a proof, which no search could give. -/
theorem no_root_three (x y : Nat) : x * x ≠ 3 * y + 2 := by
  intro h
  have h1 := r3_sq x
  rw [h, r3_target] at h1
  rcases h1 with h2 | h2 <;> exact absurd h2 (by decide)

end ZDiophantine

#print axioms ZDiophantine.pell61_witness
#print axioms ZDiophantine.r3_add
#print axioms ZDiophantine.split3
#print axioms ZDiophantine.sq_form
#print axioms ZDiophantine.r3_sq
#print axioms ZDiophantine.no_root_three
