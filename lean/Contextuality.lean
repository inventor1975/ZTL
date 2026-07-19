/-
  Contextuality.lean — the truth table itself falls: Mermin–Peres and GHZ,
  kernel-checked.

  The combinatorial core of quantum contextuality, on the EMPTY axiom list.
  Values ±1 are encoded as Bool (true = "the value is −1"); a product of
  ±1's equals +1 iff the xor-parity of the minus-bits is false.

  Mermin–Peres magic square: nine observables in a 3×3 grid; quantum
  mechanics fixes the sign pattern — every row multiplies to +I, the
  columns to +I, +I, −I (the operator identities are verified by direct
  matrix arithmetic in dilemmas/quantum_ladder.py; here is the finite
  core). Theorem: NO assignment of ±1 to the nine cells satisfies the six
  constraints — no bivalent valuation exists at all, 0 of 512.

  GHZ (three quanta): the sign pattern XXX = +1, XYY = YXY = YYX = −1
  (eigen-identities verified on the state in the same stand). Theorem: no
  assignment of ±1 to the six single-particle values satisfies the four
  constraints — 0 of 64, all-versus-nothing.

  The honest split: Lean proves the COMBINATORIAL impossibility for these
  sign patterns; that the patterns are QUANTUM's is the stand's matrix
  arithmetic. Together: the local addresses of the pair (quantum_pair §1)
  are not merely empty — they cannot be filled.

  Verify from zero:  lean lean/Contextuality.lean
-/

namespace Contextuality

/-- Decidability of ∃ over Bool — the whole file lives on this. -/
instance {p : Bool → Prop} [DecidablePred p] : Decidable (∃ b, p b) :=
  decidable_of_iff (p false ∨ p true)
    ⟨fun h => h.elim (fun hf => ⟨false, hf⟩) (fun ht => ⟨true, ht⟩),
     fun ⟨b, hb⟩ => by cases b
                       · exact Or.inl hb
                       · exact Or.inr hb⟩

/-- **The Mermin–Peres magic square has no valuation.** Rows multiply to
+1 (even minus-parity), columns to +1, +1, −1 (the third column odd) —
no ±1 table satisfies all six: 0 of 512, by kernel enumeration. -/
theorem mermin_square_no_valuation :
    ¬ ∃ a b c d e f g h i : Bool,
      (Bool.xor a (Bool.xor b c) = false) ∧
      (Bool.xor d (Bool.xor e f) = false) ∧
      (Bool.xor g (Bool.xor h i) = false) ∧
      (Bool.xor a (Bool.xor d g) = false) ∧
      (Bool.xor b (Bool.xor e h) = false) ∧
      (Bool.xor c (Bool.xor f i) = true) := by decide

/-- **GHZ, all-versus-nothing.** XXX = +1 and XYY = YXY = YYX = −1 admit
no ±1 assignment to the six single-particle values: 0 of 64. -/
theorem ghz_no_valuation :
    ¬ ∃ x1 x2 x3 y1 y2 y3 : Bool,
      (Bool.xor x1 (Bool.xor x2 x3) = false) ∧
      (Bool.xor x1 (Bool.xor y2 y3) = true) ∧
      (Bool.xor y1 (Bool.xor x2 y3) = true) ∧
      (Bool.xor y1 (Bool.xor y2 x3) = true) := by decide

/-- The parity heart of both proofs, stated once: an odd number of odd
constraints over variables that each occur an even number of times is
unsatisfiable — here in its smallest clothing: xor of all six Mermin
constraint-sums is `true` while every cell cancels. Kernel-checked
consequence: the two theorems above. -/
theorem mermin_parity_core :
    ∀ a b c d e f g h i : Bool,
      Bool.xor (Bool.xor a (Bool.xor b c))
        (Bool.xor (Bool.xor d (Bool.xor e f))
          (Bool.xor (Bool.xor g (Bool.xor h i))
            (Bool.xor (Bool.xor a (Bool.xor d g))
              (Bool.xor (Bool.xor b (Bool.xor e h))
                (Bool.xor c (Bool.xor f i)))))) = false := by decide

#print axioms mermin_square_no_valuation
#print axioms ghz_no_valuation
#print axioms mermin_parity_core

end Contextuality
