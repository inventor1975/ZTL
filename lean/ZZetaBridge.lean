-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-02.
/-!
# ZZetaBridge — a dirty atom's STABILITY = a summation method's INVARIANCE (zero axioms, Lean core)

The bridge between ZTL's notion and the analyst's (2026-11-02).

ZTL (ZDirty.lean): a dirty atom's occurrences are read each on its own; a verdict EARNED IF STABLE is true in every
COMPLETION — every assignment of ONE value to the atom at all its occurrences.
Analysis: a summation method σ is invariant under a transformation T of series (a leading zero, inserted zeros)
when σ (T a) = σ a.

The bridge: a derivation mentions "S" at occurrences i, and occurrence i DENOTES a transformed series T i a (the
series as written there: a itself, 0 + a, a with zeros inserted …). A method σ reads occurrence i as σ (T i a).
* `stable_iff_invariant` — the method's reading is a STABLE completion of the atom S (one value at all occurrences)
  if and only if σ is invariant under every transformation the derivation uses (relative to a reference occurrence).
* `leading_zero_forces` — if a derivation reads S also as 0 + S and the method is additive (where a = b + c term by
  term), stability forces σ (1 + 1 + 1 + …) = 0. The ζ-regularization gives 1 + 1 + 1 + … the value ζ(0) = −1/2,
  so it cannot make that S stable — the 0 + 1 + 2 + … = 5/12 of the brief (5/12 − (−1/12) = 1/2 = −ζ(0)).
* `not_stable_of_ones` — the contrapositive, the form the judge needs: an additive method with
  σ (1 + 1 + 1 + …) ≠ 0 cannot read S and 0 + S as one value.
A method stable under a leading zero on its WHOLE domain has no value on 1 + 2 + 3 + … at all: ZZeta.lean,
`no_stable_additive_sum`. The ZTL side here MIRRORS ZDirty's definitions (one value per atom at all its occurrences);
it does not import them (ZDirty's atoms are truth values, this atom is a number).
-/
namespace ZZetaBridge

/-! ## The ZTL side: occurrences, readings, stable completions -/

/-- a reading of an atom's k occurrences: a value at each (the dirty reading: each occurrence on its own) -/
def Reading (G : Type) (k : Nat) := Fin k → G

/-- a STABLE completion: one value at every occurrence (ZDirty's completion, for one atom) -/
def Stable {G : Type} {k : Nat} (ρ : Reading G k) : Prop := ∀ i j : Fin k, ρ i = ρ j

/-! ## The analyst's side: a method reads each occurrence's series -/

/-- the method σ's reading of the derivation whose occurrence i denotes the series `T i a` -/
def methodReading {G : Type} {k : Nat} (σ : (Nat → Nat) → G) (T : Fin k → (Nat → Nat) → (Nat → Nat))
    (a : Nat → Nat) : Reading G k :=
  fun i => σ (T i a)

/-- invariance of σ at `a` under every transformation of the derivation, relative to occurrence `r` -/
def Invariant {G : Type} {k : Nat} (σ : (Nat → Nat) → G) (T : Fin k → (Nat → Nat) → (Nat → Nat))
    (a : Nat → Nat) (r : Fin k) : Prop :=
  ∀ i, σ (T i a) = σ (T r a)

/-- THE BRIDGE: the method's reading is a stable completion iff σ is invariant under the derivation's
transformations -/
theorem stable_iff_invariant {G : Type} {k : Nat} (σ : (Nat → Nat) → G)
    (T : Fin k → (Nat → Nat) → (Nat → Nat)) (a : Nat → Nat) (r : Fin k) :
    Stable (methodReading σ T a) ↔ Invariant σ T a r :=
  ⟨fun h i => h i r, fun h i j => (h i).trans (h j).symm⟩

/-! ## The leading zero -/

def shift0 (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => a n

def nat1 : Nat → Nat := fun n => n + 1
def ones : Nat → Nat := fun _ => 1

theorem nat1_split (n : Nat) : nat1 n = ones n + shift0 nat1 n := by
  cases n with
  | zero => rfl
  | succ k => show k + 1 + 1 = 1 + (k + 1); exact Nat.add_comm (k + 1) 1

/-- a derivation reading "S" as S and as 0 + S: two occurrences, the identity and the leading zero -/
def idOrShift : Fin 2 → (Nat → Nat) → (Nat → Nat)
  | ⟨0, _⟩ => id
  | ⟨_ + 1, _⟩ => shift0

/-- if the method makes that S stable and is additive at (1, 2, 3, …) = (1, 1, 1, …) + (0, 1, 2, …), then it gives
1 + 1 + 1 + … the value 0 (values in any type with addition, zero and right cancellation) -/
theorem leading_zero_forces {G : Type} (add : G → G → G) (zero : G)
    (cancel : ∀ x y, add x y = y → x = zero) (σ : (Nat → Nat) → G)
    (hadd : σ nat1 = add (σ ones) (σ (shift0 nat1)))
    (hst : Stable (methodReading σ idOrShift nat1)) : σ ones = zero := by
  have hs : σ (shift0 nat1) = σ nat1 := (hst ⟨1, by decide⟩ ⟨0, by decide⟩)
  rw [hs] at hadd
  exact cancel _ _ hadd.symm

/-- contrapositive: an additive method with σ (1 + 1 + 1 + …) ≠ 0 (ζ: −1/2) cannot read S and 0 + S as one value -/
theorem not_stable_of_ones {G : Type} (add : G → G → G) (zero : G)
    (cancel : ∀ x y, add x y = y → x = zero) (σ : (Nat → Nat) → G)
    (hadd : σ nat1 = add (σ ones) (σ (shift0 nat1))) (hones : σ ones ≠ zero) :
    ¬ Stable (methodReading σ idOrShift nat1) :=
  fun hst => hones (leading_zero_forces add zero cancel σ hadd hst)

end ZZetaBridge

#print axioms ZZetaBridge.stable_iff_invariant
#print axioms ZZetaBridge.nat1_split
#print axioms ZZetaBridge.leading_zero_forces
#print axioms ZZetaBridge.not_stable_of_ones
