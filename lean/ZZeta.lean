-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-02.
/-!
# ZZeta — "1 + 2 + 3 + ... = -1/12" read by ZTL: the finite facts, ZERO axioms (Lean core only)

The notation names no operation. Three finite facts decide each clean reading and show why the bare one is dirty:

* `zeta_neg_one` — the zeta-continuation reading as a FINITE OPERATION: the Bernoulli numbers by their recursion
  (B₀ = 1, Bₙ = −1/(n+1) Σ_{k<n} C(n+1,k) B_k) and `ζ(−1) = −B₂/2` give −1/12, computed by the kernel. (That
  `ζ(−n) = −B_{n+1}/(n+1)` IS the analytic continuation's value is Mathlib's `riemannZeta_neg_nat_eq_bernoulli` —
  classical axioms: a separate register, the ztl-classical repository (ZClassical/Zeta.lean), not used here.)
* `partial_sums_unbounded`, `not_limit_neg_twelfth` — the limit reading: `S n ≥ n`, so past any N some partial sum
  exceeds any bound; and `|S n − (−1/12)| > 1` for every n ≥ 1 (scaled: `12 < 12·S n + 1`).
* `no_stable_additive_sum` — no summation that is ADDITIVE (`σ(b + c) = σ b + σ c`) and STABLE
  (`σ(0, a₀, a₁, …) = σ a`) on a domain closed under that shift and under the differences used, with
  `σ(1, 0, 0, …) ≠ 0`, contains (1, 2, 3, …). So "1 + 2 + 3 + …" read as `S` and as `0 + S` (a leading zero) is
  not one value of one such operation. (The popular `S − 4S` derivation does NOT use a leading zero: it inserts zeros
  between terms, which zeta regularisation respects. The leading zero shows only that a method need not respect every
  zero — 2026-11-02 correction.)
-/
namespace ZZeta

/-! ## 1. The zeta-continuation value as a finite operation (kernel-computed rationals) -/

/-- a rational as a pair, not normalized: `n / d`, `d > 0` -/
structure Q where
  n : Int
  d : Nat
deriving Repr

def Q.add (a b : Q) : Q := ⟨a.n * b.d + b.n * a.d, a.d * b.d⟩
def Q.mulNat (a : Q) (k : Nat) : Q := ⟨a.n * k, a.d⟩
def Q.neg (a : Q) : Q := ⟨-a.n, a.d⟩
def Q.divNat (a : Q) (k : Nat) : Q := ⟨a.n, a.d * k⟩
/-- equality of the values: cross-multiplication -/
def Q.eqv (a b : Q) : Bool := a.n * b.d == b.n * a.d

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- the k-th element (own definition: core's `List.getD` carries `propext`, MEASURED with `#print axioms`) -/
def nth (default : Q) : List Q → Nat → Q
  | [], _ => default
  | x :: _, 0 => x
  | _ :: xs, k + 1 => nth default xs k

/-- Bernoulli numbers (B₁ = −1/2) by the recursion, as a list B₀ … B_n -/
def bernList : Nat → List Q
  | 0 => [⟨1, 1⟩]
  | n + 1 =>
    let prev := bernList n
    let s := (List.range (n + 1)).foldl
      (fun acc k => Q.add acc (Q.mulNat (nth ⟨0, 1⟩ prev k) (choose (n + 2) k))) ⟨0, 1⟩
    prev ++ [Q.divNat (Q.neg s) (n + 2)]

def bern (n : Nat) : Q := nth ⟨0, 1⟩ (bernList n) n

/-- ζ(−1) = −B₂/2 — the value the continuation assigns, by the finite recursion -/
def zetaNegOne : Q := Q.divNat (Q.neg (bern 2)) 2

theorem bern_two : (bern 2).eqv ⟨1, 6⟩ = true := rfl
theorem zeta_neg_one : zetaNegOne.eqv ⟨-1, 12⟩ = true := rfl

/-! ## 2. The limit reading: the partial sums run away -/

def S : Nat → Nat
  | 0 => 0
  | n + 1 => S n + (n + 1)

theorem S_ge (n : Nat) : n ≤ S n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih => exact Nat.add_le_add_right ih (k + 1) |> Nat.le_trans (Nat.le_add_left (k + 1) k)

/-- past any N, some partial sum exceeds any bound B -/
theorem partial_sums_unbounded (B N : Nat) : ∃ n, N ≤ n ∧ B < S n :=
  ⟨N + (B + 1), Nat.le_add_right N (B + 1),
   Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self B) (Nat.le_add_left (B + 1) N)) (S_ge _)⟩

/-- `|S n − (−1/12)| > 1` for n ≥ 1, scaled by 12: `12 < 12·S n + 1` -/
theorem not_limit_neg_twelfth (n : Nat) (hn : 1 ≤ n) : 12 < 12 * S n + 1 :=
  Nat.lt_succ_of_le (Nat.mul_le_mul_left 12 (Nat.le_trans hn (S_ge n)))

/-! ## 3. No stable additive summation sums 1 + 2 + 3 + … -/

def shift0 (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => a n

def nat1 : Nat → Nat := fun n => n + 1
def ones : Nat → Nat := fun _ => 1
def e1 : Nat → Nat
  | 0 => 1
  | _ + 1 => 0

/-- (1, 2, 3, …) = (1, 1, 1, …) + (0, 1, 2, …), pointwise -/
theorem nat1_split (n : Nat) : nat1 n = ones n + shift0 nat1 n := by
  cases n with
  | zero => rfl
  | succ k => show k + 1 + 1 = 1 + (k + 1); exact Nat.add_comm (k + 1) 1

/-- (1, 1, 1, …) = (1, 0, 0, …) + (0, 1, 1, …), pointwise -/
theorem ones_split (n : Nat) : ones n = e1 n + shift0 ones n := by
  cases n with
  | zero => rfl
  | succ k => show 1 = 0 + 1; exact (Nat.zero_add 1).symm

/-- the values live in any type with an addition, a zero and right cancellation `x + y = y → x = 0`; additivity is
asked only where `a = b + c` term by term (no function extensionality: zero axioms) -/
theorem no_stable_additive_sum {G : Type} (add : G → G → G) (zero : G)
    (cancel : ∀ x y, add x y = y → x = zero)
    (D : (Nat → Nat) → Prop) (σ : (Nat → Nat) → G)
    (hshift : ∀ a, D a → D (shift0 a))
    (hadd : ∀ a b c, D a → D b → D c → (∀ n, a n = b n + c n) → σ a = add (σ b) (σ c))
    (hstable : ∀ a, D a → σ (shift0 a) = σ a)
    (hones : D ones) (he1D : D e1)
    (he1 : σ e1 ≠ zero) (hs : D nat1) : False := by
  have h1 : σ ones = zero := by
    have e := hadd nat1 ones (shift0 nat1) hs hones (hshift _ hs) nat1_split
    rw [hstable _ hs] at e
    exact cancel _ _ e.symm
  have h2 : σ e1 = zero := by
    have e := hadd ones e1 (shift0 ones) hones he1D (hshift _ hones) ones_split
    rw [hstable _ hones, h1] at e
    exact cancel _ _ e.symm
  exact he1 h2

end ZZeta

#print axioms ZZeta.bern_two
#print axioms ZZeta.zeta_neg_one
#print axioms ZZeta.S_ge
#print axioms ZZeta.partial_sums_unbounded
#print axioms ZZeta.not_limit_neg_twelfth
#print axioms ZZeta.nat1_split
#print axioms ZZeta.ones_split
#print axioms ZZeta.no_stable_additive_sum
