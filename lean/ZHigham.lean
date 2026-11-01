-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
import ZRound
import ZFloatPath
/-!
# ZHigham — the rounding model's arithmetic (toward Higham, Thm 10.3). Zero axioms.

`zenergy.pd_ieee` cites Higham's backward-error theorem for a floating Cholesky. Its foundation is the STANDARD
ROUNDING MODEL — every operation returns its exact result times `1 + δ`, `|δ| ≤ u` — and the count of how such factors
compound (Higham, Accuracy and Stability, 2nd ed., Lemma 3.1): `k` factors stay within `γ_k = k u / (1 − k u)` of 1.
Here, in ZNet's ordered field given by its laws, WITHOUT a division (`γ_k` written as `(1 − k u)·|θ| ≤ k u`):
  `gamma_step`   one more factor: `(1 − c)|θ| ≤ c` ⇒ `(1 − (c + u))·|θ(1 + δ) + δ| ≤ c + u`;
  `gamma_prod`   Lemma 3.1: `Π_{i ≤ k} (1 + δ_i) = 1 + θ` with `(1 − k u)|θ| ≤ k u`.
The rounding model itself is a PREMISE about the machine (IEEE 754: `|δ| ≤ 2^-53` for + − × ÷ √ in binary64,
round to nearest, no underflow); what follows from it is proved.
VR discipline: `#print axioms` at the end — the empty list, every line.
-/
namespace ZHigham
open ZNet
variable {α : Type}

theorem abs_one (F : OF α) (h1 : F.le F.zero F.one) : F.abs F.one = F.one := F.abs_of_nonneg h1

theorem one_nonneg (F : OF α) : F.le F.zero F.one := by
  have := F.sq_nonneg F.one; rw [F.mul_one] at this; exact this

/-- `|1 + δ| ≤ 1 + u` for `|δ| ≤ u`. -/
theorem abs_one_add (F : OF α) {δ u : α} (hd : F.le (F.abs δ) u) :
    F.le (F.abs (F.add F.one δ)) (F.add F.one u) := by
  apply F.le_trans (F.abs_add F.one δ)
  rw [abs_one F (one_nonneg F)]
  exact F.add_le_add (F.le_refl _) hd

/-- `m2(1 + u) + (c u + u u) = m1` from `m1 + c = 1`, `m2 + u = m1`. -/
theorem key_identity (F : OF α) {m1 m2 c u : α} (hm1 : F.add m1 c = F.one) (hm2 : F.add m2 u = m1) :
    F.add (F.mul m2 (F.add F.one u)) (F.add (F.mul c u) (F.mul u u)) = m1 := by
  -- m2(1+u) = m2 + m2 u
  rw [F.mul_add, F.mul_one]
  -- (m2 + m2 u) + (c u + u u) = m2 + ((m2 u + u u) + c u)
  rw [F.add_assoc, F.add_comm (F.mul c u) (F.mul u u), ← F.add_assoc (F.mul m2 u)]
  -- m2 u + u u = (m2 + u) u = m1 u
  rw [← add_mul, hm2]
  -- m1 u + c u = (m1 + c) u = u
  rw [← add_mul, hm1, ZRound.one_mul, hm2]

/-- ONE MORE FACTOR. `0 ≤ u`, `0 ≤ c`, `|δ| ≤ u`, `m1 + c = 1`, `m2 + u = m1`, `0 ≤ m2`, `m1·|θ| ≤ c`:
`m2·|θ(1 + δ) + δ| ≤ c + u` — `γ_k (1 + u) + u ≤ γ_{k+1}` in the multiplied form. -/
theorem gamma_step (F : OF α) {u c m1 m2 θ δ : α} (hu : F.le F.zero u) (hc : F.le F.zero c)
    (hd : F.le (F.abs δ) u) (hm1 : F.add m1 c = F.one) (hm2 : F.add m2 u = m1) (hm2n : F.le F.zero m2)
    (ih : F.le (F.mul m1 (F.abs θ)) c) :
    F.le (F.mul m2 (F.abs (F.add (F.mul θ (F.add F.one δ)) δ))) (F.add c u) := by
  let t := F.abs θ
  have ht : F.le F.zero t := F.abs_nonneg θ
  -- |θ(1+δ) + δ| ≤ t (1 + u) + u
  have h1 : F.le (F.abs (F.add (F.mul θ (F.add F.one δ)) δ)) (F.add (F.mul t (F.add F.one u)) u) := by
    apply F.le_trans (F.abs_add _ _)
    rw [F.abs_mul]
    exact F.add_le_add (F.mul_le_mul_left ht (abs_one_add F hd)) hd
  apply F.le_trans (F.mul_le_mul_left hm2n h1)
  rw [F.mul_add]
  -- m2 (t (1+u)) ≤ m1 t  and  m2 u ≤ u
  have hk := key_identity F hm1 hm2
  have hcu : F.le F.zero (F.add (F.mul c u) (F.mul u u)) := by
    have := F.add_le_add (F.mul_nonneg hc hu) (F.sq_nonneg u); rw [F.add_zero] at this; exact this
  have hA : F.le (F.mul m2 (F.add F.one u)) m1 := by
    have := F.add_le_add (F.le_refl (F.mul m2 (F.add F.one u))) hcu
    rw [F.add_zero, hk] at this; exact this
  have hA' : F.le (F.mul m2 (F.mul t (F.add F.one u))) (F.mul m1 t) := by
    rw [← F.mul_assoc, F.mul_comm m2 t, F.mul_assoc, F.mul_comm m1 t]
    exact F.mul_le_mul_left ht hA
  have hm1le : F.le m1 F.one := by
    have := F.add_le_add (F.le_refl m1) hc; rw [F.add_zero, hm1] at this; exact this
  have hm2le : F.le m2 F.one := by
    have := F.add_le_add (F.le_refl m2) hu; rw [F.add_zero, hm2] at this; exact F.le_trans this hm1le
  have hB : F.le (F.mul m2 u) u := by
    rw [F.mul_comm m2 u]
    have := F.mul_le_mul_left hu hm2le; rw [F.mul_one] at this; exact this
  exact F.add_le_add (F.le_trans hA' ih) hB

/-- `Π (1 + δ_i)` over a list. -/
def prod1 (F : OF α) : List α → α
  | [] => F.one
  | d :: ds => F.mul (F.add F.one d) (prod1 F ds)

/-- `k·u` for a list of length `k`. -/
def cnt (F : OF α) (u : α) : List α → α
  | [] => F.zero
  | _ :: ds => F.add u (cnt F u ds)

theorem cnt_nonneg (F : OF α) {u : α} (hu : F.le F.zero u) : ∀ ds : List α, F.le F.zero (cnt F u ds)
  | [] => F.le_refl _
  | _ :: ds => by
    have := F.add_le_add hu (cnt_nonneg F hu ds); rw [F.add_zero] at this; exact this

/-- `(1 + d)·P − 1 = θ (1 + d) + d` when `P = θ + 1`. -/
theorem step_identity (F : OF α) (d θ : α) :
    F.add (F.mul (F.add F.one d) (F.add θ F.one)) (F.neg F.one) = F.add (F.mul θ (F.add F.one d)) d := by
  rw [F.mul_add, F.mul_one, F.mul_comm (F.add F.one d) θ, F.add_assoc, F.add_comm (F.add F.one d) (F.neg F.one),
    ← F.add_assoc (F.neg F.one) F.one d, F.add_comm (F.neg F.one) F.one, F.add_neg, zero_add]

/-- HIGHAM'S LEMMA 3.1. `|δ_i| ≤ u`, `0 ≤ u`, `m + k u = 1`, `0 ≤ m`: `m·|Π(1 + δ_i) − 1| ≤ k u`. -/
theorem gamma_prod (F : OF α) {u : α} (hu : F.le F.zero u) :
    ∀ (ds : List α) (m : α), (∀ d, List.Mem d ds → F.le (F.abs d) u) → F.le F.zero m →
      F.add m (cnt F u ds) = F.one →
      F.le (F.mul m (F.abs (F.add (prod1 F ds) (F.neg F.one)))) (cnt F u ds)
  | [], m, _, _, _ => by
    show F.le (F.mul m (F.abs (F.add F.one (F.neg F.one)))) F.zero
    rw [F.add_neg, F.abs_zero, F.mul_zero]; exact F.le_refl _
  | d :: ds, m, hds, hm, hsum => by
    show F.le (F.mul m (F.abs (F.add (F.mul (F.add F.one d) (prod1 F ds)) (F.neg F.one)))) (F.add u (cnt F u ds))
    let c := cnt F u ds
    let m1 := F.add m u
    have hm1 : F.add m1 c = F.one := by
      show F.add (F.add m u) (cnt F u ds) = F.one
      rw [F.add_assoc]; exact hsum
    have hm1n : F.le F.zero m1 := by
      have := F.add_le_add hm hu; rw [F.add_zero] at this; exact this
    have ih := gamma_prod F hu ds m1 (fun d' hd' => hds d' (List.Mem.tail d hd')) hm1n hm1
    -- P = θ + 1 with θ = P − 1
    let θ := F.add (prod1 F ds) (F.neg F.one)
    have hP : prod1 F ds = F.add θ F.one := by
      show prod1 F ds = F.add (F.add (prod1 F ds) (F.neg F.one)) F.one
      rw [F.add_assoc, F.add_comm (F.neg F.one) F.one, F.add_neg, F.add_zero]
    rw [hP, step_identity, F.add_comm u c]
    exact gamma_step F hu (cnt_nonneg F hu ds) (hds d (.head _)) hm1 rfl hm ih

/-! ## Lemma 8.4, sequential: an accumulated sum in the rounding model, telescoped -/

/-- `Π_{j<k} (1 + δ_j)`. -/
def Pd (F : OF α) (δ : Nat → α) : Nat → α
  | 0 => F.one
  | k + 1 => F.mul (Pd F δ k) (F.add F.one (δ k))

/-- `Σ_{k<n} p_k (1 + ε_k) Π_{j<k} (1 + δ_j)`. -/
def Sm (F : OF α) (p ε δ : Nat → α) : Nat → α
  | 0 => F.zero
  | k + 1 => F.add (Sm F p ε δ k) (F.mul (F.mul (p k) (F.add F.one (ε k))) (Pd F δ k))

/-- THE TELESCOPE. Step `k` computes `s_{k+1}` from `s_k` by subtracting the product `p_k` rounded as
`p_k (1 + ε_k)` (the first model) and rounding the difference as `s_{k+1}(1 + δ_k) = s_k − p_k(1 + ε_k)` (the second
model, `fl(x − y) = (x − y)/(1 + δ)`, valid for IEEE): then `s_0 = s_n Π_{j<n}(1 + δ_j) + Σ_{k<n} p_k(1 + ε_k)
Π_{j<k}(1 + δ_j)` — every term of the exact sum carries its own product of rounding factors. -/
theorem telescope (F : OF α) (s p ε δ : Nat → α)
    (step : ∀ k, F.mul (s (k + 1)) (F.add F.one (δ k)) = F.add (s k) (F.neg (F.mul (p k) (F.add F.one (ε k))))) :
    ∀ n, s 0 = F.add (F.mul (s n) (Pd F δ n)) (Sm F p ε δ n)
  | 0 => by show s 0 = F.add (F.mul (s 0) F.one) F.zero; rw [F.mul_one, F.add_zero]
  | n + 1 => by
    rw [telescope F s p ε δ step n]
    show F.add (F.mul (s n) (Pd F δ n)) (Sm F p ε δ n) =
      F.add (F.mul (s (n + 1)) (F.mul (Pd F δ n) (F.add F.one (δ n))))
        (F.add (Sm F p ε δ n) (F.mul (F.mul (p n) (F.add F.one (ε n))) (Pd F δ n)))
    -- s_n = s_{n+1}(1 + δ_n) + p_n(1 + ε_n)
    have hs : s n = F.add (F.mul (s (n + 1)) (F.add F.one (δ n))) (F.mul (p n) (F.add F.one (ε n))) := by
      rw [step n, F.add_assoc, F.add_comm (F.neg _) _, F.add_neg, F.add_zero]
    rw [hs, add_mul, F.mul_comm (Pd F δ n) (F.add F.one (δ n)), ← F.mul_assoc, F.add_assoc,
      F.add_comm (F.mul (F.mul (p n) (F.add F.one (ε n))) (Pd F δ n)) (Sm F p ε δ n)]

/-! ## From the factors to Higham's componentwise bound -/

/-- `0 ≤ λ`, `λ ≠ 0`, `λa ≤ λb` ⇒ `a ≤ b`. -/
theorem cancel_pos (F : OF α) {lam a b : α} (hl : F.le F.zero lam) (hne : lam ≠ F.zero)
    (h : F.le (F.mul lam a) (F.mul lam b)) : F.le a b := by
  cases F.le_total a b with
  | inl hab => exact hab
  | inr hba =>
    have h2 := F.le_antisymm h (F.mul_le_mul_left hl hba)
    have h3 : F.mul lam (F.add a (F.neg b)) = F.zero := by
      rw [F.mul_add, mul_neg, h2, F.add_neg]
    cases F.mul_eq_zero h3 with
    | inl h0 => exact absurd h0 hne
    | inr h0 =>
      have := eq_neg_of_add F h0
      rw [F.neg_neg] at this
      rw [this]; exact F.le_refl b

/-- FEWER FACTORS, THE SAME BOUND, AND `γ` AS A NUMBER. `m_k·|θ| ≤ c_k` (Lemma 3.1 for `k` factors), `c_k ≤ C`,
`0 ≤ M ≤ m_k`, `M ≠ 0`, and `g·M = C` (the kernel's `g = N u /(1 − N u)` with `M = 1 − N u`, `C = N u`): `|θ| ≤ g`. -/
theorem gamma_as_number (F : OF α) {mk ck M C g θ : α} (h : F.le (F.mul mk (F.abs θ)) ck) (hck : F.le ck C)
    (hM : F.le F.zero M) (hMk : F.le M mk) (hne : M ≠ F.zero) (hg : F.mul g M = C) : F.le (F.abs θ) g := by
  have h1 : F.le (F.mul M (F.abs θ)) (F.mul mk (F.abs θ)) := by
    rw [F.mul_comm M _, F.mul_comm mk _]; exact F.mul_le_mul_left (F.abs_nonneg θ) hMk
  have h2 : F.le (F.mul M (F.abs θ)) (F.mul M g) := by
    rw [F.mul_comm M g, hg]; exact F.le_trans h1 (F.le_trans h hck)
  exact cancel_pos F hM hne h2

/-- AN ENTRY'S BACKWARD ERROR. The computed entry satisfies `c = Σ_k q_k (1 + θ_k)` (the telescope with the pivot's
term among the `q_k`, every `1 + θ_k` a product of rounding factors), `|θ_k| ≤ g`: `|Σ_k q_k − c| ≤ g Σ_k |q_k|` —
with `q_k = r_ki r_kj` this is `|D_ij| ≤ g (|R|ᵀ|R|)_ij`, the premise of `ZRound.chol_lower`. -/
theorem entry_backward (F : OF α) (l : List Nat) (q θ : Nat → α) (c g : α)
    (hc : c = S F l (fun k => F.mul (q k) (F.add F.one (θ k))))
    (hθ : ∀ k, List.Mem k l → F.le (F.abs (θ k)) g) :
    F.le (F.abs (F.add (S F l q) (F.neg c))) (F.mul g (S F l (fun k => F.abs (q k)))) := by
  have e : F.add (S F l q) (F.neg c) = F.neg (S F l (fun k => F.mul (q k) (θ k))) := by
    rw [hc, ← S_neg F _ l, ← S_add F _ _ l, ← ZFloatPath.S_neg F _ l]
    have := S_congr F l (fun k _ => show F.add (q k) (F.neg (F.mul (q k) (F.add F.one (θ k)))) =
        F.neg (F.mul (q k) (θ k)) by
      rw [F.mul_add, F.mul_one]
      apply eq_neg_of_add F
      rw [F.add_assoc, F.add_comm (F.neg (F.add (q k) (F.mul (q k) (θ k)))) (F.mul (q k) (θ k)), ← F.add_assoc,
        F.add_neg])
    exact this
  rw [e, F.abs_neg]
  apply F.le_trans (abs_S F _ l)
  rw [← S_mul F g _ l]
  exact S_le F l (fun k hk => by
    show F.le (F.abs (F.mul (q k) (θ k))) (F.mul g (F.abs (q k)))
    rw [F.abs_mul, F.mul_comm g _]
    exact F.mul_le_mul_left (F.abs_nonneg _) (hθ k hk))

/-! ## The capstone: one entry of a floating Cholesky -/

/-- The list `[δ_{k−1}, …, δ_0]`. -/
def dl (δ : Nat → α) : Nat → List α
  | 0 => []
  | k + 1 => δ k :: dl δ k

theorem Pd_eq (F : OF α) (δ : Nat → α) : ∀ k, Pd F δ k = prod1 F (dl δ k)
  | 0 => rfl
  | k + 1 => by
    show F.mul (Pd F δ k) (F.add F.one (δ k)) = F.mul (F.add F.one (δ k)) (prod1 F (dl δ k))
    rw [Pd_eq F δ k, F.mul_comm]

/-- `k·u`. -/
def natu (F : OF α) (u : α) : Nat → α
  | 0 => F.zero
  | k + 1 => F.add u (natu F u k)

theorem cnt_len (F : OF α) (u : α) : ∀ ds : List α, cnt F u ds = natu F u ds.length
  | [] => rfl
  | _ :: ds => by show F.add u (cnt F u ds) = F.add u (natu F u ds.length); rw [cnt_len F u ds]

theorem natu_mono (F : OF α) {u : α} (hu : F.le F.zero u) : ∀ a b : Nat, a ≤ b → F.le (natu F u a) (natu F u b)
  | a, 0, h => by rw [Nat.le_zero.mp h]; exact F.le_refl _
  | a, b + 1, h => by
    cases Nat.lt_or_ge a (b + 1) with
    | inl hlt =>
      have ih := natu_mono F hu a b (Nat.le_of_lt_succ hlt)
      show F.le (natu F u a) (F.add u (natu F u b))
      have := F.add_le_add hu ih; rw [zero_add] at this; exact this
    | inr hge => rw [Nat.le_antisymm h hge]; exact F.le_refl _

theorem dl_len (δ : Nat → α) : ∀ k, (dl δ k).length = k
  | 0 => rfl
  | k + 1 => by show (dl δ k).length + 1 = k + 1; rw [dl_len δ k]

/-- THE GAMMA OF A LIST. `|d| ≤ u` on a list of length `≤ N`, `M + N u = 1`, `0 ≤ M`, `M ≠ 0`, `g M = N u`:
`prod1 ds = 1 + θ` with `|θ| ≤ g`. -/
theorem list_gamma (F : OF α) {u M g : α} (N : Nat) (hu : F.le F.zero u) (ds : List α)
    (hds : ∀ d, List.Mem d ds → F.le (F.abs d) u) (hlen : ds.length ≤ N)
    (hM : F.le F.zero M) (hMN : F.add M (natu F u N) = F.one) (hne : M ≠ F.zero) (hg : F.mul g M = natu F u N) :
    F.le (F.abs (F.add (prod1 F ds) (F.neg F.one))) g := by
  let ck := cnt F u ds
  let mk := F.add M (F.add (natu F u N) (F.neg ck))   -- 1 − ck
  have hck : F.le ck (natu F u N) := by show F.le (cnt F u ds) _; rw [cnt_len]; exact natu_mono F hu _ _ hlen
  have hmk : F.add mk ck = F.one := by
    show F.add (F.add M (F.add (natu F u N) (F.neg ck))) ck = F.one
    rw [F.add_assoc, F.add_assoc, F.add_comm (F.neg ck) ck, F.add_neg, F.add_zero, hMN]
  have hMmk : F.le M mk := by
    have h0 : F.le F.zero (F.add (natu F u N) (F.neg ck)) := sub_nonneg_of_le F hck
    have := F.add_le_add (F.le_refl M) h0; rw [F.add_zero] at this; exact this
  have hmk0 : F.le F.zero mk := F.le_trans hM hMmk
  have h := gamma_prod F hu ds mk hds hmk0 hmk
  exact gamma_as_number F h hck hM hMmk hne hg

/-- The indices `[k−1, …, 0]` (our own list: core's `List.range` lemmas carry `propext`). -/
def idx : Nat → List Nat
  | 0 => []
  | k + 1 => k :: idx k

theorem mem_idx : ∀ (n k : Nat), List.Mem k (idx n) → k < n
  | 0, _, h => by cases h
  | n + 1, k, h => by
    cases h with
    | head => exact Nat.lt_succ_self n
    | tail _ h' => exact Nat.lt_trans (mem_idx n k h') (Nat.lt_succ_self n)

theorem len_app : ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add _).symm
  | _ :: xs, ys => by
    show (xs ++ ys).length + 1 = xs.length + 1 + ys.length
    rw [len_app xs ys, Nat.succ_add]

theorem mem_app {d : α} : ∀ (xs ys : List α), List.Mem d (xs ++ ys) → List.Mem d xs ∨ List.Mem d ys
  | [], _, h => Or.inr h
  | x :: xs, ys, h => by
    cases h with
    | head => exact Or.inl (.head _)
    | tail _ h' =>
      cases mem_app xs ys h' with
      | inl h1 => exact Or.inl (.tail _ h1)
      | inr h2 => exact Or.inr h2

theorem mem_dl (F : OF α) {δ : Nat → α} {u : α} (hδ : ∀ k, F.le (F.abs (δ k)) u) :
    ∀ k d, List.Mem d (dl δ k) → F.le (F.abs d) u
  | 0, _, h => by cases h
  | k + 1, d, h => by
    cases h with
    | head => exact hδ k
    | tail _ h' => exact mem_dl F hδ k d h'

theorem Sm_eq (F : OF α) (p ε δ : Nat → α) : ∀ n,
    Sm F p ε δ n = S F (idx n) (fun k => F.mul (F.mul (p k) (F.add F.one (ε k))) (Pd F δ k))
  | 0 => rfl
  | n + 1 => by
    show F.add (Sm F p ε δ n) _ = F.add _ (S F (idx n) _)
    rw [Sm_eq F p ε δ n, F.add_comm]

/-- ONE ENTRY OF A FLOATING CHOLESKY (Higham, Thm 10.3, componentwise, for sequential accumulation). The entry
starts from `s_0 = a` (the matrix entry), subtracts `n` products `p_k` in order (each rounded, `|ε_k|, |δ_k| ≤ u`),
and ends at `s_n = q·prod1 pf` — the pivot term `q` (`r_ii r_ij` for a division, `r_jj²` for the square root) with its
own rounding factors `pf` (`|·| ≤ u`; one for a division, two for `√`, two for a reciprocal and a product). With
`n + 1 ≤ N`, `n + |pf| ≤ N`, `M + N u = 1`, `g M = N u` (`g = γ_N`): `|(Σ_k p_k + q) − a| ≤ g (Σ_k |p_k| + |q|)`. -/
theorem cholesky_entry (F : OF α) (s p ε δ : Nat → α) (q u M g : α) (n N : Nat) (pf : List α)
    (hu : F.le F.zero u)
    (step : ∀ k, F.mul (s (k + 1)) (F.add F.one (δ k)) = F.add (s k) (F.neg (F.mul (p k) (F.add F.one (ε k)))))
    (hpiv : s n = F.mul q (prod1 F pf))
    (hε : ∀ k, F.le (F.abs (ε k)) u) (hδ : ∀ k, F.le (F.abs (δ k)) u) (hpf : ∀ d, List.Mem d pf → F.le (F.abs d) u)
    (hN1 : n + 1 ≤ N) (hN2 : n + pf.length ≤ N)
    (hM : F.le F.zero M) (hMN : F.add M (natu F u N) = F.one) (hne : M ≠ F.zero) (hg : F.mul g M = natu F u N) :
    F.le (F.abs (F.add (F.add (S F (idx n) p) q) (F.neg (s 0))))
      (F.mul g (F.add (S F (idx n) (fun k => F.abs (p k))) (F.abs q))) := by
  have ht := telescope F s p ε δ step n
  rw [hpiv, F.mul_assoc, Sm_eq] at ht
  -- the pivot's coefficient: 1 + θp, |θp| ≤ g
  let θp := F.add (F.mul (prod1 F pf) (Pd F δ n)) (F.neg F.one)
  have hθp : F.le (F.abs θp) g := by
    have e : F.mul (prod1 F pf) (Pd F δ n) = prod1 F (pf ++ dl δ n) := by
      rw [Pd_eq]
      clear hpiv hpf hN2 ht
      induction pf with
      | nil => show F.mul F.one _ = _; exact ZRound.one_mul F _
      | cons d ds ih =>
        show F.mul (F.mul (F.add F.one d) (prod1 F ds)) _ = F.mul (F.add F.one d) (prod1 F (ds ++ dl δ n))
        rw [F.mul_assoc, ih]
    show F.le (F.abs (F.add (F.mul (prod1 F pf) (Pd F δ n)) (F.neg F.one))) g
    rw [e]
    apply list_gamma F N hu _ _ _ hM hMN hne hg
    · intro d hd
      cases mem_app pf (dl δ n) hd with
      | inl h => exact hpf d h
      | inr h => exact mem_dl F hδ n d h
    · rw [len_app, dl_len, Nat.add_comm]; exact hN2
  -- each product's coefficient: 1 + θk, |θk| ≤ g
  let θk := fun k => F.add (F.mul (F.add F.one (ε k)) (Pd F δ k)) (F.neg F.one)
  have hθk : ∀ k, List.Mem k (idx n) → F.le (F.abs (θk k)) g := by
    intro k hk
    have hkn : k < n := mem_idx n k hk
    show F.le (F.abs (F.add (F.mul (F.add F.one (ε k)) (Pd F δ k)) (F.neg F.one))) g
    have e : F.mul (F.add F.one (ε k)) (Pd F δ k) = prod1 F (ε k :: dl δ k) := by rw [Pd_eq]; rfl
    rw [e]
    apply list_gamma F N hu _ _ _ hM hMN hne hg
    · intro d hd
      cases hd with
      | head => exact hε k
      | tail _ h => exact mem_dl F hδ k d h
    · show (dl δ k).length + 1 ≤ N
      rw [dl_len]
      exact Nat.le_trans (Nat.le_trans hkn (Nat.le_succ n)) hN1
  -- coefficient = 1 + θ, as written
  have c1 : ∀ x : α, F.add (F.add x (F.neg F.one)) F.one = x := fun x => by
    rw [F.add_assoc, F.add_comm (F.neg F.one) F.one, F.add_neg, F.add_zero]
  have hsum : S F (idx n) (fun k => F.mul (F.mul (p k) (F.add F.one (ε k))) (Pd F δ k)) =
      S F (idx n) (fun k => F.mul (p k) (F.add F.one (θk k))) :=
    S_congr F (idx n) (fun k _ => by
      show F.mul (F.mul (p k) (F.add F.one (ε k))) (Pd F δ k) =
        F.mul (p k) (F.add F.one (F.add (F.mul (F.add F.one (ε k)) (Pd F δ k)) (F.neg F.one)))
      rw [F.add_comm F.one (F.add (F.mul (F.add F.one (ε k)) (Pd F δ k)) (F.neg F.one)), c1, F.mul_assoc])
  have hpv : F.mul q (F.mul (prod1 F pf) (Pd F δ n)) = F.mul q (F.add F.one θp) := by
    show _ = F.mul q (F.add F.one (F.add (F.mul (prod1 F pf) (Pd F δ n)) (F.neg F.one)))
    rw [F.add_comm F.one (F.add (F.mul (prod1 F pf) (Pd F δ n)) (F.neg F.one)), c1]
  rw [hsum, hpv] at ht
  -- (Σp + q) − s0 = (Σp − Σp(1+θ)) + (q − q(1+θp))
  have hbk := entry_backward F (idx n) p θk _ g rfl hθk
  have hq : F.le (F.abs (F.add q (F.neg (F.mul q (F.add F.one θp))))) (F.mul g (F.abs q)) := by
    have e : F.add q (F.neg (F.mul q (F.add F.one θp))) = F.neg (F.mul q θp) := by
      apply eq_neg_of_add F
      rw [F.mul_add, F.mul_one, F.add_assoc, F.add_comm (F.neg (F.add q (F.mul q θp))) (F.mul q θp),
        ← F.add_assoc, F.add_neg]
    rw [e, F.abs_neg, F.abs_mul, F.mul_comm g _]
    exact F.mul_le_mul_left (F.abs_nonneg _) hθp
  have split : F.add (F.add (S F (idx n) p) q) (F.neg (s 0)) =
      F.add (F.add (S F (idx n) p) (F.neg (S F (idx n) (fun k => F.mul (p k) (F.add F.one (θk k))))))
            (F.add q (F.neg (F.mul q (F.add F.one θp)))) := by
    rw [ht]
    -- −(B + A) = −B + −A, then regroup
    have nab : ∀ a b : α, F.neg (F.add a b) = F.add (F.neg a) (F.neg b) := fun a b => by
      have h0 : F.add (F.add (F.neg a) (F.neg b)) (F.add a b) = F.zero := by
        rw [F.add_assoc (F.neg a) (F.neg b) (F.add a b), F.add_comm a b, ← F.add_assoc (F.neg b) b a,
          F.add_comm (F.neg b) b, F.add_neg, zero_add, F.add_comm (F.neg a) a, F.add_neg]
      exact (eq_neg_of_add F h0).symm
    rw [F.add_comm (F.mul q (F.add F.one θp)) _, nab, add4 F]
  rw [split, F.mul_add g (S F (idx n) (fun k => F.abs (p k))) (F.abs q)]
  exact F.le_trans (F.abs_add _ _) (F.add_le_add hbk hq)

/-! ## Any order: a summation TREE (blocked BLAS, FMA, vector lanes — every order is some tree) -/

/-- A summation tree: a leaf is a term `x` read with its own rounding `1 + ε` (`ε = 0` when exact); a node adds its
children and rounds the sum, `(l + r)(1 + δ)`. -/
inductive Tr (α : Type) where
  | leaf (x ε : α) : Tr α
  | node (l r : Tr α) (δ : α) : Tr α

/-- What the machine computes (the rounding model, first form, at every operation). -/
def val (F : OF α) : Tr α → α
  | .leaf x ε => F.mul x (F.add F.one ε)
  | .node l r δ => F.mul (F.add (val F l) (val F r)) (F.add F.one δ)

/-- The exact sum of the leaves. -/
def ex (F : OF α) : Tr α → α
  | .leaf x _ => x
  | .node l r _ => F.add (ex F l) (ex F r)

/-- `Σ |leaf|`. -/
def absum (F : OF α) : Tr α → α
  | .leaf x _ => F.abs x
  | .node l r _ => F.add (absum F l) (absum F r)

/-- The number of leaves. -/
def nleaves : Tr α → Nat
  | .leaf _ _ => 1
  | .node l r _ => nleaves l + nleaves r

/-- Every rounding of the tree is at most `u`. -/
def small (F : OF α) (u : α) : Tr α → Prop
  | .leaf _ ε => F.le (F.abs ε) u
  | .node l r δ => small F u l ∧ small F u r ∧ F.le (F.abs δ) u

theorem nleaves_pos : ∀ T : Tr α, 1 ≤ nleaves T
  | .leaf _ _ => Nat.le_refl 1
  | .node l _ _ => Nat.le_trans (nleaves_pos l) (Nat.le_add_right _ _)

theorem absum_nonneg (F : OF α) : ∀ T : Tr α, F.le F.zero (absum F T)
  | .leaf x _ => F.abs_nonneg x
  | .node l r _ => by
    have := F.add_le_add (absum_nonneg F l) (absum_nonneg F r); rw [F.add_zero] at this; exact this

theorem abs_ex_le (F : OF α) : ∀ T : Tr α, F.le (F.abs (ex F T)) (absum F T)
  | .leaf x _ => F.le_refl _
  | .node l r _ => F.le_trans (F.abs_add _ _) (F.add_le_add (abs_ex_le F l) (abs_ex_le F r))

/-- `m_H = 1 − H u` as an element: `M + natu H = 1`. Monotone: a smaller count has a larger `m`. -/
theorem m_mono (F : OF α) {u M M' : α} {h H : Nat} (hu : F.le F.zero u) (hh : h ≤ H)
    (hM : F.add M (natu F u H) = F.one) (hM' : F.add M' (natu F u h) = F.one) : F.le M M' := by
  have hn := natu_mono F hu h H hh
  -- M = 1 − natu H ≤ 1 − natu h = M'
  have e1 : M = F.add F.one (F.neg (natu F u H)) := by
    rw [← hM, F.add_assoc, F.add_neg, F.add_zero]
  have e2 : M' = F.add F.one (F.neg (natu F u h)) := by
    rw [← hM', F.add_assoc, F.add_neg, F.add_zero]
  rw [e1, e2]
  apply F.add_le_add (F.le_refl _)
  -- −natu H ≤ −natu h
  have := F.add_le_add (F.add_le_add hn (F.le_refl (F.neg (natu F u h)))) (F.le_refl (F.neg (natu F u H)))
  rw [F.add_neg, zero_add, F.add_comm (natu F u H) _, F.add_assoc, F.add_neg, F.add_zero] at this
  exact this

/-- THE TREE'S ERROR. `small u T`, `nleaves T ≤ H`, `M + H u = 1`, `0 ≤ M`: `M·|val T − ex T| ≤ H u·Σ|leaves|` —
any order of summation, `γ_H` in the multiplied form. -/
theorem tree_err (F : OF α) {u : α} (hu : F.le F.zero u) :
    ∀ (T : Tr α) (H : Nat) (M : α), small F u T → nleaves T ≤ H → F.le F.zero M →
      F.add M (natu F u H) = F.one →
      F.le (F.mul M (F.abs (F.add (val F T) (F.neg (ex F T))))) (F.mul (natu F u H) (absum F T))
  | .leaf x ε, H, M, hs, hH, hM, hMH => by
    show F.le (F.mul M (F.abs (F.add (F.mul x (F.add F.one ε)) (F.neg x)))) (F.mul (natu F u H) (F.abs x))
    have e : F.add (F.mul x (F.add F.one ε)) (F.neg x) = F.mul x ε := by
      rw [F.mul_add, F.mul_one, F.add_comm x _, F.add_assoc, F.add_neg, F.add_zero]
    rw [e, F.abs_mul]
    -- M |x| |ε| ≤ |x| u ≤ (H u)|x|  (M ≤ 1, |ε| ≤ u, u ≤ H u)
    have hM1 : F.le M F.one := by
      have := F.add_le_add (F.le_refl M) (natu_mono F hu 0 H (Nat.zero_le H)); rw [hMH] at this
      show F.le M F.one; rw [show natu F u 0 = F.zero from rfl, F.add_zero] at this; exact this
    have huH : F.le u (natu F u H) := by
      have h1 := natu_mono F hu 1 H hH
      have : natu F u 1 = u := by show F.add u F.zero = u; rw [F.add_zero]
      rw [this] at h1; exact h1
    have s1 : F.le (F.mul M (F.mul (F.abs x) (F.abs ε))) (F.mul (F.abs x) (F.abs ε)) := by
      rw [F.mul_comm M _]; have := F.mul_le_mul_left (F.mul_nonneg (F.abs_nonneg x) (F.abs_nonneg ε)) hM1
      rw [F.mul_one] at this; exact this
    have s2 : F.le (F.mul (F.abs x) (F.abs ε)) (F.mul (natu F u H) (F.abs x)) := by
      rw [F.mul_comm (natu F u H) _]
      exact F.mul_le_mul_left (F.abs_nonneg x) (F.le_trans hs huH)
    exact F.le_trans s1 s2
  | .node l r δ, H, M, hs, hH, hM, hMH => by
    obtain ⟨hsl, hsr, hδ⟩ := hs
    -- H = H' + 1 (a node has at least two leaves)
    cases H with
    | zero =>
      have := Nat.le_trans (Nat.add_le_add (nleaves_pos l) (nleaves_pos r)) hH
      exact absurd this (by decide)
    | succ H' =>
    let M' := F.add M u
    have hM'H : F.add M' (natu F u H') = F.one := by
      show F.add (F.add M u) (natu F u H') = F.one; rw [F.add_assoc]; exact hMH
    have hM' : F.le F.zero M' := by have := F.add_le_add hM hu; rw [F.add_zero] at this; exact this
    have hl : nleaves l ≤ H' := Nat.le_of_succ_le_succ
      (Nat.le_trans (Nat.add_le_add_left (nleaves_pos r) (nleaves l)) hH)
    have hr1 : nleaves r + 1 ≤ nleaves l + nleaves r := by
      rw [Nat.add_comm (nleaves l) (nleaves r)]; exact Nat.add_le_add_left (nleaves_pos l) (nleaves r)
    have hr : nleaves r ≤ H' := Nat.le_of_succ_le_succ (Nat.le_trans hr1 hH)
    have ihl := tree_err F hu l H' M' hsl hl hM' hM'H
    have ihr := tree_err F hu r H' M' hsr hr hM' hM'H
    let El := F.add (val F l) (F.neg (ex F l))
    let Er := F.add (val F r) (F.neg (ex F r))
    let A := F.add (absum F l) (absum F r)
    -- val − ex = (El + Er)(1 + δ) + (ex_l + ex_r) δ
    have e : F.add (val F (.node l r δ)) (F.neg (ex F (.node l r δ))) =
        F.add (F.mul (F.add El Er) (F.add F.one δ)) (F.mul (F.add (ex F l) (ex F r)) δ) := by
      show F.add (F.mul (F.add (val F l) (val F r)) (F.add F.one δ)) (F.neg (F.add (ex F l) (ex F r))) = _
      -- both sides equal (val_l + val_r)(1+δ) − (ex_l + ex_r)
      have cancel : ∀ v e : α, F.add (F.add v (F.neg e)) e = v := fun v e => by
        rw [F.add_assoc, F.add_comm (F.neg e) e, F.add_neg, F.add_zero]
      have hv : F.add (val F l) (val F r) = F.add (F.add El Er) (F.add (ex F l) (ex F r)) := by
        show _ = F.add (F.add (F.add (val F l) (F.neg (ex F l))) (F.add (val F r) (F.neg (ex F r))))
          (F.add (ex F l) (ex F r))
        rw [add4 F, cancel, cancel]
      have ealg : ∀ A X d : α, F.add (F.mul (F.add A X) (F.add F.one d)) (F.neg X) =
          F.add (F.mul A (F.add F.one d)) (F.mul X d) := by
        intro A X d
        rw [add_mul F A X (F.add F.one d), F.mul_add X F.one d, F.mul_one,
          F.add_assoc (F.mul A (F.add F.one d)) (F.add X (F.mul X d)) (F.neg X), F.add_comm X (F.mul X d),
          F.add_assoc (F.mul X d) X (F.neg X), F.add_neg, F.add_zero]
      rw [hv]
      exact ealg (F.add El Er) (F.add (ex F l) (ex F r)) δ
    rw [e]
    have hE : F.le (F.abs (F.add (F.mul (F.add El Er) (F.add F.one δ)) (F.mul (F.add (ex F l) (ex F r)) δ)))
        (F.add (F.mul (F.add (F.abs El) (F.abs Er)) (F.add F.one u)) (F.mul A u)) := by
      apply F.le_trans (F.abs_add _ _)
      rw [F.abs_mul, F.abs_mul]
      apply F.add_le_add
      · rw [F.mul_comm (F.abs (F.add El Er)) _, F.mul_comm _ (F.add F.one u)]
        apply F.le_trans (F.mul_le_mul_left (F.abs_nonneg _) (F.abs_add El Er))
        rw [F.mul_comm (F.abs (F.add F.one δ)) _, F.mul_comm (F.add F.one u) _]
        exact F.mul_le_mul_left (F.add_le_add (F.abs_nonneg El) (F.abs_nonneg Er) |> fun h => by
          rw [F.add_zero] at h; exact h) (abs_one_add F hδ)
      · apply F.le_trans (F.mul_le_mul_left (F.abs_nonneg _) hδ)
        rw [F.mul_comm (F.abs _) u, F.mul_comm A u]
        exact F.mul_le_mul_left hu (F.le_trans (F.abs_add _ _) (F.add_le_add (abs_ex_le F l) (abs_ex_le F r)))
    apply F.le_trans (F.mul_le_mul_left hM hE)
    rw [F.mul_add]
    -- M(1+u) ≤ M'  (key identity with c = natu H'),  M ≤ 1
    have hk := key_identity F hM'H rfl
    have hcu : F.le F.zero (F.add (F.mul (natu F u H') u) (F.mul u u)) := by
      have := F.add_le_add (F.mul_nonneg (natu_mono F hu 0 H' (Nat.zero_le H') |> fun h => by
        exact h) hu) (F.sq_nonneg u)
      rw [F.add_zero] at this; exact this
    have hA : F.le (F.mul M (F.add F.one u)) M' := by
      have := F.add_le_add (F.le_refl (F.mul M (F.add F.one u))) hcu; rw [F.add_zero, hk] at this; exact this
    have s1 : F.le (F.mul M (F.mul (F.add (F.abs El) (F.abs Er)) (F.add F.one u)))
        (F.mul M' (F.add (F.abs El) (F.abs Er))) := by
      rw [F.mul_comm (F.add (F.abs El) (F.abs Er)) _, ← F.mul_assoc, F.mul_comm M' _]
      rw [F.mul_comm (F.mul M (F.add F.one u)) _]
      exact F.mul_le_mul_left (by have := F.add_le_add (F.abs_nonneg El) (F.abs_nonneg Er); rw [F.add_zero] at this; exact this) hA
    have s2 : F.le (F.mul M' (F.add (F.abs El) (F.abs Er))) (F.mul (natu F u H') A) := by
      rw [F.mul_add, F.mul_add]; exact F.add_le_add ihl ihr
    have hM1 : F.le M F.one := by
      have := F.add_le_add (F.le_refl M) (natu_mono F hu 0 (H' + 1) (Nat.zero_le _)); rw [hMH] at this
      rw [show natu F u 0 = F.zero from rfl, F.add_zero] at this; exact this
    have hA0 : F.le F.zero A := by
      have := F.add_le_add (absum_nonneg F l) (absum_nonneg F r); rw [F.add_zero] at this; exact this
    have s3 : F.le (F.mul M (F.mul A u)) (F.mul u A) := by
      have hAu : F.le F.zero (F.mul A u) := F.mul_nonneg hA0 hu
      have := F.mul_le_mul_left hAu hM1
      rw [F.mul_one, F.mul_comm (F.mul A u) M] at this
      rw [F.mul_comm u A]; exact this
    have fin := F.add_le_add (F.le_trans s1 s2) s3
    show F.le _ (F.mul (F.add u (natu F u H')) A)
    rw [add_mul F u (natu F u H') A, F.add_comm (F.mul u A) (F.mul (natu F u H') A)]
    exact fin

theorem neg_add2 (F : OF α) (a b : α) : F.neg (F.add a b) = F.add (F.neg a) (F.neg b) := by
  have h0 : F.add (F.add (F.neg a) (F.neg b)) (F.add a b) = F.zero := by
    rw [F.add_assoc (F.neg a) (F.neg b) (F.add a b), F.add_comm a b, ← F.add_assoc (F.neg b) b a,
      F.add_comm (F.neg b) b, F.add_neg, zero_add, F.add_comm (F.neg a) a, F.add_neg]
  exact (eq_neg_of_add F h0).symm

/-- The closing algebra: `Dn ≤ g2·qv + G·((Sv + Dn) + Pv)`, `qv, Pv ≤ Sv`, `MG + G = 1`, `g·MG = g2 + 2G` ⇒
`Dn ≤ g·Sv` (the `|D|` on the right absorbed). -/
theorem final_alg (F : OF α) {Dn Sv qv Pv g2 G MG g : α} (hg2 : F.le F.zero g2) (hG0 : F.le F.zero G)
    (hMG0 : F.le F.zero MG) (hneG : MG ≠ F.zero) (hMG : F.add MG G = F.one)
    (hg : F.mul g MG = F.add g2 (F.add G G)) (hq : F.le qv Sv) (hP : F.le Pv Sv)
    (h : F.le Dn (F.add (F.mul g2 qv) (F.mul G (F.add (F.add Sv Dn) Pv)))) : F.le Dn (F.mul g Sv) := by
  have h1 : F.le Dn (F.add (F.mul g2 Sv) (F.mul G (F.add (F.add Sv Dn) Sv))) :=
    F.le_trans h (F.add_le_add (F.mul_le_mul_left hg2 hq)
      (F.mul_le_mul_left hG0 (F.add_le_add (F.le_refl _) hP)))
  have e : F.add (F.mul g2 Sv) (F.mul G (F.add (F.add Sv Dn) Sv)) =
      F.add (F.mul G Dn) (F.mul (F.add g2 (F.add G G)) Sv) := by
    rw [F.mul_add G (F.add Sv Dn) Sv, F.mul_add G Sv Dn, add_mul F g2 (F.add G G) Sv, add_mul F G G Sv]
    -- g2S + ((GS + GD) + GS)  =  GD + (g2S + (GS + GS))
    rw [F.add_assoc (F.mul G Sv) (F.mul G Dn) (F.mul G Sv), F.add_comm (F.mul G Dn) (F.mul G Sv),
      ← F.add_assoc (F.mul G Sv) (F.mul G Sv) (F.mul G Dn), ← F.add_assoc (F.mul g2 Sv),
      F.add_comm (F.add (F.mul g2 Sv) (F.add (F.mul G Sv) (F.mul G Sv))) (F.mul G Dn)]
  rw [e] at h1
  have e1 : F.add (F.mul G Dn) (F.mul MG Dn) = Dn := by
    rw [← add_mul F G MG Dn, F.add_comm G MG, hMG, ZRound.one_mul]
  have h2 : F.le (F.add (F.mul G Dn) (F.mul MG Dn)) (F.add (F.mul G Dn) (F.mul (F.add g2 (F.add G G)) Sv)) := by
    rw [e1]; exact h1
  have h3 := add_le_cancel F h2
  rw [← hg, F.mul_comm g MG, F.mul_assoc] at h3
  exact cancel_pos F hMG0 hneG h3

/-- ONE ENTRY OF A FLOATING CHOLESKY, ANY ORDER (closes the gap of `cholesky_entry`: blocked BLAS, FMA, vector lanes).
The entry's accumulator is a summation tree `T` over the leaves `a` and `−p_k` (`ex T = a − P`, `absum T = |a| + Pa`
with `P = Σ p_k`, `|P| ≤ Pa = Σ|p_k|`), `small u T`, `nleaves T ≤ H`; the pivot step gives `val T = q·prod1 pf` with
`|prod1 pf − 1| ≤ g2` (`list_gamma`); `G M = H u`, `M + H u = 1`; `MG + G = 1`, `MG ≠ 0`, `g·MG = g2 + 2G`:
`|(P + q) − a| ≤ g (Pa + |q|)` — Higham's componentwise bound with `g = (g2 + 2γ_H)/(1 − γ_H)` for ANY order. -/
theorem cholesky_entry_tree (F : OF α) (T : Tr α) (a P Pa q u M G MG g g2 : α) (H : Nat) (pf : List α)
    (hu : F.le F.zero u) (hs : small F u T) (hH : nleaves T ≤ H)
    (hex : ex F T = F.add a (F.neg P)) (habs : absum F T = F.add (F.abs a) Pa)
    (hPa : F.le (F.abs P) Pa)
    (hpiv : val F T = F.mul q (prod1 F pf)) (hpf : F.le (F.abs (F.add (prod1 F pf) (F.neg F.one))) g2)
    (hM : F.le F.zero M) (hMH : F.add M (natu F u H) = F.one) (hne : M ≠ F.zero) (hG : F.mul G M = natu F u H)
    (hMG0 : F.le F.zero MG) (hMG : F.add MG G = F.one) (hneG : MG ≠ F.zero)
    (hg : F.mul g MG = F.add g2 (F.add G G)) (hg2 : F.le F.zero g2) (hG0 : F.le F.zero G) :
    F.le (F.abs (F.add (F.add P q) (F.neg a))) (F.mul g (F.add Pa (F.abs q))) := by
  -- |val − ex| ≤ G (|a| + Pa)
  have herr : F.le (F.abs (F.add (val F T) (F.neg (ex F T)))) (F.mul G (F.add (F.abs a) Pa)) := by
    have h := tree_err F hu T H M hs hH hM hMH
    rw [habs, ← hG, F.mul_comm G M, F.mul_assoc] at h
    exact cancel_pos F hM hne h
  -- |q − val| ≤ g2 |q|
  have hq : F.le (F.abs (F.add q (F.neg (val F T)))) (F.mul g2 (F.abs q)) := by
    have e : F.add q (F.neg (val F T)) = F.neg (F.mul q (F.add (prod1 F pf) (F.neg F.one))) := by
      rw [hpiv, F.mul_add q (prod1 F pf) (F.neg F.one), mul_neg, F.mul_one, neg_add2, F.neg_neg,
        F.add_comm (F.neg (F.mul q (prod1 F pf))) q]
    rw [e, F.abs_neg, F.abs_mul, F.mul_comm g2 _]
    exact F.mul_le_mul_left (F.abs_nonneg q) hpf
  -- D = (q − val) + (val − ex)
  have hD : F.add (F.add P q) (F.neg a) =
      F.add (F.add q (F.neg (val F T))) (F.add (val F T) (F.neg (ex F T))) := by
    rw [F.add_assoc q (F.neg (val F T)), ← F.add_assoc (F.neg (val F T)) (val F T),
      F.add_comm (F.neg (val F T)) (val F T), F.add_neg, zero_add, hex, neg_add2, F.neg_neg,
      F.add_assoc P q (F.neg a), F.add_comm P (F.add q (F.neg a)), F.add_assoc q (F.neg a) P]
  -- |a| ≤ (Pa + |q|) + |D|
  have ha : F.le (F.abs a) (F.add (F.add Pa (F.abs q)) (F.abs (F.add (F.add P q) (F.neg a)))) := by
    have e : a = F.add (F.add P q) (F.neg (F.add (F.add P q) (F.neg a))) := by
      rw [neg_add2, F.neg_neg, ← F.add_assoc, F.add_neg, zero_add]
    have hae : F.abs a = F.abs (F.add (F.add P q) (F.neg (F.add (F.add P q) (F.neg a)))) := congrArg F.abs e
    rw [hae]
    apply F.le_trans (F.abs_add _ _)
    rw [F.abs_neg]
    exact F.add_le_add (F.le_trans (F.abs_add P q) (F.add_le_add hPa (F.le_refl _))) (F.le_refl _)
  -- |D| ≤ g2|q| + G((S + |D|) + Pa), then the closing algebra
  have hDb : F.le (F.abs (F.add (F.add P q) (F.neg a)))
      (F.add (F.mul g2 (F.abs q)) (F.mul G (F.add (F.add (F.add Pa (F.abs q)) (F.abs (F.add (F.add P q) (F.neg a)))) Pa))) := by
    rw [hD]
    apply F.le_trans (F.abs_add _ _)
    apply F.add_le_add hq
    apply F.le_trans herr
    rw [← hD]
    exact F.mul_le_mul_left hG0 (F.add_le_add ha (F.le_refl Pa))
  have hPa0 : F.le F.zero Pa := F.le_trans (F.abs_nonneg P) hPa
  have q_le : F.le (F.abs q) (F.add Pa (F.abs q)) := by
    have := F.add_le_add hPa0 (F.le_refl (F.abs q)); rw [zero_add] at this; exact this
  have Pa_le : F.le Pa (F.add Pa (F.abs q)) := by
    have := F.add_le_add (F.le_refl Pa) (F.abs_nonneg q); rw [F.add_zero] at this; exact this
  exact final_alg F hg2 hG0 hMG0 hneG hMG hg q_le Pa_le hDb

end ZHigham

#print axioms ZHigham.abs_one
#print axioms ZHigham.one_nonneg
#print axioms ZHigham.abs_one_add
#print axioms ZHigham.key_identity
#print axioms ZHigham.gamma_step
#print axioms ZHigham.cnt_nonneg
#print axioms ZHigham.step_identity
#print axioms ZHigham.gamma_prod
#print axioms ZHigham.telescope
#print axioms ZHigham.cancel_pos
#print axioms ZHigham.gamma_as_number
#print axioms ZHigham.entry_backward
#print axioms ZHigham.Pd_eq
#print axioms ZHigham.cnt_len
#print axioms ZHigham.natu_mono
#print axioms ZHigham.dl_len
#print axioms ZHigham.list_gamma
#print axioms ZHigham.mem_idx
#print axioms ZHigham.len_app
#print axioms ZHigham.mem_app
#print axioms ZHigham.mem_dl
#print axioms ZHigham.Sm_eq
#print axioms ZHigham.cholesky_entry
#print axioms ZHigham.nleaves_pos
#print axioms ZHigham.absum_nonneg
#print axioms ZHigham.abs_ex_le
#print axioms ZHigham.m_mono
#print axioms ZHigham.tree_err
#print axioms ZHigham.cholesky_entry_tree
#print axioms ZHigham.neg_add2
#print axioms ZHigham.final_alg
