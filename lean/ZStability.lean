-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
import ZRound
/-!
# ZStability — why one positive-definite matrix bounds the critical load factor over a whole box. Zero axioms.

ztl-stand's `frame.stability_lower` (2026-11-01) proves `λ < λ_cr` for every modulus in the box by proving ONE matrix
positive definite: `(1 − T) K0 + λ Σ_e N_lo,e G_e`. The step that licenses it, as quadratic forms over a list of
indices (ZNet's sums, ZRound's `qf`):
  `qf_combo`     `xᵀ(Σ_e c_e M_e)x = Σ_e c_e (xᵀ M_e x)` — the form is linear in the matrix;
  `stiff_lower`  parts `K_P ⪰ 0` with factors `p_P ≥ m`: `m·xᵀK0x ≤ xᵀK(p)x` (`K0 = Σ K_P`, `K(p) = Σ p_P K_P`);
  `geo_lower`    `G_e ⪰ 0`, `N_e ≥ N_lo,e`, `λ ≥ 0`: `λ Σ N_lo,e xᵀG_e x ≤ λ Σ N_e xᵀG_e x`;
  `stability_lower`  together: `xᵀ((1−T)K0 + λΣ N_lo G)x ≤ xᵀ(K(p) + λ K_G(N(p)))x` for every `x` — so if the left
                 matrix is positive definite, so is the right one at every `p` in the box: no buckling below `λ`.
  `witness_upper` the other side, by a WITNESS: a vector `x` with `xᵀK x + λ Σ N_hi,e xᵀG_e x ≤ 0` (`N_e ≤ N_hi,e`,
                 `G_e ⪰ 0`, `λ ≥ 0`) gives `xᵀ(K + λ K_G(N))x ≤ 0` at the true forces: `K + λK_G` is not positive
                 definite, so the critical factor is at most `λ` (ztl-stand's `stability_upper`).
What stays a premise: that `N_e(p) ≥ N_lo,e` (each a proved output range — ZNet step 4, ZFloatPath) and that the
left matrix is positive definite (ZRound's `pd_lower` from a floating Cholesky). VR discipline: the empty axiom list.
-/
namespace ZStability
open ZNet ZRound
variable {α : Type}

/-- `Σ_e c_e M_e`, entrywise. -/
def combo (F : OF α) (es : List Nat) (c : Nat → α) (M : Nat → Nat → Nat → α) : Nat → Nat → α :=
  fun i j => S F es (fun e => F.mul (c e) (M e i j))

theorem qf_combo (F : OF α) (l es : List Nat) (c : Nat → α) (M : Nat → Nat → Nat → α) (x : Nat → α) :
    qf F l (combo F es c M) x = S F es (fun e => F.mul (c e) (qf F l (M e) x)) := by
  unfold qf combo
  -- x_i (Σ_e c_e M_e,ij) x_j = Σ_e c_e (x_i M_e,ij x_j)
  have h1 : ∀ i j, F.mul (x i) (F.mul (S F es (fun e => F.mul (c e) (M e i j))) (x j)) =
      S F es (fun e => F.mul (c e) (F.mul (x i) (F.mul (M e i j) (x j)))) := by
    intro i j
    rw [F.mul_comm (S F es _) (x j), ← S_mul F (x j) _ es, ← S_mul F (x i) _ es]
    exact S_congr F es (fun e _ => by
      show F.mul (x i) (F.mul (x j) (F.mul (c e) (M e i j))) = F.mul (c e) (F.mul (x i) (F.mul (M e i j) (x j)))
      rw [F.mul_comm (x j) (F.mul (c e) (M e i j)), F.mul_assoc (c e), ← F.mul_assoc (x i) (c e),
        F.mul_comm (x i) (c e), F.mul_assoc (c e) (x i), F.mul_comm (M e i j) (x j)])
  rw [S_congr F l (fun i _ => S_congr F l (fun j _ => h1 i j))]
  rw [S_congr F l (fun i _ => S_swap F (fun j e => F.mul (c e) (F.mul (x i) (F.mul (M e i j) (x j)))) es l)]
  rw [S_swap F (fun i e => S F l (fun j => F.mul (c e) (F.mul (x i) (F.mul (M e i j) (x j))))) es l]
  exact S_congr F es (fun e _ => by
    rw [S_congr F l (fun i _ => S_mul F (c e) (fun j => F.mul (x i) (F.mul (M e i j) (x j))) l)]
    exact S_mul F (c e) _ l)

/-- THE STIFFNESS IN THE BOX. `0 ≤ k_P` (every part's form), `m ≤ p_P`, `0 ≤ m`: `m·Σ_P k_P ≤ Σ_P p_P k_P`. -/
theorem stiff_lower (F : OF α) (ps : List Nat) (k p : Nat → α) (m : α)
    (hk : ∀ P, List.Mem P ps → F.le F.zero (k P)) (hp : ∀ P, List.Mem P ps → F.le m (p P)) :
    F.le (F.mul m (S F ps k)) (S F ps (fun P => F.mul (p P) (k P))) := by
  rw [← S_mul F m k ps]
  exact S_le F ps (fun P hP => by
    rw [F.mul_comm m (k P), F.mul_comm (p P) (k P)]
    exact F.mul_le_mul_left (hk P hP) (hp P hP))

/-- THE GEOMETRIC STIFFNESS FROM BELOW. `0 ≤ g_e` (`xᵀG_e x ≥ 0`), `N_lo,e ≤ N_e`, `0 ≤ λ`:
`λ Σ N_lo,e g_e ≤ λ Σ N_e g_e`. -/
theorem geo_lower (F : OF α) (es : List Nat) (g N Nlo : Nat → α) (lam : α) (hl : F.le F.zero lam)
    (hg : ∀ e, List.Mem e es → F.le F.zero (g e)) (hN : ∀ e, List.Mem e es → F.le (Nlo e) (N e)) :
    F.le (F.mul lam (S F es (fun e => F.mul (Nlo e) (g e)))) (F.mul lam (S F es (fun e => F.mul (N e) (g e)))) := by
  apply F.mul_le_mul_left hl
  exact S_le F es (fun e he => by
    rw [F.mul_comm (Nlo e) (g e), F.mul_comm (N e) (g e)]
    exact F.mul_le_mul_left (hg e he) (hN e he))

/-- THE BOX IN ONE MATRIX. With `K_P ⪰ 0`, `p_P ≥ m = 1 − T`, `G_e ⪰ 0`, `N_e ≥ N_lo,e`, `λ ≥ 0`: for every `x`,
`m·xᵀK0x + λ Σ N_lo,e xᵀG_e x ≤ xᵀK(p)x + λ Σ N_e xᵀG_e x` — the left matrix positive definite makes the right one
positive definite at every `p`, so `λ` is below the critical factor everywhere in the box. -/
theorem stability_lower (F : OF α) (l ps es : List Nat) (KP G : Nat → Nat → Nat → α) (p N Nlo : Nat → α)
    (m lam : α) (x : Nat → α) (hl : F.le F.zero lam)
    (hK : ∀ P, List.Mem P ps → F.le F.zero (qf F l (KP P) x)) (hp : ∀ P, List.Mem P ps → F.le m (p P))
    (hG : ∀ e, List.Mem e es → F.le F.zero (qf F l (G e) x)) (hN : ∀ e, List.Mem e es → F.le (Nlo e) (N e)) :
    F.le (F.add (F.mul m (qf F l (combo F ps (fun _ => F.one) KP) x))
                (F.mul lam (qf F l (combo F es Nlo G) x)))
         (F.add (qf F l (combo F ps p KP) x) (F.mul lam (qf F l (combo F es N G) x))) := by
  rw [qf_combo, qf_combo, qf_combo, qf_combo]
  have e1 : S F ps (fun P => F.mul F.one (qf F l (KP P) x)) = S F ps (fun P => qf F l (KP P) x) :=
    S_congr F ps (fun P _ => one_mul F _)
  rw [e1]
  exact F.add_le_add (stiff_lower F ps (fun P => qf F l (KP P) x) p m hK hp)
    (geo_lower F es (fun e => qf F l (G e) x) N Nlo lam hl hG hN)

/-- THE UPPER SIDE BY A WITNESS. `qK = xᵀKx`, `g_e = xᵀG_e x ≥ 0`, `N_e ≤ N_hi,e`, `0 ≤ λ`: if
`qK + λ Σ N_hi,e g_e ≤ 0` then `qK + λ Σ N_e g_e ≤ 0` — the form is not positive at `x`, whatever the forces are
inside their proved ranges. -/
theorem witness_upper (F : OF α) (es : List Nat) (g N Nhi : Nat → α) (qK lam : α) (hl : F.le F.zero lam)
    (hg : ∀ e, List.Mem e es → F.le F.zero (g e)) (hN : ∀ e, List.Mem e es → F.le (N e) (Nhi e))
    (hW : F.le (F.add qK (F.mul lam (S F es (fun e => F.mul (Nhi e) (g e))))) F.zero) :
    F.le (F.add qK (F.mul lam (S F es (fun e => F.mul (N e) (g e))))) F.zero :=
  F.le_trans (F.add_le_add (F.le_refl qK) (geo_lower F es g Nhi N lam hl hg hN)) hW

end ZStability

#print axioms ZStability.qf_combo
#print axioms ZStability.stiff_lower
#print axioms ZStability.geo_lower
#print axioms ZStability.stability_lower
#print axioms ZStability.witness_upper
