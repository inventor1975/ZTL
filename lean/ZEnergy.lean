-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
/-!
# ZEnergy — the grouped first order of `zenergy.py`. Zero axioms.

`zenergy.py` (2026-10-31) bounds one output of `K(p) u = f` with `K(p) = Σ_P p_P K_P`, each part `K_P` a sum of
rank-one terms `Σ_{e ∈ P} g0_e s_e s_eᵀ` that share ONE factor `p_P = 1 + δ_P`, `|δ_P| ≤ t_P`. Its algebra is
ZNet's step 4 (`target_identity`, `target_second`, stated for any vectors `s_e` and any `d` with `d_e² ≤ t_e²` —
giving every term of a part the part's `δ_P` is one such `d`), except the FIRST ORDER: ZNet's `target_first` bounds
it term by term, `Σ_e g0_e t_e |T0_e| |u0_e|`; `zenergy` reads it part by part, `Σ_P t_P |Σ_{e∈P} g0_e T0_e u0_e|`,
which is never larger (the triangle inequality inside a part) and is what the kernel computes. Proved here:
  `S_append`        a sum over `l ++ m` is the sum over `l` plus the sum over `m`;
  `S_flat`          a sum over the terms of all parts is the sum over parts of the sums over their terms;
  `common_factor`   a part's terms sharing `d_e = δ`: `Σ_{e∈P} g0_e (d_e x_e) = δ · Σ_{e∈P} g0_e x_e`;
  `first_grouped`   `|Σ_P δ_P c_P| ≤ Σ_P t_P |c_P|` for `|δ_P| ≤ t_P` (no sign on `c_P` needed);
  `target_first_grouped`   the three together: the first-order term of ZNet's identity, its `d` constant on each
                    part, is bounded by `zenergy`'s `D1`.
A part of ONE term (a bar, a branch) makes `target_first_grouped` read exactly as ZNet's `target_first` (up to
`|T0 u0| = |T0| |u0|`), so trusses and networks needed nothing new; this is for parts of several terms (a beam
element given by its own LDL^T). VR discipline: `#print axioms` at the end — the empty list, every line.
-/
namespace ZEnergy
open ZNet
variable {α : Type}

/-- The terms of the parts in `pl`, part after part. -/
def flat (tl : Nat → List Nat) : List Nat → List Nat
  | [] => []
  | P :: pl => tl P ++ flat tl pl

theorem S_append (F : OF α) (f : Nat → α) : ∀ l m : List Nat, S F (l ++ m) f = F.add (S F l f) (S F m f)
  | [], m => by
    show S F m f = F.add F.zero (S F m f)
    rw [zero_add F]
  | i :: l, m => by
    show F.add (f i) (S F (l ++ m) f) = F.add (F.add (f i) (S F l f)) (S F m f)
    rw [S_append F f l m, F.add_assoc]

theorem S_flat (F : OF α) (tl : Nat → List Nat) (f : Nat → α) :
    ∀ pl : List Nat, S F (flat tl pl) f = S F pl (fun P => S F (tl P) f)
  | [] => rfl
  | P :: pl => by
    show S F (tl P ++ flat tl pl) f = F.add (S F (tl P) f) (S F pl (fun P => S F (tl P) f))
    rw [S_append F f (tl P) (flat tl pl), S_flat F tl f pl]

/-- `g0·(δ·x) = δ·(g0·x)`. -/
theorem r_swap (F : OF α) (g0 δ x : α) : F.mul g0 (F.mul δ x) = F.mul δ (F.mul g0 x) := by
  rw [← F.mul_assoc, F.mul_comm g0 δ, F.mul_assoc]

theorem common_factor (F : OF α) (l : List Nat) (g0 d x : Nat → α) (δ : α)
    (hd : ∀ e, List.Mem e l → d e = δ) :
    S F l (fun e => F.mul (g0 e) (F.mul (d e) (x e))) = F.mul δ (S F l (fun e => F.mul (g0 e) (x e))) := by
  rw [← S_mul F δ (fun e => F.mul (g0 e) (x e)) l]
  exact S_congr F l (fun e he => by
    show F.mul (g0 e) (F.mul (d e) (x e)) = F.mul δ (F.mul (g0 e) (x e))
    rw [hd e he, r_swap])

theorem first_grouped (F : OF α) (pl : List Nat) (δ t c : Nat → α)
    (ht : ∀ P, List.Mem P pl → F.le (F.abs (δ P)) (t P)) :
    F.le (F.abs (S F pl (fun P => F.mul (δ P) (c P)))) (S F pl (fun P => F.mul (t P) (F.abs (c P)))) := by
  apply F.le_trans (abs_S F _ pl)
  exact S_le F pl (fun P hP => by
    show F.le (F.abs (F.mul (δ P) (c P))) (F.mul (t P) (F.abs (c P)))
    rw [F.abs_mul, F.mul_comm (F.abs (δ P)) _, F.mul_comm (t P) _]
    exact F.mul_le_mul_left (F.abs_nonneg _) (ht P hP))

/-- THE GROUPED FIRST ORDER. The first-order term of ZNet's `target_identity`, `Σ_e g0_e d_e T0_e u0_e` over the
terms of all parts, with `d` constant on each part (`d_e = δ_P`, `|δ_P| ≤ t_P`), is at most
`Σ_P t_P |Σ_{e∈P} g0_e T0_e u0_e|` in absolute value — `zenergy`'s `D1`. -/
theorem target_first_grouped (F : OF α) (tl : Nat → List Nat) (pl : List Nat) (g0 d T0 u0 δ t : Nat → α)
    (hd : ∀ P, List.Mem P pl → ∀ e, List.Mem e (tl P) → d e = δ P)
    (ht : ∀ P, List.Mem P pl → F.le (F.abs (δ P)) (t P)) :
    F.le (F.abs (S F (flat tl pl) (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (T0 e) (u0 e))))))
      (S F pl (fun P => F.mul (t P) (F.abs (S F (tl P) (fun e => F.mul (g0 e) (F.mul (T0 e) (u0 e))))))) := by
  rw [S_flat F tl _ pl]
  have h : S F pl (fun P => S F (tl P) (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (T0 e) (u0 e))))) =
      S F pl (fun P => F.mul (δ P) (S F (tl P) (fun e => F.mul (g0 e) (F.mul (T0 e) (u0 e))))) :=
    S_congr F pl (fun P hP => common_factor F (tl P) g0 d (fun e => F.mul (T0 e) (u0 e)) (δ P) (hd P hP))
  rw [h]
  exact first_grouped F pl δ t _ ht

end ZEnergy

#print axioms ZEnergy.S_append
#print axioms ZEnergy.S_flat
#print axioms ZEnergy.r_swap
#print axioms ZEnergy.common_factor
#print axioms ZEnergy.first_grouped
#print axioms ZEnergy.target_first_grouped
