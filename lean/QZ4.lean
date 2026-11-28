import ZTL
import ZRead
import QZ3
/-!
# QZ, theorem 4 — layer 2: IF STABLE holds wherever the state SPLITS along the dirty questions. With AI, 2026-11-27.

    sh research/qz/build.sh        (compiles QZ3 to a scratch folder, then checks this file against the public kernel)

The kernel's IF STABLE (`V.stableT` / `V.stableF`, ZRead.lean): the formula is classically true (false) under every
cleaning — one value per atom. `QZ1.stable_refuted_by_lattice` shows a quantum lattice can refute it. This file says
exactly when it cannot.

THE CONDITION. `Splits s [x₁, …, xₙ]`: the state lies under its two parts along x₁,
        s ≤ (s ∧ x₁) ∨ (s ∧ ¬x₁),
and each part splits along the rest. In the vocabulary of quantum logic, `s = (s ∧ x) ∨ (s ∧ ¬x)` is the definition of
"s is COMPATIBLE with x" (s commutes with x). In a distributive lattice with excluded middle it always holds
(`splits_of_distrib`); in MO2 the state a does not split along b (`mo2_no_split`), and that is the very place where
the lattice refutes a stable verdict.

THEOREM (`stable_sound`, `stableF_sound`). Same lattices as QZ3 (order-reversing negation, x ≤ ¬¬x, top, bottom). Let
the marking agree with the state, let `zs` list every dirty atom THAT OCCURS IN THE FORMULA, and let the state split along their
elements. Then what the kernel calls stably true lies above the state, and what it calls stably false has its negation
above the state.

THE PROOF is QZ3 used on every cell. Splitting along a dirty atom gives two smaller states; in each the atom is settled
(T in one, F in the other). When no dirty atom is left the kernel's reading is the classical one (`definite`), so
stable truth is EARNED there and QZ3 puts the cell under the formula; the join of the cells is under the formula, and
the state is under that join — the only step that uses the condition.

PRIOR WORK (read 2026-11-27). In an orthomodular lattice "s commutes with x" is defined by exactly such an identity,
and the Foulis–Holland theorem says that elements one of which commutes with the others generate a distributive
sublattice (found by search, the original papers not read) — so in orthomodular lattices this layer is close to a
known fact: classical reasoning is sound inside a Boolean block. Bolotin (arXiv 1904.01364, read in full) says in
prose that each block of commuting projections is a Boolean algebra and that conjunction can be proved only inside
one; no theorem. Abramsky–Barbosa (arXiv 2011.03064, read in full): a pairwise commeasurable set extends to a Boolean
subalgebra — a step of a construction there, not a soundness theorem, and no lattice identity for compatibility.
What is ours here: the statement for the kernel's own IF STABLE, in lattices WITHOUT the orthomodular law, with the
condition placed on the state and only on the formula's dirty atoms, checked by machine.

Boundary. Dirty atoms the formula does not mention do not matter and need not split. The condition is exact in this
sense (`split_is_exact`): the stably true formula (c ∧ x) ∨ (c ∧ ¬x), with c naming the state, lies above the state
if and only if the state splits along x. It is not necessary formula by formula: x ∧ ¬x is refuted by the lattice
whether or not the state splits (1536 such cases in research/qz/splits_probe.py).
-/

namespace QZ4
open V QZ3

variable {α : Type} (L : NLat α)

/-- the state lies under its two parts along each element in turn -/
def Splits (s : α) : List α → Prop
  | [] => True
  | x :: xs => L.le s (L.join (L.meet s x) (L.meet s (L.neg x))) ∧ Splits (L.meet s x) xs ∧ Splits (L.meet s (L.neg x)) xs

/-- membership, written out (no library lemma, no axiom) -/
def In (n : Nat) : List Nat → Prop
  | [] => False
  | k :: zs => n = k ∨ In n zs

def set (v : Nat → V) (k : Nat) (x : V) : Nat → V := fun n => if n = k then x else v n

theorem set_same (v : Nat → V) (k : Nat) (x : V) : set v k x k = x := if_pos rfl
theorem set_other (v : Nat → V) (k : Nat) (x : V) {n : Nat} (h : n ≠ k) : set v k x n = v n := if_neg h

/-! ### with no dirty atom the kernel's reading is the classical one -/

theorem c_and : ∀ a b t f t' f' : Bool, t = a → f = !a → t' = b → f' = !b →
    (comb (fun x y => x && y) (t, f) (t', f')).1 = (a && b) ∧ (comb (fun x y => x && y) (t, f) (t', f')).2 = !(a && b) := by decide
theorem c_or : ∀ a b t f t' f' : Bool, t = a → f = !a → t' = b → f' = !b →
    (comb (fun x y => x || y) (t, f) (t', f')).1 = (a || b) ∧ (comb (fun x y => x || y) (t, f) (t', f')).2 = !(a || b) := by decide
theorem c_imp : ∀ a b t f t' f' : Bool, t = a → f = !a → t' = b → f' = !b →
    (comb (fun x y => !x || y) (t, f) (t', f')).1 = (!a || b) ∧ (comb (fun x y => !x || y) (t, f) (t', f')).2 = !(!a || b) := by decide
theorem c_xor : ∀ a b t f t' f' : Bool, t = a → f = !a → t' = b → f' = !b →
    (comb (fun x y => x != y) (t, f) (t', f')).1 = (a != b) ∧ (comb (fun x y => x != y) (t, f) (t', f')).2 = !(a != b) := by decide
theorem c_xnor : ∀ a b t f t' f' : Bool, t = a → f = !a → t' = b → f' = !b →
    (comb (fun x y => x == y) (t, f) (t', f')).1 = (a == b) ∧ (comb (fun x y => x == y) (t, f) (t', f')).2 = !(a == b) := by decide
theorem c_neg : ∀ a t f : Bool, t = a → f = !a → f = !a ∧ t = !(!a) := by decide

/-- the one cleaning of a marking without dirty atoms (a dirty atom would get `false`; there is none) -/
def cl (v : Nat → V) : Nat → Bool := fun n => (subs (v n)).contains true

theorem cl_cleans : ∀ x : V, (subs x).contains ((subs x).contains true) = true := by decide
theorem atom_def : ∀ x : V, x ≠ Z → (subs x).contains false = !((subs x).contains true) := by decide

/-- no atom of the formula is dirty -/
def Clean (v : Nat → V) : Fm → Prop
  | .atom n => v n ≠ Z
  | .top => True
  | .bot => True
  | .neg φ => Clean v φ
  | .conj φ ψ => Clean v φ ∧ Clean v ψ
  | .disj φ ψ => Clean v φ ∧ Clean v ψ
  | .imp φ ψ => Clean v φ ∧ Clean v ψ
  | .xor φ ψ => Clean v φ ∧ Clean v ψ
  | .xnor φ ψ => Clean v φ ∧ Clean v ψ

/-- every dirty atom of the formula is in the list -/
def DirtyIn (v : Nat → V) (zs : List Nat) : Fm → Prop
  | .atom n => v n = Z → In n zs
  | .top => True
  | .bot => True
  | .neg φ => DirtyIn v zs φ
  | .conj φ ψ => DirtyIn v zs φ ∧ DirtyIn v zs ψ
  | .disj φ ψ => DirtyIn v zs φ ∧ DirtyIn v zs ψ
  | .imp φ ψ => DirtyIn v zs φ ∧ DirtyIn v zs ψ
  | .xor φ ψ => DirtyIn v zs φ ∧ DirtyIn v zs ψ
  | .xnor φ ψ => DirtyIn v zs φ ∧ DirtyIn v zs ψ

theorem clean_of_nil (v : Nat → V) : ∀ φ : Fm, DirtyIn v [] φ → Clean v φ
  | .atom _, h => fun e => h e
  | .top, _ => True.intro
  | .bot, _ => True.intro
  | .neg φ, h => clean_of_nil v φ h
  | .conj φ ψ, h => ⟨clean_of_nil v φ h.1, clean_of_nil v ψ h.2⟩
  | .disj φ ψ, h => ⟨clean_of_nil v φ h.1, clean_of_nil v ψ h.2⟩
  | .imp φ ψ, h => ⟨clean_of_nil v φ h.1, clean_of_nil v ψ h.2⟩
  | .xor φ ψ, h => ⟨clean_of_nil v φ h.1, clean_of_nil v ψ h.2⟩
  | .xnor φ ψ, h => ⟨clean_of_nil v φ h.1, clean_of_nil v ψ h.2⟩

/-- settling the head atom (to T or F) leaves the dirty atoms of the formula in the tail -/
theorem dirty_set (v : Nat → V) (k : Nat) (zs : List Nat) (x : V) (hx : x ≠ Z) :
    ∀ φ : Fm, DirtyIn v (k :: zs) φ → DirtyIn (set v k x) zs φ
  | .atom n, h => fun e => by
      cases Nat.decEq n k with
      | isTrue e2 => subst e2; rw [set_same] at e; exact absurd e hx
      | isFalse ne => rw [set_other v k x ne] at e; exact (h e).resolve_left ne
  | .top, _ => True.intro
  | .bot, _ => True.intro
  | .neg φ, h => dirty_set v k zs x hx φ h
  | .conj φ ψ, h => ⟨dirty_set v k zs x hx φ h.1, dirty_set v k zs x hx ψ h.2⟩
  | .disj φ ψ, h => ⟨dirty_set v k zs x hx φ h.1, dirty_set v k zs x hx ψ h.2⟩
  | .imp φ ψ, h => ⟨dirty_set v k zs x hx φ h.1, dirty_set v k zs x hx ψ h.2⟩
  | .xor φ ψ, h => ⟨dirty_set v k zs x hx φ h.1, dirty_set v k zs x hx ψ h.2⟩
  | .xnor φ ψ, h => ⟨dirty_set v k zs x hx φ h.1, dirty_set v k zs x hx ψ h.2⟩

/-- a head atom that is not dirty can be dropped from the list -/
theorem dirty_skip (v : Nat → V) (k : Nat) (zs : List Nat) (hk : v k ≠ Z) :
    ∀ φ : Fm, DirtyIn v (k :: zs) φ → DirtyIn v zs φ
  | .atom n, h => fun e => (h e).resolve_left (fun e2 => by subst e2; exact hk e)
  | .top, _ => True.intro
  | .bot, _ => True.intro
  | .neg φ, h => dirty_skip v k zs hk φ h
  | .conj φ ψ, h => ⟨dirty_skip v k zs hk φ h.1, dirty_skip v k zs hk ψ h.2⟩
  | .disj φ ψ, h => ⟨dirty_skip v k zs hk φ h.1, dirty_skip v k zs hk ψ h.2⟩
  | .imp φ ψ, h => ⟨dirty_skip v k zs hk φ h.1, dirty_skip v k zs hk ψ h.2⟩
  | .xor φ ψ, h => ⟨dirty_skip v k zs hk φ h.1, dirty_skip v k zs hk ψ h.2⟩
  | .xnor φ ψ, h => ⟨dirty_skip v k zs hk φ h.1, dirty_skip v k zs hk ψ h.2⟩

theorem definite (v : Nat → V) :
    ∀ φ : Fm, Clean v φ → (rd v φ).1 = clEval (cl v) φ ∧ (rd v φ).2 = !(clEval (cl v) φ)
  | .atom n, h => ⟨rfl, atom_def (v n) h⟩
  | .top, _ => ⟨rfl, rfl⟩
  | .bot, _ => ⟨rfl, rfl⟩
  | .neg φ, h => c_neg _ _ _ (definite v φ h).1 (definite v φ h).2
  | .conj φ ψ, h => c_and _ _ _ _ _ _ (definite v φ h.1).1 (definite v φ h.1).2 (definite v ψ h.2).1 (definite v ψ h.2).2
  | .disj φ ψ, h => c_or _ _ _ _ _ _ (definite v φ h.1).1 (definite v φ h.1).2 (definite v ψ h.2).1 (definite v ψ h.2).2
  | .imp φ ψ, h => c_imp _ _ _ _ _ _ (definite v φ h.1).1 (definite v φ h.1).2 (definite v ψ h.2).1 (definite v ψ h.2).2
  | .xor φ ψ, h => c_xor _ _ _ _ _ _ (definite v φ h.1).1 (definite v φ h.1).2 (definite v ψ h.2).1 (definite v ψ h.2).2
  | .xnor φ ψ, h => c_xnor _ _ _ _ _ _ (definite v φ h.1).1 (definite v φ h.1).2 (definite v ψ h.2).1 (definite v ψ h.2).2

theorem not_true_false : ∀ b : Bool, b = true → (!b) = false := by decide

/-- no dirty atom: stably true is EARNED -/
theorem earned_of_stable (v : Nat → V) (φ : Fm) (h : Clean v φ) (st : stableT v φ) : earnedR v φ := by
  have c := st (cl v) (fun n => cl_cleans (v n))
  show (rd v φ).2 = false
  exact ((definite v φ h).2).trans (not_true_false _ c)
/-- no dirty atom: stably false is REFUTED -/
theorem refuted_of_stable (v : Nat → V) (φ : Fm) (h : Clean v φ) (st : stableF v φ) : refutedR v φ := by
  have c := st (cl v) (fun n => cl_cleans (v n))
  show (rd v φ).1 = false
  exact ((definite v φ h).1).trans c

/-! ### settling a dirty atom keeps a stable verdict -/

theorem subs_Z_all : ∀ b : Bool, (subs Z).contains b = true := by decide

theorem cleans_set {v : Nat → V} {k : Nat} (hk : v k = Z) (x : V) {c : Nat → Bool} (hc : cleans (set v k x) c) :
    cleans v c := by
  intro n
  cases Nat.decEq n k with
  | isTrue e => subst e; rw [hk]; exact subs_Z_all _
  | isFalse ne => have := hc n; rw [set_other v k x ne] at this; exact this

/-! ### agreement on the atoms of the formula survives a smaller state and the settling of an atom -/

theorem on_down {s t : α} (v : Nat → V) (val : Nat → α) (ht : L.le t s) :
    ∀ φ : Fm, AgreesOn L s v val φ → AgreesOn L t v val φ
  | .atom _, h => ⟨fun e => L.le_trans ht (h.1 e), fun e => L.le_trans ht (h.2 e)⟩
  | .top, _ => True.intro
  | .bot, _ => True.intro
  | .neg φ, h => on_down v val ht φ h
  | .conj φ ψ, h => ⟨on_down v val ht φ h.1, on_down v val ht ψ h.2⟩
  | .disj φ ψ, h => ⟨on_down v val ht φ h.1, on_down v val ht ψ h.2⟩
  | .imp φ ψ, h => ⟨on_down v val ht φ h.1, on_down v val ht ψ h.2⟩
  | .xor φ ψ, h => ⟨on_down v val ht φ h.1, on_down v val ht ψ h.2⟩
  | .xnor φ ψ, h => ⟨on_down v val ht φ h.1, on_down v val ht ψ h.2⟩

theorem on_setT (s : α) (v : Nat → V) (val : Nat → α) (k : Nat) :
    ∀ φ : Fm, AgreesOn L s v val φ → AgreesOn L (L.meet s (val k)) (set v k T) val φ
  | .atom n, h => by
      cases Nat.decEq n k with
      | isTrue e => subst e; show (set v n T n = T → _) ∧ (set v n T n = F → _); rw [set_same]
                    exact ⟨fun _ => L.meet_le_r _ _, fun e => V.noConfusion e⟩
      | isFalse ne => show (set v k T n = T → _) ∧ (set v k T n = F → _); rw [set_other v k T ne]
                      exact ⟨fun e => L.le_trans (L.meet_le_l _ _) (h.1 e), fun e => L.le_trans (L.meet_le_l _ _) (h.2 e)⟩
  | .top, _ => True.intro
  | .bot, _ => True.intro
  | .neg φ, h => on_setT s v val k φ h
  | .conj φ ψ, h => ⟨on_setT s v val k φ h.1, on_setT s v val k ψ h.2⟩
  | .disj φ ψ, h => ⟨on_setT s v val k φ h.1, on_setT s v val k ψ h.2⟩
  | .imp φ ψ, h => ⟨on_setT s v val k φ h.1, on_setT s v val k ψ h.2⟩
  | .xor φ ψ, h => ⟨on_setT s v val k φ h.1, on_setT s v val k ψ h.2⟩
  | .xnor φ ψ, h => ⟨on_setT s v val k φ h.1, on_setT s v val k ψ h.2⟩

theorem on_setF (s : α) (v : Nat → V) (val : Nat → α) (k : Nat) :
    ∀ φ : Fm, AgreesOn L s v val φ → AgreesOn L (L.meet s (L.neg (val k))) (set v k F) val φ
  | .atom n, h => by
      cases Nat.decEq n k with
      | isTrue e => subst e; show (set v n F n = T → _) ∧ (set v n F n = F → _); rw [set_same]
                    exact ⟨fun e => V.noConfusion e, fun _ => L.meet_le_r _ _⟩
      | isFalse ne => show (set v k F n = T → _) ∧ (set v k F n = F → _); rw [set_other v k F ne]
                      exact ⟨fun e => L.le_trans (L.meet_le_l _ _) (h.1 e), fun e => L.le_trans (L.meet_le_l _ _) (h.2 e)⟩
  | .top, _ => True.intro
  | .bot, _ => True.intro
  | .neg φ, h => on_setF s v val k φ h
  | .conj φ ψ, h => ⟨on_setF s v val k φ h.1, on_setF s v val k ψ h.2⟩
  | .disj φ ψ, h => ⟨on_setF s v val k φ h.1, on_setF s v val k ψ h.2⟩
  | .imp φ ψ, h => ⟨on_setF s v val k φ h.1, on_setF s v val k ψ h.2⟩
  | .xor φ ψ, h => ⟨on_setF s v val k φ h.1, on_setF s v val k ψ h.2⟩
  | .xnor φ ψ, h => ⟨on_setF s v val k φ h.1, on_setF s v val k ψ h.2⟩

/-! ### the induction over the dirty atoms, for any target element -/

theorem by_cells (val : Nat → α) (y : α) (Good C : (Nat → V) → Prop) (D : (Nat → V) → List Nat → Prop)
    (A : α → (Nat → V) → Prop)
    (base : ∀ s v, A s v → C v → Good v → L.le s y)
    (keep : ∀ v k x, v k = Z → Good v → Good (set v k x))
    (d_nil : ∀ v, D v [] → C v)
    (d_set : ∀ v k zs x, x ≠ Z → D v (k :: zs) → D (set v k x) zs)
    (d_skip : ∀ v k zs, v k ≠ Z → D v (k :: zs) → D v zs)
    (a_down : ∀ s t v, L.le t s → A s v → A t v)
    (a_T : ∀ s v k, A s v → A (L.meet s (val k)) (set v k T))
    (a_F : ∀ s v k, A s v → A (L.meet s (L.neg (val k))) (set v k F)) :
    ∀ (zs : List Nat) (s : α) (v : Nat → V), A s v → D v zs →
      Splits L s (zs.map val) → Good v → L.le s y
  | [], s, v, ag, hz, _, g => base s v ag (d_nil v hz) g
  | k :: zs, s, v, ag, hz, sp, g => by
    obtain ⟨cover, sp1, sp2⟩ := sp
    refine L.le_trans cover (L.join_le ?_ ?_)
    · -- the part of the state under val k
      cases hk : v k with
      | Z =>
        exact by_cells val y Good C D A base keep d_nil d_set d_skip a_down a_T a_F zs _ (set v k T) (a_T s v k ag)
          (d_set v k zs T (fun e => V.noConfusion e) hz) sp1 (keep v k T hk g)
      | T =>
        exact by_cells val y Good C D A base keep d_nil d_set d_skip a_down a_T a_F zs _ v
          (a_down s _ v (L.meet_le_l _ _) ag)
          (d_skip v k zs (fun e => by rw [hk] at e; exact V.noConfusion e) hz) sp1 g
      | F =>
        exact by_cells val y Good C D A base keep d_nil d_set d_skip a_down a_T a_F zs _ v
          (a_down s _ v (L.meet_le_l _ _) ag)
          (d_skip v k zs (fun e => by rw [hk] at e; exact V.noConfusion e) hz) sp1 g
    · -- the part of the state under the negation of val k
      cases hk : v k with
      | Z =>
        exact by_cells val y Good C D A base keep d_nil d_set d_skip a_down a_T a_F zs _ (set v k F) (a_F s v k ag)
          (d_set v k zs F (fun e => V.noConfusion e) hz) sp2 (keep v k F hk g)
      | T =>
        exact by_cells val y Good C D A base keep d_nil d_set d_skip a_down a_T a_F zs _ v
          (a_down s _ v (L.meet_le_l _ _) ag)
          (d_skip v k zs (fun e => by rw [hk] at e; exact V.noConfusion e) hz) sp2 g
      | F =>
        exact by_cells val y Good C D A base keep d_nil d_set d_skip a_down a_T a_F zs _ v
          (a_down s _ v (L.meet_le_l _ _) ag)
          (d_skip v k zs (fun e => by rw [hk] at e; exact V.noConfusion e) hz) sp2 g

/-- **QZ 4a.** Where the state splits along the dirty questions of the formula, what the kernel calls stably true
lies above it. Only the atoms of the formula are looked at. -/
theorem stable_sound_on (s : α) (v : Nat → V) (val : Nat → α) (zs : List Nat) (φ : Fm) (ag : AgreesOn L s v val φ)
    (hz : DirtyIn v zs φ) (sp : Splits L s (zs.map val)) (st : stableT v φ) : L.le s (qe L val φ) :=
  by_cells L val (qe L val φ) (fun w => stableT w φ) (fun w => Clean w φ) (fun w l => DirtyIn w l φ)
    (fun t w => AgreesOn L t w val φ)
    (fun s w a h g => earned_sound_on L s w val φ a (earned_of_stable w φ h g))
    (fun _ _ x hk g c hc => g c (cleans_set hk x hc))
    (fun w h => clean_of_nil w φ h) (fun w k l x hx h => dirty_set w k l x hx φ h)
    (fun w k l hk h => dirty_skip w k l hk φ h)
    (fun _ _ w ht a => on_down L w val ht φ a) (fun s w k a => on_setT L s w val k φ a)
    (fun s w k a => on_setF L s w val k φ a) zs s v ag hz sp st

/-- **QZ 4b.** …and what it calls stably false has its negation above the state. -/
theorem stableF_sound_on (s : α) (v : Nat → V) (val : Nat → α) (zs : List Nat) (φ : Fm) (ag : AgreesOn L s v val φ)
    (hz : DirtyIn v zs φ) (sp : Splits L s (zs.map val)) (st : stableF v φ) : L.le s (L.neg (qe L val φ)) :=
  by_cells L val (L.neg (qe L val φ)) (fun w => stableF w φ) (fun w => Clean w φ) (fun w l => DirtyIn w l φ)
    (fun t w => AgreesOn L t w val φ)
    (fun s w a h g => refuted_sound_on L s w val φ a (refuted_of_stable w φ h g))
    (fun _ _ x hk g c hc => g c (cleans_set hk x hc))
    (fun w h => clean_of_nil w φ h) (fun w k l x hx h => dirty_set w k l x hx φ h)
    (fun w k l hk h => dirty_skip w k l hk φ h)
    (fun _ _ w ht a => on_down L w val ht φ a) (fun s w k a => on_setT L s w val k φ a)
    (fun s w k a => on_setF L s w val k φ a) zs s v ag hz sp st

/-- QZ 4a for a marking that agrees with the state on every atom (the earlier form). -/
theorem stable_sound (s : α) (v : Nat → V) (val : Nat → α) (ag : Agrees L s v val) (zs : List Nat) (φ : Fm)
    (hz : DirtyIn v zs φ) (sp : Splits L s (zs.map val)) (st : stableT v φ) : L.le s (qe L val φ) :=
  stable_sound_on L s v val zs φ (agrees_on_of L ag φ) hz sp st

/-- QZ 4b for a marking that agrees with the state on every atom (the earlier form). -/
theorem stableF_sound (s : α) (v : Nat → V) (val : Nat → α) (ag : Agrees L s v val) (zs : List Nat) (φ : Fm)
    (hz : DirtyIn v zs φ) (sp : Splits L s (zs.map val)) (st : stableF v φ) : L.le s (L.neg (qe L val φ)) :=
  stableF_sound_on L s v val zs φ (agrees_on_of L ag φ) hz sp st

/-- **QZ 4d. One context is enough.** Let `t` be what the formula's own settled atoms say (the state lies under it, it
agrees with the marking on the atoms of the formula) and let `t` split along the formula's dirty atoms. Then a stably
true formula lies above the state - whatever ELSE is known, even things that cannot be asked together with the
formula's questions. This is the rule of the guard (research/qz/qz_guard.py): look at the claim's own atoms only. -/
theorem stable_sound_under (s t : α) (hst : L.le s t) (v : Nat → V) (val : Nat → α) (zs : List Nat) (φ : Fm)
    (ag : AgreesOn L t v val φ) (hz : DirtyIn v zs φ) (sp : Splits L t (zs.map val)) (st : stableT v φ) :
    L.le s (qe L val φ) :=
  L.le_trans hst (stable_sound_on L t v val zs φ ag hz sp st)

theorem stableF_sound_under (s t : α) (hst : L.le s t) (v : Nat → V) (val : Nat → α) (zs : List Nat) (φ : Fm)
    (ag : AgreesOn L t v val φ) (hz : DirtyIn v zs φ) (sp : Splits L t (zs.map val)) (st : stableF v φ) :
    L.le s (L.neg (qe L val φ)) :=
  L.le_trans hst (stableF_sound_on L t v val zs φ ag hz sp st)

/-! ### when the condition holds, and when it does not -/

/-- In a distributive lattice with excluded middle every state splits along every list: one context. -/
theorem splits_of_distrib (refl : ∀ a : α, L.le a a)
    (lem : ∀ s x : α, L.le s (L.join x (L.neg x)))
    (dist : ∀ s x y : α, L.le (L.meet s (L.join x y)) (L.join (L.meet s x) (L.meet s y))) :
    ∀ (xs : List α) (s : α), Splits L s xs
  | [], _ => True.intro
  | x :: xs, s =>
    ⟨L.le_trans (L.le_meet (refl s) (lem s x)) (dist s x (L.neg x)),
     splits_of_distrib refl lem dist xs _, splits_of_distrib refl lem dist xs _⟩

/-- In MO2 the state a does not split along b: the two questions cannot be asked together. -/
theorem mo2_no_split : ¬ Splits mo2 Q.a [Q.b] := by
  intro h
  have h1 : qle Q.a (qjoin (qmeet Q.a Q.b) (qmeet Q.a (qneg Q.b))) := h.1
  exact absurd h1 (by decide)

/-- …while with nothing asked the state ⊤ splits along b: one context. -/
theorem mo2_split : Splits mo2 Q.top [Q.b] :=
  ⟨(by decide : qle Q.top (qjoin (qmeet Q.top Q.b) (qmeet Q.top (qneg Q.b)))), True.intro, True.intro⟩

/-! ### the condition cannot be weakened: one stably true formula holds exactly where the state splits -/

/-- "c, and x or not x, said the distributed way": (c ∧ x) ∨ (c ∧ ¬x), with c the atom 0 and x the atom 1 -/
def distributed : Fm := .disj (.conj (.atom 0) (.atom 1)) (.conj (.atom 0) (.neg (.atom 1)))

/-- c is established, x is dirty -/
def vCX : Nat → V := fun n => if n = 0 then T else Z

theorem only_true : ∀ b : Bool, (subs T).contains b = true → b = true := by decide
theorem taut : ∀ b : Bool, ((true && b) || (true && !b)) = true := by decide

/-- that formula is stably true: with c established, whatever one value x has -/
theorem distributed_stable : stableT vCX distributed := by
  intro c hc
  have h0 : c 0 = true := only_true (c 0) (hc 0)
  show ((c 0 && c 1) || (c 0 && !(c 1))) = true
  rw [h0]; exact taut (c 1)

/-- **QZ 4c. Exactness.** Let c be the state itself and x any element. The stably true formula (c ∧ x) ∨ (c ∧ ¬x) lies
above the state exactly when the state splits along x. So the condition of `stable_sound` is not only enough: for
this formula it is the very thing the verdict claims, and no weaker condition on the state would do. -/
theorem split_is_exact (s x : α) :
    (L.le s (qe L (fun n => if n = 0 then s else x) distributed) → Splits L s [x]) ∧
    (Splits L s [x] → L.le s (qe L (fun n => if n = 0 then s else x) distributed)) :=
  ⟨fun h => ⟨h, True.intro, True.intro⟩, fun h => h.1⟩

end QZ4

#print axioms QZ4.stable_sound
#print axioms QZ4.stableF_sound
#print axioms QZ4.stable_sound_under
#print axioms QZ4.stableF_sound_under
#print axioms QZ4.splits_of_distrib
#print axioms QZ4.mo2_no_split
#print axioms QZ4.mo2_split
#print axioms QZ4.distributed_stable
#print axioms QZ4.split_is_exact
