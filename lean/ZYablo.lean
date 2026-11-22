/-
  ZYablo.lean — E36: YABLO, AND WHERE EXACTLY THE WALL IS.

  THE CAVEAT THIS ANSWERS. §10 said it plainly: "Yablo stays invisible — every
  finite truncation is grounded (§11), so the passport of infinite regress
  needs an infinite instrument." §11 checked the truncation at n = 3 and found
  the unique model F, F, T. That is one truncation, and no instrument at all
  for the limit.

  THREE THEOREMS, AND TOGETHER THEY LOCATE THE WALL RATHER THAN CLIMB IT.

    1. EVERY finite truncation is grounded, for every n, with exactly one
       model: the last sentence true, all others false. So the finite
       instrument is not merely too weak to see the paradox — there is
       nothing there to see. The n = 3 check was not a sample.

    2. The INFINITE system admits NO verdict assignment whatever
       (`yablo_greedy_homeless`). This is the infinite instrument the caveat
       asked for, and it is one theorem rather than a procedure.

    3. The infinite system is NEVER DETERMINED by the stable step
       (`yablo_never_determined`, pure branch: one classical value per sentence): every sentence has two completions on which its
       definition differs. So Yablo receives the same diagnosis as the liar —
       homeless where signatures are issued, never settled where the solver
       grounds — except that for Yablo this could not be seen at any finite stage.

  AND THE CLASSICAL STEP IS AVOIDED, WHICH IS WHY THIS IS HERE AT ALL. The
  textbook argument goes: `v i = T` forces every later sentence false, so
  `v (i+1) = F`, so NOT every sentence after `i+1` is false, so SOME later
  one is true — and that last step is `¬∀ → ∃¬`, which needs classical logic
  and would have taken the file to the classical tier.

  TWO THINGS ARE ASSUMED RATHER THAN DERIVED, AND BOTH ARE SAID HERE.

    * Bivalence of the sentences is written into `GreedyAdmissible` as a
      clause. It is a fact of this logic — §6: a quantified formula never
      takes Z — but this file posits it rather than re-deriving it from an
      evaluation of an infinite quantifier, which would need the parameter
      tableaux §27 still lists as open.

    * The rendering `v i = T ↔ ∀ j > i, v j = F` is the strict universal of
      §6 with the greedy denial of §3.1 inside it (¬F = T, ¬T = F, ¬Z = F),
      so "sⱼ is false" is strictly T exactly when `v j = F`. That is a
      reading of the system, and a reader who rejects the reading rejects
      the theorem with it.

  AND THE POSITIVE CONTROL IS THEOREM 3, NOT AN AFTERTHOUGHT. An
  impossibility theorem is worthless if the definition it refutes is
  unsatisfiable by construction. The truncation of the SAME shape to any
  finite n has a model, and exactly one — so `GreedyAdmissible` is refuted
  by Yablo's infinity, not by its own wording.

  It is not needed. From "every j > i is F" it already follows that every
  j > i+1 is F, since j > i+1 implies j > i. The fixpoint condition then
  makes `v (i+1) = T` outright, contradicting `v (i+1) = F`. No witness is
  extracted, nothing is refuted into existence, and the empty axiom list
  survives. A paradox of infinite regress, proved without a single classical
  step: that is worth more here than the result itself.
-/
import ZTL

namespace ZYablo

open V

/-! ### The system

    `sᵢ` says: every later sentence is false. A valuation assigns a verdict
    to each index. -/

/-- Admissibility in the VERDICT register: every sentence carries a classical
verdict (greediness — a quantified formula never takes Z, §6), and it is T
exactly when every later sentence is F. -/
def GreedyAdmissible (v : Nat → V) : Prop :=
  ∀ i, (v i = T ∨ v i = F) ∧ (v i = T ↔ ∀ j, i < j → v j = F)

/-! ### 1. The infinite system is homeless in the verdict register -/

/-- No sentence can be true. Constructive: the contradiction is found by
STEPPING ONE PLACE, not by extracting a counterexample. -/
theorem no_true_sentence (v : Nat → V) (h : GreedyAdmissible v) :
    ∀ i, v i ≠ T := by
  intro i hi
  have hlater : ∀ j, i < j → v j = F := (h i).2.mp hi
  have hnext : ∀ j, i + 1 < j → v j = F := fun j hj =>
    hlater j (Nat.lt_trans (Nat.lt_succ_self i) hj)
  have hT : v (i + 1) = T := (h (i + 1)).2.mpr hnext
  have hF : v (i + 1) = F := hlater (i + 1) (Nat.lt_succ_self i)
  rw [hT] at hF
  exact V.noConfusion hF

/-- **YABLO IS HOMELESS.** No assignment of verdicts to the infinite system
is admissible — and this is what no finite truncation can show. -/
theorem yablo_greedy_homeless : ¬ ∃ v : Nat → V, GreedyAdmissible v := by
  intro ⟨v, h⟩
  have hnoT := no_true_sentence v h
  have hallF : ∀ j, 0 < j → v j = F := by
    intro j _
    cases (h j).1 with
    | inl hT => exact absurd hT (hnoT j)
    | inr hF => exact hF
  exact hnoT 0 ((h 0).2.mpr hallF)

/-! ### 2. …and never determined by the stable step (pure branch, 2026-11-22) -/

/-- Sentence i's definition under a completion `c` (one classical value per sentence, the stable test of
`ZGround`): every later sentence is false. -/
def yabloVal (c : Nat → Bool) (i : Nat) : Prop := ∀ j, i < j → c j = false

/-- `Nat.beq n n = true`, hand-rolled (the library's lemma pulls propext). -/
theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

/-- **YABLO STAYS IN THE SOLVER'S PHASE.** For every sentence there are two completions of the undetermined
sentences on which its definition takes different values — all later sentences false (true), or the next one
true (false) — so the stable step never determines it: the all-undetermined state is where Yablo rests. The
same diagnosis as the liar, reached for a system no finite stage could diagnose. -/
theorem yablo_never_determined (i : Nat) :
    yabloVal (fun _ => false) i ∧ ¬ yabloVal (fun j => Nat.beq j (i + 1)) i := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro h
  have hh : Nat.beq (i + 1) (i + 1) = false := h (i + 1) (Nat.lt_succ_self i)
  rw [beq_self] at hh
  exact Bool.noConfusion hh

/-! ### 3. Every finite truncation is grounded — for every n -/

/-- The truncation to `s₀ … s_{n-1}`: the quantifier ranges only inside. -/
def TruncAdmissible (n : Nat) (v : Nat → V) : Prop :=
  ∀ i, i < n → ((v i = T ∨ v i = F)
              ∧ (v i = T ↔ ∀ j, i < j → j < n → v j = F))

/-- The model: the LAST sentence true, every earlier one false. -/
def truncModel (n : Nat) (i : Nat) : V :=
  match Nat.beq (i + 1) n with
  | true  => T
  | false => F

theorem natBeq_refl : ∀ m : Nat, Nat.beq m m = true
  | 0     => rfl
  | m + 1 => natBeq_refl m

theorem truncModel_last (n : Nat) : truncModel (n + 1) n = T := by
  show (match Nat.beq (n + 1) (n + 1) with | true => T | false => F) = T
  rw [natBeq_refl (n + 1)]

theorem natBeq_false_of_ne : ∀ a b : Nat, a < b → Nat.beq a b = false
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | a + 1, b + 1, h => natBeq_false_of_ne a b (Nat.lt_of_succ_lt_succ h)

theorem truncModel_earlier (n i : Nat) (h : i + 1 < n) : truncModel n i = F := by
  show (match Nat.beq (i + 1) n with | true => T | false => F) = F
  rw [natBeq_false_of_ne (i + 1) n h]

/-- **THE UNIQUE MODEL, AT EVERY n.** The truncation is grounded and its
model is forced: no choice is left anywhere. §11 checked n = 3; this is
every n at once. -/
theorem trunc_unique (n : Nat) (v : Nat → V) (h : TruncAdmissible (n + 1) v) :
    ∀ i, i < n + 1 → v i = truncModel (n + 1) i := by
  intro i hi
  have hlast : v n = T := by
    refine (h n (Nat.lt_succ_self n)).2.mpr ?_
    intro j hj hjn
    exact absurd (Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hjn)) (Nat.lt_irrefl n)
  cases Nat.lt_or_ge i n with
  | inl hlt =>
      have hnotT : v i ≠ T := by
        intro hT
        have := (h i (Nat.lt_trans hlt (Nat.lt_succ_self n))).2.mp hT n hlt
          (Nat.lt_succ_self n)
        rw [hlast] at this
        exact V.noConfusion this
      have hF : v i = F := by
        cases (h i (Nat.lt_trans hlt (Nat.lt_succ_self n))).1 with
        | inl hT => exact absurd hT hnotT
        | inr hF => exact hF
      rw [hF, truncModel_earlier (n + 1) i (Nat.succ_lt_succ hlt)]
  | inr hge =>
      have hin : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
      rw [hin, hlast, truncModel_last n]

end ZYablo

#print axioms ZYablo.no_true_sentence
#print axioms ZYablo.yablo_greedy_homeless
#print axioms ZYablo.yablo_never_determined
#print axioms ZYablo.trunc_unique
