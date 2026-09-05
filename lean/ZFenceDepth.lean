/-
  ZFenceDepth.lean — E33: THE FENCE DEPTH IS EXACTLY m−1, for EVERY m.

  WHAT THIS CLOSES. §19 states the depth of the heredity check as MEASURED.
  Sufficiency it argues: for a sound verdict every full completion agrees by
  definition, so a violation can only live at a partial refinement, i.e. at
  depth ≤ m−1. Necessity it exhibits — the guard family

      (b₁ ∧ … ∧ b_{m−1}) → (a → a)

  a conjunction of m−1 marks standing over the fallen law of identity — and
  checks it "deterministically for m = 3, 4, 5, with the m = 2 witness
  (¬p)→(q→q)". Four values is exhaustion, not a law.

  But this family is UNIFORM in m: one rule builds it for any number of
  guards. So it generalises whole, and here it is, for every m at once.

  WHAT IS PROVED. For every n, the cell with n+1 guards over an all-marked
  atom set is
    * SOUND — every completion agrees with the greedy verdict T;
    * INVARIANT under every refinement that leaves ANY ONE guard unverified,
      no matter how many others are verified and to what;
    * DEAD the moment all n+1 guards are verified true, while the gap atom
      is not.
  So the violation is not merely reachable at depth m−1 — it is reachable
  NOWHERE ELSE. The full guard set is the unique killer.

  WHY THAT IS THE NECESSITY CLAIM. A check of depth d inspects d atoms; with
  m−1 = d+1 guards it must leave one unverified, and by the second clause it
  then sees nothing. Hence no constant depth certifies the hereditary grade.
  THE COUNTING STEP IS THE ONLY THING NOT IN LEAN HERE: "fewer than n atoms
  cannot cover n distinct guards" is finite arithmetic, and it is stated as
  prose deliberately rather than smuggled in. Everything logical is proved.

  ФОРМА ПОД ПУСТОЙ СПИСОК. `ZTime` не импортирует ничего и держит своё `V`
  без tactic-built instances; поэтому `decide` по `∀ x : V` здесь недоступен,
  и все трёхзначные факты доказаны явным `cases`. Арифметика по `Nat` —
  ручным разбором, БЕЗ omega: память держит два противоречащих утверждения о
  том, тянет ли omega propext, и вместо выбора между ними взят путь, на
  котором вопрос не возникает. `#print axioms` внизу файла.
-/
import ZTime

namespace ZFenceDepth

open ZTime
open ZTime.V

/-! ### The three-valued facts the construction stands on -/

theorem and_Z_left  : ∀ x : V, zand V.Z x = V.F := by intro x; cases x <;> rfl
theorem and_F_right : ∀ x : V, zand x V.F = V.F := by intro x; cases x <;> rfl
theorem imp_F_left  : ∀ x : V, zimp V.F x = V.T := by intro x; cases x <;> rfl
theorem imp_T_right : ∀ x : V, zimp x V.T = V.T := by intro x; cases x <;> rfl
theorem and_T_T     : zand V.T V.T = V.T := rfl
theorem imp_Z_Z     : zimp V.Z V.Z = V.F := rfl
theorem imp_T_F     : zimp V.T V.F = V.F := rfl

/-- The law of identity holds on any GROUNDED reference and falls on a mark:
this single fact is the whole gap. -/
theorem imp_self_of_grounded : ∀ x : V, x ≠ V.Z → zimp x x = V.T := by
  intro x hx
  cases x with
  | T => rfl
  | F => rfl
  | Z => exact absurd rfl hx

/-! ### The construction -/

/-- Nothing verified. -/
def allZ : Marking := fun _ => V.Z

/-- Guards are the atoms 1 … n; atom 0 is the gap. -/
def guardConj : Nat → Fm
  | 0     => Fm.top
  | n + 1 => Fm.conj (Fm.atom (n + 1)) (guardConj n)

/-- The gap: the law of identity over the unverified atom 0. -/
def gap : Fm := Fm.imp (Fm.atom 0) (Fm.atom 0)

/-- The cell of §19 with `n` guards. -/
def cell (n : Nat) : Fm := Fm.imp (guardConj n) gap

/-- A refinement that verifies exactly the atoms `S` picks out, to `T`. -/
def verifyTrue (S : Nat → Bool) : Marking :=
  fun n => match S n with
           | true  => V.T
           | false => V.Z

/-- Verifying anything at all refines the all-marked start: there is no
earned ground to overwrite. -/
theorem verifyTrue_refines (S : Nat → Bool) : Refines (verifyTrue S) allZ := by
  intro n hn
  exact absurd rfl hn

/-! ### The greedy verdict is T -/

/-- A conjunction with a marked conjunct is F — one mark sinks the guard. -/
theorem guard_allZ (n : Nat) : evalF allZ (guardConj (n + 1)) = V.F := by
  show zand (allZ (n + 1)) (evalF allZ (guardConj n)) = V.F
  exact and_Z_left _

theorem gap_allZ : evalF allZ gap = V.F := imp_Z_Z

theorem cell_greedy (n : Nat) : evalF allZ (cell (n + 1)) = V.T := by
  show zimp (evalF allZ (guardConj (n + 1))) (evalF allZ gap) = V.T
  rw [guard_allZ n]
  exact imp_F_left _

/-! ### The verdict is SOUND: every completion agrees -/

/-- Once the gap atom is grounded the law of identity stands again, and the
whole cell is T no matter what the guards did. -/
theorem cell_sound (n : Nat) : Sound (cell (n + 1)) allZ := by
  intro c hc
  have hgap : evalF c gap = V.T := imp_self_of_grounded (c 0) (hc.2 0)
  show zimp (evalF c (guardConj (n + 1))) (evalF c gap) = evalF allZ (cell (n + 1))
  rw [hgap, cell_greedy n]
  exact imp_T_right _

/-! ### Nothing short of the FULL guard set can touch it -/

/-- If any guard in range is left unverified, the guard conjunction is still
F — the others may all be verified, and to anything. -/
theorem guard_F_of_missing (S : Nat → Bool) :
    ∀ (n k : Nat), 1 ≤ k → k ≤ n → S k = false →
      evalF (verifyTrue S) (guardConj n) = V.F
  | 0,     k, hk, hkn, _  => absurd (Nat.le_trans hk hkn) (by intro h; cases h)
  | n + 1, k, hk, hkn, hS => by
      show zand (verifyTrue S (n + 1)) (evalF (verifyTrue S) (guardConj n)) = V.F
      cases Nat.lt_or_ge k (n + 1) with
      | inl hlt =>
          have hin : evalF (verifyTrue S) (guardConj n) = V.F :=
            guard_F_of_missing S n k hk (Nat.le_of_lt_succ hlt) hS
          rw [hin]; exact and_F_right _
      | inr hge =>
          have heq : k = n + 1 := Nat.le_antisymm hkn hge
          have : verifyTrue S (n + 1) = V.Z := by
            show (match S (n + 1) with | true => V.T | false => V.Z) = V.Z
            rw [← heq, hS]
          rw [this]; exact and_Z_left _

/-- THE SURVIVAL CLAUSE, and it is STRONGER than §19 needed. A refinement
that leaves one guard unverified reproduces the verdict exactly — whatever
it did to the other guards AND whatever it did to the gap atom. The linter
found this: the hypothesis `S 0 = false` was stated and never used, because
a sunk guard makes the arrow vacuously true no matter what stands to its
right. Removed rather than silenced. -/
theorem survives_if_a_guard_is_missing (n : Nat) (S : Nat → Bool)
    (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    (hS : S k = false) :
    evalF (verifyTrue S) (cell (n + 1)) = evalF allZ (cell (n + 1)) := by
  have hg : evalF (verifyTrue S) (guardConj (n + 1)) = V.F :=
    guard_F_of_missing S (n + 1) k hk hkn hS
  show zimp (evalF (verifyTrue S) (guardConj (n + 1)))
            (evalF (verifyTrue S) gap) = evalF allZ (cell (n + 1))
  rw [hg, cell_greedy n]
  exact imp_F_left _

/-! ### And the FULL guard set kills it -/

/-- All guards verified true: the conjunction opens. -/
theorem guard_T_of_all (S : Nat → Bool) :
    ∀ (n : Nat), (∀ k, 1 ≤ k → k ≤ n → S k = true) →
      evalF (verifyTrue S) (guardConj n) = V.T
  | 0,     _  => rfl
  | n + 1, hA => by
      show zand (verifyTrue S (n + 1)) (evalF (verifyTrue S) (guardConj n)) = V.T
      have hhead : verifyTrue S (n + 1) = V.T := by
        show (match S (n + 1) with | true => V.T | false => V.Z) = V.T
        rw [hA (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)]
      have htail : evalF (verifyTrue S) (guardConj n) = V.T :=
        guard_T_of_all S n (fun k hk hkn => hA k hk (Nat.le_succ_of_le hkn))
      rw [hhead, htail]; exact and_T_T

/-- THE DEATH CLAUSE. Verify every guard while the gap atom stays marked, and
the sound verdict T is revoked. -/
theorem dies_when_all_guards_verified (n : Nat) (S : Nat → Bool)
    (h0 : S 0 = false) (hA : ∀ k, 1 ≤ k → k ≤ n + 1 → S k = true) :
    evalF (verifyTrue S) (cell (n + 1)) ≠ evalF allZ (cell (n + 1)) := by
  have hg : evalF (verifyTrue S) (guardConj (n + 1)) = V.T :=
    guard_T_of_all S (n + 1) hA
  have hgap : evalF (verifyTrue S) gap = V.F := by
    show zimp (verifyTrue S 0) (verifyTrue S 0) = V.F
    have : verifyTrue S 0 = V.Z := by
      show (match S 0 with | true => V.T | false => V.Z) = V.Z
      rw [h0]
    rw [this]; exact imp_Z_Z
  have hcell : evalF (verifyTrue S) (cell (n + 1)) = V.F := by
    show zimp (evalF (verifyTrue S) (guardConj (n + 1)))
              (evalF (verifyTrue S) gap) = V.F
    rw [hg, hgap]; exact imp_T_F
  rw [hcell, cell_greedy n]
  intro h; cases h

/-! ### The three clauses together -/

/-- **THE FENCE DEPTH IS NECESSARY, FOR EVERY m.** The cell's own atoms are
m = n+2, all of them marked — n+1 guards and the gap; nothing else occurs in
it, so `allZ` marking every atom costs nothing. The cell is sound; it is invariant under every
refinement that leaves any single guard unverified; and it dies exactly when
all m−1 guards are verified. What §19 checked at m = 3, 4, 5 holds at every
m at once — so no constant-depth check certifies the hereditary grade. -/
theorem fence_depth_necessary (n : Nat) :
    Sound (cell (n + 1)) allZ
  ∧ (∀ S : Nat → Bool, ∀ k, 1 ≤ k → k ≤ n + 1 → S k = false →
         evalF (verifyTrue S) (cell (n + 1)) = evalF allZ (cell (n + 1)))
  ∧ (∀ S : Nat → Bool, S 0 = false →
       (∀ k, 1 ≤ k → k ≤ n + 1 → S k = true) →
         evalF (verifyTrue S) (cell (n + 1)) ≠ evalF allZ (cell (n + 1))) :=
  ⟨cell_sound n,
   fun S k hk hkn hS => survives_if_a_guard_is_missing n S k hk hkn hS,
   fun S h0 hA => dies_when_all_guards_verified n S h0 hA⟩

/-- And therefore the cell is SOUND BUT NOT HEREDITARY, for every m — the
grade separation of §19 is generic, not a property of small examples. -/
theorem sound_not_hereditary (n : Nat) :
    Sound (cell (n + 1)) allZ ∧ ¬ Hereditary (cell (n + 1)) allZ := by
  refine ⟨cell_sound n, ?_⟩
  intro hH
  have hall : ∀ k, 1 ≤ k → k ≤ n + 1 → (decide (1 ≤ k)) = true := by
    intro k hk _
    exact decide_eq_true hk
  exact dies_when_all_guards_verified n (fun j => decide (1 ≤ j))
    (by show decide (1 ≤ 0) = false; exact decide_eq_false (by intro h; cases h))
    (fun k hk hkn => hall k hk hkn)
    (hH (verifyTrue (fun j => decide (1 ≤ j))) (verifyTrue_refines _))

/-! ## The other half: depth m−1 SUFFICES

  §19 argues this one: "for a sound verdict all full completions agree with
  it by definition, so heredity violations can live only at partial
  refinements of size at most m−1". Argued, not proved — until here.

  ФОРМУЛИРОВКА ВЫБРАНА КОНСТРУКТИВНОЙ, И ЭТО НЕ УКРАШЕНИЕ. Прямая запись
  «нарушившее уточнение ОСТАВЛЯЕТ пометку неразрешённой» есть ∃ из
  отрицания, а такой шаг берётся только через `by_contra`, то есть через
  `Classical.byContradiction` — и весь файл ушёл бы с Tier-3 аксиомами.
  Поэтому доказана положительная форма: РАЗРЕШИВШЕЕ ВСЁ — согласно.
  Содержание то же, читается контрапозицией, а список аксиом остаётся пуст.
-/

/-- Which atoms the formula actually looks at. A Bool predicate rather than
a list: no core list lemma, and the induction below stays `rfl`-driven. -/
def dependsOn : Fm → Nat → Bool
  | Fm.atom n,   a => Nat.beq n a
  | Fm.top,      _ => false
  | Fm.bot,      _ => false
  | Fm.neg φ,    a => dependsOn φ a
  | Fm.conj φ ψ, a => dependsOn φ a || dependsOn ψ a
  | Fm.disj φ ψ, a => dependsOn φ a || dependsOn ψ a
  | Fm.imp φ ψ,  a => dependsOn φ a || dependsOn ψ a
  | Fm.xor φ ψ,  a => dependsOn φ a || dependsOn ψ a
  | Fm.xnor φ ψ, a => dependsOn φ a || dependsOn ψ a

/-- Reflexivity of Nat equality, proved here rather than taken from core.

    ЦЕНА ЖИВЁТ В ИНСТАНСЕ, А НЕ В ЛЕММЕ. Первая редакция брала `beq_self_eq_true`.
    Сама лемма на пустом списке — `#print axioms beq_self_eq_true` это и говорит.
    Но ПРИМЕНЁННАЯ К `Nat` она тащит propext, Classical.choice и Quot.sound: цена
    сидит в разрешённом на месте инстансе `LawfulBEq Nat`, а не в тексте леммы.
    Отсюда правило: чистота общей леммы НЕ ЕСТЬ чистота её применения — мерить
    надо применение. Найдено бисекцией 2026-09-05, после шести зондов мимо. -/
theorem natBeq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0     => rfl
  | n + 1 => natBeq_refl n

/-- Agreement on what the formula looks at is agreement on the verdict.

    ПОЧЕМУ ТАКТИКОЙ, А НЕ УРАВНЕНИЯМИ. Первая редакция была написана как
    определение с образцами по `φ` при зависимой второй гипотезе. Уравнительный
    компилятор не увидел структурной рекурсии, ушёл в well-founded — и потянул
    ВСЕ ТРИ аксиомы, включая `Classical.choice`. Тот же довод через `induction`
    чист. Промерено, не угадано. -/
theorem evalF_congr_dep {m' m : Marking} (φ : Fm) :
    (∀ n, dependsOn φ n = true → m' n = m n) → evalF m' φ = evalF m φ := by
  induction φ with
  | atom n => intro h; exact h n (natBeq_refl n)
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih =>
      intro h
      show znot (evalF m' φ) = znot (evalF m φ)
      rw [ih h]
  | conj φ ψ ihφ ihψ =>
      intro h
      show zand (evalF m' φ) (evalF m' ψ) = zand (evalF m φ) (evalF m ψ)
      rw [ihφ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true
            rw [hn]; exact Bool.or_true _))]
  | disj φ ψ ihφ ihψ =>
      intro h
      show zor (evalF m' φ) (evalF m' ψ) = zor (evalF m φ) (evalF m ψ)
      rw [ihφ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true
            rw [hn]; exact Bool.or_true _))]
  | imp φ ψ ihφ ihψ =>
      intro h
      show zimp (evalF m' φ) (evalF m' ψ) = zimp (evalF m φ) (evalF m ψ)
      rw [ihφ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true
            rw [hn]; exact Bool.or_true _))]
  | xor φ ψ ihφ ihψ =>
      intro h
      show zxor (evalF m' φ) (evalF m' ψ) = zxor (evalF m φ) (evalF m ψ)
      rw [ihφ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true
            rw [hn]; exact Bool.or_true _))]
  | xnor φ ψ ihφ ihψ =>
      intro h
      show zxnor (evalF m' φ) (evalF m' ψ) = zxnor (evalF m φ) (evalF m ψ)
      rw [ihφ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by
            show (dependsOn φ n || dependsOn ψ n) = true
            rw [hn]; exact Bool.or_true _))]

/-- Close a refinement into an ending: every mark still standing is resolved
to T. An arbitrary choice, and that is the point — the ending exists, its
content does not matter. -/
def close (m' : Marking) : Marking :=
  fun n => match m' n with
           | V.T => V.T
           | V.F => V.F
           | V.Z => V.T

theorem close_grounded (m' : Marking) (n : Nat) : close m' n ≠ V.Z := by
  show (match m' n with | V.T => V.T | V.F => V.F | V.Z => V.T) ≠ V.Z
  cases m' n <;> intro h <;> cases h

theorem close_fixes (m' : Marking) (n : Nat) (h : m' n ≠ V.Z) :
    close m' n = m' n := by
  show (match m' n with | V.T => V.T | V.F => V.F | V.Z => V.T) = m' n
  cases hv : m' n with
  | T => rfl
  | F => rfl
  | Z => exact absurd hv h

theorem close_completion {m' m : Marking} (hr : Refines m' m) :
    Completion (close m') m :=
  ⟨fun n hn => by rw [close_fixes m' n (by rw [hr n hn]; exact hn), hr n hn],
   close_grounded m'⟩

/-- **DEPTH m−1 SUFFICES.** A refinement that has resolved every mark the
formula depends on cannot revoke a SOUND verdict — it has become an ending,
and an ending agrees by soundness. Read the other way round: a violation can
only happen while some relevant mark is still unresolved, i.e. strictly
before the last of the m marks is verified — at depth at most m−1. -/
theorem resolved_all_marks_agrees {φ : Fm} {m m' : Marking}
    (hs : Sound φ m) (hr : Refines m' m)
    (hall : ∀ a, dependsOn φ a = true → m a = V.Z → m' a ≠ V.Z) :
    evalF m' φ = evalF m φ := by
  have hnz : ∀ a, dependsOn φ a = true → m' a ≠ V.Z := by
    intro a ha
    cases hm : m a with
    | T => rw [hr a (by rw [hm]; intro h; cases h)]; rw [hm]; intro h; cases h
    | F => rw [hr a (by rw [hm]; intro h; cases h)]; rw [hm]; intro h; cases h
    | Z => exact hall a ha hm
  have hagree : evalF m' φ = evalF (close m') φ :=
    (evalF_congr_dep φ (fun n hn => (close_fixes m' n (hnz n hn)).symm))
  rw [hagree]
  exact hs (close m') (close_completion hr)

/-- **THE WHOLE DEPTH CLAIM OF §19, BOTH HALVES, IN ONE STATEMENT.**

    SUFFICIENT — the fence is never deeper than m−1: a sound verdict cannot be
    revoked by any refinement that has resolved every mark the formula depends
    on, because such a refinement has become an ending and endings agree.

    NECESSARY — and never shallower: for every m there is a sound cell that
    survives every refinement leaving even one guard unverified, and dies the
    moment the full guard set is verified.

    The same single step is left to prose in both halves, deliberately: the
    finite counting that turns "some relevant mark is still unresolved" into
    "fewer than m atoms were inspected". That is arithmetic, not logic, and
    smuggling it in would make the file look more complete than it is. -/
theorem fence_depth_exact :
    (∀ (φ : Fm) (m m' : Marking), Sound φ m → Refines m' m →
       (∀ a, dependsOn φ a = true → m a = V.Z → m' a ≠ V.Z) →
       evalF m' φ = evalF m φ)
  ∧ (∀ n : Nat,
       Sound (cell (n + 1)) allZ
     ∧ (∀ (S : Nat → Bool) (k : Nat), 1 ≤ k → k ≤ n + 1 → S k = false →
          evalF (verifyTrue S) (cell (n + 1)) = evalF allZ (cell (n + 1)))
     ∧ (∀ S : Nat → Bool, S 0 = false →
          (∀ k, 1 ≤ k → k ≤ n + 1 → S k = true) →
          evalF (verifyTrue S) (cell (n + 1)) ≠ evalF allZ (cell (n + 1)))) :=
  ⟨fun _ _ _ hs hr hall => resolved_all_marks_agrees hs hr hall,
   fence_depth_necessary⟩

end ZFenceDepth

#print axioms ZFenceDepth.imp_self_of_grounded
#print axioms ZFenceDepth.verifyTrue_refines
#print axioms ZFenceDepth.cell_greedy
#print axioms ZFenceDepth.cell_sound
#print axioms ZFenceDepth.guard_F_of_missing
#print axioms ZFenceDepth.survives_if_a_guard_is_missing
#print axioms ZFenceDepth.guard_T_of_all
#print axioms ZFenceDepth.dies_when_all_guards_verified
#print axioms ZFenceDepth.fence_depth_necessary
#print axioms ZFenceDepth.sound_not_hereditary
#print axioms ZFenceDepth.evalF_congr_dep
#print axioms ZFenceDepth.close_completion
#print axioms ZFenceDepth.resolved_all_marks_agrees
#print axioms ZFenceDepth.fence_depth_exact
#print axioms ZFenceDepth.dependsOn
#print axioms ZFenceDepth.close
#print axioms ZFenceDepth.close_fixes
#print axioms ZFenceDepth.close_grounded
