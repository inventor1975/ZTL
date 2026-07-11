import ZTL

/-!
# Lean-порт Э5: множества с непроверенными элементами. Ноль аксиом.

Равенство элементов — атом (T/F для проверенных, Z при любой метке);
членство/включение — рекурсивные свёртки zor/zand. Законы тождества
падают на мечеными — унаследовано от таблиц, теоремами.
-/

namespace V

inductive El where
  | v : Nat → El
  | z : Nat → El

/-- Атом равенства: тождество меток не зарабатывается (даже с собой). -/
def eqAtom : El → El → V
  | .v a, .v b => cond (a == b) T F
  | .v _, .z _ => Z
  | .z _, .v _ => Z
  | .z _, .z _ => Z

/-- Членство: ∃-свёртка (строгий свидетель). -/
def memL (x : El) : List El → V
  | [] => F
  | e :: es => zor (eqAtom x e) (memL x es)

/-- Включение: ∀-свёртка (все строго T). -/
def subL (S₁ S₂ : List El) : V :=
  match S₁ with
  | [] => T
  | e :: es => zand (memL e S₂) (subL es S₂)

def seteq (S₁ S₂ : List El) : V := zand (subL S₁ S₂) (subL S₂ S₁)

/-! ## Служебные значные леммы (перебором, чисто) -/

theorem zorZ : ∀ x : V, (x = T ∨ x = F) → zor x Z = x := by decide
theorem zorF : ∀ x : V, (x = T ∨ x = F) → zor F x = x := by decide
theorem zandXF : ∀ x : V, zand x F = F := by decide
theorem zandFX : ∀ y : V, zand F y = F := by decide
theorem memL_classical : ∀ (x : El) (es : List El),
    memL x es = T ∨ memL x es = F := by
  intro x es
  induction es with
  | nil => exact Or.inr rfl
  | cons e es ih =>
    show zor (eqAtom x e) (memL x es) = T ∨ zor (eqAtom x e) (memL x es) = F
    exact lift2_classical _ _ _

/-! ## Теорема 1: метка не зарабатывает членства НИГДЕ (Z ∉ что угодно) -/

theorem memZ : ∀ (i : Nat) (es : List El), memL (.z i) es = F := by
  intro i es
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h1 : zor (eqAtom (.z i) e) (memL (.z i) es)
        = zor (eqAtom (.z i) e) F := congrArg _ ih
    have h2 : zor (eqAtom (.z i) e) F = F := by cases e <;> rfl
    exact h1.trans h2

/-! ## Теорема 2: меченое множество не влезает даже в себя (S ⊆ S падает) -/

theorem sub_marked_false : ∀ (i : Nat) (pre S : List El),
    subL (pre ++ [.z i]) S = F := by
  intro i pre S
  induction pre with
  | nil =>
    exact (congrArg (fun x => zand x (subL [] S)) (memZ i S)).trans (zandFX _)
  | cons e pre ih =>
    exact (congrArg (zand (memL e S)) ih).trans (zandXF _)

/-- Следствие: рефлексивность равенства множеств падает на мечеными. -/
theorem seteq_self_marked (i : Nat) (pre : List El) :
    seteq (pre ++ [El.z i]) (pre ++ [El.z i]) = F :=
  (congrArg (fun x => zand x (subL (pre ++ [El.z i]) (pre ++ [El.z i])))
    (sub_marked_false i pre (pre ++ [El.z i]))).trans (zandFX _)

/-! ## Конкретика Э5 (вычислением, как в Python-стенде) -/

-- {Z,Z} = {Z}: склейка не заработана
example : seteq [.z 1, .z 1] [.z 1] = F := rfl
-- Z ∈ {Z} — та же метка! — членство не заработано
example : memL (.z 1) [.z 1] = F := rfl
-- проверенные — классика: 1 ∈ {1,2,Z}, 3 ∉ {1,2,Z}
example : memL (.v 1) [.v 1, .v 2, .z 7] = T := rfl
example : memL (.v 3) [.v 1, .v 2, .z 7] = F := rfl
-- чистая рефлексивность жива, меченая пала
example : seteq [.v 1, .v 2] [.v 1, .v 2] = T := rfl
example : seteq [.v 1, .v 2, .z 7] [.v 1, .v 2, .z 7] = F := rfl

/-! ## Мощность: интервал; |{Z}| = [1,1] — мощность без тождества -/

def cardLo (core quar : Nat) : Nat := if core = 0 then min quar 1 else core
def cardHi (core quar : Nat) : Nat := core + quar

example : cardLo 2 0 = 2 ∧ cardHi 2 0 = 2 := ⟨rfl, rfl⟩   -- |{1,2}| = [2,2]
example : cardLo 2 1 = 2 ∧ cardHi 2 1 = 3 := ⟨rfl, rfl⟩   -- |{1,2,Z}| = [2,3]
example : cardLo 0 1 = 1 ∧ cardHi 0 1 = 1 := ⟨rfl, rfl⟩   -- |{Z}| = [1,1] (!)
example : cardLo 0 2 = 1 ∧ cardHi 0 2 = 2 := ⟨rfl, rfl⟩   -- |{Z,Z}| = [1,2]

#print axioms memZ
#print axioms sub_marked_false
#print axioms seteq_self_marked

end V
