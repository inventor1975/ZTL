/-!
# ZTL — Zero-Trust Logic: машинно-проверенное ядро

Три значения T/F/Z; порождающий принцип «истина не в кредит»:
связка возвращает T, только если T вынуждена при каждом классическом
прочтении Z. Все связки ПОРОЖДАЮТСЯ подъёмом (`lift1`/`lift2`) —
таблицы не постулируются, а вычисляются; опорные клетки куратора
доказываются как теоремы.

Дисциплина VR: `#print axioms` в конце файла — весь корпус обязан
держаться на пустом списке аксиом (чистый перебор, `decide`).
-/

inductive V where
  | T
  | F
  | Z
deriving DecidableEq, Repr

namespace V

/-- Классические прочтения значения: Z читается и как истина, и как ложь. -/
def subs : V → List Bool
  | T => [true]
  | F => [false]
  | Z => [true, false]

/-- Подъём унарной классической связки: T, только если T вынуждена
при каждом прочтении. -/
def lift1 (f : Bool → Bool) (x : V) : V :=
  if (subs x).all (fun a => f a) then T else F

/-- Подъём бинарной классической связки (каждое вхождение Z независимо). -/
def lift2 (f : Bool → Bool → Bool) (x y : V) : V :=
  if (subs x).all (fun a => (subs y).all (fun b => f a b)) then T else F

def znot  : V → V     := lift1 (fun a => !a)
def zand  : V → V → V := lift2 (fun a b => a && b)
def zor   : V → V → V := lift2 (fun a b => a || b)
def zimp  : V → V → V := lift2 (fun a b => !a || b)
def zxor  : V → V → V := lift2 (fun a b => a != b)
def zxnor : V → V → V := lift2 (fun a b => a == b)

/-- Детектор карантина, выразимый внутри языка: isZ x = ¬(x↔x). -/
def isZ (x : V) : V := znot (zxnor x x)

/-- Перебор трёх значений разрешим — этим живут все `decide` ниже. -/
instance (p : V → Prop) [DecidablePred p] : Decidable (∀ x : V, p x) :=
  decidable_of_iff (p T ∧ p F ∧ p Z)
    ⟨fun ⟨hT, hF, hZ⟩ x => by cases x <;> assumption,
     fun h => ⟨h T, h F, h Z⟩⟩

/-! ## Опорные клетки куратора (аксиомы диалога 2026-07-10) — теперь теоремы -/

theorem ax_not_Z    : znot Z = F := by decide
theorem ax_notnot_Z : znot (znot Z) = T := by decide
theorem ax_xnor_ZZ  : zxnor Z Z = F := by decide
theorem ax_xnor_ZT  : zxnor Z T = F := by decide
theorem ax_xor_ZZ   : zxor Z Z = F := by decide
theorem ax_xor_ZF   : zxor Z F = F := by decide
theorem ax_xor_ZT   : zxor Z T = F := by decide

/-! ## Теорема жадности: составные формулы классичны, Z живёт лишь на атомах -/

theorem lift1_classical (f : Bool → Bool) (x : V) :
    lift1 f x = T ∨ lift1 f x = F := by
  unfold lift1; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem lift2_classical (f : Bool → Bool → Bool) (x y : V) :
    lift2 f x y = T ∨ lift2 f x y = F := by
  unfold lift2; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Живые законы (12) -/

theorem imp_def   : ∀ p q, zimp p q = zor (znot p) q := by decide
theorem xor_def   : ∀ p q, zxor p q = zor (zand p (znot q)) (zand (znot p) q) := by decide
theorem xnor_def  : ∀ p q, zxnor p q = zor (zand p q) (zand (znot p) (znot q)) := by decide
theorem xnor_imps : ∀ p q, zxnor p q = zand (zimp p q) (zimp q p) := by decide
theorem and_comm' : ∀ p q, zand p q = zand q p := by decide
theorem or_comm'  : ∀ p q, zor p q = zor q p := by decide
theorem and_assoc' : ∀ p q r, zand (zand p q) r = zand p (zand q r) := by decide
theorem or_assoc'  : ∀ p q r, zor (zor p q) r = zor p (zor q r) := by decide
theorem and_distrib : ∀ p q r, zand p (zor q r) = zor (zand p q) (zand p r) := by decide
theorem or_distrib  : ∀ p q r, zor p (zand q r) = zand (zor p q) (zor p r) := by decide
theorem no_contradiction : ∀ p, znot (zand p (znot p)) = T := by decide
theorem imp_trans_law : ∀ p q r,
    zimp (zand (zimp p q) (zimp q r)) (zimp p r) = T := by decide

/-- Modus ponens, семантический: заслуженная истина транспортируется. -/
theorem modus_ponens : ∀ p q : V, p = T → zimp p q = T → q = T := by decide

/-! ## Павшие законы (14) — манифест, машинно заверенный -/

theorem double_neg_fails : ¬ ∀ p, znot (znot p) = p := by decide
theorem deMorgan1_fails : ¬ ∀ p q, znot (zand p q) = zor (znot p) (znot q) := by decide
theorem deMorgan2_fails : ¬ ∀ p q, znot (zor p q) = zand (znot p) (znot q) := by decide
theorem contraposition_fails : ¬ ∀ p q, zimp p q = zimp (znot q) (znot p) := by decide
theorem xor_as_not_xnor_fails : ¬ ∀ p q, zxor p q = znot (zxnor p q) := by decide
theorem and_idem_fails : ¬ ∀ p, zand p p = p := by decide
theorem or_idem_fails : ¬ ∀ p, zor p p = p := by decide
theorem absorption_fails : ¬ ∀ p q, zand p (zor p q) = p := by decide
theorem and_true_fails : ¬ ∀ p, zand p T = p := by decide
theorem or_false_fails : ¬ ∀ p, zor p F = p := by decide
theorem lem_fails : ¬ ∀ p, zor p (znot p) = T := by decide
theorem imp_refl_fails : ¬ ∀ p, zimp p p = T := by decide
theorem peirce_fails : ¬ ∀ p q, zimp (zimp (zimp p q) p) p = T := by decide
theorem k_axiom_fails : ¬ ∀ p q, zimp q (zimp p q) = T := by decide

/-! ## Мини-теоремы каркаса (препринт §3.5) -/

/-- У отрицания нет неподвижной точки — лжец таблично бездомен;
карантинный флаг неустраним. -/
theorem liar_homeless : ∀ v : V, znot v ≠ v := by decide

/-- Карантин детектируем изнутри (дверь для мстителя — плата развилки 3). -/
theorem isZ_detects : isZ Z = T ∧ isZ T = F ∧ isZ F = F := by decide

/-- Раскол «правила против законов» в одной точке: правило p⊨p тривиально,
а закон ⊨p→p пал — теорема дедукции односторонняя. -/
theorem dt_one_way : zimp Z Z = F := by decide

/-- Кванторы на доме {a}: ∀ = строгая конъюнкция экземпляров. -/
def allq (v : V) : V := if v = T then T else F
def exq  (v : V) : V := if v = T then T else F

/-- Кванторная асимметрия: UI жив как ЗАКОН (⊨ ∀yP→P(a)) —
универсалия заслужена, тратится свободно... -/
theorem ui_law : ∀ v : V, zimp (allq v) v = T := by decide

/-- ...а EG как закон пал (P(a)=Z не даёт ∃): строгий свидетель обязателен. -/
theorem eg_law_fails : ¬ ∀ v : V, zimp v (exq v) = T := by decide

#print axioms modus_ponens
#print axioms lem_fails
#print axioms liar_homeless
#print axioms lift2_classical

end V
