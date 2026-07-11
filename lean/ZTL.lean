/-!
# ZTL — Zero-Trust Logic: машинно-проверенное ядро

Значения T/F (вердикты двузначны) + метка входа Z; порождающий
принцип «истина не в кредит»:
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

/-! ## Часть II: следование, два регистра, неподвижная точка -/

/-! ### Правила вывода как следования (выделенное значение {T}) -/

theorem rule_modus_tollens : ∀ p q, zimp p q = T → znot q = T → znot p = T := by decide
theorem rule_contraposition : ∀ p q, zimp p q = T → zimp (znot q) (znot p) = T := by decide
theorem rule_disj_syllogism : ∀ p q, zor p q = T → znot p = T → q = T := by decide
theorem rule_and_intro : ∀ p q, p = T → q = T → zand p q = T := by decide
theorem rule_and_elim : ∀ p q, zand p q = T → p = T := by decide
theorem rule_or_intro : ∀ p q, p = T → zor p q = T := by decide
theorem rule_dn_intro : ∀ p, p = T → znot (znot p) = T := by decide
theorem rule_transitivity : ∀ p q r, zimp p q = T → zimp q r = T → zimp p r = T := by decide
theorem rule_K : ∀ p q, q = T → zimp p q = T := by decide
theorem rule_explosion : ∀ p q, p = T → znot p = T → q = T := by decide
theorem rule_resolution : ∀ p q r, zor p q = T → zor (znot p) r = T → zor q r = T := by decide

/-- Павшее правило: ¬¬-удаление (Z протекает сквозь двойное отрицание). -/
theorem rule_dn_elim_fails : ¬ ∀ p, znot (znot p) = T → p = T := by decide
/-- Павшее правило: тавтология в заключении (свежий атом не заслуживает T). -/
theorem rule_taut_concl_fails : ¬ ∀ p q, p = T → zor q (znot q) = T := by decide

/-! Раскол «правила против законов»: контрапозиция-ПРАВИЛО жива
(rule_contraposition), контрапозиция-ЗАКОН пала (contraposition_fails).
Классика склеивает их теоремой дедукции; у ZTL она односторонняя
(dt_one_way: zimp Z Z = F при тривиальном p⊨p). -/

/-! ### Паракомплектность, не параконсистентность -/

theorem no_gluts : ∀ p, ¬(p = T ∧ znot p = T) := by decide

/-! ### Ленивый регистр (сильный Клини) и информационный порядок -/

def knot : V → V
  | T => F | F => T | Z => Z

def kand : V → V → V
  | F, _ => F | _, F => F
  | Z, _ => Z | _, Z => Z
  | T, T => T

def kor : V → V → V
  | T, _ => T | _, T => T
  | Z, _ => Z | _, Z => Z
  | F, F => F

/-- Информационный порядок: Z ⊑ всё, T и F несравнимы. -/
def leqb (a b : V) : Bool := a == b || a == Z

theorem kleene_not_monotone : ∀ a b, leqb a b = true →
    leqb (knot a) (knot b) = true := by decide
theorem kleene_and_monotone : ∀ a b c d, leqb a c = true → leqb b d = true →
    leqb (kand a b) (kand c d) = true := by decide
theorem kleene_or_monotone : ∀ a b c d, leqb a c = true → leqb b d = true →
    leqb (kor a b) (kor c d) = true := by decide

/-- Жадный регистр немонотонен — аргумент Кнастера–Тарского неприменим. -/
theorem eager_and_not_monotone : ¬ ∀ a b c d, leqb a c = true →
    leqb b d = true → leqb (zand a b) (zand c d) = true := by decide
theorem eager_not_not_monotone : ¬ ∀ a b, leqb a b = true →
    leqb (znot a) (znot b) = true := by decide

/-! ### Лжец, карусель, мститель — неподвижные точки -/

/-- Лжец находит дом в ленивом регистре... -/
theorem liar_kleene_home : knot Z = Z := rfl

/-- ...а карусель Журдена не имеет жадной модели ни при каких значениях:
требование v(A)=v(B) и v(B)=v(¬A) невыполнимо (все 9 пар). -/
theorem carousel_no_model : ∀ a b : V, ¬(a = b ∧ b = znot a) := by decide

/-- Ленивое заземление карусели: (Z,Z) — неподвижная точка. -/
theorem carousel_kleene_fp : (Z : V) = Z ∧ knot Z = Z := ⟨rfl, rfl⟩

/-- Пуля мстителя, вычисленная: содержание μ = ¬Tr(μ) ∨ isZ(μ) при
заземлённом μ=Z жадно даёт T — а истина предложению не выдаётся. -/
theorem revenge_bullet : zor (znot Z) (isZ Z) = T := by decide

#print axioms modus_ponens
#print axioms lem_fails
#print axioms liar_homeless
#print axioms lift2_classical
#print axioms rule_contraposition
#print axioms eager_and_not_monotone
#print axioms carousel_no_model
#print axioms revenge_bullet

end V
