import ZTL

/-!
# Факты: кванторы на конечных доменах и динамика парадоксов. Ноль аксиом.

Кванторы над конечным доменом — это свёртки: ∀ = zand (все строго T),
∃ = zor (строгий свидетель). Домены 1–2 представлены кортежами значений.
Динамика: периоды осцилляций, Карри, чётность циклов, обрезка Ябло.
-/

namespace V

/-! ## Кванторы, домен 2: ∀ = zand, ∃ = zor -/

/-- UI-закон жив на доме 2: ⊨ ∀P → P(a). -/
theorem ui_law_dom2 : ∀ p₁ p₂ : V, zimp (zand p₁ p₂) p₁ = T := by decide

/-- EG-закон пал: ⊭ P(a) → ∃P (Z-свидетель не считается). -/
theorem eg_law_dom2_fails : ¬ ∀ p₁ p₂ : V, zimp p₁ (zor p₁ p₂) = T := by
  decide

/-- Живое правило: ∀¬ ⊨ ¬∃. -/
theorem allnot_notex_dom2 : ∀ p₁ p₂ : V,
    zand (znot p₁) (znot p₂) = T → znot (zor p₁ p₂) = T := by decide

/-- Павшее правило: ¬∃ ⊭ ∀¬ (Z прячется под отрицанием). -/
theorem notex_allnot_dom2_fails : ¬ ∀ p₁ p₂ : V,
    (znot (zor p₁ p₂) = T → zand (znot p₁) (znot p₂) = T) := by decide

/-- Павшее правило-зеркало: ¬∀ ⊭ ∃¬. -/
theorem notall_exnot_dom2_fails : ¬ ∀ p₁ p₂ : V,
    (znot (zand p₁ p₂) = T → zor (znot p₁) (znot p₂) = T) := by decide

/-- Кв. LEM пал: ⊭ ∀x (P(x) ∨ ¬P(x)). -/
theorem qlem_dom2_fails : ¬ ∀ p₁ p₂ : V,
    zand (zor p₁ (znot p₁)) (zor p₂ (znot p₂)) = T := by decide

/-- «Пьяница» пал: ⊭ ∃x (P(x) → ∀y P(y)). -/
theorem drinker_dom2_fails : ¬ ∀ p₁ p₂ : V,
    zor (zimp p₁ (zand p₁ p₂)) (zimp p₂ (zand p₁ p₂)) = T := by decide

/-! ## Динамика: осцилляции и неподвижные точки -/

/-- Лжец: период 2 на классике (¬¬v = v, ¬v ≠ v). -/
theorem liar_period2 : ∀ v : V, (v = T ∨ v = F) →
    znot (znot v) = v ∧ znot v ≠ v := by decide

/-- Карусель Журдена: скачок J(a,b) = (b, ¬a) не имеет неподвижных точек. -/
theorem carousel_no_fp : ∀ a b : V, ¬(b = a ∧ znot a = b) := by decide

/-- Карусель: период 4 на классике. -/
theorem carousel_period4 : ∀ a b : V, (a = T ∨ a = F) → (b = T ∨ b = F) →
    (znot (znot a), znot (znot b)) = (a, b) := by decide

/-- Карри c = (Tr c → ⊥): жадно бездомен — и без отрицания. -/
theorem curry_homeless : ∀ v : V, zimp v F ≠ v := by decide

/-- Карри находит дом в ленивом регистре: kimp Z ⊥ = Z. -/
theorem curry_kleene_home : kor (knot Z) F = Z := rfl

/-- Чётность, цикл 3 с одной инверсией: моделей нет. -/
theorem odd3_no_model : ∀ a b c : V, ¬(a = b ∧ b = c ∧ c = znot a) := by
  decide

/-- Чётность, цикл 2 с двумя инверсиями: модели ЕСТЬ (недоопределённость). -/
theorem even2_has_model : ∃ a b : V, a = znot b ∧ b = znot a :=
  ⟨T, F, rfl, rfl⟩

/-- Обрезка Ябло (n=3): единственная модель F,F,T — заземлена, парадокса
нет; парадокс Ябло живёт только на актуальной бесконечности. -/
theorem yablo3_unique : ∀ a b c : V,
    (a = zand (znot b) (znot c) ∧ b = znot c ∧ c = T) ↔
    (a = F ∧ b = F ∧ c = T) := by decide

/-- Крокодил: сделка R↔M на заземлённой точке (Z,Z) не заслуживает
истины — договор ничтожен. -/
theorem crocodile_deal_void : zxnor Z Z = F := rfl

#print axioms ui_law_dom2
#print axioms notex_allnot_dom2_fails
#print axioms liar_period2
#print axioms carousel_period4
#print axioms curry_homeless
#print axioms yablo3_unique

end V
