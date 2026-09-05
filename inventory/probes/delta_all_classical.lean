/-
  НЕ ЧАСТЬ КОРПУСА, И ЭТО НАМЕРЕННО.

  Здесь лежит классическое доказательство четвёртого правила параметрических
  таблиц — `F:∀xφ → N:φ(c*)`. Оно НЕ входит ни в lakefile, ни в аудит, потому
  что корпус несёт один инвариант, с которого начинается статья: всякая его
  теорема на пустом списке аксиом. Теорема, которая инвариант ломает, не
  получает исключения в стороже — она получает отдельный стенд.

  Прибор `ПАРАМЕТР-ЯРУС.py` гоняет этот файл и сверяет, что список аксиом
  ИМЕННО ТАКОЙ, какой заявлен. Если он вдруг станет пустым — значит нашёлся
  бесвыборный путь, и стенд обязан покраснеть, а не промолчать.
-/
import ZTL

open V

def IsAll {α : Type} (φ : α → V) (v : V) : Prop :=
  (v = T ↔ ∀ d, φ d = T) ∧ (v = T ∨ v = F)

theorem delta_all_classical {α : Type} (φ : α → V) (v : V)
    (h : IsAll φ v) (hv : v = F) : ∃ d, φ d ≠ T := by
  have hnot : ¬ ∀ d, φ d = T := by
    intro hall
    have : v = T := h.1.mpr hall
    rw [hv] at this
    exact V.noConfusion this
  exact Classical.byContradiction (fun hne =>
    hnot (fun d => Classical.byContradiction (fun hd => hne ⟨d, hd⟩)))

#print axioms delta_all_classical
