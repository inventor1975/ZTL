/-
  НЕ ЧАСТЬ КОРПУСА, И ЭТО НАМЕРЕННО — второй зонд рядом с
  `delta_all_classical.lean`, тем же приёмом.

  Движок E48/E51 с 06.09.2026 (E54) несёт четвёртое правило δ₂ — `F:∀xφ →
  N:φ(c*)` — ЗА ФЛАГОМ `d2`. Его надёжность входит в корпус ГИПОТЕЗОЙ
  `ZParamEngine.Delta2Step`: «если δ₂ сохраняет выполнимость, то поиск с
  флагом надёжен». Здесь та гипотеза доказана — классически, потому что из
  «не всякий экземпляр строго T» надо добыть экземпляр, а это `¬∀ → ∃¬`.

  Прибор `ПАРАМЕТР-ЯРУС.py` гоняет этот файл и сверяет, что список аксиом
  ИМЕННО классический. Станет пустым — найден бесвыборный путь; стенд обязан
  покраснеть, а не промолчать.
-/
import ZParamEngine

open V
open ZParamSyntax
open ZParamTableau
open ZParamEngine

theorem delta2_step_classical {α : Type} (I : Nat → List α → V) (d : α) :
    Delta2Step I d := by
  intro htot ρ b φ c hb hmem hfresh
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvF : v = F := (vF v).mp hs
  have hnot : ¬ ∀ a, Holds I ρ d (a :: []) φ T := by
    intro hall
    have hspec : ((v = T) ↔ ∀ a, Holds I ρ d (a :: []) φ T) ∧ (v = T ∨ v = F) := hv
    have : v = T := hspec.1.mpr hall
    rw [hvF] at this
    exact V.noConfusion this
  -- the classical step: from ¬∀ to a witness
  have ⟨a, ha⟩ : ∃ a, ¬ Holds I ρ d (a :: []) φ T :=
    Classical.byContradiction (fun hne =>
      hnot (fun a => Classical.byContradiction (fun hd => hne ⟨a, hd⟩)))
  refine ⟨a, ?_⟩
  intro nd hnd
  have hc : upd ρ c a c = a := by
    show (match Nat.beq c c with | true => a | false => ρ c) = a
    rw [natBeq_refl c]
  have hφ : occurs c φ = false := hfresh _ (List.Mem.head b)
  cases hnd with
  | head =>
      have ⟨u, hu⟩ := htot (upd ρ c a) (inst c 0 φ) []
      refine ⟨u, hu, ?_⟩
      have hnT : u ≠ T := by
        intro huT
        rw [huT] at hu
        have h1 : Holds I (upd ρ c a) d (upd ρ c a c :: []) φ T :=
          (holds_inst I (upd ρ c a) d c φ [] T 0).mp hu
        rw [hc] at h1
        exact ha ((holds_fresh I ρ c a d φ (a :: []) T hφ).mp h1)
      exact (vN u).mpr ((vN_neq u).mpr hnT)
  | tail _ ht =>
      have ⟨w, hw, hsw⟩ := hb nd ht
      have hnf : occurs c nd.2 = false := hfresh nd (List.Mem.tail _ ht)
      exact ⟨w, (holds_fresh I ρ c a d nd.2 [] w hnf).mpr hw, hsw⟩

#print axioms delta2_step_classical
