import ZTL

/-!
# Торговый сертификат: корректность и полнота движка таблó ZTL

Движок работает на порождающем базисе {¬,∧,∨}; связки →,⊕,↔ сводятся
к базису живыми тождествами (imp_def, xor_def, xnor_def — теоремы ZTL).
Главная теорема closes_iff: таблó закрывается ⟺ узлы невыполнимы.
Следствие tproves_iff: выводимость Γ ⊢ φ ⟺ семантическое следование.
-/

namespace V

abbrev Sign := List V

abbrev SignT : Sign := [T]
abbrev SignF : Sign := [F]
abbrev SignP : Sign := [T, Z]
abbrev SignN : Sign := [F, Z]

abbrev Node := Sign × Fm

/-- Оценка удовлетворяет узлу: значение формулы лежит в знаке. -/
def satN (v : Nat → V) (nd : Node) : Prop := evalF v nd.2 ∈ nd.1

def satL (v : Nat → V) (ns : List Node) : Prop := ∀ nd ∈ ns, satN v nd

/-- Накопленные ограничения на атомы. -/
abbrev Env := Nat → Sign

def envOK (v : Nat → V) (e : Env) : Prop := ∀ n, v n ∈ e n

/-- Выполнимость набора узлов при ограничениях. -/
def SAT (e : Env) (ws : List Node) : Prop := ∃ v, envOK v e ∧ satL v ws

def inter (l s : Sign) : Sign := l.filter (fun a => decide (a ∈ s))

theorem mem_inter {x : V} {l s : Sign} : x ∈ inter l s ↔ x ∈ l ∧ x ∈ s := by
  constructor
  · intro h
    have h' := List.mem_filter.mp h
    exact ⟨h'.1, of_decide_eq_true h'.2⟩
  · intro ⟨h1, h2⟩
    exact List.mem_filter.mpr ⟨h1, decide_eq_true h2⟩

def upd (e : Env) (n : Nat) (s : Sign) : Env := fun m => if m = n then s else e m

/-- Взвешенный размер: тяжёлые связки весят столько, чтобы сведение
к базису строго уменьшало вес. -/
def Fm.size : Fm → Nat
  | .atom _   => 1
  | .neg φ    => φ.size + 1
  | .conj φ ψ => φ.size + ψ.size + 1
  | .disj φ ψ => φ.size + ψ.size + 1
  | .imp φ ψ  => φ.size + ψ.size + 3
  | .xor φ ψ  => 2 * φ.size + 2 * ψ.size + 6
  | .xnor φ ψ => 2 * φ.size + 2 * ψ.size + 6

theorem Fm.size_pos : ∀ φ : Fm, 1 ≤ φ.size := by
  intro φ; cases φ <;> simp only [Fm.size] <;> omega

def wsize : List Node → Nat
  | [] => 0
  | nd :: rest => nd.2.size + wsize rest

/-- Движок таблó: атом — пересечение ограничений; ¬,∧,∨ — знаковые
правила (ослабленные знаки только в F-полярности); →,⊕,↔ — сведение
к базису каноническими тождествами. -/
def closes (e : Env) : List Node → Bool
  | [] => false
  | (s, .atom n) :: rest =>
      if inter (e n) s = [] then true
      else closes (upd e n (inter (e n) s)) rest
  | (s, .neg φ) :: rest =>
      if T ∈ s then
        if F ∈ s then closes e rest
        else closes e ((SignF, φ) :: rest)
      else
        if F ∈ s then closes e ((SignP, φ) :: rest)
        else true
  | (s, .conj φ ψ) :: rest =>
      if T ∈ s then
        if F ∈ s then closes e rest
        else closes e ((SignT, φ) :: (SignT, ψ) :: rest)
      else
        if F ∈ s then
          closes e ((SignN, φ) :: rest) && closes e ((SignN, ψ) :: rest)
        else true
  | (s, .disj φ ψ) :: rest =>
      if T ∈ s then
        if F ∈ s then closes e rest
        else closes e ((SignT, φ) :: rest) && closes e ((SignT, ψ) :: rest)
      else
        if F ∈ s then closes e ((SignN, φ) :: (SignN, ψ) :: rest)
        else true
  | (s, .imp φ ψ) :: rest =>
      closes e ((s, .disj (.neg φ) ψ) :: rest)
  | (s, .xor φ ψ) :: rest =>
      closes e ((s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) :: rest)
  | (s, .xnor φ ψ) :: rest =>
      closes e ((s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) :: rest)
  termination_by ws => wsize ws
  decreasing_by
    all_goals simp only [wsize, Fm.size]
    all_goals omega

/-! ## Значные леммы (перебором) -/

theorem vT : ∀ x : V, x ∈ SignT ↔ x = T := by decide
theorem vF : ∀ x : V, x ∈ SignF ↔ x = F := by decide
theorem vP : ∀ x : V, x ∈ SignP ↔ (x = T ∨ x = Z) := by decide
theorem vN : ∀ x : V, x ∈ SignN ↔ (x = F ∨ x = Z) := by decide
theorem vFull : ∀ x : V, x ∈ ([T, F, Z] : Sign) := by decide
theorem vN_neq : ∀ x : V, (x = F ∨ x = Z) ↔ ¬(x = T) := by decide

/-! ## Знак против классического значения -/

theorem mem_cls_T {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : T ∈ s) (hF : F ∉ s) : x ∈ s ↔ x = T := by
  constructor
  · intro h; rcases hx with rfl | rfl
    · rfl
    · exact absurd h hF
  · rintro rfl; exact hT

theorem mem_cls_F {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : T ∉ s) (hF : F ∈ s) : x ∈ s ↔ x = F := by
  constructor
  · intro h; rcases hx with rfl | rfl
    · exact absurd h hT
    · rfl
  · rintro rfl; exact hF

theorem mem_cls_both {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : T ∈ s) (hF : F ∈ s) : x ∈ s := by
  rcases hx with rfl | rfl
  · exact hT
  · exact hF

theorem not_mem_cls {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : T ∉ s) (hF : F ∉ s) : x ∉ s := by
  rcases hx with rfl | rfl
  · exact hT
  · exact hF

/-! ## Инструменты для satL и SAT -/

theorem satL_nil (v : Nat → V) : satL v [] := by
  intro nd h; cases h

theorem satL_cons {v : Nat → V} {nd : Node} {ns : List Node} :
    satL v (nd :: ns) ↔ satN v nd ∧ satL v ns := by
  constructor
  · intro h
    exact ⟨h nd (List.mem_cons_self ..),
           fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact h2 x hx

theorem SAT_head_congr {e : Env} {nd nd' : Node} {ws : List Node}
    (h : ∀ v, satN v nd ↔ satN v nd') :
    SAT e (nd :: ws) ↔ SAT e (nd' :: ws) := by
  constructor
  · rintro ⟨v, hOK, hs⟩
    have ⟨h1, h2⟩ := satL_cons.mp hs
    exact ⟨v, hOK, satL_cons.mpr ⟨(h v).mp h1, h2⟩⟩
  · rintro ⟨v, hOK, hs⟩
    have ⟨h1, h2⟩ := satL_cons.mp hs
    exact ⟨v, hOK, satL_cons.mpr ⟨(h v).mpr h1, h2⟩⟩

theorem SAT_head_split2 {e : Env} {nd a b : Node} {ws : List Node}
    (h : ∀ v, satN v nd ↔ (satN v a ∧ satN v b)) :
    SAT e (nd :: ws) ↔ SAT e (a :: b :: ws) := by
  constructor
  · rintro ⟨v, hOK, hs⟩
    have ⟨h1, h2⟩ := satL_cons.mp hs
    have ⟨ha, hb⟩ := (h v).mp h1
    exact ⟨v, hOK, satL_cons.mpr ⟨ha, satL_cons.mpr ⟨hb, h2⟩⟩⟩
  · rintro ⟨v, hOK, hs⟩
    have ⟨ha, hs'⟩ := satL_cons.mp hs
    have ⟨hb, h2⟩ := satL_cons.mp hs'
    exact ⟨v, hOK, satL_cons.mpr ⟨(h v).mpr ⟨ha, hb⟩, h2⟩⟩

theorem SAT_head_or {e : Env} {nd a b : Node} {ws : List Node}
    (h : ∀ v, satN v nd ↔ (satN v a ∨ satN v b)) :
    SAT e (nd :: ws) ↔ (SAT e (a :: ws) ∨ SAT e (b :: ws)) := by
  constructor
  · rintro ⟨v, hOK, hs⟩
    have ⟨h1, h2⟩ := satL_cons.mp hs
    rcases (h v).mp h1 with ha | hb
    · exact Or.inl ⟨v, hOK, satL_cons.mpr ⟨ha, h2⟩⟩
    · exact Or.inr ⟨v, hOK, satL_cons.mpr ⟨hb, h2⟩⟩
  · rintro (⟨v, hOK, hs⟩ | ⟨v, hOK, hs⟩)
    · have ⟨h1, h2⟩ := satL_cons.mp hs
      exact ⟨v, hOK, satL_cons.mpr ⟨(h v).mpr (Or.inl h1), h2⟩⟩
    · have ⟨h1, h2⟩ := satL_cons.mp hs
      exact ⟨v, hOK, satL_cons.mpr ⟨(h v).mpr (Or.inr h1), h2⟩⟩

theorem SAT_head_true {e : Env} {nd : Node} {ws : List Node}
    (h : ∀ v, satN v nd) : SAT e (nd :: ws) ↔ SAT e ws := by
  constructor
  · rintro ⟨v, hOK, hs⟩; exact ⟨v, hOK, (satL_cons.mp hs).2⟩
  · rintro ⟨v, hOK, hs⟩; exact ⟨v, hOK, satL_cons.mpr ⟨h v, hs⟩⟩

theorem SAT_head_false {e : Env} {nd : Node} {ws : List Node}
    (h : ∀ v, ¬ satN v nd) : ¬ SAT e (nd :: ws) := by
  rintro ⟨v, _, hs⟩; exact h v (satL_cons.mp hs).1

/-- Атомный шаг: голова-атом эквивалентна сужению ограничений. -/
theorem SAT_atom {e : Env} {s : Sign} {n : Nat} {ws : List Node} :
    SAT e ((s, .atom n) :: ws) ↔ SAT (upd e n (inter (e n) s)) ws := by
  constructor
  · rintro ⟨v, hOK, hs⟩
    have ⟨h1, h2⟩ := satL_cons.mp hs
    refine ⟨v, fun m => ?_, h2⟩
    by_cases hm : m = n
    · subst hm
      simp only [upd, if_pos rfl]
      exact mem_inter.mpr ⟨hOK m, h1⟩
    · simp only [upd, if_neg hm]
      exact hOK m
  · rintro ⟨v, hOK, hs⟩
    have hn : v n ∈ inter (e n) s := by
      have h := hOK n
      simp only [upd, if_pos rfl] at h
      exact h
    refine ⟨v, fun m => ?_, satL_cons.mpr ⟨(mem_inter.mp hn).2, hs⟩⟩
    by_cases hm : m = n
    · subst hm; exact (mem_inter.mp hn).1
    · have h := hOK m
      simp only [upd, if_neg hm] at h
      exact h

/-! ## Главная теорема -/

theorem closes_iff : ∀ (N : Nat) (e : Env) (ws : List Node),
    wsize ws ≤ N → (∀ n, e n ≠ []) →
    (closes e ws = true ↔ ¬ SAT e ws) := by
  intro N
  induction N with
  | zero =>
    intro e ws hle he
    match ws with
    | [] =>
      simp only [closes]
      constructor
      · intro h; exact nomatch h
      · intro h
        exact absurd ⟨fun n => (e n).head (he n),
          fun n => List.head_mem (he n), satL_nil _⟩ h
    | nd :: rest =>
      exfalso
      have := Fm.size_pos nd.2
      simp only [wsize] at hle
      omega
  | succ N ih =>
    intro e ws hle he
    match ws with
    | [] =>
      simp only [closes]
      constructor
      · intro h; exact nomatch h
      · intro h
        exact absurd ⟨fun n => (e n).head (he n),
          fun n => List.head_mem (he n), satL_nil _⟩ h
    | (s, .atom n) :: rest =>
      have hle' : wsize rest ≤ N := by
        simp only [wsize, Fm.size] at hle; omega
      simp only [closes]
      split
      · next hemp =>
        constructor
        · intro _
          rw [SAT_atom, hemp]
          rintro ⟨v, hOK, -⟩
          have h := hOK n
          simp only [upd, if_pos rfl] at h
          cases h
        · intro _; rfl
      · next hemp =>
        have he' : ∀ m, upd e n (inter (e n) s) m ≠ [] := by
          intro m
          by_cases hm : m = n
          · subst hm; simp only [upd, if_pos rfl]; exact hemp
          · simp only [upd, if_neg hm]; exact he m
        rw [ih _ rest hle' he']
        exact not_congr SAT_atom.symm
    | (s, .neg φ) :: rest =>
      have hcls : ∀ v, znot (evalF v φ) = T ∨ znot (evalF v φ) = F :=
        fun v => lift1_classical _ _
      simp only [closes]
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest ≤ N := by
            simp only [wsize, Fm.size] at hle
            have := Fm.size_pos φ; omega
          have hdrop : SAT e ((s, .neg φ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          rw [ih _ rest hle' he]
          exact not_congr hdrop.symm
        · next hF =>
          have hle' : wsize ((SignF, φ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢; omega
          rw [ih _ _ hle' he]
          refine not_congr (SAT_head_congr fun v => ?_).symm
          show znot (evalF v φ) ∈ s ↔ evalF v φ ∈ SignF
          rw [mem_cls_T (hcls v) hT hF, cover_not_T, vF]
      · next hT =>
        split
        · next hF =>
          have hle' : wsize ((SignP, φ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢; omega
          rw [ih _ _ hle' he]
          refine not_congr (SAT_head_congr fun v => ?_).symm
          show znot (evalF v φ) ∈ s ↔ evalF v φ ∈ SignP
          rw [mem_cls_F (hcls v) hT hF, cover_not_F, vP]
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v => not_mem_cls (hcls v) hT hF
          · intro _; rfl
    | (s, .conj φ ψ) :: rest =>
      have hcls : ∀ v, zand (evalF v φ) (evalF v ψ) = T ∨
          zand (evalF v φ) (evalF v ψ) = F :=
        fun v => lift2_classical _ _ _
      simp only [closes]
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest ≤ N := by
            simp only [wsize, Fm.size] at hle
            have := Fm.size_pos φ; omega
          have hdrop : SAT e ((s, .conj φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          rw [ih _ rest hle' he]
          exact not_congr hdrop.symm
        · next hF =>
          have hle' : wsize ((SignT, φ) :: (SignT, ψ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢; omega
          rw [ih _ _ hle' he]
          refine not_congr (SAT_head_split2 fun v => ?_).symm
          show zand (evalF v φ) (evalF v ψ) ∈ s ↔
            (evalF v φ ∈ SignT ∧ evalF v ψ ∈ SignT)
          rw [mem_cls_T (hcls v) hT hF, cover_and_T, vT, vT]
      · next hT =>
        split
        · next hF =>
          have hle1 : wsize ((SignN, φ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢
            have := Fm.size_pos ψ; omega
          have hle2 : wsize ((SignN, ψ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢
            have := Fm.size_pos φ; omega
          have hpt : ∀ v, satN v (s, .conj φ ψ) ↔
              (satN v (SignN, φ) ∨ satN v (SignN, ψ)) := by
            intro v
            show zand (evalF v φ) (evalF v ψ) ∈ s ↔
              (evalF v φ ∈ SignN ∨ evalF v ψ ∈ SignN)
            rw [mem_cls_F (hcls v) hT hF, cover_and_F, vN, vN]
          rw [Bool.and_eq_true, ih _ _ hle1 he, ih _ _ hle2 he,
              SAT_head_or hpt, not_or]
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v => not_mem_cls (hcls v) hT hF
          · intro _; rfl
    | (s, .disj φ ψ) :: rest =>
      have hcls : ∀ v, zor (evalF v φ) (evalF v ψ) = T ∨
          zor (evalF v φ) (evalF v ψ) = F :=
        fun v => lift2_classical _ _ _
      simp only [closes]
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest ≤ N := by
            simp only [wsize, Fm.size] at hle
            have := Fm.size_pos φ; omega
          have hdrop : SAT e ((s, .disj φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          rw [ih _ rest hle' he]
          exact not_congr hdrop.symm
        · next hF =>
          have hle1 : wsize ((SignT, φ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢
            have := Fm.size_pos ψ; omega
          have hle2 : wsize ((SignT, ψ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢
            have := Fm.size_pos φ; omega
          have hpt : ∀ v, satN v (s, .disj φ ψ) ↔
              (satN v (SignT, φ) ∨ satN v (SignT, ψ)) := by
            intro v
            show zor (evalF v φ) (evalF v ψ) ∈ s ↔
              (evalF v φ ∈ SignT ∨ evalF v ψ ∈ SignT)
            rw [mem_cls_T (hcls v) hT hF, cover_or_T, vT, vT]
          rw [Bool.and_eq_true, ih _ _ hle1 he, ih _ _ hle2 he,
              SAT_head_or hpt, not_or]
      · next hT =>
        split
        · next hF =>
          have hle' : wsize ((SignN, φ) :: (SignN, ψ) :: rest) ≤ N := by
            simp only [wsize, Fm.size] at hle ⊢; omega
          rw [ih _ _ hle' he]
          refine not_congr (SAT_head_split2 fun v => ?_).symm
          show zor (evalF v φ) (evalF v ψ) ∈ s ↔
            (evalF v φ ∈ SignN ∧ evalF v ψ ∈ SignN)
          rw [mem_cls_F (hcls v) hT hF, cover_or_F, vN, vN]
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v => not_mem_cls (hcls v) hT hF
          · intro _; rfl
    | (s, .imp φ ψ) :: rest =>
      have hle' : wsize ((s, .disj (.neg φ) ψ) :: rest) ≤ N := by
        simp only [wsize, Fm.size] at hle ⊢; omega
      have step : closes e ((s, .imp φ ψ) :: rest) =
          closes e ((s, .disj (.neg φ) ψ) :: rest) := by
        simp only [closes]
      have hpt : ∀ v, satN v (s, .imp φ ψ) ↔
          satN v (s, .disj (.neg φ) ψ) := by
        intro v
        show zimp (evalF v φ) (evalF v ψ) ∈ s ↔
          zor (znot (evalF v φ)) (evalF v ψ) ∈ s
        rw [imp_def]
      rw [step, ih _ _ hle' he]
      exact not_congr (SAT_head_congr hpt).symm
    | (s, .xor φ ψ) :: rest =>
      have hle' : wsize ((s, .disj (.conj φ (.neg ψ))
          (.conj (.neg φ) ψ)) :: rest) ≤ N := by
        simp only [wsize, Fm.size] at hle ⊢; omega
      have step : closes e ((s, .xor φ ψ) :: rest) =
          closes e ((s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) :: rest) := by
        simp only [closes]
      have hpt : ∀ v, satN v (s, .xor φ ψ) ↔
          satN v (s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) := by
        intro v
        show zxor (evalF v φ) (evalF v ψ) ∈ s ↔
          zor (zand (evalF v φ) (znot (evalF v ψ)))
              (zand (znot (evalF v φ)) (evalF v ψ)) ∈ s
        rw [xor_def]
      rw [step, ih _ _ hle' he]
      exact not_congr (SAT_head_congr hpt).symm
    | (s, .xnor φ ψ) :: rest =>
      have hle' : wsize ((s, .disj (.conj φ ψ)
          (.conj (.neg φ) (.neg ψ))) :: rest) ≤ N := by
        simp only [wsize, Fm.size] at hle ⊢; omega
      have step : closes e ((s, .xnor φ ψ) :: rest) =
          closes e ((s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) :: rest) := by
        simp only [closes]
      have hpt : ∀ v, satN v (s, .xnor φ ψ) ↔
          satN v (s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) := by
        intro v
        show zxnor (evalF v φ) (evalF v ψ) ∈ s ↔
          zor (zand (evalF v φ) (evalF v ψ))
              (zand (znot (evalF v φ)) (znot (evalF v ψ))) ∈ s
        rw [xnor_def]
      rw [step, ih _ _ hle' he]
      exact not_congr (SAT_head_congr hpt).symm

/-! ## Следствие: выводимость = следование -/

def e0 : Env := fun _ => [T, F, Z]

/-- Γ ⊢ φ: посылки со строгим знаком T, заключение — с ослабленным N. -/
def tproves (ps : List Fm) (c : Fm) : Bool :=
  closes e0 (ps.map (fun p => (SignT, p)) ++ [(SignN, c)])

theorem satL_append {v : Nat → V} {xs ys : List Node} :
    satL v (xs ++ ys) ↔ satL v xs ∧ satL v ys := by
  constructor
  · intro h
    exact ⟨fun nd hnd => h nd (List.mem_append.mpr (Or.inl hnd)),
           fun nd hnd => h nd (List.mem_append.mpr (Or.inr hnd))⟩
  · rintro ⟨h1, h2⟩ nd hnd
    rcases List.mem_append.mp hnd with h | h
    · exact h1 nd h
    · exact h2 nd h

/-- Сертификат: движок выдаёт ⊢ ⟺ семантическое следование по {T}. -/
theorem tproves_iff (ps : List Fm) (c : Fm) :
    tproves ps c = true ↔
    ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T := by
  have he0 : ∀ n : Nat, e0 n ≠ [] := fun _ h => nomatch h
  have key := closes_iff
      (wsize (ps.map (fun p => (SignT, p)) ++ [(SignN, c)])) e0
      (ps.map (fun p => (SignT, p)) ++ [(SignN, c)])
      (Nat.le_refl _) he0
  unfold tproves
  rw [key]
  constructor
  · intro h v hp
    by_cases hc : evalF v c = T
    · exact hc
    exfalso
    apply h
    refine ⟨v, fun n => vFull _, ?_⟩
    rw [satL_append, satL_cons]
    refine ⟨fun nd hnd => ?_, ?_, satL_nil _⟩
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hnd
      show evalF v p ∈ SignT
      rw [vT]; exact hp p hp'
    · show evalF v c ∈ SignN
      rw [vN, vN_neq]; exact hc
  · rintro h ⟨v, _, hs⟩
    rw [satL_append, satL_cons] at hs
    obtain ⟨h1, h2, -⟩ := hs
    have hc : evalF v c ∈ SignN := h2
    rw [vN, vN_neq] at hc
    apply hc
    apply h v
    intro p hp'
    have hm : evalF v p ∈ SignT :=
      h1 (SignT, p) (List.mem_map.mpr ⟨p, hp', rfl⟩)
    rwa [vT] at hm

/-! ## Дымовые прогоны сертифицированного движка -/

#eval tproves [] (.imp (.atom 0) (.atom 0))                      -- false: ⊬ p→p
#eval tproves [.atom 0, .imp (.atom 0) (.atom 1)] (.atom 1)      -- true: MP
#eval tproves [] (.neg (.conj (.atom 0) (.neg (.atom 0))))       -- true: ¬(p∧¬p)
#eval tproves [] (.disj (.atom 0) (.neg (.atom 0)))              -- false: ⊬ LEM
#eval tproves [.imp (.atom 0) (.atom 1)]
      (.imp (.neg (.atom 1)) (.neg (.atom 0)))                   -- true: контрапозиция-правило
#eval tproves [.neg (.neg (.atom 0))] (.atom 0)                  -- false: ¬¬-удаление пало

#print axioms closes_iff
#print axioms tproves_iff

end V
