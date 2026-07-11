import TableauCert

/-!
# Родной движок: прямые правила для →, ⊕, ↔ — и эквивалентность движков

closesN — движок с родными знаковыми правилами тяжёлых связок (без
сведения к базису). Доказываются closesN_iff (корректность+полнота) и
engines_agree: оба движка выдают одинаковые вердикты. Ноль аксиом.
-/

namespace V

/-- Перестановка для двухузловых ветвей: a+(b+r)+1 = a+b+1+r. -/
theorem addShuffle (a b r : Nat) : a + (b + r) + 1 = a + b + 1 + r := by
  rw [← Nat.add_assoc, Nat.add_right_comm]

theorem boolEqOfIff : ∀ a b : Bool, ((a = true) ↔ (b = true)) → a = b := by
  decide

/-- Двухузловое ИЛИ-ветвление. -/
theorem SAT_head_or2 {e : Env} {nd a1 a2 b1 b2 : Node} {ws : List Node}
    (h : ∀ v, satN v nd ↔
      ((satN v a1 ∧ satN v a2) ∨ (satN v b1 ∧ satN v b2))) :
    SAT e (nd :: ws) ↔ (SAT e (a1 :: a2 :: ws) ∨ SAT e (b1 :: b2 :: ws)) := by
  constructor
  · rintro ⟨v, hOK, h1, h2⟩
    rcases (h v).mp h1 with ⟨x, y⟩ | ⟨x, y⟩
    · exact Or.inl ⟨v, hOK, x, y, h2⟩
    · exact Or.inr ⟨v, hOK, x, y, h2⟩
  · rintro (⟨v, hOK, x, y, h2⟩ | ⟨v, hOK, x, y, h2⟩)
    · exact ⟨v, hOK, (h v).mpr (Or.inl ⟨x, y⟩), h2⟩
    · exact ⟨v, hOK, (h v).mpr (Or.inr ⟨x, y⟩), h2⟩

/-- Родной движок: атом/¬/∧/∨ как в closes; →,⊕,↔ — прямыми правилами. -/
def closesN (fuel : Nat) (e : Env) (ws : List Node) : Bool :=
  match fuel, ws with
  | 0, _ => false
  | _ + 1, [] => false
  | fuel + 1, (s, .atom n) :: rest =>
      if sIsEmpty (inter (e n) s) = true then true
      else closesN fuel (upd e n (inter (e n) s)) rest
  | fuel + 1, (s, .neg φ) :: rest =>
      if s T = true then
        if s F = true then closesN fuel e rest
        else closesN fuel e ((SignF, φ) :: rest)
      else
        if s F = true then closesN fuel e ((SignP, φ) :: rest)
        else true
  | fuel + 1, (s, .conj φ ψ) :: rest =>
      if s T = true then
        if s F = true then closesN fuel e rest
        else closesN fuel e ((SignT, φ) :: (SignT, ψ) :: rest)
      else
        if s F = true then
          closesN fuel e ((SignN, φ) :: rest) &&
          closesN fuel e ((SignN, ψ) :: rest)
        else true
  | fuel + 1, (s, .disj φ ψ) :: rest =>
      if s T = true then
        if s F = true then closesN fuel e rest
        else closesN fuel e ((SignT, φ) :: rest) &&
             closesN fuel e ((SignT, ψ) :: rest)
      else
        if s F = true then closesN fuel e ((SignN, φ) :: (SignN, ψ) :: rest)
        else true
  | fuel + 1, (s, .imp φ ψ) :: rest =>
      if s T = true then
        if s F = true then closesN fuel e rest
        else closesN fuel e ((SignF, φ) :: rest) &&
             closesN fuel e ((SignT, ψ) :: rest)
      else
        if s F = true then closesN fuel e ((SignP, φ) :: (SignN, ψ) :: rest)
        else true
  | fuel + 1, (s, .xor φ ψ) :: rest =>
      if s T = true then
        if s F = true then closesN fuel e rest
        else closesN fuel e ((SignT, φ) :: (SignF, ψ) :: rest) &&
             closesN fuel e ((SignF, φ) :: (SignT, ψ) :: rest)
      else
        if s F = true then
          closesN fuel e ((SignP, φ) :: (SignP, ψ) :: rest) &&
          closesN fuel e ((SignN, φ) :: (SignN, ψ) :: rest)
        else true
  | fuel + 1, (s, .xnor φ ψ) :: rest =>
      if s T = true then
        if s F = true then closesN fuel e rest
        else closesN fuel e ((SignT, φ) :: (SignT, ψ) :: rest) &&
             closesN fuel e ((SignF, φ) :: (SignF, ψ) :: rest)
      else
        if s F = true then
          closesN fuel e ((SignP, φ) :: (SignN, ψ) :: rest) &&
          closesN fuel e ((SignN, φ) :: (SignP, ψ) :: rest)
        else true
  termination_by structural fuel

/-! ## Границы убывания для тяжёлых голов (чистая Nat-арифметика) -/

section Bounds
variable (Sφ Sψ R : Nat)

-- imp-размер: ((Sφ+1)+Sψ+1)+2
theorem impB1 : Sφ + R + 1 ≤ Sφ + 1 + Sψ + 1 + 2 + R :=
  Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm Sφ R 1))
    (Nat.add_le_add_right
      (Nat.le_trans (Nat.le_add_right (Sφ + 1) Sψ)
        (Nat.le_trans (Nat.le_add_right _ 1) (Nat.le_add_right _ 2))) R)

theorem impB2 : Sψ + R + 1 ≤ Sφ + 1 + Sψ + 1 + 2 + R :=
  Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm Sψ R 1))
    (Nat.add_le_add_right
      (Nat.le_trans
        (Nat.add_le_add_right (Nat.le_add_left Sψ (Sφ + 1)) 1)
        (Nat.le_add_right _ 2)) R)

theorem impB3 : Sφ + (Sψ + R) + 1 ≤ Sφ + 1 + Sψ + 1 + 2 + R :=
  Nat.le_trans (Nat.le_of_eq (addShuffle Sφ Sψ R))
    (Nat.add_le_add_right
      (Nat.le_trans
        (Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.le_add_right Sφ 1) Sψ) 1)
        (Nat.le_add_right _ 2)) R)

-- xor-размер: (Sφ+(Sψ+1)+1)+((Sφ+1)+Sψ+1)+3
theorem xorB : Sφ + (Sψ + R) + 1 ≤
    Sφ + (Sψ + 1) + 1 + (Sφ + 1 + Sψ + 1) + 3 + R :=
  Nat.le_trans (Nat.le_of_eq (addShuffle Sφ Sψ R))
    (Nat.add_le_add_right
      (Nat.le_trans (Nat.le_of_eq (Nat.add_assoc Sφ Sψ 1))
        (Nat.le_trans (Nat.le_add_right (Sφ + (Sψ + 1)) 1)
          (Nat.le_trans (Nat.le_add_right _ _)
            (Nat.le_add_right _ 3)))) R)

-- xnor-размер: (Sφ+Sψ+1)+((Sφ+1)+(Sψ+1)+1)+3
theorem xnorB : Sφ + (Sψ + R) + 1 ≤
    Sφ + Sψ + 1 + (Sφ + 1 + (Sψ + 1) + 1) + 3 + R :=
  Nat.le_trans (Nat.le_of_eq (addShuffle Sφ Sψ R))
    (Nat.add_le_add_right
      (Nat.le_trans (Nat.le_add_right (Sφ + Sψ + 1) _)
        (Nat.le_add_right _ 3)) R)

end Bounds

/-- Универсальный сброс головы (для drop-случаев): R < fuel. -/
theorem dropBound {hd : Fm} {R fuel : Nat}
    (hb : Fm.size hd + R < fuel + 1) : R < fuel :=
  boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_comm R 1))
    (Nat.add_le_add_right (Fm.size_pos hd) R)) hb

/-! ## Сертификат родного движка -/

theorem closesN_iff : ∀ (fuel : Nat) (e : Env) (ws : List Node),
    wsize ws < fuel → (∀ n, sIsEmpty (e n) = false) →
    (closesN fuel e ws = true ↔ ¬ SAT e ws) := by
  intro fuel
  induction fuel with
  | zero =>
    intro e ws hle he
    exact absurd hle (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro e ws hle he
    match ws with
    | [] =>
      constructor
      · intro h; exact nomatch h
      · intro h
        exact absurd ⟨fun n => sPick (e n),
          fun n => sPick_mem (he n), satL_nil _⟩ h
    | (s, .atom n) :: rest =>
      have hb : Fm.size (.atom n) + wsize rest < fuel + 1 := hle
      have hle' : wsize rest < fuel := dropBound hb
      show (if sIsEmpty (inter (e n) s) = true then true
            else closesN fuel (upd e n (inter (e n) s)) rest) = true ↔ _
      split
      · next hemp =>
        constructor
        · intro _
          rintro ⟨v, hOK, h1, _⟩
          have hmem : inter (e n) s (v n) = true :=
            (andEqTrue _ _).mpr ⟨hOK n, h1⟩
          have hne := sNonempty_of_mem hmem
          rw [hemp] at hne
          cases hne
        · intro _; rfl
      · next hemp =>
        have he' : ∀ m, sIsEmpty (upd e n (inter (e n) s) m) = false := by
          intro m
          by_cases hm : m = n
          · subst hm
            have hu : upd e m (inter (e m) s) m = inter (e m) s := if_pos rfl
            rw [hu]
            exact bNotTrue _ hemp
          · have hu : upd e n (inter (e n) s) m = e m := if_neg hm
            rw [hu]
            exact he m
        exact (ih _ rest hle' he').trans (notCongr SAT_atom.symm)
    | (s, .neg φ) :: rest =>
      have hcls : ∀ v, znot (evalF v φ) = T ∨ znot (evalF v φ) = F :=
        fun v => lift1_classical _ _
      have hb : Fm.size φ + 1 + wsize rest < fuel + 1 := hle
      show (if s T = true then
              if s F = true then closesN fuel e rest
              else closesN fuel e ((SignF, φ) :: rest)
            else
              if s F = true then closesN fuel e ((SignP, φ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel := dropBound hle
          have hdrop : SAT e ((s, .neg φ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
        · next hF =>
          have hle' : wsize ((SignF, φ) :: rest) < fuel :=
            boundStep (Nat.le_of_eq (Nat.add_right_comm _ _ 1)) hb
          have hpt : ∀ v, satN v (s, .neg φ) ↔ satN v (SignF, φ) := fun v =>
            (mem_cls_T (hcls v) hT (bNotTrue _ hF)).trans
              ((cover_not_T _).trans (vF _).symm)
          exact (ih _ _ hle' he).trans (notCongr (SAT_head_congr hpt).symm)
      · next hT =>
        split
        · next hF =>
          have hle' : wsize ((SignP, φ) :: rest) < fuel :=
            boundStep (Nat.le_of_eq (Nat.add_right_comm _ _ 1)) hb
          have hpt : ∀ v, satN v (s, .neg φ) ↔ satN v (SignP, φ) := fun v =>
            (mem_cls_F (hcls v) (bNotTrue _ hT) hF).trans
              ((cover_not_F _).trans (vP _).symm)
          exact (ih _ _ hle' he).trans (notCongr (SAT_head_congr hpt).symm)
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v =>
              not_mem_cls (hcls v) (bNotTrue _ hT) (bNotTrue _ hF)
          · intro _; rfl
    | (s, .conj φ ψ) :: rest =>
      have hcls : ∀ v, zand (evalF v φ) (evalF v ψ) = T ∨
          zand (evalF v φ) (evalF v ψ) = F :=
        fun v => lift2_classical _ _ _
      have hb : Fm.size φ + Fm.size ψ + 1 + wsize rest < fuel + 1 := hle
      show (if s T = true then
              if s F = true then closesN fuel e rest
              else closesN fuel e ((SignT, φ) :: (SignT, ψ) :: rest)
            else
              if s F = true then
                closesN fuel e ((SignN, φ) :: rest) &&
                closesN fuel e ((SignN, ψ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel := dropBound hle
          have hdrop : SAT e ((s, .conj φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
        · next hF =>
          have hle' : wsize ((SignT, φ) :: (SignT, ψ) :: rest) < fuel :=
            boundStep (Nat.le_trans
              (Nat.le_of_eq (addShuffle (Fm.size φ) (Fm.size ψ) (wsize rest)))
              (Nat.le_refl _)) hb
          have hpt : ∀ v, satN v (s, .conj φ ψ) ↔
              (satN v (SignT, φ) ∧ satN v (SignT, ψ)) := fun v =>
            (mem_cls_T (hcls v) hT (bNotTrue _ hF)).trans
              ((cover_and_T _ _).trans (andCongr (vT _).symm (vT _).symm))
          exact (ih _ _ hle' he).trans (notCongr (SAT_head_split2 hpt).symm)
      · next hT =>
        split
        · next hF =>
          have hle1 : wsize ((SignN, φ) :: rest) < fuel :=
            boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm _ _ 1))
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.le_add_right _ _) 1) _)) hb
          have hle2 : wsize ((SignN, ψ) :: rest) < fuel :=
            boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm _ _ 1))
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.le_add_left _ _) 1) _)) hb
          have hpt : ∀ v, satN v (s, .conj φ ψ) ↔
              (satN v (SignN, φ) ∨ satN v (SignN, ψ)) := fun v =>
            (mem_cls_F (hcls v) (bNotTrue _ hT) hF).trans
              ((cover_and_F _ _).trans (orCongr (vN _).symm (vN _).symm))
          exact (andEqTrue _ _).trans
            ((andCongr (ih _ _ hle1 he) (ih _ _ hle2 he)).trans
              (notOr.symm.trans (notCongr (SAT_head_or hpt).symm)))
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v =>
              not_mem_cls (hcls v) (bNotTrue _ hT) (bNotTrue _ hF)
          · intro _; rfl
    | (s, .disj φ ψ) :: rest =>
      have hcls : ∀ v, zor (evalF v φ) (evalF v ψ) = T ∨
          zor (evalF v φ) (evalF v ψ) = F :=
        fun v => lift2_classical _ _ _
      have hb : Fm.size φ + Fm.size ψ + 1 + wsize rest < fuel + 1 := hle
      show (if s T = true then
              if s F = true then closesN fuel e rest
              else closesN fuel e ((SignT, φ) :: rest) &&
                   closesN fuel e ((SignT, ψ) :: rest)
            else
              if s F = true then
                closesN fuel e ((SignN, φ) :: (SignN, ψ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel := dropBound hle
          have hdrop : SAT e ((s, .disj φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
        · next hF =>
          have hle1 : wsize ((SignT, φ) :: rest) < fuel :=
            boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm _ _ 1))
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.le_add_right _ _) 1) _)) hb
          have hle2 : wsize ((SignT, ψ) :: rest) < fuel :=
            boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm _ _ 1))
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.le_add_left _ _) 1) _)) hb
          have hpt : ∀ v, satN v (s, .disj φ ψ) ↔
              (satN v (SignT, φ) ∨ satN v (SignT, ψ)) := fun v =>
            (mem_cls_T (hcls v) hT (bNotTrue _ hF)).trans
              ((cover_or_T _ _).trans (orCongr (vT _).symm (vT _).symm))
          exact (andEqTrue _ _).trans
            ((andCongr (ih _ _ hle1 he) (ih _ _ hle2 he)).trans
              (notOr.symm.trans (notCongr (SAT_head_or hpt).symm)))
      · next hT =>
        split
        · next hF =>
          have hle' : wsize ((SignN, φ) :: (SignN, ψ) :: rest) < fuel :=
            boundStep (Nat.le_of_eq
              (addShuffle (Fm.size φ) (Fm.size ψ) (wsize rest))) hb
          have hpt : ∀ v, satN v (s, .disj φ ψ) ↔
              (satN v (SignN, φ) ∧ satN v (SignN, ψ)) := fun v =>
            (mem_cls_F (hcls v) (bNotTrue _ hT) hF).trans
              ((cover_or_F _ _).trans (andCongr (vN _).symm (vN _).symm))
          exact (ih _ _ hle' he).trans (notCongr (SAT_head_split2 hpt).symm)
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v =>
              not_mem_cls (hcls v) (bNotTrue _ hT) (bNotTrue _ hF)
          · intro _; rfl
    | (s, .imp φ ψ) :: rest =>
      have hcls : ∀ v, zimp (evalF v φ) (evalF v ψ) = T ∨
          zimp (evalF v φ) (evalF v ψ) = F :=
        fun v => lift2_classical _ _ _
      have hb : Fm.size φ + 1 + Fm.size ψ + 1 + 2 + wsize rest < fuel + 1 := hle
      show (if s T = true then
              if s F = true then closesN fuel e rest
              else closesN fuel e ((SignF, φ) :: rest) &&
                   closesN fuel e ((SignT, ψ) :: rest)
            else
              if s F = true then
                closesN fuel e ((SignP, φ) :: (SignN, ψ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel := dropBound hle
          have hdrop : SAT e ((s, .imp φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
        · next hF =>
          have hle1 : wsize ((SignF, φ) :: rest) < fuel :=
            boundStep (impB1 (Fm.size φ) (Fm.size ψ) (wsize rest)) hb
          have hle2 : wsize ((SignT, ψ) :: rest) < fuel :=
            boundStep (impB2 (Fm.size φ) (Fm.size ψ) (wsize rest)) hb
          have hpt : ∀ v, satN v (s, .imp φ ψ) ↔
              (satN v (SignF, φ) ∨ satN v (SignT, ψ)) := fun v =>
            (mem_cls_T (hcls v) hT (bNotTrue _ hF)).trans
              ((cover_imp_T _ _).trans (orCongr (vF _).symm (vT _).symm))
          exact (andEqTrue _ _).trans
            ((andCongr (ih _ _ hle1 he) (ih _ _ hle2 he)).trans
              (notOr.symm.trans (notCongr (SAT_head_or hpt).symm)))
      · next hT =>
        split
        · next hF =>
          have hle' : wsize ((SignP, φ) :: (SignN, ψ) :: rest) < fuel :=
            boundStep (impB3 (Fm.size φ) (Fm.size ψ) (wsize rest)) hb
          have hpt : ∀ v, satN v (s, .imp φ ψ) ↔
              (satN v (SignP, φ) ∧ satN v (SignN, ψ)) := fun v =>
            (mem_cls_F (hcls v) (bNotTrue _ hT) hF).trans
              ((cover_imp_F _ _).trans (andCongr (vP _).symm (vN _).symm))
          exact (ih _ _ hle' he).trans (notCongr (SAT_head_split2 hpt).symm)
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v =>
              not_mem_cls (hcls v) (bNotTrue _ hT) (bNotTrue _ hF)
          · intro _; rfl
    | (s, .xor φ ψ) :: rest =>
      have hcls : ∀ v, zxor (evalF v φ) (evalF v ψ) = T ∨
          zxor (evalF v φ) (evalF v ψ) = F :=
        fun v => lift2_classical _ _ _
      have hb : Fm.size φ + (Fm.size ψ + 1) + 1 + (Fm.size φ + 1 + Fm.size ψ + 1)
          + 3 + wsize rest < fuel + 1 := hle
      show (if s T = true then
              if s F = true then closesN fuel e rest
              else closesN fuel e ((SignT, φ) :: (SignF, ψ) :: rest) &&
                   closesN fuel e ((SignF, φ) :: (SignT, ψ) :: rest)
            else
              if s F = true then
                closesN fuel e ((SignP, φ) :: (SignP, ψ) :: rest) &&
                closesN fuel e ((SignN, φ) :: (SignN, ψ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel := dropBound hle
          have hdrop : SAT e ((s, .xor φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
        · next hF =>
          have hlb := xorB (Fm.size φ) (Fm.size ψ) (wsize rest)
          have hle1 : wsize ((SignT, φ) :: (SignF, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hle2 : wsize ((SignF, φ) :: (SignT, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hpt : ∀ v, satN v (s, .xor φ ψ) ↔
              ((satN v (SignT, φ) ∧ satN v (SignF, ψ)) ∨
               (satN v (SignF, φ) ∧ satN v (SignT, ψ))) := fun v =>
            (mem_cls_T (hcls v) hT (bNotTrue _ hF)).trans
              ((cover_xor_T _ _).trans
                (orCongr (andCongr (vT _).symm (vF _).symm)
                         (andCongr (vF _).symm (vT _).symm)))
          exact (andEqTrue _ _).trans
            ((andCongr (ih _ _ hle1 he) (ih _ _ hle2 he)).trans
              (notOr.symm.trans (notCongr (SAT_head_or2 hpt).symm)))
      · next hT =>
        split
        · next hF =>
          have hlb := xorB (Fm.size φ) (Fm.size ψ) (wsize rest)
          have hle1 : wsize ((SignP, φ) :: (SignP, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hle2 : wsize ((SignN, φ) :: (SignN, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hpt : ∀ v, satN v (s, .xor φ ψ) ↔
              ((satN v (SignP, φ) ∧ satN v (SignP, ψ)) ∨
               (satN v (SignN, φ) ∧ satN v (SignN, ψ))) := fun v =>
            (mem_cls_F (hcls v) (bNotTrue _ hT) hF).trans
              ((cover_xor_F _ _).trans
                (orCongr (andCongr (vP _).symm (vP _).symm)
                         (andCongr (vN _).symm (vN _).symm)))
          exact (andEqTrue _ _).trans
            ((andCongr (ih _ _ hle1 he) (ih _ _ hle2 he)).trans
              (notOr.symm.trans (notCongr (SAT_head_or2 hpt).symm)))
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v =>
              not_mem_cls (hcls v) (bNotTrue _ hT) (bNotTrue _ hF)
          · intro _; rfl
    | (s, .xnor φ ψ) :: rest =>
      have hcls : ∀ v, zxnor (evalF v φ) (evalF v ψ) = T ∨
          zxnor (evalF v φ) (evalF v ψ) = F :=
        fun v => lift2_classical _ _ _
      have hb : Fm.size φ + Fm.size ψ + 1 + (Fm.size φ + 1 + (Fm.size ψ + 1) + 1)
          + 3 + wsize rest < fuel + 1 := hle
      show (if s T = true then
              if s F = true then closesN fuel e rest
              else closesN fuel e ((SignT, φ) :: (SignT, ψ) :: rest) &&
                   closesN fuel e ((SignF, φ) :: (SignF, ψ) :: rest)
            else
              if s F = true then
                closesN fuel e ((SignP, φ) :: (SignN, ψ) :: rest) &&
                closesN fuel e ((SignN, φ) :: (SignP, ψ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel := dropBound hle
          have hdrop : SAT e ((s, .xnor φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
        · next hF =>
          have hlb := xnorB (Fm.size φ) (Fm.size ψ) (wsize rest)
          have hle1 : wsize ((SignT, φ) :: (SignT, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hle2 : wsize ((SignF, φ) :: (SignF, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hpt : ∀ v, satN v (s, .xnor φ ψ) ↔
              ((satN v (SignT, φ) ∧ satN v (SignT, ψ)) ∨
               (satN v (SignF, φ) ∧ satN v (SignF, ψ))) := fun v =>
            (mem_cls_T (hcls v) hT (bNotTrue _ hF)).trans
              ((cover_xnor_T _ _).trans
                (orCongr (andCongr (vT _).symm (vT _).symm)
                         (andCongr (vF _).symm (vF _).symm)))
          exact (andEqTrue _ _).trans
            ((andCongr (ih _ _ hle1 he) (ih _ _ hle2 he)).trans
              (notOr.symm.trans (notCongr (SAT_head_or2 hpt).symm)))
      · next hT =>
        split
        · next hF =>
          have hlb := xnorB (Fm.size φ) (Fm.size ψ) (wsize rest)
          have hle1 : wsize ((SignP, φ) :: (SignN, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hle2 : wsize ((SignN, φ) :: (SignP, ψ) :: rest) < fuel :=
            boundStep hlb hb
          have hpt : ∀ v, satN v (s, .xnor φ ψ) ↔
              ((satN v (SignP, φ) ∧ satN v (SignN, ψ)) ∨
               (satN v (SignN, φ) ∧ satN v (SignP, ψ))) := fun v =>
            (mem_cls_F (hcls v) (bNotTrue _ hT) hF).trans
              ((cover_xnor_F _ _).trans
                (orCongr (andCongr (vP _).symm (vN _).symm)
                         (andCongr (vN _).symm (vP _).symm)))
          exact (andEqTrue _ _).trans
            ((andCongr (ih _ _ hle1 he) (ih _ _ hle2 he)).trans
              (notOr.symm.trans (notCongr (SAT_head_or2 hpt).symm)))
        · next hF =>
          constructor
          · intro _
            exact SAT_head_false fun v =>
              not_mem_cls (hcls v) (bNotTrue _ hT) (bNotTrue _ hF)
          · intro _; rfl

/-! ## Эквивалентность движков -/

def tprovesN (ps : List Fm) (c : Fm) : Bool :=
  closesN (wsize (ps.map (fun p => (SignT, p)) ++ [(SignN, c)]) + 1) e0
    (ps.map (fun p => (SignT, p)) ++ [(SignN, c)])

theorem tprovesN_iff (ps : List Fm) (c : Fm) :
    tprovesN ps c = true ↔
    ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T := by
  have he0 : ∀ n : Nat, sIsEmpty (e0 n) = false := fun _ => rfl
  have key := closesN_iff
      (wsize (ps.map (fun p => (SignT, p)) ++ [(SignN, c)]) + 1) e0
      (ps.map (fun p => (SignT, p)) ++ [(SignN, c)])
      (Nat.lt_succ_self _) he0
  refine key.trans ⟨fun h v hp => ?_, fun h => ?_⟩
  · by_cases hc : evalF v c = T
    · exact hc
    exfalso
    apply h
    exact ⟨v, fun n => rfl,
      (satL_bridge c ps).mpr ⟨hp, (vN _).mpr ((vN_neq _).mpr hc)⟩⟩
  · rintro ⟨v, _, hs⟩
    have ⟨hall, hc⟩ := (satL_bridge c ps).mp hs
    exact (vN_neq _).mp ((vN _).mp hc) (h v hall)

/-- Родной движок и движок-на-базисе выдают ОДИНАКОВЫЕ вердикты. -/
theorem engines_agree (ps : List Fm) (c : Fm) :
    tprovesN ps c = tproves ps c :=
  boolEqOfIff _ _ ((tprovesN_iff ps c).trans (tproves_iff ps c).symm)

#print axioms closesN_iff
#print axioms engines_agree

end V
