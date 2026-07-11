import ZTL

/-!
# The trade certificate: soundness and completeness of the ZTL tableau engine

Zero axioms. To achieve this: signs are functions V → Bool (no core
list lemmas), satL is a recursive conjunction (no ∀-membership), the
engine is structural recursion on fuel (no WF machinery), the proofs
are combinator chains of Iff (no rw by equivalences), the size bounds
are defeq restatements + omega-free arithmetic (no simp over match
equations). The connectives →,⊕,↔ reduce to the basis {¬,∧,∨} by the
surviving identities (imp_def, xor_def, xnor_def — theorems of the core).
-/

namespace V

/-! ## In-house combinators (zero dependencies) -/

theorem iffOfEq {a b : Prop} (h : a = b) : a ↔ b := h ▸ Iff.rfl

theorem notCongr {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b :=
  ⟨fun na hb => na (h.mpr hb), fun nb ha => nb (h.mp ha)⟩

theorem andCongr {a b c d : Prop} (h1 : a ↔ c) (h2 : b ↔ d) :
    (a ∧ b) ↔ (c ∧ d) :=
  ⟨fun ⟨x, y⟩ => ⟨h1.mp x, h2.mp y⟩, fun ⟨x, y⟩ => ⟨h1.mpr x, h2.mpr y⟩⟩

theorem orCongr {a b c d : Prop} (h1 : a ↔ c) (h2 : b ↔ d) :
    (a ∨ b) ↔ (c ∨ d) :=
  ⟨fun h => h.elim (fun x => Or.inl (h1.mp x)) (fun y => Or.inr (h2.mp y)),
   fun h => h.elim (fun x => Or.inl (h1.mpr x)) (fun y => Or.inr (h2.mpr y))⟩

theorem notOr {a b : Prop} : ¬(a ∨ b) ↔ (¬a ∧ ¬b) :=
  ⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩,
   fun ⟨na, nb⟩ h => h.elim na nb⟩

theorem andEqTrue : ∀ a b : Bool, (a && b) = true ↔ (a = true ∧ b = true) := by
  decide

theorem boundStep {a b f : Nat} (h1 : a + 1 ≤ b) (h2 : b < f + 1) : a < f :=
  Nat.le_trans h1 (Nat.le_of_lt_succ h2)

theorem bNotTrue : ∀ b : Bool, ¬(b = true) → b = false := by
  intro b h
  cases b
  · rfl
  · exact absurd rfl h

/-! ## Signs as functions V → Bool -/

abbrev Sign := V → Bool

def SignT : Sign := fun x => decide (x = T)
def SignF : Sign := fun x => decide (x = F)
def SignP : Sign := fun x => decide (x = T ∨ x = Z)
def SignN : Sign := fun x => decide (x = F ∨ x = Z)

theorem vT : ∀ x : V, SignT x = true ↔ x = T := by decide
theorem vF : ∀ x : V, SignF x = true ↔ x = F := by decide
theorem vP : ∀ x : V, SignP x = true ↔ (x = T ∨ x = Z) := by decide
theorem vN : ∀ x : V, SignN x = true ↔ (x = F ∨ x = Z) := by decide
theorem vN_neq : ∀ x : V, (x = F ∨ x = Z) ↔ ¬(x = T) := by decide

def inter (a b : Sign) : Sign := fun x => a x && b x

def sIsEmpty (s : Sign) : Bool := !(s T || s F || s Z)

theorem bNotOr1 : ∀ a b c : Bool, a = true → (!(a || b || c)) = false := by decide
theorem bNotOr2 : ∀ a b c : Bool, b = true → (!(a || b || c)) = false := by decide
theorem bNotOr3 : ∀ a b c : Bool, c = true → (!(a || b || c)) = false := by decide
theorem bAllFalse : ∀ a b c : Bool, a = false → b = false → c = false →
    (!(a || b || c)) = true := by decide

theorem sNonempty_of_mem {s : Sign} {x : V} (h : s x = true) :
    sIsEmpty s = false := by
  cases x
  · exact bNotOr1 (s T) (s F) (s Z) h
  · exact bNotOr2 (s T) (s F) (s Z) h
  · exact bNotOr3 (s T) (s F) (s Z) h

/-- Picking a representative from a non-empty sign. -/
def sPick (s : Sign) : V :=
  if s T = true then T else if s F = true then F else Z

theorem sPick_mem {s : Sign} (h : sIsEmpty s = false) : s (sPick s) = true := by
  by_cases hT : s T = true
  · have hp : sPick s = T := if_pos hT
    rw [hp]; exact hT
  · have h1 : sPick s = if s F = true then F else Z := if_neg hT
    by_cases hF : s F = true
    · rw [h1, if_pos hF]; exact hF
    · rw [h1, if_neg hF]
      cases hZ : s Z
      · exfalso
        have hT' : s T = false := bNotTrue _ hT
        have hF' : s F = false := bNotTrue _ hF
        have : sIsEmpty s = true := bAllFalse (s T) (s F) (s Z) hT' hF' hZ
        rw [this] at h
        cases h
      · rfl

/-! ## Nodes, valuations, satisfiability -/

abbrev Node := Sign × Fm

/-- A valuation satisfies a node: the formula's value lies in the sign. -/
def satN (v : Nat → V) (nd : Node) : Prop := nd.1 (evalF v nd.2) = true

/-- A recursive conjunction (no list membership). -/
def satL (v : Nat → V) : List Node → Prop
  | [] => True
  | nd :: ns => satN v nd ∧ satL v ns

abbrev Env := Nat → Sign

def envOK (v : Nat → V) (e : Env) : Prop := ∀ n, e n (v n) = true

def SAT (e : Env) (ws : List Node) : Prop := ∃ v, envOK v e ∧ satL v ws

def upd (e : Env) (n : Nat) (s : Sign) : Env := fun m => if m = n then s else e m

/-- Weighted size: the heavy connectives weigh just enough that the
reduction to the basis strictly decreases the weight. -/
def Fm.size : Fm → Nat
  | .atom _   => 1
  | .top      => 1
  | .bot      => 1
  | .neg φ    => φ.size + 1
  | .conj φ ψ => φ.size + ψ.size + 1
  | .disj φ ψ => φ.size + ψ.size + 1
  | .imp φ ψ  => φ.size + 1 + ψ.size + 1 + 2
  | .xor φ ψ  => φ.size + (ψ.size + 1) + 1 + (φ.size + 1 + ψ.size + 1) + 3
  | .xnor φ ψ => φ.size + ψ.size + 1 + (φ.size + 1 + (ψ.size + 1) + 1) + 3

theorem Fm.size_pos : ∀ φ : Fm, 1 ≤ φ.size := by
  intro φ
  cases φ
  case atom n => exact Nat.le_refl 1
  case top => exact Nat.le_refl 1
  case bot => exact Nat.le_refl 1
  case neg φ => exact Nat.le_add_left 1 _
  case conj φ ψ => exact Nat.le_add_left 1 _
  case disj φ ψ => exact Nat.le_add_left 1 _
  case imp φ ψ => exact Nat.le_add_left 1 _
  case xor φ ψ => exact Nat.le_add_left 1 _
  case xnor φ ψ => exact Nat.le_add_left 1 _

def wsize : List Node → Nat
  | [] => 0
  | nd :: rest => nd.2.size + wsize rest

/-- The tableau engine: structural recursion on fuel. An atom —
constraint intersection; ¬,∧,∨ — the signed rules (weak signs only in
F-polarity); →,⊕,↔ — reduction to the basis. -/
def closes (fuel : Nat) (e : Env) (ws : List Node) : Bool :=
  match fuel, ws with
  | 0, _ => false
  | _ + 1, [] => false
  | fuel + 1, (s, .atom n) :: rest =>
      if sIsEmpty (inter (e n) s) = true then true
      else closes fuel (upd e n (inter (e n) s)) rest
  | fuel + 1, (s, .top) :: rest =>
      if s T = true then closes fuel e rest else true
  | fuel + 1, (s, .bot) :: rest =>
      if s F = true then closes fuel e rest else true
  | fuel + 1, (s, .neg φ) :: rest =>
      if s T = true then
        if s F = true then closes fuel e rest
        else closes fuel e ((SignF, φ) :: rest)
      else
        if s F = true then closes fuel e ((SignP, φ) :: rest)
        else true
  | fuel + 1, (s, .conj φ ψ) :: rest =>
      if s T = true then
        if s F = true then closes fuel e rest
        else closes fuel e ((SignT, φ) :: (SignT, ψ) :: rest)
      else
        if s F = true then
          closes fuel e ((SignN, φ) :: rest) && closes fuel e ((SignN, ψ) :: rest)
        else true
  | fuel + 1, (s, .disj φ ψ) :: rest =>
      if s T = true then
        if s F = true then closes fuel e rest
        else closes fuel e ((SignT, φ) :: rest) && closes fuel e ((SignT, ψ) :: rest)
      else
        if s F = true then closes fuel e ((SignN, φ) :: (SignN, ψ) :: rest)
        else true
  | fuel + 1, (s, .imp φ ψ) :: rest =>
      closes fuel e ((s, .disj (.neg φ) ψ) :: rest)
  | fuel + 1, (s, .xor φ ψ) :: rest =>
      closes fuel e ((s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) :: rest)
  | fuel + 1, (s, .xnor φ ψ) :: rest =>
      closes fuel e ((s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) :: rest)
  termination_by structural fuel

/-! ## A sign against a classical value -/

theorem mem_cls_T {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : s T = true) (hF : s F = false) : s x = true ↔ x = T := by
  constructor
  · intro h
    rcases hx with rfl | rfl
    · rfl
    · rw [hF] at h; cases h
  · rintro rfl; exact hT

theorem mem_cls_F {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : s T = false) (hF : s F = true) : s x = true ↔ x = F := by
  constructor
  · intro h
    rcases hx with rfl | rfl
    · rw [hT] at h; cases h
    · rfl
  · rintro rfl; exact hF

theorem mem_cls_both {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : s T = true) (hF : s F = true) : s x = true := by
  rcases hx with rfl | rfl
  · exact hT
  · exact hF

theorem not_mem_cls {x : V} {s : Sign} (hx : x = T ∨ x = F)
    (hT : s T = false) (hF : s F = false) : ¬(s x = true) := by
  intro h
  rcases hx with rfl | rfl
  · rw [hT] at h; cases h
  · rw [hF] at h; cases h

/-! ## Tools for satL and SAT -/

theorem satL_nil (v : Nat → V) : satL v [] := trivial

theorem satL_cons {v : Nat → V} {nd : Node} {ns : List Node} :
    satL v (nd :: ns) ↔ satN v nd ∧ satL v ns := Iff.rfl

theorem SAT_head_congr {e : Env} {nd nd' : Node} {ws : List Node}
    (h : ∀ v, satN v nd ↔ satN v nd') :
    SAT e (nd :: ws) ↔ SAT e (nd' :: ws) := by
  constructor
  · rintro ⟨v, hOK, h1, h2⟩
    exact ⟨v, hOK, (h v).mp h1, h2⟩
  · rintro ⟨v, hOK, h1, h2⟩
    exact ⟨v, hOK, (h v).mpr h1, h2⟩

theorem SAT_head_split2 {e : Env} {nd a b : Node} {ws : List Node}
    (h : ∀ v, satN v nd ↔ (satN v a ∧ satN v b)) :
    SAT e (nd :: ws) ↔ SAT e (a :: b :: ws) := by
  constructor
  · rintro ⟨v, hOK, h1, h2⟩
    have ⟨ha, hb⟩ := (h v).mp h1
    exact ⟨v, hOK, ha, hb, h2⟩
  · rintro ⟨v, hOK, ha, hb, h2⟩
    exact ⟨v, hOK, (h v).mpr ⟨ha, hb⟩, h2⟩

theorem SAT_head_or {e : Env} {nd a b : Node} {ws : List Node}
    (h : ∀ v, satN v nd ↔ (satN v a ∨ satN v b)) :
    SAT e (nd :: ws) ↔ (SAT e (a :: ws) ∨ SAT e (b :: ws)) := by
  constructor
  · rintro ⟨v, hOK, h1, h2⟩
    rcases (h v).mp h1 with ha | hb
    · exact Or.inl ⟨v, hOK, ha, h2⟩
    · exact Or.inr ⟨v, hOK, hb, h2⟩
  · rintro (⟨v, hOK, h1, h2⟩ | ⟨v, hOK, h1, h2⟩)
    · exact ⟨v, hOK, (h v).mpr (Or.inl h1), h2⟩
    · exact ⟨v, hOK, (h v).mpr (Or.inr h1), h2⟩

theorem SAT_head_true {e : Env} {nd : Node} {ws : List Node}
    (h : ∀ v, satN v nd) : SAT e (nd :: ws) ↔ SAT e ws := by
  constructor
  · rintro ⟨v, hOK, _, h2⟩; exact ⟨v, hOK, h2⟩
  · rintro ⟨v, hOK, h2⟩; exact ⟨v, hOK, h v, h2⟩

theorem SAT_head_false {e : Env} {nd : Node} {ws : List Node}
    (h : ∀ v, ¬ satN v nd) : ¬ SAT e (nd :: ws) := by
  rintro ⟨v, _, h1, _⟩; exact h v h1

/-- The atom step: an atom head is equivalent to narrowing the constraints. -/
theorem SAT_atom {e : Env} {s : Sign} {n : Nat} {ws : List Node} :
    SAT e ((s, .atom n) :: ws) ↔ SAT (upd e n (inter (e n) s)) ws := by
  constructor
  · rintro ⟨v, hOK, h1, h2⟩
    refine ⟨v, fun m => ?_, h2⟩
    by_cases hm : m = n
    · subst hm
      have hu : upd e m (inter (e m) s) m = inter (e m) s := if_pos rfl
      rw [hu]
      exact (andEqTrue _ _).mpr ⟨hOK m, h1⟩
    · have hu : upd e n (inter (e n) s) m = e m := if_neg hm
      exact hu ▸ hOK m
  · rintro ⟨v, hOK, hs⟩
    have hn : inter (e n) s (v n) = true := by
      have h := hOK n
      have hu : upd e n (inter (e n) s) n = inter (e n) s := if_pos rfl
      rw [hu] at h
      exact h
    have hpair := (andEqTrue _ _).mp hn
    refine ⟨v, fun m => ?_, hpair.2, hs⟩
    by_cases hm : m = n
    · subst hm; exact hpair.1
    · have h := hOK m
      have hu : upd e n (inter (e n) s) m = e m := if_neg hm
      rw [hu] at h
      exact h

/-! ## The main theorem -/

theorem closes_iff : ∀ (fuel : Nat) (e : Env) (ws : List Node),
    wsize ws < fuel → (∀ n, sIsEmpty (e n) = false) →
    (closes fuel e ws = true ↔ ¬ SAT e ws) := by
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
      have hb1 : (1 : Nat) + wsize rest < fuel + 1 := hb
      have hle' : wsize rest < fuel :=
        boundStep (Nat.le_of_eq (Nat.add_comm _ 1)) hb1
      show (if sIsEmpty (inter (e n) s) = true then true
            else closes fuel (upd e n (inter (e n) s)) rest) = true ↔ _
      split
      · next hemp =>
        constructor
        · intro _
          rintro ⟨v, hOK, h1, _⟩
          have hmem : inter (e n) s (v n) = true :=
            (andEqTrue _ _).mpr ⟨hOK n, h1⟩
          have := sNonempty_of_mem hmem
          rw [hemp] at this
          cases this
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
    | (s, .top) :: rest =>
      have hb : Fm.size .top + wsize rest < fuel + 1 := hle
      have hle' : wsize rest < fuel :=
        boundStep (Nat.le_of_eq (Nat.add_comm _ 1)) hb
      show (if s T = true then closes fuel e rest else true) = true ↔ _
      split
      · next hT =>
        have hdrop : SAT e ((s, .top) :: rest) ↔ SAT e rest :=
          SAT_head_true fun _ => hT
        exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
      · next hT =>
        constructor
        · intro _
          exact SAT_head_false fun _ h1 => hT h1
        · intro _; rfl
    | (s, .bot) :: rest =>
      have hb : Fm.size .bot + wsize rest < fuel + 1 := hle
      have hle' : wsize rest < fuel :=
        boundStep (Nat.le_of_eq (Nat.add_comm _ 1)) hb
      show (if s F = true then closes fuel e rest else true) = true ↔ _
      split
      · next hF =>
        have hdrop : SAT e ((s, .bot) :: rest) ↔ SAT e rest :=
          SAT_head_true fun _ => hF
        exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
      · next hF =>
        constructor
        · intro _
          exact SAT_head_false fun _ h1 => hF h1
        · intro _; rfl
    | (s, .neg φ) :: rest =>
      have hcls : ∀ v, znot (evalF v φ) = T ∨ znot (evalF v φ) = F :=
        fun v => lift1_classical _ _
      have hb : Fm.size φ + 1 + wsize rest < fuel + 1 := hle
      show (if s T = true then
              if s F = true then closes fuel e rest
              else closes fuel e ((SignF, φ) :: rest)
            else
              if s F = true then closes fuel e ((SignP, φ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel :=
            boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_comm _ 1))
              (Nat.add_le_add_right (Nat.le_add_left 1 _) _)) hb
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
              if s F = true then closes fuel e rest
              else closes fuel e ((SignT, φ) :: (SignT, ψ) :: rest)
            else
              if s F = true then
                closes fuel e ((SignN, φ) :: rest) &&
                closes fuel e ((SignN, ψ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel :=
            boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_comm _ 1))
              (Nat.add_le_add_right (Nat.le_add_left 1 _) _)) hb
          have hdrop : SAT e ((s, .conj φ ψ) :: rest) ↔ SAT e rest :=
            SAT_head_true fun v => mem_cls_both (hcls v) hT hF
          exact (ih _ rest hle' he).trans (notCongr hdrop.symm)
        · next hF =>
          have e1 : Fm.size φ + (Fm.size ψ + wsize rest) + 1
              = Fm.size φ + Fm.size ψ + 1 + wsize rest := by
            rw [← Nat.add_assoc,
                Nat.add_right_comm (Fm.size φ + Fm.size ψ) (wsize rest) 1]
          have hle' : wsize ((SignT, φ) :: (SignT, ψ) :: rest) < fuel :=
            boundStep (Nat.le_of_eq e1) hb
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
              if s F = true then closes fuel e rest
              else closes fuel e ((SignT, φ) :: rest) &&
                   closes fuel e ((SignT, ψ) :: rest)
            else
              if s F = true then
                closes fuel e ((SignN, φ) :: (SignN, ψ) :: rest)
              else true) = true ↔ _
      split
      · next hT =>
        split
        · next hF =>
          have hle' : wsize rest < fuel :=
            boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_comm _ 1))
              (Nat.add_le_add_right (Nat.le_add_left 1 _) _)) hb
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
          have e1 : Fm.size φ + (Fm.size ψ + wsize rest) + 1
              = Fm.size φ + Fm.size ψ + 1 + wsize rest := by
            rw [← Nat.add_assoc,
                Nat.add_right_comm (Fm.size φ + Fm.size ψ) (wsize rest) 1]
          have hle' : wsize ((SignN, φ) :: (SignN, ψ) :: rest) < fuel :=
            boundStep (Nat.le_of_eq e1) hb
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
      have hb : Fm.size (.disj (.neg φ) ψ) + 2 + wsize rest < fuel + 1 := hle
      have hle' : wsize ((s, .disj (.neg φ) ψ) :: rest) < fuel :=
        boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm _ _ 1))
          (Nat.add_le_add_right (Nat.le_succ _) _)) hb
      have hpt : ∀ v, satN v (s, .imp φ ψ) ↔
          satN v (s, .disj (.neg φ) ψ) := fun v =>
        iffOfEq (congrArg (fun x => s x = true)
          (imp_def (evalF v φ) (evalF v ψ)))
      exact (ih _ _ hle' he).trans (notCongr (SAT_head_congr hpt).symm)
    | (s, .xor φ ψ) :: rest =>
      have hb : Fm.size (.disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) + 2
          + wsize rest < fuel + 1 := hle
      have hle' : wsize ((s, .disj (.conj φ (.neg ψ))
          (.conj (.neg φ) ψ)) :: rest) < fuel :=
        boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm _ _ 1))
          (Nat.add_le_add_right (Nat.le_succ _) _)) hb
      have hpt : ∀ v, satN v (s, .xor φ ψ) ↔
          satN v (s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) := fun v =>
        iffOfEq (congrArg (fun x => s x = true)
          (xor_def (evalF v φ) (evalF v ψ)))
      exact (ih _ _ hle' he).trans (notCongr (SAT_head_congr hpt).symm)
    | (s, .xnor φ ψ) :: rest =>
      have hb : Fm.size (.disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) + 2
          + wsize rest < fuel + 1 := hle
      have hle' : wsize ((s, .disj (.conj φ ψ)
          (.conj (.neg φ) (.neg ψ))) :: rest) < fuel :=
        boundStep (Nat.le_trans (Nat.le_of_eq (Nat.add_right_comm _ _ 1))
          (Nat.add_le_add_right (Nat.le_succ _) _)) hb
      have hpt : ∀ v, satN v (s, .xnor φ ψ) ↔
          satN v (s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) := fun v =>
        iffOfEq (congrArg (fun x => s x = true)
          (xnor_def (evalF v φ) (evalF v ψ)))
      exact (ih _ _ hle' he).trans (notCongr (SAT_head_congr hpt).symm)

/-! ## Corollary: derivability = entailment -/

def e0 : Env := fun _ => fun _ => true

/-- Γ ⊢ φ: premises under the strict sign T, the conclusion under the weak N. -/
def tproves (ps : List Fm) (c : Fm) : Bool :=
  closes (wsize (ps.map (fun p => (SignT, p)) ++ [(SignN, c)]) + 1) e0
    (ps.map (fun p => (SignT, p)) ++ [(SignN, c)])

theorem satL_bridge {v : Nat → V} (c : Fm) : ∀ (ps : List Fm),
    satL v (ps.map (fun p => (SignT, p)) ++ [(SignN, c)]) ↔
    ((∀ p, p ∈ ps → evalF v p = T) ∧ SignN (evalF v c) = true) := by
  intro ps
  induction ps with
  | nil =>
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨(fun p hp => nomatch hp), h1⟩
    · rintro ⟨-, h2⟩
      exact ⟨h2, trivial⟩
  | cons q ps ihp =>
    constructor
    · rintro ⟨h1, h2⟩
      have ⟨hall, hc⟩ := ihp.mp h2
      refine ⟨fun p hp => ?_, hc⟩
      cases hp with
      | head => exact (vT _).mp h1
      | tail _ hp' => exact hall p hp'
    · rintro ⟨hall, hc⟩
      exact ⟨(vT _).mpr (hall q (List.Mem.head _)),
             ihp.mpr ⟨fun p hp => hall p (List.Mem.tail _ hp), hc⟩⟩

/-- The certificate: the engine returns ⊢ ⟺ semantic entailment over {T}. -/
theorem tproves_iff (ps : List Fm) (c : Fm) :
    tproves ps c = true ↔
    ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T := by
  have he0 : ∀ n : Nat, sIsEmpty (e0 n) = false := fun _ => rfl
  have key := closes_iff
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

/-! ## Smoke runs of the certified engine -/

#eval tproves [] (.imp (.atom 0) (.atom 0))                      -- false: ⊬ p→p
#eval tproves [.atom 0, .imp (.atom 0) (.atom 1)] (.atom 1)      -- true: MP
#eval tproves [] (.neg (.conj (.atom 0) (.neg (.atom 0))))       -- true: ¬(p∧¬p)
#eval tproves [] (.disj (.atom 0) (.neg (.atom 0)))              -- false: ⊬ LEM
#eval tproves [.imp (.atom 0) (.atom 1)]
      (.imp (.neg (.atom 1)) (.neg (.atom 0)))                   -- true: contraposition-rule
#eval tproves [.neg (.neg (.atom 0))] (.atom 0)                  -- false: ¬¬-elimination fell

#print axioms closes_iff
#print axioms tproves_iff

end V
