import ZTL

/-!
# Lean port of E5: sets with unverified elements. Zero axioms.

Element equality is an atom (T/F for verified, Z with any mark);
membership/inclusion are recursive zor/zand folds. The identity laws
fall on marked sets — inherited from the tables, as theorems.
-/

namespace V

inductive El where
  | v : Nat → El
  | z : Nat → El

/-- The equality atom: mark identity is never earned (not even with itself). -/
def eqAtom : El → El → V
  | .v a, .v b => cond (a == b) T F
  | .v _, .z _ => Z
  | .z _, .v _ => Z
  | .z _, .z _ => Z

/-- Membership: an ∃-fold (a strict witness). -/
def memL (x : El) : List El → V
  | [] => F
  | e :: es => zor (eqAtom x e) (memL x es)

/-- Inclusion: an ∀-fold (all strictly T). -/
def subL (S₁ S₂ : List El) : V :=
  match S₁ with
  | [] => T
  | e :: es => zand (memL e S₂) (subL es S₂)

def seteq (S₁ S₂ : List El) : V := zand (subL S₁ S₂) (subL S₂ S₁)

/-! ## Auxiliary value lemmas (by enumeration, clean) -/

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

/-! ## Theorem 1: a mark earns membership NOWHERE (Z ∉ anything) -/

theorem memZ : ∀ (i : Nat) (es : List El), memL (.z i) es = F := by
  intro i es
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h1 : zor (eqAtom (.z i) e) (memL (.z i) es)
        = zor (eqAtom (.z i) e) F := congrArg _ ih
    have h2 : zor (eqAtom (.z i) e) F = F := by cases e <;> rfl
    exact h1.trans h2

/-! ## Theorem 2: a marked set does not fit even into itself (S ⊆ S falls) -/

theorem sub_marked_false : ∀ (i : Nat) (pre S : List El),
    subL (pre ++ [.z i]) S = F := by
  intro i pre S
  induction pre with
  | nil =>
    exact (congrArg (fun x => zand x (subL [] S)) (memZ i S)).trans (zandFX _)
  | cons e pre ih =>
    exact (congrArg (zand (memL e S)) ih).trans (zandXF _)

/-- Corollary: reflexivity of set equality falls on marked sets. -/
theorem seteq_self_marked (i : Nat) (pre : List El) :
    seteq (pre ++ [El.z i]) (pre ++ [El.z i]) = F :=
  (congrArg (fun x => zand x (subL (pre ++ [El.z i]) (pre ++ [El.z i])))
    (sub_marked_false i pre (pre ++ [El.z i]))).trans (zandFX _)

/-! ## Concrete E5 facts (by computation, as in the Python stand) -/

-- {Z,Z} = {Z}: merging is not earned
example : seteq [.z 1, .z 1] [.z 1] = F := rfl
-- Z ∈ {Z} — the same mark! — membership is not earned
example : memL (.z 1) [.z 1] = F := rfl
-- verified elements — classical: 1 ∈ {1,2,Z}, 3 ∉ {1,2,Z}
example : memL (.v 1) [.v 1, .v 2, .z 7] = T := rfl
example : memL (.v 3) [.v 1, .v 2, .z 7] = F := rfl
-- clean reflexivity is alive, marked reflexivity fell
example : seteq [.v 1, .v 2] [.v 1, .v 2] = T := rfl
example : seteq [.v 1, .v 2, .z 7] [.v 1, .v 2, .z 7] = F := rfl

/-! ## Cardinality: an interval; |{Z}| = [1,1] — cardinality without identity -/

def cardLo (core quar : Nat) : Nat := if core = 0 then min quar 1 else core
def cardHi (core quar : Nat) : Nat := core + quar

example : cardLo 2 0 = 2 ∧ cardHi 2 0 = 2 := ⟨rfl, rfl⟩   -- |{1,2}| = [2,2]
example : cardLo 2 1 = 2 ∧ cardHi 2 1 = 3 := ⟨rfl, rfl⟩   -- |{1,2,Z}| = [2,3]
example : cardLo 0 1 = 1 ∧ cardHi 0 1 = 1 := ⟨rfl, rfl⟩   -- |{Z}| = [1,1] (!)
example : cardLo 0 2 = 1 ∧ cardHi 0 2 = 2 := ⟨rfl, rfl⟩   -- |{Z,Z}| = [1,2]

/-! ## C-extension, general: clean sets behave classically

The finitely-presented contrast to E6's streams: a registry of
VERIFIED elements certifies each of its own members (memL = T), and
reflexivity of ⊆ and = holds on every mark-free list — against
sub_marked_false / seteq_self_marked above, this is the inheritance
boundary drawn exactly at the mark. -/

/-- Mark-free check. -/
def cleanL : List El → Bool
  | [] => true
  | .v _ :: es => cleanL es
  | .z _ :: es => false

theorem zorTX : ∀ x : V, zor T x = T := by decide
theorem zorXT : ∀ x : V, zor x T = T := by decide

/-- Hand-rolled: core's Nat.beq_refl is simp-proved (propext); here
`==` on Nat is decide-based, so reflexivity is one clean line. -/
theorem beqRefl (n : Nat) : (n == n) = true := decide_eq_true rfl

theorem eqAtom_refl_v (a : Nat) : eqAtom (.v a) (.v a) = T := by
  show cond (a == a) T F = T
  rw [beqRefl a]
  rfl

/-- A verified element certifies its membership wherever it stands. -/
theorem memL_self (a : Nat) : ∀ (pre post : List El),
    memL (.v a) (pre ++ .v a :: post) = T := by
  intro pre post
  induction pre with
  | nil =>
    show zor (eqAtom (.v a) (.v a)) (memL (.v a) post) = T
    rw [eqAtom_refl_v a]
    exact zorTX _
  | cons e pre ih =>
    show zor (eqAtom (.v a) e) (memL (.v a) (pre ++ .v a :: post)) = T
    rw [ih]
    exact zorXT _

theorem append_cons_el : ∀ (pre : List El) (x : El) (S : List El),
    (pre ++ [x]) ++ S = pre ++ x :: S := by
  intro pre
  induction pre with
  | nil => intro x S; rfl
  | cons e pre ih =>
    intro x S
    exact congrArg (e :: ·) (ih x S)

/-- Reflexivity of inclusion on clean lists (with an accumulator). -/
theorem subL_refl_aux : ∀ (S pre : List El), cleanL S = true →
    subL S (pre ++ S) = T := by
  intro S
  induction S with
  | nil => intro pre _; rfl
  | cons e S ih =>
    intro pre hc
    cases e with
    | z i => exact nomatch hc
    | v a =>
      have hm := memL_self a pre S
      have hs := ih (pre ++ [El.v a]) hc
      rw [append_cons_el] at hs
      show zand (memL (.v a) (pre ++ .v a :: S))
                (subL S (pre ++ .v a :: S)) = T
      rw [hm, hs]
      rfl

/-- S ⊆ S holds on every clean list — C-extension as a theorem. -/
theorem subL_refl_clean (S : List El) (h : cleanL S = true) :
    subL S S = T :=
  subL_refl_aux S [] h

/-- S = S holds on every clean list — against seteq_self_marked. -/
theorem seteq_refl_clean (S : List El) (h : cleanL S = true) :
    seteq S S = T := by
  show zand (subL S S) (subL S S) = T
  rw [subL_refl_clean S h]
  rfl

#print axioms memZ
#print axioms sub_marked_false
#print axioms seteq_self_marked
#print axioms memL_self
#print axioms subL_refl_clean
#print axioms seteq_refl_clean

end V
