import ZTL
/-! # ZEvidence — ZTL is the classical logic of evidence (2026-10-28). Zero axioms.
An evidence valuation says, for each atom, whether it is established true (t), established false (f),
or neither. Every ZTL formula translates into a classical formula over the evidence atoms t_n, f_n,
and its ZTL value is T exactly when the translation is classically true. -/
namespace V

inductive CF where
  | ev   : Nat → Bool → CF        -- ev n true: "n is established true"; ev n false: "n is established false"
  | top  : CF
  | bot  : CF
  | neg  : CF → CF
  | conj : CF → CF → CF
  | imp  : CF → CF → CF

/-- classical evaluation, with the evidence read off a ZTL valuation -/
def cev (v : Nat → V) : CF → Bool
  | .ev n b => if b then v n == T else v n == F
  | .top => true
  | .bot => false
  | .neg c => !cev v c
  | .conj c d => cev v c && cev v d
  | .imp c d => !cev v c || cev v d

def cconst (b : Bool) : CF := if b then .top else .bot

/-- "the argument φ (with translation t) can read as b": for an atom, the evidence does not exclude b;
for a compound, its evVerdict is b. -/
def evVerdict (t : CF) : Bool → CF
  | true => t
  | false => .neg t

def argPoss : Fm → CF → Bool → CF
  | .atom n, _, b => .neg (.ev n (!b))
  | .top, _, b => cconst b
  | .bot, _, b => cconst (!b)
  | .neg _, t, b => evVerdict t b
  | .conj _ _, t, b => evVerdict t b
  | .disj _ _, t, b => evVerdict t b
  | .imp _ _, t, b => evVerdict t b
  | .xor _ _, t, b => evVerdict t b
  | .xnor _ _, t, b => evVerdict t b

/-- a binary connective holds iff it is forced over every reading of its two arguments -/
def bin (g : Bool → Bool → Bool) (P Q : Bool → CF) : CF :=
  .conj (.conj (.imp (.conj (P true) (Q true)) (cconst (g true true)))
               (.imp (.conj (P true) (Q false)) (cconst (g true false))))
        (.conj (.imp (.conj (P false) (Q true)) (cconst (g false true)))
               (.imp (.conj (P false) (Q false)) (cconst (g false false))))

def evTr : Fm → CF
  | .atom n => .ev n true
  | .top => .top
  | .bot => .bot
  | .neg φ => .conj (.imp (argPoss φ (evTr φ) true) .bot) (.imp (argPoss φ (evTr φ) false) .top)
  | .conj φ ψ => bin (fun a b => a && b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))
  | .disj φ ψ => bin (fun a b => a || b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))
  | .imp φ ψ  => bin (fun a b => !a || b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))
  | .xor φ ψ  => bin (fun a b => a != b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))
  | .xnor φ ψ => bin (fun a b => a == b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))

/-- the readings of a value, as a Bool test -/
def rd1 (x : V) (b : Bool) : Bool := (subs x).contains b

theorem cconst_cev (v : Nat → V) (b : Bool) : cev v (cconst b) = b := by cases b <;> rfl

theorem bin_cev (v : Nat → V) (g : Bool → Bool → Bool) (P Q : Bool → CF) :
    cev v (bin g P Q) = (((!(cev v (P true) && cev v (Q true)) || (g) true true) && (!(cev v (P true) && cev v (Q false)) || (g) true false)) && ((!(cev v (P false) && cev v (Q true)) || (g) false true) && (!(cev v (P false) && cev v (Q false)) || (g) false false))) := by
  show (((!(cev v (P true) && cev v (Q true)) || cev v (cconst (g true true))) &&
        (!(cev v (P true) && cev v (Q false)) || cev v (cconst (g true false)))) &&
       ((!(cev v (P false) && cev v (Q true)) || cev v (cconst (g false true))) &&
        (!(cev v (P false) && cev v (Q false)) || cev v (cconst (g false false))))) = _
  rw [cconst_cev, cconst_cev, cconst_cev, cconst_cev]

theorem lnot : ∀ x : V, (znot x == T) = ((!(rd1 x true) || false) && (!(rd1 x false) || true)) := by decide
theorem l_conj : ∀ x y : V, (zand x y == T) = (((!(rd1 x true && rd1 y true) || (fun a b => a && b) true true) && (!(rd1 x true && rd1 y false) || (fun a b => a && b) true false)) && ((!(rd1 x false && rd1 y true) || (fun a b => a && b) false true) && (!(rd1 x false && rd1 y false) || (fun a b => a && b) false false))) := by decide
theorem l_disj : ∀ x y : V, (zor x y == T) = (((!(rd1 x true && rd1 y true) || (fun a b => a || b) true true) && (!(rd1 x true && rd1 y false) || (fun a b => a || b) true false)) && ((!(rd1 x false && rd1 y true) || (fun a b => a || b) false true) && (!(rd1 x false && rd1 y false) || (fun a b => a || b) false false))) := by decide
theorem l_imp : ∀ x y : V, (zimp x y == T) = (((!(rd1 x true && rd1 y true) || (fun a b => !a || b) true true) && (!(rd1 x true && rd1 y false) || (fun a b => !a || b) true false)) && ((!(rd1 x false && rd1 y true) || (fun a b => !a || b) false true) && (!(rd1 x false && rd1 y false) || (fun a b => !a || b) false false))) := by decide
theorem l_xor : ∀ x y : V, (zxor x y == T) = (((!(rd1 x true && rd1 y true) || (fun a b => a != b) true true) && (!(rd1 x true && rd1 y false) || (fun a b => a != b) true false)) && ((!(rd1 x false && rd1 y true) || (fun a b => a != b) false true) && (!(rd1 x false && rd1 y false) || (fun a b => a != b) false false))) := by decide
theorem l_xnor : ∀ x y : V, (zxnor x y == T) = (((!(rd1 x true && rd1 y true) || (fun a b => a == b) true true) && (!(rd1 x true && rd1 y false) || (fun a b => a == b) true false)) && ((!(rd1 x false && rd1 y true) || (fun a b => a == b) false true) && (!(rd1 x false && rd1 y false) || (fun a b => a == b) false false))) := by decide

theorem atom_rd (x : V) (b : Bool) : (!(if !b then x == T else x == F)) = rd1 x b := by
  cases x <;> cases b <;> rfl
theorem cls_true (x : V) (h : x = T ∨ x = F) : (x == T) = rd1 x true := by
  rcases h with h | h <;> subst h <;> rfl
theorem cls_false (x : V) (h : x = T ∨ x = F) : (!(x == T)) = rd1 x false := by
  rcases h with h | h <;> subst h <;> rfl

theorem ev_compound_classical (v : Nat → V) (φ : Fm) (h : ∀ n, φ ≠ .atom n) :
    evalF v φ = T ∨ evalF v φ = F := by
  rcases evalF_classical v φ with ⟨n, hn⟩ | h' | h'
  · exact absurd hn (h n)
  · exact Or.inl h'
  · exact Or.inr h'

/-- The translation is exact, and every argument reads exactly as the evidence allows. -/
theorem tr_exact (v : Nat → V) : ∀ φ : Fm, cev v (evTr φ) = (evalF v φ == T) ∧
    ∀ b, cev v (argPoss φ (evTr φ) b) = rd1 (evalF v φ) b := by
  intro φ
  induction φ with
  | atom n => exact ⟨rfl, fun b => atom_rd (v n) b⟩
  | top => exact ⟨rfl, fun b => by cases b <;> rfl⟩
  | bot => exact ⟨rfl, fun b => by cases b <;> rfl⟩
  | neg φ ih =>
      have e : cev v (evTr (.neg φ)) = (evalF v (.neg φ) == T) := by
        show (((!(cev v (argPoss φ (evTr φ) true)) || false) && (!(cev v (argPoss φ (evTr φ) false)) || true)))
            = (znot (evalF v φ) == T)
        rw [ih.2 true, ih.2 false, lnot]
      have hc := ev_compound_classical v (.neg φ) (fun n h => Fm.noConfusion h)
      refine ⟨e, fun b => ?_⟩
      cases b
      · show (!cev v (evTr (.neg φ))) = _
        rw [e]; exact cls_false _ hc
      · show cev v (evTr (.neg φ)) = _
        rw [e]; exact cls_true _ hc
  | conj φ ψ ihφ ihψ =>
      have e : cev v (evTr (.conj φ ψ)) = (evalF v (.conj φ ψ) == T) := by
        show cev v (bin (fun a b => a && b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))) = (zand (evalF v φ) (evalF v ψ) == T)
        rw [bin_cev, ihφ.2 true, ihφ.2 false, ihψ.2 true, ihψ.2 false, l_conj]
      have hc := ev_compound_classical v (.conj φ ψ) (fun n h => Fm.noConfusion h)
      refine ⟨e, fun b => ?_⟩
      cases b
      · show (!cev v (evTr (.conj φ ψ))) = _
        rw [e]; exact cls_false _ hc
      · show cev v (evTr (.conj φ ψ)) = _
        rw [e]; exact cls_true _ hc
  | disj φ ψ ihφ ihψ =>
      have e : cev v (evTr (.disj φ ψ)) = (evalF v (.disj φ ψ) == T) := by
        show cev v (bin (fun a b => a || b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))) = (zor (evalF v φ) (evalF v ψ) == T)
        rw [bin_cev, ihφ.2 true, ihφ.2 false, ihψ.2 true, ihψ.2 false, l_disj]
      have hc := ev_compound_classical v (.disj φ ψ) (fun n h => Fm.noConfusion h)
      refine ⟨e, fun b => ?_⟩
      cases b
      · show (!cev v (evTr (.disj φ ψ))) = _
        rw [e]; exact cls_false _ hc
      · show cev v (evTr (.disj φ ψ)) = _
        rw [e]; exact cls_true _ hc
  | imp φ ψ ihφ ihψ =>
      have e : cev v (evTr (.imp φ ψ)) = (evalF v (.imp φ ψ) == T) := by
        show cev v (bin (fun a b => !a || b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))) = (zimp (evalF v φ) (evalF v ψ) == T)
        rw [bin_cev, ihφ.2 true, ihφ.2 false, ihψ.2 true, ihψ.2 false, l_imp]
      have hc := ev_compound_classical v (.imp φ ψ) (fun n h => Fm.noConfusion h)
      refine ⟨e, fun b => ?_⟩
      cases b
      · show (!cev v (evTr (.imp φ ψ))) = _
        rw [e]; exact cls_false _ hc
      · show cev v (evTr (.imp φ ψ)) = _
        rw [e]; exact cls_true _ hc
  | xor φ ψ ihφ ihψ =>
      have e : cev v (evTr (.xor φ ψ)) = (evalF v (.xor φ ψ) == T) := by
        show cev v (bin (fun a b => a != b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))) = (zxor (evalF v φ) (evalF v ψ) == T)
        rw [bin_cev, ihφ.2 true, ihφ.2 false, ihψ.2 true, ihψ.2 false, l_xor]
      have hc := ev_compound_classical v (.xor φ ψ) (fun n h => Fm.noConfusion h)
      refine ⟨e, fun b => ?_⟩
      cases b
      · show (!cev v (evTr (.xor φ ψ))) = _
        rw [e]; exact cls_false _ hc
      · show cev v (evTr (.xor φ ψ)) = _
        rw [e]; exact cls_true _ hc
  | xnor φ ψ ihφ ihψ =>
      have e : cev v (evTr (.xnor φ ψ)) = (evalF v (.xnor φ ψ) == T) := by
        show cev v (bin (fun a b => a == b) (argPoss φ (evTr φ)) (argPoss ψ (evTr ψ))) = (zxnor (evalF v φ) (evalF v ψ) == T)
        rw [bin_cev, ihφ.2 true, ihφ.2 false, ihψ.2 true, ihψ.2 false, l_xnor]
      have hc := ev_compound_classical v (.xnor φ ψ) (fun n h => Fm.noConfusion h)
      refine ⟨e, fun b => ?_⟩
      cases b
      · show (!cev v (evTr (.xnor φ ψ))) = _
        rw [e]; exact cls_false _ hc
      · show cev v (evTr (.xnor φ ψ)) = _
        rw [e]; exact cls_true _ hc

/-- ZTL is the classical logic of evidence: a formula is T iff its translation is classically true. -/
theorem ztl_is_evidence_logic (v : Nat → V) (φ : Fm) : evalF v φ = T ↔ cev v (evTr φ) = true := by
  rw [(tr_exact v φ).1]; cases evalF v φ <;> decide

end V

#print axioms V.tr_exact
#print axioms V.ztl_is_evidence_logic
