import ZTL

/-!
# ZDescent — a Thing brought down to acts: the descent π and conservativity, in ZTL's own logic. Zero axioms.

2026-10-23 (after Agrippa: "for Things Agrippa is right"; the curator: "when we bring them a level down we can speak
of their operational part"). Two registers share one formula language `Fm`: OPERATIONAL atoms and FORMAL atoms
(Things — a cardinal, choice, an actual infinity, any posit; `Fo n` says atom n is one). The DESCENT `descend tr`
replaces each Thing by its operational meaning `tr n`, an ordinary formula; operational atoms stay.

VR-Forms proves this shape (Theorem III.1, `VR/Forms/Conservativity*.lean`) for CLASSICAL Hilbert provability — Peirce's
law is among its axioms. Classical logic is the special case of ZTL in which no atom is left unsettled
(`ClassicalAgreement.evalF_agrees`: on mark-free valuations the two agree on every formula); ZTL is the wider frame,
since it also reads unsettled ground — and there Peirce's law, "A or not A", even `p → p` hold only once their atoms
are settled (`not_conversely`). So the classical proof does not carry over by itself. Proved here, with ZTL's
three-valued evaluation as the logic and no proof system at all:

  `descend_eval`   evaluating the descended formula = evaluating the original where each Thing takes the value of its
                   operational meaning (one substitution lemma, by structure);
  `conservative`   if the descent of every formal axiom follows from the operational theory, then every OPERATIONAL
                   formula that follows from the two-register theory already follows from the operational one: the
                   formal register adds no operational knowledge. Its operational part is exactly its descent;
  `every_base_is_not_knowledge`  the control the curator caught: "A or not A" is T under every base that settles A
                   either way — and is NOT a consequence in ZTL, because the base that has not settled A counts. What
                   a Thing gives below is what follows WITHOUT it (its descent), not "what holds whichever way it is
                   set" (that is the classical supervaluation move).

Consequence here is ZTL's: Γ ⊨ φ iff every valuation (T, F or Z on atoms) giving every member of Γ the value T gives
φ the value T. A Thing whose descent is not operationally available makes `conservative`'s premise fail — the theorem
then says nothing, which is the point: whether choice (or any Thing) is operationally harmless is a question about
its descent, asked one Thing at a time.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace V

/-- The descent: each formal atom (a Thing) becomes its operational meaning; everything else is kept. -/
def descend (Fo : Nat → Bool) (tr : Nat → Fm) : Fm → Fm
  | .atom n   => if Fo n then tr n else .atom n
  | .top      => .top
  | .bot      => .bot
  | .neg φ    => .neg (descend Fo tr φ)
  | .conj φ ψ => .conj (descend Fo tr φ) (descend Fo tr ψ)
  | .disj φ ψ => .disj (descend Fo tr φ) (descend Fo tr ψ)
  | .imp φ ψ  => .imp (descend Fo tr φ) (descend Fo tr ψ)
  | .xor φ ψ  => .xor (descend Fo tr φ) (descend Fo tr ψ)
  | .xnor φ ψ => .xnor (descend Fo tr φ) (descend Fo tr ψ)

/-- A formula of the operational register: no Thing occurs in it. -/
def Op (Fo : Nat → Bool) : Fm → Prop
  | .atom n   => Fo n = false
  | .top      => True
  | .bot      => True
  | .neg φ    => Op Fo φ
  | .conj φ ψ => Op Fo φ ∧ Op Fo ψ
  | .disj φ ψ => Op Fo φ ∧ Op Fo ψ
  | .imp φ ψ  => Op Fo φ ∧ Op Fo ψ
  | .xor φ ψ  => Op Fo φ ∧ Op Fo ψ
  | .xnor φ ψ => Op Fo φ ∧ Op Fo ψ

/-- The valuation a descent induces: a Thing takes the value of its operational meaning. -/
def lifted (Fo : Nat → Bool) (tr : Nat → Fm) (v : Nat → V) : Nat → V :=
  fun n => if Fo n then evalF v (tr n) else v n

theorem descend_eval (Fo : Nat → Bool) (tr : Nat → Fm) (v : Nat → V) :
    ∀ φ, evalF v (descend Fo tr φ) = evalF (lifted Fo tr v) φ := by
  intro φ
  induction φ with
  | atom n =>
      show evalF v (if Fo n then tr n else .atom n) = (if Fo n then evalF v (tr n) else v n)
      cases h : Fo n with
      | true => rfl
      | false => rfl
  | top => rfl
  | bot => rfl
  | neg φ ih => show znot _ = znot _; rw [ih]
  | conj φ ψ ihφ ihψ => show zand _ _ = zand _ _; rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ => show zor _ _ = zor _ _; rw [ihφ, ihψ]
  | imp φ ψ ihφ ihψ => show zimp _ _ = zimp _ _; rw [ihφ, ihψ]
  | xor φ ψ ihφ ihψ => show zxor _ _ = zxor _ _; rw [ihφ, ihψ]
  | xnor φ ψ ihφ ihψ => show zxnor _ _ = zxnor _ _; rw [ihφ, ihψ]

/-- An operational formula does not see the Things: the lifted valuation reads it as the original does. -/
theorem op_eval (Fo : Nat → Bool) (tr : Nat → Fm) (v : Nat → V) :
    ∀ φ, Op Fo φ → evalF (lifted Fo tr v) φ = evalF v φ := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      show (if Fo n then evalF v (tr n) else v n) = v n
      have h' : Fo n = false := h
      rw [h']; rfl
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih => intro h; show znot _ = znot _; rw [ih h]
  | conj φ ψ ihφ ihψ => intro h; show zand _ _ = zand _ _; rw [ihφ h.1, ihψ h.2]
  | disj φ ψ ihφ ihψ => intro h; show zor _ _ = zor _ _; rw [ihφ h.1, ihψ h.2]
  | imp φ ψ ihφ ihψ => intro h; show zimp _ _ = zimp _ _; rw [ihφ h.1, ihψ h.2]
  | xor φ ψ ihφ ihψ => intro h; show zxor _ _ = zxor _ _; rw [ihφ h.1, ihψ h.2]
  | xnor φ ψ ihφ ihψ => intro h; show zxnor _ _ = zxnor _ _; rw [ihφ h.1, ihψ h.2]

/-- ZTL consequence: every valuation making every member of Γ true makes φ true. -/
def Cons (Γ : Fm → Prop) (φ : Fm) : Prop := ∀ v : Nat → V, (∀ γ, Γ γ → evalF v γ = T) → evalF v φ = T

/-- CONSERVATIVITY IN ZTL. The descent of every formal axiom follows operationally ⇒ the two-register theory has no
operational consequence the operational theory lacks. -/
theorem conservative (Fo : Nat → Bool) (tr : Nat → Fm) (T₁ T₀ : Fm → Prop)
    (harmless : ∀ α, T₁ α → Cons T₀ (descend Fo tr α))
    (φ : Fm) (hop : Op Fo φ) (h : Cons T₁ φ) : Cons T₀ φ := by
  intro v hv
  have m₁ : ∀ α, T₁ α → evalF (lifted Fo tr v) α = T := by
    intro α hα
    rw [← descend_eval Fo tr v α]
    exact harmless α hα v hv
  rw [← op_eval Fo tr v φ hop]
  exact h _ m₁

/-- "A or not A". -/
def em (n : Nat) : Fm := .disj (.atom n) (.neg (.atom n))

/-- THE CONTROL. Under every base that settles A — A true, or A false — "A or not A" is T; yet it is not a ZTL
consequence of nothing: the base where A is unsettled (Z) does not give it T. "Holds in every settled base" is not
knowledge. -/
theorem every_base_is_not_knowledge (n : Nat) :
    (evalF (fun _ => T) (em n) = T ∧ evalF (fun _ => F) (em n) = T) ∧ ¬ Cons (fun _ => False) (em n) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro h
  have e : zor Z (znot Z) = T := h (fun _ => Z) (fun _ hγ => False.elim hγ)
  exact absurd e (by decide)

end V

#print axioms V.descend_eval
#print axioms V.op_eval
#print axioms V.conservative
#print axioms V.every_base_is_not_knowledge
