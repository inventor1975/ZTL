import TableauCert
import ZRead

/-!
# ZGround — the passport's grounding, from ZTL alone (pure branch, 2026-11-22). Zero axioms.

A system is a list of defining formulas (sentence i defined by the i-th formula, over atoms Tr(0), Tr(1), …).
Which sentences have a definite value? Kripke's construction (1975): start knowing nothing, re-evaluate every
definition, keep what has become determined, repeat until nothing changes — the least fixed point; the names
that never settle are the quarantine. The FRAME (iterate to a fixed point) is Kripke's; the existence of the
fixed point is the Knaster–Tarski theorem, proved below for every finite system. The STEP — "has this name
become determined?" — is ZTL's own rule (curator, 2026-11-22), not a borrowed table:

  * an OWN name (a sentence of the system) not yet determined is in the solver's phase `Ph.n` ("not yet
    computed", SPEC §N: present only under self-reference, never a truth value). It is ours: one value at all
    its occurrences. A name becomes determined T (F) when its definition is T (F) under EVERY classical value
    of the still-undetermined names (`comps`: every completion) — the stable test, the judge's IF STABLE;
  * a FOREIGN input (an atom outside the system) is never determined by the system; the step reads it the
    same way — classically, one value per atom (curator 2026-11-22: "first classics; if classics gives no
    answer, then Z and ZTL's verdicts"). ZTL's tables give the VERDICT, not the grounding.

The phase is a separate type
`Ph` so that `n` can never be confused with the mark Z. Monotone (`evalS_mono`): more determined names only
narrow the completions, so a determined value is never revoked — which is all Knaster–Tarski needs.
-/

namespace V

/-! ## The solver's phase -/

inductive Ph where
  | t
  | f
  | n   -- not yet computed (the solver's phase N)
deriving DecidableEq, Repr

instance (p : Ph → Prop) [DecidablePred p] : Decidable (∀ x : Ph, p x) :=
  decidable_of_iff (p .n ∧ p .t ∧ p .f)
    ⟨fun ⟨hn, ht, hf⟩ x => by cases x <;> assumption,
     fun h => ⟨h .n, h .t, h .f⟩⟩

/-- The information order: n below t and f, t and f incomparable. -/
-- Non-overlapping rows: an overlapping wildcard row pulls propext in through the compiled matcher
-- (measured here, as in ZTL.lean).
def phLeq : Ph → Ph → Bool
  | .n, .n => true | .n, .t => true | .n, .f => true
  | .t, .n => false | .t, .t => true | .t, .f => false
  | .f, .n => false | .f, .t => false | .f, .f => true

theorem phLeq_refl : ∀ a : Ph, phLeq a a = true := by decide
theorem leqN : ∀ b : Ph, phLeq .n b = true := by decide
theorem vbeq : ∀ a b : Ph, (a == b) = true ↔ a = b := by decide
theorem leq_ne_n : ∀ a b : Ph, phLeq a b = true → ¬(a = b) → (a = .n ∧ ¬(b = .n)) := by decide
theorem leq_nn : ∀ a b : Ph, phLeq a b = true → ¬(a = .n) → b = a := by decide

abbrev PVal := List Ph
abbrev Sys := List Fm

/-- Read a phase list (off the end = n). -/
def getP : PVal → Nat → Ph
  | [], _ => .n
  | a :: _, 0 => a
  | _ :: v, n + 1 => getP v n

def pvLeq : PVal → PVal → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: v, b :: w => phLeq a b && pvLeq v w

def pvEq : PVal → PVal → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: v, b :: w => (a == b) && pvEq v w

theorem pvEq_iff : ∀ v w : PVal, pvEq v w = true ↔ v = w := by
  intro v
  induction v with
  | nil =>
    intro w
    cases w with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b w => exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | cons a v ih =>
    intro w
    cases w with
    | nil => exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
    | cons b w =>
      refine ((andEqTrue _ _).trans (andCongr (vbeq a b) (ih w))).trans ?_
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩

theorem getP_mono : ∀ v w : PVal, pvLeq v w = true →
    ∀ n, phLeq (getP v n) (getP w n) = true := by
  intro v
  induction v with
  | nil =>
    intro w h n
    cases w with
    | nil => exact leqN _
    | cons b w => exact nomatch h
  | cons a v ih =>
    intro w h n
    cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hp := (andEqTrue _ _).mp h
      cases n with
      | zero => exact hp.1
      | succ n => exact ih w hp.2 n

/-! ## Completions: every classical value of the undetermined own names -/

def comps : PVal → List (List Bool)
  | [] => [[]]
  | .n :: v => (comps v).map (List.cons true) ++ (comps v).map (List.cons false)
  | .t :: v => (comps v).map (List.cons true)
  | .f :: v => (comps v).map (List.cons false)

/-- hand-rolled `all` (the library's lemmas about `List.all` carry propext) -/
def allB : List (List Bool) → (List Bool → Bool) → Bool
  | [], _ => true
  | c :: cs, p => p c && allB cs p

theorem and_true_iff2 : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by decide
theorem and_mk : ∀ a b : Bool, a = true → b = true → (a && b) = true := by decide

theorem allB_append : ∀ (xs ys : List (List Bool)) (p : List Bool → Bool),
    allB (xs ++ ys) p = true → allB xs p = true ∧ allB ys p = true := by
  intro xs; induction xs with
  | nil => intro ys p h; exact ⟨rfl, h⟩
  | cons x xs ih =>
    intro ys p h
    have h2 := and_true_iff2 _ _ h
    have h3 := ih ys p h2.2
    exact ⟨and_mk _ _ h2.1 h3.1, h3.2⟩

theorem allB_append_mk : ∀ (xs ys : List (List Bool)) (p : List Bool → Bool),
    allB xs p = true → allB ys p = true → allB (xs ++ ys) p = true := by
  intro xs; induction xs with
  | nil => intro ys p _ h; exact h
  | cons x xs ih =>
    intro ys p hx hy
    have h2 := and_true_iff2 _ _ hx
    exact and_mk _ _ h2.1 (ih ys p h2.2 hy)

theorem allB_map : ∀ (xs : List (List Bool)) (b : Bool) (p : List Bool → Bool),
    allB (xs.map (List.cons b)) p = allB xs (fun c => p (b :: c)) := by
  intro xs; induction xs with
  | nil => intro _ _; rfl
  | cons x xs ih => intro b p; show (p (b :: x) && allB (xs.map (List.cons b)) p) = _; rw [ih]; rfl

/-- more determined ⇒ fewer completions: what holds on all completions of `v` holds on all of `w` -/
theorem comps_mono : ∀ v w : PVal, pvLeq v w = true →
    ∀ p, allB (comps v) p = true → allB (comps w) p = true := by
  intro v
  induction v with
  | nil =>
    intro w h p hp
    cases w with
    | nil => exact hp
    | cons b w => exact nomatch h
  | cons a v ih =>
    intro w h p hp
    cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hl := (andEqTrue _ _).mp h
      cases a with
      | n =>
        have hs := allB_append _ _ p hp
        rw [allB_map, allB_map] at hs
        have hT := ih w hl.2 _ hs.1
        have hF := ih w hl.2 _ hs.2
        cases b with
        | n => exact allB_append_mk _ _ p (by rw [allB_map]; exact hT) (by rw [allB_map]; exact hF)
        | t => show allB ((comps w).map (List.cons true)) p = true; rw [allB_map]; exact hT
        | f => show allB ((comps w).map (List.cons false)) p = true; rw [allB_map]; exact hF
      | t =>
        cases b with
        | t =>
          show allB ((comps w).map (List.cons true)) p = true
          have hp' : allB ((comps v).map (List.cons true)) p = true := hp
          rw [allB_map] at hp' ⊢; exact ih w hl.2 _ hp'
        | n => exact nomatch hl.1
        | f => exact nomatch hl.1
      | f =>
        cases b with
        | f =>
          show allB ((comps w).map (List.cons false)) p = true
          have hp' : allB ((comps v).map (List.cons false)) p = true := hp
          rw [allB_map] at hp' ⊢; exact ih w hl.2 _ hp'
        | n => exact nomatch hl.1
        | t => exact nomatch hl.1

/-- one completion always exists: the first -/
def firstC : PVal → List Bool
  | [] => []
  | .n :: v => true :: firstC v
  | .t :: v => true :: firstC v
  | .f :: v => false :: firstC v

theorem allB_first : ∀ (v : PVal) (p : List Bool → Bool), allB (comps v) p = true → p (firstC v) = true := by
  intro v
  induction v with
  | nil => intro p h; exact (and_true_iff2 _ _ h).1
  | cons a v ih =>
    intro p h
    cases a with
    | n =>
      have hs := (allB_append _ _ p h).1
      rw [allB_map] at hs; exact ih (fun c => p (true :: c)) hs
    | t =>
      have hs : allB ((comps v).map (List.cons true)) p = true := h
      rw [allB_map] at hs; exact ih (fun c => p (true :: c)) hs
    | f =>
      have hs : allB ((comps v).map (List.cons false)) p = true := h
      rw [allB_map] at hs; exact ih (fun c => p (false :: c)) hs

/-! ## The stable step -/

/-- the highest atom a formula mentions -/
def maxAtom : Fm → Nat
  | .atom n    => n
  | .top       => 0
  | .bot       => 0
  | .neg φ     => maxAtom φ
  | .conj φ ψ  => Nat.max (maxAtom φ) (maxAtom ψ)
  | .disj φ ψ  => Nat.max (maxAtom φ) (maxAtom ψ)
  | .imp φ ψ   => Nat.max (maxAtom φ) (maxAtom ψ)
  | .xor φ ψ   => Nat.max (maxAtom φ) (maxAtom ψ)
  | .xnor φ ψ  => Nat.max (maxAtom φ) (maxAtom ψ)

/-- extend a phase list with undetermined atoms: a FOREIGN atom (beyond the system) is never determined here;
the stable test reads it classically, like an own undetermined sentence -/
def pad (v : PVal) (k : Nat) : PVal := v ++ List.replicate (k - v.length) Ph.n

/-- a completion read as a classical valuation (off the end: never reached, `pad` covers every atom) -/
def bget : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: c, n + 1 => bget c n

/-- THE STEP — classics first, in one place (curator 2026-11-22): t (f) if the definition is classically true
(false) under EVERY classical value of every undetermined atom it mentions, own or foreign (one value per atom:
the stable test, `ZRead.clEval`); otherwise still n. ZTL's tables are not used here: they give the VERDICT when
classics gives no answer, not the grounding. -/
def evalS (v : PVal) (φ : Fm) : Ph :=
  if allB (comps (pad v (maxAtom φ + 1))) (fun c => clEval (bget c) φ) = true then .t
  else if allB (comps (pad v (maxAtom φ + 1))) (fun c => !clEval (bget c) φ) = true then .f
  else .n

theorem pvLeq_len : ∀ v w : PVal, pvLeq v w = true → v.length = w.length := by
  intro v
  induction v with
  | nil => intro w h; cases w with
    | nil => rfl
    | cons b w => exact nomatch h
  | cons a v ih => intro w h; cases w with
    | nil => exact nomatch h
    | cons b w => exact congrArg Nat.succ (ih w ((andEqTrue _ _).mp h).2)

theorem pvLeq_refl : ∀ r : PVal, pvLeq r r = true := by
  intro r; induction r with
  | nil => rfl
  | cons a r ih => exact (andEqTrue _ _).mpr ⟨phLeq_refl a, ih⟩

theorem pvLeq_append : ∀ (v w r : PVal), pvLeq v w = true → pvLeq (v ++ r) (w ++ r) = true := by
  intro v
  induction v with
  | nil => intro w r h; cases w with
    | nil => exact pvLeq_refl r
    | cons b w => exact nomatch h
  | cons a v ih => intro w r h; cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hp := (andEqTrue _ _).mp h
      exact (andEqTrue _ _).mpr ⟨hp.1, ih w r hp.2⟩

theorem pad_mono {v w : PVal} (h : pvLeq v w = true) (k : Nat) : pvLeq (pad v k) (pad w k) = true := by
  unfold pad; rw [pvLeq_len v w h]; exact pvLeq_append v w _ h

theorem not_both (b : Bool) (h1 : b = true) (h2 : (!b) = true) : False := by
  revert h1 h2; cases b <;> decide

theorem evalS_mono {v w : PVal} (h : pvLeq v w = true) (φ : Fm) :
    phLeq (evalS v φ) (evalS w φ) = true := by
  have hp := pad_mono h (maxAtom φ + 1)
  unfold evalS
  by_cases hT : allB (comps (pad v (maxAtom φ + 1))) (fun c => clEval (bget c) φ) = true
  · rw [if_pos hT, if_pos (comps_mono _ _ hp _ hT)]; rfl
  · rw [if_neg hT]
    by_cases hF : allB (comps (pad v (maxAtom φ + 1))) (fun c => !clEval (bget c) φ) = true
    · rw [if_pos hF]
      have hFw := comps_mono _ _ hp _ hF
      have hTw : ¬ allB (comps (pad w (maxAtom φ + 1))) (fun c => clEval (bget c) φ) = true := fun hTw =>
        not_both _ (allB_first _ _ hTw) (allB_first _ _ hFw)
      rw [if_neg hTw, if_pos hFw]; rfl
    · rw [if_neg hF]; exact leqN _

/-- The stable jump: re-evaluate every definition. -/
def jumpS (d : Sys) (v : PVal) : PVal := d.map (fun φ => evalS v φ)

theorem jumpS_mono (d : Sys) {v w : PVal} (h : pvLeq v w = true) :
    pvLeq (jumpS d v) (jumpS d w) = true := by
  induction d with
  | nil => rfl
  | cons φ d ih => exact (andEqTrue _ _).mpr ⟨evalS_mono h φ, ih⟩

/-! ## The ascending iteration from ⊥ -/

def bot (n : Nat) : PVal := List.replicate n Ph.n

def iter (d : Sys) : Nat → PVal
  | 0 => bot d.length
  | k + 1 => jumpS d (iter d k)

theorem replicate_leq : ∀ w : PVal, pvLeq (List.replicate w.length Ph.n) w = true := by
  intro w
  induction w with
  | nil => rfl
  | cons b w ih => exact (andEqTrue _ _).mpr ⟨leqN b, ih⟩

-- Core's List.length_map/length_replicate carry propext (simp-proved);
-- hand-rolled replacements keep the ledger empty.
theorem jumpS_length (d : Sys) (v : PVal) :
    (jumpS d v).length = d.length := by
  induction d with
  | nil => rfl
  | cons φ d ih => exact congrArg Nat.succ ih

theorem bot_leq {w : PVal} {n : Nat} (hw : w.length = n) :
    pvLeq (bot n) w = true := by
  have h := replicate_leq w
  rw [hw] at h
  exact h

theorem iter_length (d : Sys) : ∀ k, (iter d k).length = d.length := by
  intro k
  cases k with
  | zero =>
    show (List.replicate d.length Ph.n).length = d.length
    induction d.length with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  | succ k => exact jumpS_length d _

/-- The iteration is an ascending chain. -/
theorem chain (d : Sys) : ∀ k, pvLeq (iter d k) (iter d (k + 1)) = true := by
  intro k
  induction k with
  | zero => exact bot_leq (iter_length d 1)
  | succ k ih => exact jumpS_mono d ih

/-! ## The information measure and stabilization -/

/-- How many coordinates have earned a classical value. -/
def info : PVal → Nat
  | [] => 0
  | a :: v => (if a = Ph.n then 0 else 1) + info v

theorem info_le_length : ∀ v : PVal, info v ≤ v.length := by
  intro v
  induction v with
  | nil => exact Nat.le_refl 0
  | cons a v ih =>
    by_cases h : a = Ph.n
    · rw [show info (a :: v) = 0 + info v from by rw [info, if_pos h]]
      rw [Nat.zero_add]
      exact Nat.le_trans ih (Nat.le_succ _)
    · rw [show info (a :: v) = 1 + info v from by rw [info, if_neg h]]
      rw [Nat.add_comm]
      exact Nat.succ_le_succ ih

theorem info_mono : ∀ v w : PVal, pvLeq v w = true → info v ≤ info w := by
  intro v
  induction v with
  | nil =>
    intro w h
    cases w with
    | nil => exact Nat.le_refl 0
    | cons b w => exact nomatch h
  | cons a v ih =>
    intro w h
    cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hp := (andEqTrue _ _).mp h
      have ihw := ih w hp.2
      by_cases ha : a = Ph.n
      · rw [show info (a :: v) = 0 + info v from by rw [info, if_pos ha],
            Nat.zero_add]
        exact Nat.le_trans ihw (Nat.le_add_left _ _)
      · have hb : b = a := leq_nn a b hp.1 ha
        have hbz : ¬(b = Ph.n) := fun hz => ha (hb ▸ hz : a = Ph.n)
        rw [show info (a :: v) = 1 + info v from by rw [info, if_neg ha],
            show info (b :: w) = 1 + info w from by rw [info, if_neg hbz]]
        exact Nat.add_le_add_left ihw 1

theorem info_strict : ∀ v w : PVal, pvLeq v w = true → ¬(v = w) →
    info v < info w := by
  intro v
  induction v with
  | nil =>
    intro w h hne
    cases w with
    | nil => exact absurd rfl hne
    | cons b w => exact nomatch h
  | cons a v ih =>
    intro w h hne
    cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hp := (andEqTrue _ _).mp h
      by_cases hab : a = b
      · have hvw : ¬(v = w) := fun ht => hne (hab ▸ ht ▸ rfl)
        have hlt := ih w hp.2 hvw
        subst hab
        by_cases ha : a = Ph.n
        · rw [show info (a :: v) = 0 + info v from by rw [info, if_pos ha],
              show info (a :: w) = 0 + info w from by rw [info, if_pos ha],
              Nat.zero_add, Nat.zero_add]
          exact hlt
        · rw [show info (a :: v) = 1 + info v from by rw [info, if_neg ha],
              show info (a :: w) = 1 + info w from by rw [info, if_neg ha]]
          exact Nat.add_lt_add_left hlt 1
      · have ⟨haz, hbz⟩ := leq_ne_n a b hp.1 hab
        rw [show info (a :: v) = 0 + info v from by rw [info, if_pos haz],
            show info (b :: w) = 1 + info w from by rw [info, if_neg hbz],
            Nat.zero_add, Nat.add_comm]
        exact Nat.lt_succ_of_le (info_mono v w hp.2)

/-- One fixed step stays fixed. -/
theorem persist (d : Sys) {m : Nat} (h : iter d m = iter d (m + 1)) :
    iter d (m + 1) = iter d (m + 2) := congrArg (jumpS d) h

/-- Either the iteration has stabilized at m, or it has earned ≥ m
classical coordinates. -/
theorem fix_or_grow (d : Sys) : ∀ m : Nat,
    iter d m = iter d (m + 1) ∨ m ≤ info (iter d m) := by
  intro m
  induction m with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ m ih =>
    cases hb : pvEq (iter d m) (iter d (m + 1)) with
    | true => exact Or.inl (persist d ((pvEq_iff _ _).mp hb))
    | false =>
      have hne : ¬(iter d m = iter d (m + 1)) := fun he => by
        rw [(pvEq_iff _ _).mpr he] at hb
        exact nomatch hb
      cases ih with
      | inl hfix => exact absurd hfix hne
      | inr hgrow =>
        exact Or.inr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hgrow
          (info_strict _ _ (chain d m) hne)))

/-- THE LEAST FIXED POINT: the iteration stabilizes within n+1 steps. -/
def lfp (d : Sys) : PVal := iter d (d.length + 1)

/-- Knaster–Tarski, existence: lfp is a fixed point of the stable jump. -/
theorem kt_fixed (d : Sys) : jumpS d (lfp d) = lfp d := by
  cases fix_or_grow d (d.length + 1) with
  | inl h => exact h.symm
  | inr h =>
    exact absurd (Nat.le_trans h (Nat.le_trans
      (info_le_length _) (Nat.le_of_eq (iter_length d _))))
      (Nat.not_succ_le_self d.length)

/-- Knaster–Tarski, minimality: lfp lies below every fixed point. -/
theorem kt_least (d : Sys) (w : PVal) (hw : w.length = d.length)
    (hfix : jumpS d w = w) : pvLeq (lfp d) w = true := by
  have key : ∀ k, pvLeq (iter d k) w = true := by
    intro k
    induction k with
    | zero => exact bot_leq hw
    | succ k ih =>
      have h := jumpS_mono d ih
      rw [hfix] at h
      exact h
  exact key (d.length + 1)

/-- Quarantine is well-defined: a name grounded in the least fixed point carries the SAME classical
value in every fixed point. -/
theorem grounded_absolute (d : Sys) (w : PVal) (hw : w.length = d.length)
    (hfix : jumpS d w = w) (n : Nat) (hg : ¬(getP (lfp d) n = Ph.n)) :
    getP w n = getP (lfp d) n :=
  leq_nn _ _ (getP_mono _ _ (kt_least d w hw hfix) n) hg


/-! ## The cases, computed by the kernel -/

/-- The liar L ≡ ¬L: never determined — quarantine. -/
theorem liar_lfp : lfp [.neg (.atom 0)] = [.n] := rfl
/-- The truth-teller τ ≡ τ: never determined (two classical solutions; a blank for a decree). -/
theorem truthteller_lfp : lfp [.atom 0] = [.n] := rfl
/-- Curry with ⊥ ≡ s ∧ ¬s (γ = 0, ⊥ = 1, s = 2): ⊥ IS determined, F, under every value of s — the hole the
lazy register left (it called γ's refusal "conditional") is closed: γ ≡ γ → F is the liar in a costume. -/
theorem curry_lfp : lfp [.imp (.atom 0) (.atom 1), .conj (.atom 2) (.neg (.atom 2)), .atom 2] = [.n, .f, .n] := rfl
/-- A foreign input (atom 5, outside the system): S ≡ ¬J is classically T or F as J is — classics gives no
answer, so S is NOT grounded (it waits on J); the verdict on it is ZTL's, ¬Z = F (the judge: F, OPEN). -/
theorem foreign_input_lfp : lfp [.neg (.atom 5)] = [.n] := rfl
/-- …while a foreign input that cannot matter is grounded: S ≡ J ∨ ¬J is classically T for either J. -/
theorem foreign_irrelevant_lfp : lfp [.disj (.atom 5) (.neg (.atom 5))] = [.t] := rfl
/-- The strong liar σ ≡ ¬σ ∧ σ: F under every value of σ — determined by its form. -/
theorem strong_liar_lfp : lfp [.conj (.neg (.atom 0)) (.atom 0)] = [.f] := rfl

#print axioms comps_mono
#print axioms evalS_mono
#print axioms jumpS_mono
#print axioms kt_fixed
#print axioms kt_least
#print axioms grounded_absolute
#print axioms liar_lfp
#print axioms truthteller_lfp
#print axioms curry_lfp
#print axioms foreign_input_lfp
#print axioms foreign_irrelevant_lfp
#print axioms strong_liar_lfp

end V
