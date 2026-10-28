import ZDirty
/-! # ZGames — two adversaries, one principle (2026-10-28). Zero axioms.
A dirty parameter belongs to an adversary who sets every read of it so as to make the verdict false.
A STRATEGY assigns a classical value to every read; reads are addressed by their path in the formula
tree (left child = 0, right child = 1), so different occurrences are different reads.

  * Scope = the whole formula: one strategy for all reads, and the formula's final classical value
    must survive every strategy.                       → strong Kleene logic   (`formula_scope_is_kleene`)
  * Scope = each check: every connective is a separate check; the adversary sets the reads of THAT
    check's dirty atoms to falsify it, and the check's result is recorded and passed on as a clean
    fact to the next check.                            → ZTL                   (`check_scope_is_ztl`)
-/
namespace V

/-- classical value of φ when the adversary's strategy σ answers every dirty read -/
def play (v : Nat → V) : (List Bool → Bool) → Fm → Bool
  | σ, .atom n    => if v n = Z then σ [] else v n == T
  | _, .top       => true
  | _, .bot       => false
  | σ, .neg φ     => !play v (fun p => σ (false :: p)) φ
  | σ, .conj φ ψ  => play v (fun p => σ (false :: p)) φ && play v (fun p => σ (true :: p)) ψ
  | σ, .disj φ ψ  => play v (fun p => σ (false :: p)) φ || play v (fun p => σ (true :: p)) ψ
  | σ, .imp φ ψ   => !play v (fun p => σ (false :: p)) φ || play v (fun p => σ (true :: p)) ψ
  | σ, .xor φ ψ   => play v (fun p => σ (false :: p)) φ != play v (fun p => σ (true :: p)) ψ
  | σ, .xnor φ ψ  => play v (fun p => σ (false :: p)) φ == play v (fun p => σ (true :: p)) ψ

/-- the formula survives the whole-formula adversary -/
def SafeFormula (v : Nat → V) (φ : Fm) : Prop := ∀ σ, play v σ φ = true

/-- some strategy drives φ to the classical value b -/
def AdvReach (v : Nat → V) (φ : Fm) (b : Bool) : Prop := ∃ σ, play v σ φ = b

/-- glue two strategies for the two subtrees -/
def glue (σ₀ σ₁ : List Bool → Bool) : List Bool → Bool
  | false :: p => σ₀ p
  | true :: p  => σ₁ p
  | []         => σ₀ []

theorem glue0 (σ₀ σ₁ : List Bool → Bool) : (fun p => glue σ₀ σ₁ (false :: p)) = fun p => σ₀ p := rfl
theorem glue1 (σ₀ σ₁ : List Bool → Bool) : (fun p => glue σ₀ σ₁ (true :: p)) = fun p => σ₁ p := rfl

-- one step per connective: soundness (a play's value is reachable) and completeness (every reachable value is played)
theorem negS : ∀ p0 p1 a : Bool, ok a (p0, p1) = true → ok (!a) (p1, p0) = true := by decide
theorem negC : ∀ p0 p1 b : Bool, ok b (p1, p0) = true → ok (!b) (p0, p1) = true := by decide
theorem conjS : ∀ p0 p1 q0 q1 a c : Bool, ok a (p0, p1) = true → ok c (q0, q1) = true →
    ok ((fun a b => a && b) a c) (comb (fun a b => a && b) (p0, p1) (q0, q1)) = true := by decide
theorem conjC : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a && b) (p0, p1) (q0, q1)) = true →
    ((ok true (p0, p1) && ok true (q0, q1) && ((fun a b => a && b) true true == b)) ||
     (ok true (p0, p1) && ok false (q0, q1) && ((fun a b => a && b) true false == b)) ||
     (ok false (p0, p1) && ok true (q0, q1) && ((fun a b => a && b) false true == b)) ||
     (ok false (p0, p1) && ok false (q0, q1) && ((fun a b => a && b) false false == b))) = true := by decide
theorem disjS : ∀ p0 p1 q0 q1 a c : Bool, ok a (p0, p1) = true → ok c (q0, q1) = true →
    ok ((fun a b => a || b) a c) (comb (fun a b => a || b) (p0, p1) (q0, q1)) = true := by decide
theorem disjC : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a || b) (p0, p1) (q0, q1)) = true →
    ((ok true (p0, p1) && ok true (q0, q1) && ((fun a b => a || b) true true == b)) ||
     (ok true (p0, p1) && ok false (q0, q1) && ((fun a b => a || b) true false == b)) ||
     (ok false (p0, p1) && ok true (q0, q1) && ((fun a b => a || b) false true == b)) ||
     (ok false (p0, p1) && ok false (q0, q1) && ((fun a b => a || b) false false == b))) = true := by decide
theorem impS : ∀ p0 p1 q0 q1 a c : Bool, ok a (p0, p1) = true → ok c (q0, q1) = true →
    ok ((fun a b => !a || b) a c) (comb (fun a b => !a || b) (p0, p1) (q0, q1)) = true := by decide
theorem impC : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => !a || b) (p0, p1) (q0, q1)) = true →
    ((ok true (p0, p1) && ok true (q0, q1) && ((fun a b => !a || b) true true == b)) ||
     (ok true (p0, p1) && ok false (q0, q1) && ((fun a b => !a || b) true false == b)) ||
     (ok false (p0, p1) && ok true (q0, q1) && ((fun a b => !a || b) false true == b)) ||
     (ok false (p0, p1) && ok false (q0, q1) && ((fun a b => !a || b) false false == b))) = true := by decide
theorem xorS : ∀ p0 p1 q0 q1 a c : Bool, ok a (p0, p1) = true → ok c (q0, q1) = true →
    ok ((fun a b => a != b) a c) (comb (fun a b => a != b) (p0, p1) (q0, q1)) = true := by decide
theorem xorC : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a != b) (p0, p1) (q0, q1)) = true →
    ((ok true (p0, p1) && ok true (q0, q1) && ((fun a b => a != b) true true == b)) ||
     (ok true (p0, p1) && ok false (q0, q1) && ((fun a b => a != b) true false == b)) ||
     (ok false (p0, p1) && ok true (q0, q1) && ((fun a b => a != b) false true == b)) ||
     (ok false (p0, p1) && ok false (q0, q1) && ((fun a b => a != b) false false == b))) = true := by decide
theorem xnorS : ∀ p0 p1 q0 q1 a c : Bool, ok a (p0, p1) = true → ok c (q0, q1) = true →
    ok ((fun a b => a == b) a c) (comb (fun a b => a == b) (p0, p1) (q0, q1)) = true := by decide
theorem xnorC : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a == b) (p0, p1) (q0, q1)) = true →
    ((ok true (p0, p1) && ok true (q0, q1) && ((fun a b => a == b) true true == b)) ||
     (ok true (p0, p1) && ok false (q0, q1) && ((fun a b => a == b) true false == b)) ||
     (ok false (p0, p1) && ok true (q0, q1) && ((fun a b => a == b) false true == b)) ||
     (ok false (p0, p1) && ok false (q0, q1) && ((fun a b => a == b) false false == b))) = true := by decide

theorem atomS (x : V) (σ : List Bool → Bool) :
    ok (if x = Z then σ [] else x == T) ((subs x).contains true, (subs x).contains false) = true := by
  cases x <;> cases h : σ [] <;> first | rfl | (simp only [ok]; decide)

/-- Soundness: whatever the adversary does, the value it gets is one the dirty reading allows. -/
theorem play_sound (v : Nat → V) : ∀ (φ : Fm) (σ : List Bool → Bool), ok (play v σ φ) (rd v φ) = true
  | .atom n, σ => atomS (v n) σ
  | .top, _ => rfl
  | .bot, _ => rfl
  | .neg φ, σ => by
      have h := play_sound v φ (fun p => σ (false :: p))
      revert h; show _ → ok (!play v (fun p => σ (false :: p)) φ) ((rd v φ).2, (rd v φ).1) = true
      cases rd v φ with | mk p0 p1 => exact negS p0 p1 _
  | .conj φ ψ, σ => by
      have h1 := play_sound v φ (fun p => σ (false :: p))
      have h2 := play_sound v ψ (fun p => σ (true :: p))
      show ok ((fun a b => a && b) (play v (fun p => σ (false :: p)) φ) (play v (fun p => σ (true :: p)) ψ))
          (comb (fun a b => a && b) (rd v φ) (rd v ψ)) = true
      revert h1 h2; cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact conjS p0 p1 q0 q1 _ _
  | .disj φ ψ, σ => by
      have h1 := play_sound v φ (fun p => σ (false :: p))
      have h2 := play_sound v ψ (fun p => σ (true :: p))
      show ok ((fun a b => a || b) (play v (fun p => σ (false :: p)) φ) (play v (fun p => σ (true :: p)) ψ))
          (comb (fun a b => a || b) (rd v φ) (rd v ψ)) = true
      revert h1 h2; cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact disjS p0 p1 q0 q1 _ _
  | .imp φ ψ, σ => by
      have h1 := play_sound v φ (fun p => σ (false :: p))
      have h2 := play_sound v ψ (fun p => σ (true :: p))
      show ok ((fun a b => !a || b) (play v (fun p => σ (false :: p)) φ) (play v (fun p => σ (true :: p)) ψ))
          (comb (fun a b => !a || b) (rd v φ) (rd v ψ)) = true
      revert h1 h2; cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact impS p0 p1 q0 q1 _ _
  | .xor φ ψ, σ => by
      have h1 := play_sound v φ (fun p => σ (false :: p))
      have h2 := play_sound v ψ (fun p => σ (true :: p))
      show ok ((fun a b => a != b) (play v (fun p => σ (false :: p)) φ) (play v (fun p => σ (true :: p)) ψ))
          (comb (fun a b => a != b) (rd v φ) (rd v ψ)) = true
      revert h1 h2; cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact xorS p0 p1 q0 q1 _ _
  | .xnor φ ψ, σ => by
      have h1 := play_sound v φ (fun p => σ (false :: p))
      have h2 := play_sound v ψ (fun p => σ (true :: p))
      show ok ((fun a b => a == b) (play v (fun p => σ (false :: p)) φ) (play v (fun p => σ (true :: p)) ψ))
          (comb (fun a b => a == b) (rd v φ) (rd v ψ)) = true
      revert h1 h2; cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact xnorS p0 p1 q0 q1 _ _

theorem negE : ∀ p0 p1 b : Bool, ok b (p1, p0) = true → ok (!b) (p0, p1) = true := by decide
theorem conjE : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a && b) (p0, p1) (q0, q1)) = true →
    ∃ a c : Bool, ok a (p0, p1) = true ∧ ok c (q0, q1) = true ∧ (fun a b => a && b) a c = b := by decide
theorem disjE : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a || b) (p0, p1) (q0, q1)) = true →
    ∃ a c : Bool, ok a (p0, p1) = true ∧ ok c (q0, q1) = true ∧ (fun a b => a || b) a c = b := by decide
theorem impE : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => !a || b) (p0, p1) (q0, q1)) = true →
    ∃ a c : Bool, ok a (p0, p1) = true ∧ ok c (q0, q1) = true ∧ (fun a b => !a || b) a c = b := by decide
theorem xorE : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a != b) (p0, p1) (q0, q1)) = true →
    ∃ a c : Bool, ok a (p0, p1) = true ∧ ok c (q0, q1) = true ∧ (fun a b => a != b) a c = b := by decide
theorem xnorE : ∀ p0 p1 q0 q1 b : Bool, ok b (comb (fun a b => a == b) (p0, p1) (q0, q1)) = true →
    ∃ a c : Bool, ok a (p0, p1) = true ∧ ok c (q0, q1) = true ∧ (fun a b => a == b) a c = b := by decide

theorem atomE (x : V) (b : Bool) (h : ok b ((subs x).contains true, (subs x).contains false) = true) :
    (if x = Z then b else x == T) = b := by
  revert h; cases x <;> cases b <;> decide

/-- Completeness: every value the dirty reading allows, some strategy of the adversary produces. -/
theorem play_complete (v : Nat → V) : ∀ (φ : Fm) (b : Bool), ok b (rd v φ) = true → ∃ σ, play v σ φ = b
  | .atom n, b, h => ⟨fun _ => b, atomE (v n) b h⟩
  | .top, b, h => by
      cases b with
      | true => exact ⟨fun _ => true, rfl⟩
      | false => exact nomatch h
  | .bot, b, h => by
      cases b with
      | false => exact ⟨fun _ => false, rfl⟩
      | true => exact nomatch h
  | .neg φ, b, h => by
      have h' : ok (!b) (rd v φ) = true := by
        revert h; show ok b ((rd v φ).2, (rd v φ).1) = true → _
        cases rd v φ with | mk p0 p1 => exact negE p0 p1 b
      obtain ⟨σ, hσ⟩ := play_complete v φ (!b) h'
      exact ⟨glue σ σ, by show (!play v (fun p => σ p) φ) = b; rw [show (fun p => σ p) = σ from rfl, hσ]; cases b <;> rfl⟩
  | .conj φ ψ, b, h => by
      have h' : ∃ a c : Bool, ok a (rd v φ) = true ∧ ok c (rd v ψ) = true ∧ (fun a b => a && b) a c = b := by
        revert h; show ok b (comb (fun a b => a && b) (rd v φ) (rd v ψ)) = true → _
        cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact conjE p0 p1 q0 q1 b
      obtain ⟨a, c, ha, hc, hg⟩ := h'
      obtain ⟨σa, hσa⟩ := play_complete v φ a ha
      obtain ⟨σc, hσc⟩ := play_complete v ψ c hc
      exact ⟨glue σa σc, by
        show (fun a b => a && b) (play v (fun p => σa p) φ) (play v (fun p => σc p) ψ) = b
        rw [show (fun p => σa p) = σa from rfl, show (fun p => σc p) = σc from rfl, hσa, hσc]; exact hg⟩
  | .disj φ ψ, b, h => by
      have h' : ∃ a c : Bool, ok a (rd v φ) = true ∧ ok c (rd v ψ) = true ∧ (fun a b => a || b) a c = b := by
        revert h; show ok b (comb (fun a b => a || b) (rd v φ) (rd v ψ)) = true → _
        cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact disjE p0 p1 q0 q1 b
      obtain ⟨a, c, ha, hc, hg⟩ := h'
      obtain ⟨σa, hσa⟩ := play_complete v φ a ha
      obtain ⟨σc, hσc⟩ := play_complete v ψ c hc
      exact ⟨glue σa σc, by
        show (fun a b => a || b) (play v (fun p => σa p) φ) (play v (fun p => σc p) ψ) = b
        rw [show (fun p => σa p) = σa from rfl, show (fun p => σc p) = σc from rfl, hσa, hσc]; exact hg⟩
  | .imp φ ψ, b, h => by
      have h' : ∃ a c : Bool, ok a (rd v φ) = true ∧ ok c (rd v ψ) = true ∧ (fun a b => !a || b) a c = b := by
        revert h; show ok b (comb (fun a b => !a || b) (rd v φ) (rd v ψ)) = true → _
        cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact impE p0 p1 q0 q1 b
      obtain ⟨a, c, ha, hc, hg⟩ := h'
      obtain ⟨σa, hσa⟩ := play_complete v φ a ha
      obtain ⟨σc, hσc⟩ := play_complete v ψ c hc
      exact ⟨glue σa σc, by
        show (fun a b => !a || b) (play v (fun p => σa p) φ) (play v (fun p => σc p) ψ) = b
        rw [show (fun p => σa p) = σa from rfl, show (fun p => σc p) = σc from rfl, hσa, hσc]; exact hg⟩
  | .xor φ ψ, b, h => by
      have h' : ∃ a c : Bool, ok a (rd v φ) = true ∧ ok c (rd v ψ) = true ∧ (fun a b => a != b) a c = b := by
        revert h; show ok b (comb (fun a b => a != b) (rd v φ) (rd v ψ)) = true → _
        cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact xorE p0 p1 q0 q1 b
      obtain ⟨a, c, ha, hc, hg⟩ := h'
      obtain ⟨σa, hσa⟩ := play_complete v φ a ha
      obtain ⟨σc, hσc⟩ := play_complete v ψ c hc
      exact ⟨glue σa σc, by
        show (fun a b => a != b) (play v (fun p => σa p) φ) (play v (fun p => σc p) ψ) = b
        rw [show (fun p => σa p) = σa from rfl, show (fun p => σc p) = σc from rfl, hσa, hσc]; exact hg⟩
  | .xnor φ ψ, b, h => by
      have h' : ∃ a c : Bool, ok a (rd v φ) = true ∧ ok c (rd v ψ) = true ∧ (fun a b => a == b) a c = b := by
        revert h; show ok b (comb (fun a b => a == b) (rd v φ) (rd v ψ)) = true → _
        cases rd v φ with | mk p0 p1 => cases rd v ψ with | mk q0 q1 => exact xnorE p0 p1 q0 q1 b
      obtain ⟨a, c, ha, hc, hg⟩ := h'
      obtain ⟨σa, hσa⟩ := play_complete v φ a ha
      obtain ⟨σc, hσc⟩ := play_complete v ψ c hc
      exact ⟨glue σa σc, by
        show (fun a b => a == b) (play v (fun p => σa p) φ) (play v (fun p => σc p) ψ) = b
        rw [show (fun p => σa p) = σa from rfl, show (fun p => σc p) = σc from rfl, hσa, hσc]; exact hg⟩

theorem safe_iff_rd (v : Nat → V) (φ : Fm) : SafeFormula v φ ↔ (rd v φ).2 = false := by
  constructor
  · intro hs
    cases h : (rd v φ).2 with
    | false => rfl
    | true =>
        obtain ⟨σ, hσ⟩ := play_complete v φ false (by show (rd v φ).2 = true; exact h)
        have := hs σ; rw [hσ] at this; exact absurd this (by decide)
  · intro h σ
    have hs := play_sound v φ σ
    cases hb : play v σ φ with
    | true => rfl
    | false => rw [hb] at hs; have : (rd v φ).2 = true := hs; rw [h] at this; exact absurd this (by decide)

/-- **The whole-formula adversary is strong Kleene.** φ survives every strategy iff its strong Kleene value is T. -/
theorem formula_scope_is_kleene (v : Nat → V) (φ : Fm) : SafeFormula v φ ↔ kev v φ = T :=
  (safe_iff_rd v φ).trans (earned_iff_kleene_T v φ)


/-! ## The check-scope adversary
Each connective is a separate check. The adversary answers each dirty read of THAT check so as to falsify
it; an argument that is itself a check enters as its recorded result, a clean fact the adversary no longer
controls. `opts` lists what an argument can be at the moment of the check. -/
/-- what a check reads of an argument φ whose own recorded result is r: a dirty atom, anything the
adversary picks; a clean atom or a constant, its value; a compound, its recorded result -/
def optsOf (v : Nat → V) : Fm → Bool → List Bool
  | .atom n, _ => subs (v n)
  | .top, _ => [true]
  | .bot, _ => [false]
  | .neg _, r => [r]
  | .conj _ _, r => [r]
  | .disj _ _, r => [r]
  | .imp _ _, r => [r]
  | .xor _ _, r => [r]
  | .xnor _ _, r => [r]

/-- the recorded result of the check at the root of φ (for an atom: whether it is clean and true) -/
def record (v : Nat → V) : Fm → Bool
  | .atom n => v n == T
  | .top => true
  | .bot => false
  | .neg φ => (optsOf v φ (record v φ)).all (fun a => !a)
  | .conj φ ψ => (optsOf v φ (record v φ)).all (fun a => (optsOf v ψ (record v ψ)).all (fun c => a && c))
  | .disj φ ψ => (optsOf v φ (record v φ)).all (fun a => (optsOf v ψ (record v ψ)).all (fun c => a || c))
  | .imp φ ψ => (optsOf v φ (record v φ)).all (fun a => (optsOf v ψ (record v ψ)).all (fun c => !a || c))
  | .xor φ ψ => (optsOf v φ (record v φ)).all (fun a => (optsOf v ψ (record v ψ)).all (fun c => a != c))
  | .xnor φ ψ => (optsOf v φ (record v φ)).all (fun a => (optsOf v ψ (record v ψ)).all (fun c => a == c))

def opts (v : Nat → V) (φ : Fm) : List Bool := optsOf v φ (record v φ)


theorem rnot : ∀ x : V, (znot x == T) = (subs x).all (fun a => !a) := by decide
theorem rconj : ∀ x y : V, (zand x y == T) = (subs x).all (fun a => (subs y).all (fun c => (fun a c => a && c) a c)) := by decide
theorem rdisj : ∀ x y : V, (zor x y == T) = (subs x).all (fun a => (subs y).all (fun c => (fun a c => a || c) a c)) := by decide
theorem rimp : ∀ x y : V, (zimp x y == T) = (subs x).all (fun a => (subs y).all (fun c => (fun a c => !a || c) a c)) := by decide
theorem rxor : ∀ x y : V, (zxor x y == T) = (subs x).all (fun a => (subs y).all (fun c => (fun a c => a != c) a c)) := by decide
theorem rxnor : ∀ x y : V, (zxnor x y == T) = (subs x).all (fun a => (subs y).all (fun c => (fun a c => a == c) a c)) := by decide
theorem compound_classical (v : Nat → V) (φ : Fm) (h : ∀ n, φ ≠ .atom n) :
    evalF v φ = T ∨ evalF v φ = F := by
  rcases evalF_classical v φ with ⟨n, hn⟩ | h' | h'
  · exact absurd hn (h n)
  · exact Or.inl h'
  · exact Or.inr h'

theorem subs_of_classical (x : V) (h : x = T ∨ x = F) : [x == T] = subs x := by
  rcases h with h | h <;> subst h <;> rfl

/-- **The check-scope adversary is ZTL.** The recorded result of every check is its ZTL verdict, and what a
check reads of any argument is exactly the readings of that argument's ZTL value. -/
theorem check_scope_is_ztl (v : Nat → V) : ∀ φ : Fm, record v φ = (evalF v φ == T) ∧ opts v φ = subs (evalF v φ) := by
  intro φ
  induction φ with
  | atom n => exact ⟨rfl, rfl⟩
  | top => exact ⟨rfl, rfl⟩
  | bot => exact ⟨rfl, rfl⟩
  | neg φ ih =>
      have r : record v (.neg φ) = (evalF v (.neg φ) == T) := by
        show (opts v φ).all (fun a => !a) = (znot (evalF v φ) == T)
        rw [ih.2, rnot]
      refine ⟨r, ?_⟩
      show [record v (.neg φ)] = _
      rw [r]; exact subs_of_classical _ (compound_classical v (.neg φ) (fun n h => Fm.noConfusion h))
  | conj φ ψ ihφ ihψ =>
      have r : record v (.conj φ ψ) = (evalF v (.conj φ ψ) == T) := by
        show (opts v φ).all (fun a => (opts v ψ).all (fun c => (fun a c => a && c) a c)) = (zand (evalF v φ) (evalF v ψ) == T)
        rw [ihφ.2, ihψ.2, rconj]
      refine ⟨r, ?_⟩
      show [record v (.conj φ ψ)] = _
      rw [r]; exact subs_of_classical _ (compound_classical v (.conj φ ψ) (fun n h => Fm.noConfusion h))
  | disj φ ψ ihφ ihψ =>
      have r : record v (.disj φ ψ) = (evalF v (.disj φ ψ) == T) := by
        show (opts v φ).all (fun a => (opts v ψ).all (fun c => (fun a c => a || c) a c)) = (zor (evalF v φ) (evalF v ψ) == T)
        rw [ihφ.2, ihψ.2, rdisj]
      refine ⟨r, ?_⟩
      show [record v (.disj φ ψ)] = _
      rw [r]; exact subs_of_classical _ (compound_classical v (.disj φ ψ) (fun n h => Fm.noConfusion h))
  | imp φ ψ ihφ ihψ =>
      have r : record v (.imp φ ψ) = (evalF v (.imp φ ψ) == T) := by
        show (opts v φ).all (fun a => (opts v ψ).all (fun c => (fun a c => !a || c) a c)) = (zimp (evalF v φ) (evalF v ψ) == T)
        rw [ihφ.2, ihψ.2, rimp]
      refine ⟨r, ?_⟩
      show [record v (.imp φ ψ)] = _
      rw [r]; exact subs_of_classical _ (compound_classical v (.imp φ ψ) (fun n h => Fm.noConfusion h))
  | xor φ ψ ihφ ihψ =>
      have r : record v (.xor φ ψ) = (evalF v (.xor φ ψ) == T) := by
        show (opts v φ).all (fun a => (opts v ψ).all (fun c => (fun a c => a != c) a c)) = (zxor (evalF v φ) (evalF v ψ) == T)
        rw [ihφ.2, ihψ.2, rxor]
      refine ⟨r, ?_⟩
      show [record v (.xor φ ψ)] = _
      rw [r]; exact subs_of_classical _ (compound_classical v (.xor φ ψ) (fun n h => Fm.noConfusion h))
  | xnor φ ψ ihφ ihψ =>
      have r : record v (.xnor φ ψ) = (evalF v (.xnor φ ψ) == T) := by
        show (opts v φ).all (fun a => (opts v ψ).all (fun c => (fun a c => a == c) a c)) = (zxnor (evalF v φ) (evalF v ψ) == T)
        rw [ihφ.2, ihψ.2, rxnor]
      refine ⟨r, ?_⟩
      show [record v (.xnor φ ψ)] = _
      rw [r]; exact subs_of_classical _ (compound_classical v (.xnor φ ψ) (fun n h => Fm.noConfusion h))

/-- Same adversary, same reads, two scopes. What survives the whole-formula adversary survives every check;
the converse fails: ¬¬p with p dirty passes every check (the inner check fails and is recorded as failed,
the outer check reads that record) but not the whole-formula adversary, who reads p as false. -/
theorem formula_safe_implies_checks (v : Nat → V) (φ : Fm) (h : SafeFormula v φ) : evalF v φ = T :=
  never_stricter v φ ((safe_iff_rd v φ).mp h)

theorem scopes_differ : evalF (fun _ => Z) (.neg (.neg (.atom 0))) = T ∧
    ¬ SafeFormula (fun _ => Z) (.neg (.neg (.atom 0))) := by
  refine ⟨by decide, fun h => ?_⟩
  have := h (fun _ => false)
  exact absurd this (by decide)

end V

#print axioms V.check_scope_is_ztl
#print axioms V.formula_safe_implies_checks
#print axioms V.scopes_differ
#print axioms V.play_sound
#print axioms V.play_complete
#print axioms V.formula_scope_is_kleene
