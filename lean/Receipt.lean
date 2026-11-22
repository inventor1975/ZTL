import ZGround
import ZForced
import ContextClosure

/-!
# The receipt is complete: what it omits could not have mattered. Zero axioms.

`ztljudge` answers with a value AND a label — which dirty atoms are
still holding the answer up. The label is what makes a refusal ACCOUNTABLE: it
names the cause instead of merely withholding the verdict. Its docstring has
carried the honest qualifier since it was written — *a sound over-approximation
of the load-bearing atoms, measured, not assumed* — because 10,806 pending cells
of the depth-2 pool over two atoms is a census, and a census does not license a
general claim.

This file removes the qualifier on the sound half.

WHAT IS PROVED. For every formula of the whole language, every valuation, and
every atom the reader never verified: if the label leaves that atom out, then
changing it changes nothing.

    receipt_complete        :  v a = Z  →  labF v φ a = false
                                        →  foC (setA a x v) φ = foC v φ
    receipt_complete_greedy :  the same, for `evalF` — the register that
                               actually issues verdicts

Contrapositively — and this is the reading that matters — **an atom that could
change the answer is always on the receipt.** The judge never withholds a
verdict for a reason it failed to name.

THE SECOND THEOREM WAS PREDICTED TO BE FALSE, by me, in writing
(`lab/greedy/PREDICTIONS.md`, P1), on the ground that the greedy lift is
non-monotone and connective-local. The census refuted the prediction — zero
misses in 296,161 cells carrying a dirty atom — and the reason is
`greedy_agrees_when_decided` plus the shape of the greedy tables. Recorded here
rather than quietly dropped, because a prediction that was wrong is the only
kind worth keeping.

WHY THE HYPOTHESIS `v a = Z` IS NOT DECORATION. Without it the statement is
false, and cheaply: `p ∧ q` with `p = T`, `q = Z` labels `{q}`, yet flipping the
VERIFIED `p` to `F` moves the value from `Z` to `F`. A verified atom can be
load-bearing and is deliberately not tracked — the label answers "what is still
missing", not "what does this answer depend on".

WHAT IS NOT PROVED, and it is the other half of the same docstring: the label
also names INNOCENT atoms, and measurement says it does so more as formulas
deepen — 16% of pending cells at depth 2 over two atoms, 21% at depth 2 over
three, 35% at depth ≤ 6 over four (`lab/receipt/`). So this is a proof of
soundness, never of exactness, and the corpus should keep saying "a cheap
candidate list, not the exact answer".

MEASURED FIRST, in both directions. The bench that licensed this file audits
every cell, not only the pending ones — an earlier version skipped decided
cells and would have measured strictly less than the theorem it was meant to
support. Zero misses in 412,593 cells.

WHY IT WAS WORTH PROVING (the curator's question, 2026-08-19): can we prove
classical logic's ascent into metalevels is *erroneous*? No — Tarski's hierarchy
is forced by Tarski's own theorem, and there is no wrong step to expose. What
can be proved is the difference in the REMAINDER. A stratification removes the
paradoxical sentence without trace: it is not in the language, so nothing can be
asked about what was removed. Here the refusal stays an object of the calculus
and carries its cause — and the theorem below says the cause is never missing.
That is a statement about our own construction, not a verdict on theirs.
-/

namespace V

/-! ## The label, exactly as the judge computes it

Each combination takes the two branch VALUES and the two branch labels, and
answers which label survives. The rule is the one the forced outcome (`foC`, ZForced) already
follows for its value: a branch that decides the matter alone carries the whole
receipt, because the other branch is then irrelevant. Rows are enumerated over
`V × V` with no overlap — an overlapping wildcard row pulls `propext` in
through the compiled matcher (`ZTL.lean` measured that pitfall for `phAnd`). -/

def conjL : Ph → Ph → Bool → Bool → Bool
  | .t, .t, _,  _  => false
  | .t, .f, _,  lb => lb
  | .t, .n, la, lb => la || lb
  | .f, .t, la, _  => la
  | .f, .f, la, _  => la
  | .f, .n, la, _  => la
  | .n, .t, la, lb => la || lb
  | .n, .f, _,  lb => lb
  | .n, .n, la, lb => la || lb

def disjL : Ph → Ph → Bool → Bool → Bool
  | .t, .t, la, _  => la
  | .t, .f, la, _  => la
  | .t, .n, la, _  => la
  | .f, .t, _,  lb => lb
  | .f, .f, _,  _  => false
  | .f, .n, la, lb => la || lb
  | .n, .t, _,  lb => lb
  | .n, .f, la, lb => la || lb
  | .n, .n, la, lb => la || lb

/-- Implication is `phOr (phNot a) b` in the value register, so its receipt is
the disjunction's receipt read through the flipped antecedent. -/
def impL : Ph → Ph → Bool → Bool → Bool
  | .t, .t, _,  lb => lb
  | .t, .f, _,  _  => false
  | .t, .n, la, lb => la || lb
  | .f, .t, la, _  => la
  | .f, .f, la, _  => la
  | .f, .n, la, _  => la
  | .n, .t, _,  lb => lb
  | .n, .f, la, lb => la || lb
  | .n, .n, la, lb => la || lb

/-- Neither `xor` nor `xnor` can be decided by one side, so nothing is ever
dropped: either both branches are settled and the receipt is empty, or both
stay on it. -/
def xorL : Ph → Ph → Bool → Bool → Bool
  | .t, .t, _,  _  => false
  | .t, .f, _,  _  => false
  | .f, .t, _,  _  => false
  | .f, .f, _,  _  => false
  | .t, .n, la, lb => la || lb
  | .f, .n, la, lb => la || lb
  | .n, .t, la, lb => la || lb
  | .n, .f, la, lb => la || lb
  | .n, .n, la, lb => la || lb

def atomL (x : V) (n m : Nat) : Bool :=
  match x with
  | T => false
  | F => false
  | Z => decide (n = m)

/-- The judge's label, over the whole language. -/
def labF (v : Nat → V) : Fm → Nat → Bool
  | .atom n,   m => atomL (v n) n m
  | .top,      _ => false
  | .bot,      _ => false
  | .neg φ,    m => labF v φ m
  | .conj φ ψ, m => conjL (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m)
  | .disj φ ψ, m => disjL (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m)
  | .imp φ ψ,  m => impL  (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m)
  | .xor φ ψ,  m => xorL  (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m)
  | .xnor φ ψ, m => xorL  (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m)

/-! ## A decided matter has an empty receipt

Nothing is pending once the answer is in, and this is what lets the main
induction reach the branches it has no direct hypothesis about. -/

def decidedB : Ph → Bool
  | .t => true
  | .f => true
  | .n => false

theorem label_empty_of_decided (v : Nat → V) (m : Nat) :
    ∀ φ : Fm, decidedB (foC v φ) = true → labF v φ m = false := by
  intro φ
  induction φ with
  | atom n =>
      show decidedB (phAtom (v n)) = true → atomL (v n) n m = false
      cases hv : v n <;> intro h <;> first
        | rfl
        | exact absurd h (by decide)
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ihφ =>
      show decidedB (phNot (foC v φ)) = true → labF v φ m = false
      cases hφ : foC v φ <;> intro h <;> first
        | exact ihφ (by rw [hφ]; rfl)
        | exact absurd h (by decide)
  | conj φ ψ ihφ ihψ =>
      show decidedB (phAnd (foC v φ) (foC v ψ)) = true →
           conjL (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m) = false
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rfl
        | exact absurd h (by decide)
        | exact ihφ (by rw [hφ]; rfl)
        | exact ihψ (by rw [hψ]; rfl)
  | disj φ ψ ihφ ihψ =>
      show decidedB (phOr (foC v φ) (foC v ψ)) = true →
           disjL (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m) = false
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rfl
        | exact absurd h (by decide)
        | exact ihφ (by rw [hφ]; rfl)
        | exact ihψ (by rw [hψ]; rfl)
  | imp φ ψ ihφ ihψ =>
      show decidedB (phImp (foC v φ) (foC v ψ)) = true →
           impL (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m) = false
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rfl
        | exact absurd h (by decide)
        | exact ihφ (by rw [hφ]; rfl)
        | exact ihψ (by rw [hψ]; rfl)
  | xor φ ψ ihφ ihψ =>
      show decidedB (phXor (foC v φ) (foC v ψ)) = true →
           xorL (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m) = false
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rfl
        | exact absurd h (by decide)
        | exact ihφ (by rw [hφ]; rfl)
        | exact ihψ (by rw [hψ]; rfl)
  | xnor φ ψ ihφ ihψ =>
      show decidedB (phXnor (foC v φ) (foC v ψ)) = true →
           xorL (foC v φ) (foC v ψ) (labF v φ m) (labF v ψ m) = false
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rfl
        | exact absurd h (by decide)
        | exact ihφ (by rw [hφ]; rfl)
        | exact ihψ (by rw [hψ]; rfl)


/-! ## The theorem: whatever the receipt omits could not have mattered -/

/-- If the label leaves out an atom the reader never verified, then setting
that atom to anything leaves the answer exactly where it was.

Read the other way round: **an atom that could change the answer is always on
the receipt.** A refusal in this calculus never withholds a verdict for a reason
it failed to name — which is the property a stratification cannot state at all,
its excluded sentence having no value to attribute anything to. -/
theorem receipt_complete (a : Nat) (x : V) (v : Nat → V) (hv : v a = Z) :
    ∀ φ : Fm, labF v φ a = false → foC (setA a x v) φ = foC v φ := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      show phAtom (setA a x v n) = phAtom (v n)
      cases hna : decide (n = a) with
      | false => exact congrArg phAtom (setA_other x v (of_decide_eq_false hna))
      | true =>
          have hn : n = a := of_decide_eq_true hna
          have hvn : v n = Z := by rw [hn]; exact hv
          have h2 : atomL (v n) n a = false := h
          rw [hvn] at h2
          have h3 : decide (n = a) = false := h2
          rw [hna] at h3
          exact Bool.noConfusion h3
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ihφ =>
      intro h
      show phNot (foC (setA a x v) φ) = phNot (foC v φ)
      rw [ihφ h]
  | conj φ ψ ihφ ihψ =>
      show conjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           phAnd (foC (setA a x v) φ) (foC (setA a x v) ψ)
             = phAnd (foC v φ) (foC v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl)), hφ, hψ]
        | rw [ihφ (orF h).1, ihψ (orF h).2, hφ, hψ]
        | (rw [ihφ h, hφ]; cases hy : foC (setA a x v) ψ <;> rfl)
        | (rw [ihψ h, hψ]; cases hy : foC (setA a x v) φ <;> rfl)
  | disj φ ψ ihφ ihψ =>
      show disjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           phOr (foC (setA a x v) φ) (foC (setA a x v) ψ)
             = phOr (foC v φ) (foC v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl)), hφ, hψ]
        | rw [ihφ (orF h).1, ihψ (orF h).2, hφ, hψ]
        | (rw [ihφ h, hφ]; cases hy : foC (setA a x v) ψ <;> rfl)
        | (rw [ihψ h, hψ]; cases hy : foC (setA a x v) φ <;> rfl)
  | imp φ ψ ihφ ihψ =>
      show impL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           phImp (foC (setA a x v) φ) (foC (setA a x v) ψ)
             = phImp (foC v φ) (foC v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl)), hφ, hψ]
        | rw [ihφ (orF h).1, ihψ (orF h).2, hφ, hψ]
        | (rw [ihφ h, hφ]; cases hy : foC (setA a x v) ψ <;> rfl)
        | (rw [ihψ h, hψ]; cases hy : foC (setA a x v) φ <;> rfl)
  | xor φ ψ ihφ ihψ =>
      show xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           phXor (foC (setA a x v) φ) (foC (setA a x v) ψ)
             = phXor (foC v φ) (foC v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl)), hφ, hψ]
        | rw [ihφ (orF h).1, ihψ (orF h).2, hφ, hψ]
        | (rw [ihφ h, hφ]; cases hy : foC (setA a x v) ψ <;> rfl)
        | (rw [ihψ h, hψ]; cases hy : foC (setA a x v) φ <;> rfl)
  | xnor φ ψ ihφ ihψ =>
      show xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           phXnor (foC (setA a x v) φ) (foC (setA a x v) ψ)
             = phXnor (foC v φ) (foC v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl)), hφ, hψ]
        | rw [ihφ (orF h).1, ihψ (orF h).2, hφ, hψ]
        | (rw [ihφ h, hφ]; cases hy : foC (setA a x v) ψ <;> rfl)
        | (rw [ihψ h, hψ]; cases hy : foC (setA a x v) φ <;> rfl)

/-! ## The register that issues verdicts

`receipt_complete` covers the FORCED outcome, but the judge prints the label beside
a GREEDY verdict, and a reader has every reason to take it as covering that. I
predicted it would not (`lab/greedy/PREDICTIONS.md`, P1): the greedy lift is
connective-local and non-monotone — `eager_and_not_monotone` and
`eager_not_not_monotone` are theorems of this corpus — so a branch the forced outcome calls
decisive, whose holes the label therefore drops, looked like the obvious place
for the receipt to leak.

The census refuted the prediction: zero misses in 296,161 cells carrying at
least one dirty atom. It holds because of a fact worth stating on its own —

    greedy_agrees_when_decided :  whenever the forced outcome commits,
                                  the GREEDY one agrees with it

— and because the greedy tables absorb exactly where the label drops a branch:
`F` on either side of `∧`, `T` on either side of `∨`, a false antecedent or a
true consequent of `→`. `xor` and `xnor` absorb nowhere, and there the label
drops nothing. The two facts line up, which is why the receipt survives the
crossing. -/

theorem greedy_agrees_when_decided (v : Nat → V) :
    ∀ φ : Fm, decidedB (foC v φ) = true → evalF v φ = phVal (foC v φ) := by
  intro φ
  induction φ with
  | atom n =>
      show decidedB (phAtom (v n)) = true → v n = phVal (phAtom (v n))
      cases v n <;> intro h <;> first | rfl | exact absurd h (by decide)
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ihφ =>
      show decidedB (phNot (foC v φ)) = true → znot (evalF v φ) = phVal (phNot (foC v φ))
      cases hφ : foC v φ <;> intro h <;> first
        | (rw [ihφ (by rw [hφ]; rfl), hφ]; rfl)
        | exact absurd h (by decide)
  | conj φ ψ ihφ ihψ =>
      show decidedB (phAnd (foC v φ) (foC v ψ)) = true →
           zand (evalF v φ) (evalF v ψ) = phVal (phAnd (foC v φ) (foC v ψ))
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | (rw [ihφ (by rw [hφ]; rfl), ihψ (by rw [hψ]; rfl), hφ, hψ]; rfl)
        | exact absurd h (by decide)
        | (rw [ihφ (by rw [hφ]; rfl), hφ]; cases hy : evalF v ψ <;> rfl)
        | (rw [ihψ (by rw [hψ]; rfl), hψ]; cases hy : evalF v φ <;> rfl)
  | disj φ ψ ihφ ihψ =>
      show decidedB (phOr (foC v φ) (foC v ψ)) = true →
           zor (evalF v φ) (evalF v ψ) = phVal (phOr (foC v φ) (foC v ψ))
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | (rw [ihφ (by rw [hφ]; rfl), ihψ (by rw [hψ]; rfl), hφ, hψ]; rfl)
        | exact absurd h (by decide)
        | (rw [ihφ (by rw [hφ]; rfl), hφ]; cases hy : evalF v ψ <;> rfl)
        | (rw [ihψ (by rw [hψ]; rfl), hψ]; cases hy : evalF v φ <;> rfl)
  | imp φ ψ ihφ ihψ =>
      show decidedB (phImp (foC v φ) (foC v ψ)) = true →
           zimp (evalF v φ) (evalF v ψ) = phVal (phImp (foC v φ) (foC v ψ))
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | (rw [ihφ (by rw [hφ]; rfl), ihψ (by rw [hψ]; rfl), hφ, hψ]; rfl)
        | exact absurd h (by decide)
        | (rw [ihφ (by rw [hφ]; rfl), hφ]; cases hy : evalF v ψ <;> rfl)
        | (rw [ihψ (by rw [hψ]; rfl), hψ]; cases hy : evalF v φ <;> rfl)
  | xor φ ψ ihφ ihψ =>
      show decidedB (phXor (foC v φ) (foC v ψ)) = true →
           zxor (evalF v φ) (evalF v ψ) = phVal (phXor (foC v φ) (foC v ψ))
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | (rw [ihφ (by rw [hφ]; rfl), ihψ (by rw [hψ]; rfl), hφ, hψ]; rfl)
        | exact absurd h (by decide)
        | (rw [ihφ (by rw [hφ]; rfl), hφ]; cases hy : evalF v ψ <;> rfl)
        | (rw [ihψ (by rw [hψ]; rfl), hψ]; cases hy : evalF v φ <;> rfl)
  | xnor φ ψ ihφ ihψ =>
      show decidedB (phXnor (foC v φ) (foC v ψ)) = true →
           zxnor (evalF v φ) (evalF v ψ) = phVal (phXnor (foC v φ) (foC v ψ))
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | (rw [ihφ (by rw [hφ]; rfl), ihψ (by rw [hψ]; rfl), hφ, hψ]; rfl)
        | exact absurd h (by decide)
        | (rw [ihφ (by rw [hφ]; rfl), hφ]; cases hy : evalF v ψ <;> rfl)
        | (rw [ihψ (by rw [hψ]; rfl), hψ]; cases hy : evalF v φ <;> rfl)

/-! ## The receipt crosses the register -/

/-- The same guarantee for the register that actually issues verdicts: an
dirty atom the label omits cannot move the greedy verdict either. -/
theorem receipt_complete_greedy (a : Nat) (x : V) (v : Nat → V) (hv : v a = Z) :
    ∀ φ : Fm, labF v φ a = false → evalF (setA a x v) φ = evalF v φ := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      show setA a x v n = v n
      cases hna : decide (n = a) with
      | false => exact setA_other x v (of_decide_eq_false hna)
      | true =>
          have hn : n = a := of_decide_eq_true hna
          have hvn : v n = Z := by rw [hn]; exact hv
          have h2 : atomL (v n) n a = false := h
          rw [hvn] at h2
          have h3 : decide (n = a) = false := h2
          rw [hna] at h3
          exact Bool.noConfusion h3
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ihφ =>
      intro h
      show znot (evalF (setA a x v) φ) = znot (evalF v φ)
      rw [ihφ h]
  | conj φ ψ ihφ ihψ =>
      show conjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           zand (evalF (setA a x v) φ) (evalF (setA a x v) ψ)
             = zand (evalF v φ) (evalF v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl))]
        | rw [ihφ (orF h).1, ihψ (orF h).2]
        | (rw [ihφ h, greedy_agrees_when_decided v φ (by rw [hφ]; rfl), hφ];
           cases hy : evalF (setA a x v) ψ <;> cases hz : evalF v ψ <;> rfl)
        | (rw [ihψ h, greedy_agrees_when_decided v ψ (by rw [hψ]; rfl), hψ];
           cases hy : evalF (setA a x v) φ <;> cases hz : evalF v φ <;> rfl)
  | disj φ ψ ihφ ihψ =>
      show disjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           zor (evalF (setA a x v) φ) (evalF (setA a x v) ψ)
             = zor (evalF v φ) (evalF v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl))]
        | rw [ihφ (orF h).1, ihψ (orF h).2]
        | (rw [ihφ h, greedy_agrees_when_decided v φ (by rw [hφ]; rfl), hφ];
           cases hy : evalF (setA a x v) ψ <;> cases hz : evalF v ψ <;> rfl)
        | (rw [ihψ h, greedy_agrees_when_decided v ψ (by rw [hψ]; rfl), hψ];
           cases hy : evalF (setA a x v) φ <;> cases hz : evalF v φ <;> rfl)
  | imp φ ψ ihφ ihψ =>
      show impL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           zimp (evalF (setA a x v) φ) (evalF (setA a x v) ψ)
             = zimp (evalF v φ) (evalF v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl))]
        | rw [ihφ (orF h).1, ihψ (orF h).2]
        | (rw [ihφ h, greedy_agrees_when_decided v φ (by rw [hφ]; rfl), hφ];
           cases hy : evalF (setA a x v) ψ <;> cases hz : evalF v ψ <;> rfl)
        | (rw [ihψ h, greedy_agrees_when_decided v ψ (by rw [hψ]; rfl), hψ];
           cases hy : evalF (setA a x v) φ <;> cases hz : evalF v φ <;> rfl)
  | xor φ ψ ihφ ihψ =>
      show xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           zxor (evalF (setA a x v) φ) (evalF (setA a x v) ψ)
             = zxor (evalF v φ) (evalF v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl))]
        | rw [ihφ (orF h).1, ihψ (orF h).2]
        | (rw [ihφ h, greedy_agrees_when_decided v φ (by rw [hφ]; rfl), hφ];
           cases hy : evalF (setA a x v) ψ <;> cases hz : evalF v ψ <;> rfl)
        | (rw [ihψ h, greedy_agrees_when_decided v ψ (by rw [hψ]; rfl), hψ];
           cases hy : evalF (setA a x v) φ <;> cases hz : evalF v φ <;> rfl)
  | xnor φ ψ ihφ ihψ =>
      show xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = false →
           zxnor (evalF (setA a x v) φ) (evalF (setA a x v) ψ)
             = zxnor (evalF v φ) (evalF v ψ)
      cases hφ : foC v φ <;> cases hψ : foC v ψ <;> intro h <;> first
        | rw [ihφ (label_empty_of_decided v a φ (by rw [hφ]; rfl)),
              ihψ (label_empty_of_decided v a ψ (by rw [hψ]; rfl))]
        | rw [ihφ (orF h).1, ihψ (orF h).2]
        | (rw [ihφ h, greedy_agrees_when_decided v φ (by rw [hφ]; rfl), hφ];
           cases hy : evalF (setA a x v) ψ <;> cases hz : evalF v ψ <;> rfl)
        | (rw [ihψ h, greedy_agrees_when_decided v ψ (by rw [hψ]; rfl), hψ];
           cases hy : evalF (setA a x v) φ <;> cases hz : evalF v φ <;> rfl)

#print axioms conjL
#print axioms disjL
#print axioms impL
#print axioms xorL
#print axioms labF
#print axioms label_empty_of_decided
#print axioms receipt_complete
#print axioms greedy_agrees_when_decided
#print axioms receipt_complete_greedy

end V
