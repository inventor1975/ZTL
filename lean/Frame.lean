/-
  Frame.lean — the three mini-theorems of §3.5, promoted from prose.

  The preprint calls these "incompatibilities (mini-theorems)" and backs
  them with a parenthesis: "(verified by substitution)". The theorem
  inventory of 2026-07-20 flagged that as the only place where the word
  "theorem" sat on unformalised reasoning about the core itself — a
  paper whose subject is the difference between earned and borrowed
  truth cannot afford it. All three are finite statements about a finite
  matrix, so all three are cheap. Here they are.

  §3.5.1  {¬Z = F, T→Z = F} ⟹ contraposition-as-identity is impossible.
  §3.5.2  Housing the liar requires a fixed point of ¬; the tables have
          none, and for Z it is pessimism that excludes it — so the
          quarantine flag is not a value one could reach by editing a
          cell. It lives outside the value layer.
  §3.5.3  Collapse Z to F at the ATOM (instead of at the operator) and
          the system becomes classical VERBATIM: evaluation agrees with
          Boolean evaluation on the nose, so every classical tautology
          returns and the rules/laws split vanishes. This is the fork
          that would turn ZTL into Bochvar's B3□ — stated as a theorem
          about what would be lost, not as an aside.

  VR discipline: self-contained over the core, `#print axioms` for every
  public object, empty list throughout.
-/
import ZTL

namespace Frame

open V

/-! ## §3.5.1 — contraposition dies at two named cells -/

/-- The two cells the preprint names, as they actually stand. -/
theorem cells : znot Z = F ∧ zimp T Z = F := by decide

/-- MT1. Contraposition-as-identity is refuted by a substitution that
uses ONLY those two cells: at p = T, q = Z the left side is `T→Z = F`
while the right side is `¬Z→¬T = F→F = T`. The point is not that the
law fails (that is `contraposition_fails`) but WHERE it fails: flipping
either cited cell is what a rescue would cost. -/
theorem mt1_contraposition_impossible :
    zimp T Z ≠ zimp (znot Z) (znot T) := by decide

/-- The dependence made explicit: the refutation is a consequence of the
two cells, not of the whole table. Read as: any table agreeing with ZTL
on these two entries refutes contraposition at this very point. -/
theorem mt1_from_the_cells :
    znot Z = F → zimp T Z = F → znot T = F → zimp F F = T →
    zimp T Z ≠ zimp (znot Z) (znot T) := by
  intro h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  decide

/-! ## §3.5.2 — the quarantine flag is outside the value layer -/

/-- Housing the liar means being a fixed point of negation: λ says ¬λ,
so a value v that housed it would satisfy ¬v = v. -/
theorem mt2_housing_means_fixed_point : ∀ v : V, znot v ≠ v := by decide

/-- And for Z specifically it is pessimism — ¬Z = F, not Z — that does
the excluding. So quarantine is not reachable by adding a fourth value
in the same style: it is a property of the *input mark*, not a verdict
the tables could return. -/
theorem mt2_pessimism_excludes_Z : znot Z = F ∧ (F : V) ≠ Z := by decide

/-- MT2, assembled: no value houses the liar, and the specific reason at
Z is the pessimistic cell. The quarantine flag is therefore irremovable
in the exact sense that removing it would require a ¬-fixed point, which
the frame does not contain. -/
theorem mt2_quarantine_irremovable :
    (∀ v : V, znot v ≠ v) ∧ znot Z = F ∧ (F : V) ≠ Z := by decide

/-! ## §3.5.3 — collapsing at the atom is the classical fork

The claim under test is the strong one: not "some laws come back" but
"the system becomes classical verbatim". So we prove agreement with
Boolean evaluation on the nose, and read the laws off as a corollary.
-/

/-- Boolean evaluation of the same syntax — the classical yardstick. -/
def beval (b : Nat → Bool) : Fm → Bool
  | .atom n   => b n
  | .top      => true
  | .bot      => false
  | .neg φ    => !(beval b φ)
  | .conj φ ψ => (beval b φ) && (beval b ψ)
  | .disj φ ψ => (beval b φ) || (beval b ψ)
  | .imp φ ψ  => !(beval b φ) || (beval b ψ)
  | .xor φ ψ  => (beval b φ) != (beval b ψ)
  | .xnor φ ψ => (beval b φ) == (beval b ψ)

/-- The collapse itself: Z is read as F at the atom, before any operator
sees it. This is the fork — in ZTL the mark reaches the connective and
is read there; here it is spent one step earlier. -/
def collapse : V → Bool
  | T => true
  | F => false
  | Z => false

def embed : Bool → V
  | true  => T
  | false => F

/-- The connectives commute with the embedding on classical arguments —
one cell-check each, and the whole agreement theorem rests on these. -/
theorem embed_not (a : Bool) : znot (embed a) = embed (!a) := by
  cases a <;> decide

theorem embed_and (a b : Bool) : zand (embed a) (embed b) = embed (a && b) := by
  cases a <;> cases b <;> decide

theorem embed_or (a b : Bool) : zor (embed a) (embed b) = embed (a || b) := by
  cases a <;> cases b <;> decide

theorem embed_imp (a b : Bool) :
    zimp (embed a) (embed b) = embed (!a || b) := by
  cases a <;> cases b <;> decide

theorem embed_xor (a b : Bool) : zxor (embed a) (embed b) = embed (a != b) := by
  cases a <;> cases b <;> decide

theorem embed_xnor (a b : Bool) :
    zxnor (embed a) (embed b) = embed (a == b) := by
  cases a <;> cases b <;> decide

/-- MT3, the core of it. Under the atom-collapse the ZTL evaluation of
EVERY formula equals the embedded Boolean evaluation. Not "the fallen
laws come back" — the semantics is classical, term by term. -/
theorem mt3_collapse_is_classical (v : Nat → V) :
    ∀ φ : Fm, evalF (fun n => embed (collapse (v n))) φ
            = embed (beval (fun n => collapse (v n)) φ) := by
  -- `simp only` is banned here: it taints the term with propext even on
  -- pure Eq lemmas. Explicit `show` (definitional unfolding) plus `rw`
  -- by equations keeps the whole induction on the empty list.
  intro φ
  induction φ with
  | atom n   => rfl
  | top      => rfl
  | bot      => rfl
  | neg φ ih =>
      show znot (evalF _ φ) = embed (!(beval _ φ))
      rw [ih, embed_not]
  | conj φ ψ ih1 ih2 =>
      show zand (evalF _ φ) (evalF _ ψ) = embed ((beval _ φ) && (beval _ ψ))
      rw [ih1, ih2, embed_and]
  | disj φ ψ ih1 ih2 =>
      show zor (evalF _ φ) (evalF _ ψ) = embed ((beval _ φ) || (beval _ ψ))
      rw [ih1, ih2, embed_or]
  | imp φ ψ ih1 ih2 =>
      show zimp (evalF _ φ) (evalF _ ψ) = embed (!(beval _ φ) || (beval _ ψ))
      rw [ih1, ih2, embed_imp]
  | xor φ ψ ih1 ih2 =>
      show zxor (evalF _ φ) (evalF _ ψ) = embed ((beval _ φ) != (beval _ ψ))
      rw [ih1, ih2, embed_xor]
  | xnor φ ψ ih1 ih2 =>
      show zxnor (evalF _ φ) (evalF _ ψ) = embed ((beval _ φ) == (beval _ ψ))
      rw [ih1, ih2, embed_xnor]

/-- Corollary — every classical tautology returns. This is the content
of "all classical laws are restored": there is no ZTL-specific price
list left to write, and with it the rules/laws split disappears. -/
theorem mt3_every_tautology_returns (v : Nat → V) (φ : Fm)
    (htaut : ∀ b : Nat → Bool, beval b φ = true) :
    evalF (fun n => embed (collapse (v n))) φ = T := by
  rw [mt3_collapse_is_classical v φ, htaut]
  rfl

/-- The two flagship casualties, back on their feet under the collapse —
`p → p` (the one-directional deduction theorem's witness) and excluded
middle. Their return is exactly what §3.5.3 says is lost with the fork. -/
theorem mt3_imp_refl_returns (v : Nat → V) (n : Nat) :
    evalF (fun k => embed (collapse (v k)))
          (.imp (.atom n) (.atom n)) = T := by
  apply mt3_every_tautology_returns
  intro b
  show (!(b n) || b n) = true
  cases b n <;> rfl

theorem mt3_lem_returns (v : Nat → V) (n : Nat) :
    evalF (fun k => embed (collapse (v k)))
          (.disj (.atom n) (.neg (.atom n))) = T := by
  apply mt3_every_tautology_returns
  intro b
  show (b n || !(b n)) = true
  cases b n <;> rfl

/-- And the contrast that makes the fork a fork: the SAME formula `p→p`
is F in ZTL proper, where the mark reaches the operator. One step in the
pipeline, and the whole price list appears or vanishes. -/
theorem mt3_the_fork (n : Nat) :
    evalF (fun _ => Z) (.imp (.atom n) (.atom n)) = F := rfl

#print axioms cells
#print axioms mt1_contraposition_impossible
#print axioms mt1_from_the_cells
#print axioms mt2_housing_means_fixed_point
#print axioms mt2_pessimism_excludes_Z
#print axioms mt2_quarantine_irremovable
#print axioms embed_not
#print axioms embed_and
#print axioms embed_or
#print axioms embed_imp
#print axioms embed_xor
#print axioms embed_xnor
#print axioms mt3_collapse_is_classical
#print axioms mt3_every_tautology_returns
#print axioms mt3_imp_refl_returns
#print axioms mt3_lem_returns
#print axioms mt3_the_fork

end Frame
