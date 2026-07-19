/-!
# JunctionWitness — plugging quantum into quantum: the cover law falls
# at the seam, kernel-checked

The curator's observation (2026-07-19): PSSL's mirror gives quantum the
three laws ZTL drops (LEM, DNE, identity) — yet on TWO quanta a face of
one of those three falls for quantum as well. The precision, stated
honestly and proved here:

  * LEM as a LATTICE IDENTITY (x ∨ x⊥ = ⊤) is IRON at every number of
    quanta (lem_holds, QuantumWitness.lean; the iron laws of
    dilemmas/quantum_ladder.py).
  * What falls is the COVER face of the disjunction — "a true OR has a
    true disjunct" — and at the JUNCTION of two quantum logics it falls
    in a NEW, correlation form: the singlet lies in the span of the two
    product atoms |ud⟩, |du⟩ (the pair proposition "spins are opposite"
    is true), yet it lies in NEITHER atom and in NO local plane of
    EITHER factor (spin1=up/down, spin2=up/down all fail). The truth
    lives only at the seam. This is entanglement written as a lattice
    fact, over the integers.

Everything is exact integer linear algebra on unnormalised vectors
(rays do not need √2): the positive claim exhibits the coefficients
(singlet = 1·|ud⟩ + (−1)·|du⟩, five definitional branches); each
negative claim extracts one impossible component equation and closes by
explicit congruence arithmetic + `decide` (pure terms — no omega, no rw-at). No function extensionality (all claims are pointwise), no
classical axioms — the empty axiom list, verifiable from zero:

    lean lean/JunctionWitness.lean
-/

namespace JunctionWitness

/-- Integer vectors indexed by Nat (coordinates ≥ 4 are 0) — Nat
indexing on purpose: Fin-literals of the current toolchain carry
bound-proofs that drag propext into every term touching them. -/
def Vec := Nat → Int

def vec (a b c d : Int) : Vec := fun n =>
  if n = 0 then a else if n = 1 then b
  else if n = 2 then c else if n = 3 then d else 0

/-- ψ lies on the ray of u (an atom holds the state). -/
def InRay (u ψ : Vec) : Prop := ∃ a : Int, ∀ i, ψ i = a * u i

/-- ψ lies in the span of u and v (a 2-dimensional proposition holds). -/
def InSpan2 (u v ψ : Vec) : Prop :=
  ∃ a b : Int, ∀ i, ψ i = a * u i + b * v i

/-- Basis |00⟩,|01⟩,|10⟩,|11⟩ (first slot = particle 1: 0 = up). -/
def e00 : Vec := vec 1 0 0 0
def e01 : Vec := vec 0 1 0 0     -- |ud⟩
def e10 : Vec := vec 0 0 1 0     -- |du⟩
def e11 : Vec := vec 0 0 0 1

/-- The singlet ray (unnormalised): |ud⟩ − |du⟩. -/
def singlet : Vec := vec 0 1 (-1) 0

/-! ## The junction theorem, piece by piece -/

/-- **The pair proposition holds**: the singlet lies in the span of the
two product atoms — "spins are opposite" is TRUE at the singlet. -/
theorem pair_true : InSpan2 e01 e10 singlet :=
  ⟨1, -1, fun n => match n with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | _ + 4 => rfl⟩

/-- ...yet the singlet is in NEITHER product atom. -/
theorem add_mz (a b : Int) : a * 0 + b * 0 = 0 :=
  (congrArg (fun x => x + b * 0) (Int.mul_zero a)).trans
    ((congrArg (fun x => (0 : Int) + x) (Int.mul_zero b)).trans rfl)

theorem disjunct_ud_fails : ¬ InRay e01 singlet :=
  fun hex => Exists.elim hex (fun a h =>
    absurd ((h 2).trans (Int.mul_zero a)) (by decide))

theorem disjunct_du_fails : ¬ InRay e10 singlet :=
  fun hex => Exists.elim hex (fun a h =>
    absurd ((h 1).trans (Int.mul_zero a)) (by decide))

/-- ...and in NO local plane of particle 1: spin1 = up is the span of
|00⟩,|01⟩ — the singlet is not there... -/
theorem spin1_up_fails : ¬ InSpan2 e00 e01 singlet :=
  fun hex => Exists.elim hex (fun a hex2 => Exists.elim hex2 (fun b h =>
    absurd ((h 2).trans (add_mz a b)) (by decide)))

/-- ...nor in spin1 = down (span of |10⟩,|11⟩)... -/
theorem spin1_down_fails : ¬ InSpan2 e10 e11 singlet :=
  fun hex => Exists.elim hex (fun a hex2 => Exists.elim hex2 (fun b h =>
    absurd ((h 1).trans (add_mz a b)) (by decide)))

/-- ...nor in spin2 = up (span of |00⟩,|10⟩)... -/
theorem spin2_up_fails : ¬ InSpan2 e00 e10 singlet :=
  fun hex => Exists.elim hex (fun a hex2 => Exists.elim hex2 (fun b h =>
    absurd ((h 1).trans (add_mz a b)) (by decide)))

/-- ...nor in spin2 = down (span of |01⟩,|11⟩). -/
theorem spin2_down_fails : ¬ InSpan2 e01 e11 singlet :=
  fun hex => Exists.elim hex (fun a hex2 => Exists.elim hex2 (fun b h =>
    absurd ((h 2).trans (add_mz a b)) (by decide)))

/-- **The junction theorem.** Plugging two quantum logics together
creates a proposition that is TRUE at the singlet — the join of the two
product atoms — while the state lies in NEITHER atom and in NO local
plane of EITHER factor. The cover face of the disjunction ("a true OR
has a true disjunct"), one face of the trio ZTL surrenders, falls for
QUANTUM at the seam of composition — in correlation form, which is
entanglement as a lattice fact. (LEM as the lattice identity
x ∨ x⊥ = ⊤ stays iron; the fall is the cover, not the identity.) -/
theorem junction :
    InSpan2 e01 e10 singlet
    ∧ ¬ InRay e01 singlet ∧ ¬ InRay e10 singlet
    ∧ ¬ InSpan2 e00 e01 singlet ∧ ¬ InSpan2 e10 e11 singlet
    ∧ ¬ InSpan2 e00 e10 singlet ∧ ¬ InSpan2 e01 e11 singlet :=
  ⟨pair_true, disjunct_ud_fails, disjunct_du_fails,
   spin1_up_fails, spin1_down_fails, spin2_up_fails, spin2_down_fails⟩

#print axioms pair_true
#print axioms disjunct_ud_fails
#print axioms disjunct_du_fails
#print axioms spin1_up_fails
#print axioms spin1_down_fails
#print axioms spin2_up_fails
#print axioms spin2_down_fails
#print axioms junction

end JunctionWitness
