import ZTopology

/-!
# ZQuasi — quasi-sets in ZTL: the number of ACTS is earned, the number of OBJECTS is not

The curator's line of 2026-10-02: quasi-sets (Krause; Dalla Chiara and Toraldo di Francia)
are native to ZTL. Measured first with ztljudge, proved here.

The case. A detector clicks twice. `c1`, `c2` — the two clicks, each witnessed (T).
`same` — "the two clicks came from one and the same thing": nothing witnessed it (Z).

Vocabulary (2026-10-30). `earned` / `refuted` are `ZTopology`'s: T / F now and under every refinement — the
HEREDITARY T / F. The judge's words since 2026-10-29 differ: EARNED / REFUTED = the strong Kleene T / F (which
implies hereditary), EARNED IF STABLE = T in every cleaning. Each item says where the two agree.

Proved here, on the empty axiom list:
1. `occurrences_earned` — "there were two occurrences" (c1 ∧ c2) is a hereditary T, proved through its strong
   Kleene T: the judge's EARNED as well.
2. `two_objects_open`, `one_object_open` — "two distinct things" (c1 ∧ c2 ∧ ¬same) and
   "one thing" (c1 ∧ c2 ∧ same) are each neither a hereditary T nor a hereditary F: further data
   could settle either way (the judge: OPEN).
3. `one_or_two_not_earned` — not even "one or two things" is a hereditary T: it is F as written, since
   excluded middle on an unwitnessed identity is not granted (`ZTopology.excluded_middle_not_earned`). It is T in
   every cleaning, so the judge says EARNED IF STABLE.
4. `count_follows_identity` — once identity is witnessed (same = F), "two things" is a hereditary T, proved
   through its strong Kleene T (the judge's EARNED):
   the number of objects is earned exactly by witnessing identity; nothing else is needed.

So in ZTL a quasi-set is a count of WITNESSING ACTS whose bearers' identity is Z, and the
number of OBJECTS inherits that Z — it is derived, not postulated.

Where this stands against prior work (checked once, 2026-10-02). Krause's quasi-set theory
makes `x = y` ill-formed for m-atoms and then ADDS the quasi-cardinal `qc` as a primitive,
so a quasi-set does have a number of elements; quasets (Dalla Chiara, Toraldo di Francia)
likewise have a well-defined cardinal. Holik ("Neither Name, Nor Number", 2011) argues that
for some quantum systems particle number itself is not well defined — the nearest claim to
ours. What may be new here is narrower: the split between the count of acts (earned) and
the count of objects (not earned) falls out of one judge with no primitive for number, and
it is machine-checked. The physics (which systems, which states) is not modelled here.
-/

namespace ZQuasi

open V
open ZTopology

/-- Atom 0 = first click, atom 1 = second click, atom 2 = "same thing". -/
def clicks : Nat → V
  | 0 => T
  | 1 => T
  | _ => Z

def twoOccurrences : Fm := .conj (.atom 0) (.atom 1)
def twoObjects : Fm := .conj twoOccurrences (.neg (.atom 2))
def oneObject : Fm := .conj twoOccurrences (.atom 2)
def oneOrTwo : Fm := .conj twoOccurrences (.disj (.atom 2) (.neg (.atom 2)))

/-- Identity witnessed: the clicks came from one thing. -/
def sameT : Nat → V
  | 0 => T
  | 1 => T
  | _ => T

/-- Identity witnessed the other way: two different things. -/
def sameF : Nat → V
  | 0 => T
  | 1 => T
  | _ => F

theorem refines_sameT : refines clicks sameT := by
  intro n; match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem refines_sameF : refines clicks sameF := by
  intro n; match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- 1. Two occurrences: a hereditary T (through the strong Kleene T, so also the judge's EARNED). -/
theorem occurrences_earned : earned twoOccurrences clicks :=
  kleene_sub_earned rfl

/-- 2a. "Two distinct things": not a hereditary T (identity might turn out T) ... -/
theorem two_objects_not_earned : ¬ earned twoObjects clicks := by
  intro h
  have h1 : evalF sameT twoObjects = T := h sameT refines_sameT
  have h2 : evalF sameT twoObjects = F := rfl
  exact V.noConfusion (h2.symm.trans h1)

/-- ... and not a hereditary F (identity might turn out F). -/
theorem two_objects_not_refuted : ¬ refuted twoObjects clicks := by
  intro h
  have h1 : evalF sameF twoObjects = F := h sameF refines_sameF
  have h2 : evalF sameF twoObjects = T := rfl
  exact V.noConfusion (h2.symm.trans h1)

theorem two_objects_open : ¬ earned twoObjects clicks ∧ ¬ refuted twoObjects clicks :=
  ⟨two_objects_not_earned, two_objects_not_refuted⟩

/-- 2b. "One thing": the mirror. -/
theorem one_object_open : ¬ earned oneObject clicks ∧ ¬ refuted oneObject clicks := by
  constructor
  · intro h
    have h1 : evalF sameF oneObject = T := h sameF refines_sameF
    have h2 : evalF sameF oneObject = F := rfl
    exact V.noConfusion (h2.symm.trans h1)
  · intro h
    have h1 : evalF sameT oneObject = F := h sameT refines_sameT
    have h2 : evalF sameT oneObject = T := rfl
    exact V.noConfusion (h2.symm.trans h1)

/-- 3. Not even "one or two things" is a hereditary T (F as written; the judge: EARNED IF STABLE). -/
theorem one_or_two_not_earned : ¬ earned oneOrTwo clicks := by
  intro h
  have h1 : evalF clicks oneOrTwo = T := earned_now h
  have h2 : evalF clicks oneOrTwo = F := rfl
  exact V.noConfusion (h2.symm.trans h1)

/-- 4. Witness the identity and the number of objects is a hereditary T (through the strong Kleene T, so also
the judge's EARNED). -/
theorem count_follows_identity : earned twoObjects sameF :=
  kleene_sub_earned rfl

end ZQuasi

#print axioms ZQuasi.occurrences_earned
#print axioms ZQuasi.two_objects_open
#print axioms ZQuasi.one_object_open
#print axioms ZQuasi.one_or_two_not_earned
#print axioms ZQuasi.count_follows_identity
