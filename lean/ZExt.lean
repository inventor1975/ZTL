import ZTL

/-!
# ZExt — extensionality of sets, read in ZTL. Zero axioms. (2026-11-25)

THE QUESTION (the curator, 2026-11-25: "раз propext ошибочен на грязном параметре — это дверь к новой теореме, или
к опровержению чего-то классического, или к взгляду под другим углом"). Classical set theory has extensionality:
two sets with the same members are equal, and so are interchangeable everywhere. In Lean it rests on `propext` (and
`funext`). ZTL refutes `propext`'s reading on unverified data (`ZAxiomsRead.propext_fails_dirty`, the same fact as
`ZAlgebra.not_selfextensional`). What happens to extensionality?

A SET READ IN ZTL is a membership with a ZTL value: `A x = T` (membership earned), `F` (refuted), `Z` (unverified).
"x ∈ A" in the classical sense is the EARNED membership, `A x = T`. Then:

    compl_ext_fails_dirty   two sets with the same members can have complements with DIFFERENT members —
                            the classical theorem "same members ⇒ same non-members" is refuted on unverified data
    coext_gap               and the leak is exactly one thing: F against Z — refuted against unverified
    compl_ext_clean         on verified sets (no Z) the classical theorem holds
    scoext_iff_same         TWO-SIDED extensionality — the same members AND the same non-members — is equality,
                            dirty data included (Nelson's "strong equivalence", here a theorem of the three values)
    compl_ext_strong        so two-sided extensionality survives complement, union and intersection everywhere
    inter_coext, union_coext   one-sided extensionality survives ∩ and ∪: only ¬ lets the unverified leak through
                            (the same boundary as ContextClosure's negation-free fragment)

READING. Classically "the same members" is enough, because "not a member" is the same as "not earned a member".
In ZTL they differ: Z is not earned AND not refuted. One-sided extensionality cannot see that difference, and the
complement makes it visible: the complement of a refuted membership is earned, the complement of an unverified one is
not. So the classical principle splits into two, and only the two-sided one is the identity of sets.

NOT CLAIMED: that Lean's `Set.ext` is false. In Lean a membership is a Prop, and there is no third value. What is
shown is that extensionality read on unverified data needs its second side.

`Same` is pointwise equality: equality of the functions would need `funext`, an axiom here.
-/

namespace ZExt

open V

/-- A set over `α` read in ZTL: membership earned (T), refuted (F), or unverified (Z). -/
abbrev ZSet (α : Type) := α → V

/-- Complement, intersection, union: ZTL's own connectives, pointwise. -/
def compl {α : Type} (A : ZSet α) : ZSet α := fun x => znot (A x)
def inter {α : Type} (A B : ZSet α) : ZSet α := fun x => zand (A x) (B x)
def union {α : Type} (A B : ZSet α) : ZSet α := fun x => zor (A x) (B x)

/-- Classical extensionality's premise: the same EARNED members. -/
def Coext {α : Type} (A B : ZSet α) : Prop := ∀ x, A x = T ↔ B x = T

/-- Two-sided: the same members and the same non-members. -/
def SCoext {α : Type} (A B : ZSet α) : Prop := ∀ x, (A x = T ↔ B x = T) ∧ (A x = F ↔ B x = F)

/-- The same value at every element (pointwise: no `funext`). -/
def Same {α : Type} (A B : ZSet α) : Prop := ∀ x, A x = B x

/-- Verified: no element unverified. -/
def Clean {α : Type} (A : ZSet α) : Prop := ∀ x, A x ≠ Z

/-! ### The three values, once -/

theorem v_not_T : ∀ a : V, znot a = T ↔ a = F := by decide
theorem v_and_T : ∀ a b : V, zand a b = T ↔ (a = T ∧ b = T) := by decide
theorem v_or_T  : ∀ a b : V, zor a b = T ↔ (a = T ∨ b = T) := by decide

/-- One-sided agreement that is not equality is exactly F against Z. -/
theorem pt_gap : ∀ a b : V, (a = T ↔ b = T) → a ≠ b → (a = F ∧ b = Z) ∨ (a = Z ∧ b = F) := by decide

/-- On verified values one-sided agreement is equality. -/
theorem pt_clean : ∀ a b : V, a ≠ Z → b ≠ Z → (a = T ↔ b = T) → a = b := by decide

/-- Two-sided agreement is equality, the unverified value included. -/
theorem pt_strong : ∀ a b : V, ((a = T ↔ b = T) ∧ (a = F ↔ b = F)) ↔ a = b := by decide

/-! ### The classical theorem, refuted on unverified data -/

/-- Same members, different non-members: A refutes the element, B leaves it unverified. -/
theorem compl_ext_fails_dirty :
    ∃ A B : ZSet Unit, Coext A B ∧ ¬ Coext (compl A) (compl B) :=
  ⟨fun _ => F, fun _ => Z, fun _ => (by decide : (F = T ↔ Z = T)),
   fun h => absurd ((h ()).mp (by decide : znot F = T)) (by decide : ¬ znot Z = T)⟩

/-- "Same members ⇒ same members of the complements" — classically trivial — is not a theorem of ZTL's sets. -/
theorem not_compl_ext : ¬ ∀ A B : ZSet Unit, Coext A B → Coext (compl A) (compl B) := fun h =>
  match compl_ext_fails_dirty with
  | ⟨A, B, hc, hn⟩ => hn (h A B hc)

/-- Where they differ, it is F against Z, and nothing else. -/
theorem coext_gap {α : Type} (A B : ZSet α) (h : Coext A B) (x : α) (hx : A x ≠ B x) :
    (A x = F ∧ B x = Z) ∨ (A x = Z ∧ B x = F) :=
  pt_gap (A x) (B x) (h x) hx

/-! ### What holds -/

theorem same_coext {α : Type} {A B : ZSet α} (h : Same A B) : Coext A B :=
  fun x => ⟨fun hx => (h x) ▸ hx, fun hx => (h x).symm ▸ hx⟩

theorem same_compl {α : Type} {A B : ZSet α} (h : Same A B) : Same (compl A) (compl B) :=
  fun x => congrArg znot (h x)

theorem same_inter {α : Type} {A B C D : ZSet α} (h1 : Same A B) (h2 : Same C D) : Same (inter A C) (inter B D) :=
  fun x => (congrArg (fun u => zand u (C x)) (h1 x)).trans (congrArg (zand (B x)) (h2 x))

theorem same_union {α : Type} {A B C D : ZSet α} (h1 : Same A B) (h2 : Same C D) : Same (union A C) (union B D) :=
  fun x => (congrArg (fun u => zor u (C x)) (h1 x)).trans (congrArg (zor (B x)) (h2 x))

/-- On verified sets, the same members is equality. -/
theorem coext_clean_same {α : Type} (A B : ZSet α) (hA : Clean A) (hB : Clean B) (h : Coext A B) : Same A B :=
  fun x => pt_clean (A x) (B x) (hA x) (hB x) (h x)

/-- On verified sets the classical theorem holds. -/
theorem compl_ext_clean {α : Type} (A B : ZSet α) (hA : Clean A) (hB : Clean B) (h : Coext A B) :
    Coext (compl A) (compl B) :=
  same_coext (same_compl (coext_clean_same A B hA hB h))

/-- Two-sided extensionality is the identity of sets — unverified elements included. -/
theorem scoext_iff_same {α : Type} (A B : ZSet α) : SCoext A B ↔ Same A B :=
  ⟨fun h x => (pt_strong (A x) (B x)).mp (h x), fun h x => (pt_strong (A x) (B x)).mpr (h x)⟩

/-- … and so it survives complement, intersection and union, everywhere. -/
theorem compl_ext_strong {α : Type} (A B : ZSet α) (h : SCoext A B) : SCoext (compl A) (compl B) :=
  (scoext_iff_same _ _).mpr (same_compl ((scoext_iff_same A B).mp h))

theorem inter_ext_strong {α : Type} (A B C D : ZSet α) (h1 : SCoext A B) (h2 : SCoext C D) :
    SCoext (inter A C) (inter B D) :=
  (scoext_iff_same _ _).mpr (same_inter ((scoext_iff_same A B).mp h1) ((scoext_iff_same C D).mp h2))

theorem union_ext_strong {α : Type} (A B C D : ZSet α) (h1 : SCoext A B) (h2 : SCoext C D) :
    SCoext (union A C) (union B D) :=
  (scoext_iff_same _ _).mpr (same_union ((scoext_iff_same A B).mp h1) ((scoext_iff_same C D).mp h2))

/-! ### One-sided extensionality survives ∩ and ∪: only ¬ lets the unverified through -/

theorem inter_coext {α : Type} (A B C D : ZSet α) (h1 : Coext A B) (h2 : Coext C D) :
    Coext (inter A C) (inter B D) := fun x =>
  have e1 := v_and_T (A x) (C x)
  have e2 := v_and_T (B x) (D x)
  ⟨fun h => let ⟨p, q⟩ := e1.mp h; e2.mpr ⟨(h1 x).mp p, (h2 x).mp q⟩,
   fun h => let ⟨p, q⟩ := e2.mp h; e1.mpr ⟨(h1 x).mpr p, (h2 x).mpr q⟩⟩

theorem union_coext {α : Type} (A B C D : ZSet α) (h1 : Coext A B) (h2 : Coext C D) :
    Coext (union A C) (union B D) := fun x =>
  have e1 := v_or_T (A x) (C x)
  have e2 := v_or_T (B x) (D x)
  ⟨fun h => match e1.mp h with
     | .inl p => e2.mpr (.inl ((h1 x).mp p))
     | .inr q => e2.mpr (.inr ((h2 x).mp q)),
   fun h => match e2.mp h with
     | .inl p => e1.mpr (.inl ((h1 x).mpr p))
     | .inr q => e1.mpr (.inr ((h2 x).mpr q))⟩

/-- … and the earned members of a complement are exactly the REFUTED members — not the "non-members". -/
theorem compl_members {α : Type} (A : ZSet α) (x : α) : compl A x = T ↔ A x = F := v_not_T (A x)

end ZExt

#print axioms ZExt.compl_ext_fails_dirty
#print axioms ZExt.not_compl_ext
#print axioms ZExt.coext_gap
#print axioms ZExt.compl_ext_clean
#print axioms ZExt.scoext_iff_same
#print axioms ZExt.compl_ext_strong
#print axioms ZExt.inter_ext_strong
#print axioms ZExt.union_ext_strong
#print axioms ZExt.inter_coext
#print axioms ZExt.union_coext
#print axioms ZExt.compl_members
