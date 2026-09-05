import ClassicalAgreement
import Linear
import ZTaint

/-!
# Proof validity against eligibility for reliance. Zero axioms.

An external question, asked of us from outside: a proof kernel certifies that a
proof inhabits a formal statement. It does not certify that the statement may be
RELIED UPON for a particular downstream consequence. Can the second question be
formalised as a compositional layer beside the first, or does it collapse into
ordinary hypotheses of the proof system?

**The collapse question is the whole point, and it is answered here against
ourselves.** A layer that merely renames existing hypotheses would be worth
nothing, and the honest way to find out is to state exactly where it adds
nothing and exactly where it cannot be replaced.

The answer measured below has three parts:

1. WHERE THE LAYER IS INERT — every ground verified. `V.evalF_agrees` already
   proves conservativity over the whole language: on a mark-free valuation the
   verdict is the classical one, formula for formula. Nothing is added.
2. WHERE THE LAYER IS INERT — every ground used ONCE. `Linear.linear_no_loss`
   already proves that at multiplicity one no answer both readings agree on is
   lost. Nothing is added.
3. WHERE IT CANNOT BE REPLACED — the same unverified ground used TWICE. Here the
   verdict changes, and no reformulation as ordinary hypotheses can follow,
   because ordinary hypotheses admit contraction and this does not.

Point 3 is the load-bearing one, and it is small enough to state exactly:

    the bundle connective is COMMUTATIVE but NOT IDEMPOTENT

A set needs both. A multiset needs only the first. So a bundle of grounds is a
MULTISET, and a hypothesis context in an ordinary proof system is a SET. That is
a structural difference, not a stylistic one.

**What this file does NOT establish**, and the omission is deliberate: nothing
here says a formal statement faithfully renders its source. That is a separate
and open burden. The separation proved here begins AFTER a statement is given.
-/

namespace RelianceBridge

open V

/-! ## 1. The two graphs over one language

`cval` is the proof side: ordinary classical evaluation. `evalF` is the reliance
side. Both are already in the corpus; nothing new is postulated. -/

/-- Grounds a consequence is asked to stand on, in the order a proof uses them.
A LIST, not a set: a derivation records how many times it leans on a lemma. -/
-- ОБРАЗЦЫ НЕ ПЕРЕСЕКАЮТСЯ, и это не стиль. Запись `| [φ] | φ :: r` даёт ровно
-- те же значения и тянет `propext`: перекрытие образцов заставляет уравнительный
-- компилятор строить расщепитель через равенство пропозиций. Промерено зондом:
-- перекрывающаяся редакция — propext, эта — пустой список.
def bundle : List Fm → Fm
  | []           => .top
  | [φ]          => φ
  | φ :: ψ :: r  => .conj φ (bundle (ψ :: r))

/-- Reliance verdict of a bundle under a marking of grounds. -/
def verdict (m : Nat → V) (Γ : List Fm) : V := evalF m (bundle Γ)

/-- Eligible means the verdict is earned outright. `Z` is not eligibility, and
neither is `F`. -/
def eligible (m : Nat → V) (Γ : List Fm) : Bool := verdict m Γ == T

/-! ## 2. The named grounds of one consequence

Four atoms, and nothing else is smuggled in: the proof obligation itself, the
source-to-statement warrant, sufficiency of authority for THIS consequence, and
currentness of the epoch that authority belongs to. -/

def proofValid : Fm := .atom 0
def sourceWarrant : Fm := .atom 1
def authoritySufficient : Fm := .atom 2
def epochCurrent : Fm := .atom 3

/-- The reliance bundle: each ground appears ONCE. By part 2 above this is
exactly the regime in which the layer loses nothing. -/
def relianceBundle : List Fm :=
  [proofValid, sourceWarrant, authoritySufficient, epochCurrent]

/-- Everything checked. -/
def mAuthorized : Nat → V := fun _ => T
/-- The proof is checked; the source-to-statement warrant is not. -/
def mNoWarrant : Nat → V := fun n => if n = 1 then Z else T
/-- The proof is checked; authority for this consequence is not established. -/
def mWeakAuthority : Nat → V := fun n => if n = 2 then Z else T
/-- Historical epoch: everything checked, as it stood. -/
def mEpochThen : Nat → V := fun _ => T
/-- Current epoch: the currentness of that authority is no longer established. -/
def mEpochNow : Nat → V := fun n => if n = 3 then Z else T

/-! ## 3. The four cases, computed by the kernel

In every one of the four the PROOF stands: `evalF m proofValid = T` throughout.
Only the reliance verdict moves. -/

/-- **Case 1 — authorised control.** Warrant present, authority sufficient,
epoch current: reliance is earned. -/
theorem case1_authorized :
    eligible mAuthorized relianceBundle = true := by decide

/-- **Case 2 — missing warrant.** The proof is valid and stays valid; reliance
does not close. -/
theorem case2_missing_warrant :
    evalF mNoWarrant proofValid = T ∧ eligible mNoWarrant relianceBundle = false := by
  decide

/-- **Case 3 — insufficient authority.** Same shape, different ground. -/
theorem case3_weak_authority :
    evalF mWeakAuthority proofValid = T
      ∧ eligible mWeakAuthority relianceBundle = false := by
  decide

/-- **Case 4 — epoch change.** ONE formula, ONE proof, two epochs. The proof is
untouched by the passage of time; the reliance verdict is not. -/
theorem case4_epoch_change :
    evalF mEpochThen proofValid = T
      ∧ evalF mEpochNow proofValid = T
      ∧ eligible mEpochThen relianceBundle = true
      ∧ eligible mEpochNow relianceBundle = false := by
  decide

/-- **The separation, in one line.** There is a state in which the proof
obligation is discharged and reliance is refused. `PROVED` does not imply
`ELIGIBLE`. -/
theorem proved_does_not_imply_eligible :
    ∃ m : Nat → V, evalF m proofValid = T ∧ eligible m relianceBundle = false :=
  ⟨mNoWarrant, by decide, by decide⟩

/-! ## 4. Does the layer collapse into ordinary hypotheses?

This is the question that decides whether any of the above is worth stating. The
test is not rhetorical: a hypothesis context in an ordinary proof system is a
SET of assumptions, and set-hood is exactly two structural rules — permutation
and contraction. If the reliance bundle obeyed both, it would be a hypothesis
context under another name and this file should be withdrawn. -/

/-- Contraction, on the proof side: assuming a ground twice is assuming it once.
This is why hypothesis contexts are sets. -/
theorem and_contract_classical (a c : Bool) : (a && (a && c)) = (a && c) := by
  cases a <;> cases c <;> rfl

/-- **Contraction holds for the proof graph.** Adding a second copy of a premise
changes no classical verdict, whatever the premise and whatever the rest. -/
theorem contraction_proof_side (φ ψ : Fm) (b : Nat → Bool) :
    cval b (.conj φ (.conj φ ψ)) = cval b (.conj φ ψ) :=
  and_contract_classical (cval b φ) (cval b ψ)

/-- Permutation, on the reliance side: the order of grounds is immaterial. -/
theorem bundle_commutative : ∀ x y : V, zand x y = zand y x := by decide

/-- **And contraction FAILS on the reliance side.** One unverified ground, used
twice, is not the same as used once. -/
theorem contraction_fails_reliance : ∃ x : V, zand x x ≠ x :=
  ⟨Z, by decide⟩

/-- The witness in the language, not merely in the value algebra: one ground,
two bundles with the same underlying SET of grounds, two different verdicts. -/
theorem same_grounds_two_verdicts :
    verdict (fun _ => Z) [proofValid] = Z
      ∧ verdict (fun _ => Z) [proofValid, proofValid] = F := by decide

/-- **THE NON-COLLAPSE RESULT.** The bundle connective is commutative and not
idempotent. A set of hypotheses requires both; a multiset requires only the
first. So a reliance bundle is a multiset of grounds, and cannot be represented
as an ordinary hypothesis context without adding the very structure that is
supposed to be unnecessary. -/
theorem reliance_is_multiset_not_set :
    (∀ x y : V, zand x y = zand y x) ∧ (∃ x : V, zand x x ≠ x) :=
  ⟨bundle_commutative, contraction_fails_reliance⟩

/-! ### The other structural rule, and it falls too

A hypothesis context is a set under TWO rules, not one. Contraction is the
second; the first is weakening — adding an assumption never costs anything.

The case is not ours: it is the one our own fidelity contract records, and it is
the sharper of the two because the added ground is a CLASSICAL TAUTOLOGY. Adding
`q ∨ ¬q` over an unverified `q` to a bundle that was earned outright destroys
the verdict. Classically that conjunct is free. Here it is not free, because it
introduces an unverified ground, and an unverified ground is what the discipline
is about. -/

/-- Excluded middle over one atom: the classically weightless ground. -/
def excludedMiddle (a : Nat) : Fm := .disj (.atom a) (.neg (.atom a))

/-- Proof checked, one further ground unverified. -/
def mOneUnchecked : Nat → V := fun n => if n = 0 then T else Z

/-- **Weakening holds for the proof graph.** A ground that is true adds nothing
and takes nothing. -/
theorem and_true_r (a : Bool) : (a && true) = a := by cases a <;> rfl

theorem weakening_proof_side (φ ψ : Fm) (b : Nat → Bool) (h : cval b ψ = true) :
    cval b (.conj φ ψ) = cval b φ := by
  show (cval b φ && cval b ψ) = cval b φ
  rw [h]; exact and_true_r _

/-- **Weakening FAILS on the reliance side**, and the added ground is a
classical tautology. `p` alone is earned; `p` together with `q ∨ ¬q` over an
unverified `q` is refused. -/
theorem weakening_fails_reliance :
    verdict mOneUnchecked [proofValid] = T
      ∧ verdict mOneUnchecked [proofValid, excludedMiddle 1] = F := by decide

/-- **Both set-forming rules fail.** Permutation survives; weakening and
contraction do not. A hypothesis context needs all three. -/
theorem neither_weakening_nor_contraction :
    (∀ x y : V, zand x y = zand y x)
      ∧ (∃ x : V, zand x x ≠ x)
      ∧ (verdict mOneUnchecked [proofValid] ≠
         verdict mOneUnchecked [proofValid, excludedMiddle 1]) :=
  ⟨bundle_commutative, contraction_fails_reliance, by decide⟩

/-! ### What this does NOT say

It does not say Lean cannot express reliance. Lean expresses anything a
multiset expresses; that was never in question. The measured claim is narrower
and it is about IDENTITY, not expressive power:

> the reliance bundle is not the proof system's own hypothesis context.

A proof assistant that wants both must carry a SECOND context beside its own,
obeying different structural rules. That second context is precisely the
"separate compositional layer" whose necessity was the question. If someone
shows a faithful encoding into ONE ordinary hypothesis context — one that keeps
weakening and contraction and still refuses reliance in cases 2, 3 and 4 — this
file is refuted, and that would be the useful outcome.

## 5. Where the layer is honestly inert

Two results already in the corpus, restated here as the price of the claim
above. They are what keeps this from being an argument for putting the layer
everywhere. -/

/-- **Inert on verified ground.** With no mark anywhere the verdict is the
classical one, for every formula of the language. This is `V.evalF_agrees`. -/
theorem inert_when_all_verified (b : Nat → Bool) (φ : Fm) :
    evalF (fun n => emb (b n)) φ = emb (cval b φ) :=
  evalF_agrees b φ

/-- **Nothing gained on tautologies.** Every ZTL tautology is already a
classical one, so the layer never manufactures a new law. -/
theorem no_new_laws (φ : Fm) (h : ∀ v : Nat → V, evalF v φ = T) :
    ∀ b : Nat → Bool, cval b φ = true :=
  ztl_taut_is_classical φ h

/-! ## 6. What a proof DAG cannot do to a mark

The reliance side has one further property with a direct reading in the proof
graph: applying lemmas is function application, and no chain of applications
launders an unverified reference. The pedigree grows; the mark does not come
off. Restated from `ZTaint.no_laundering`, whose subject is exactly a chain of
verified functions applied to a marked element. -/

theorem no_chain_of_lemmas_launders (fs : List (Nat → Nat)) (i : Nat) :
    ZTaint.isMark (ZTaint.taints fs (El.z i)) = true :=
  ZTaint.no_laundering_mark fs i

/-- And the only sanitiser is not an application at all: it is SUBSTITUTION of a
checked element for an unchecked one — an act outside the proof graph. -/
theorem sanitiser_is_outside_the_graph (n : Nat) :
    ZTaint.isMark (El.v n) = false :=
  ZTaint.sanitizer_is_substitution n

end RelianceBridge

#print axioms RelianceBridge.case1_authorized
#print axioms RelianceBridge.case2_missing_warrant
#print axioms RelianceBridge.case3_weak_authority
#print axioms RelianceBridge.case4_epoch_change
#print axioms RelianceBridge.proved_does_not_imply_eligible
#print axioms RelianceBridge.and_contract_classical
#print axioms RelianceBridge.contraction_proof_side
#print axioms RelianceBridge.bundle_commutative
#print axioms RelianceBridge.contraction_fails_reliance
#print axioms RelianceBridge.same_grounds_two_verdicts
#print axioms RelianceBridge.and_true_r
#print axioms RelianceBridge.weakening_proof_side
#print axioms RelianceBridge.weakening_fails_reliance
#print axioms RelianceBridge.neither_weakening_nor_contraction
#print axioms RelianceBridge.reliance_is_multiset_not_set
#print axioms RelianceBridge.inert_when_all_verified
#print axioms RelianceBridge.no_new_laws
#print axioms RelianceBridge.no_chain_of_lemmas_launders
#print axioms RelianceBridge.sanitiser_is_outside_the_graph
