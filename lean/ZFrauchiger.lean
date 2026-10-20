import Hardy

/-!
# ZFrauchiger — the Frauchiger–Renner chain under ZTL's time, kernel-checked. Zero axioms.

2026-10-20 (`ztl-physics/fr.py`, the curator's "Делай"). Frauchiger & Renner's state is Hardy's: with the record of
Fbar's coin r (h, t) and F's spin z (dn, up), Ψ ∝ |h,dn⟩ + |t,dn⟩ + |t,up⟩ — `Hardy.psi` under relabelling. The four
agents chain three probability-1 statements: S3 (Wbar got okb ⇒ F saw up), S2 (F saw up ⇒ Fbar saw t), S1 (Fbar saw
t ⇒ W gets fail) — and W gets ok in 1/12 of the runs. Hardy.lean already holds the rule "an unasked, non-commuting
question is Z"; this file adds the TIME the paradox needs and the two runs `fr.py` measured:

THE PHYSICS, exactly (unnormalised integer vectors, P = amp² / norms² as in Hardy.lean):
  `contradiction_run`   amp(okb ⊗ ok | Ψ) = 1 — P = 1/(2·2·3) = 1/12: the contested run happens;
  `s3_after_okb`        the state Wbar's okb leaves on L is ∝ |up⟩ — S3 still holds there;
  `s2_s1_after_okb`     on that state S2 and S1 hold with 1/2 only (|⟨t|okb⟩|²·2 = ‖okb‖², |⟨up|fail⟩|²·2 = ‖fail‖²);
  `copy_s3`             Fbar's record COPIED to an environment first: given okb, z = up has 1/3 only;
  `record_erased`       the record's projector and Wbar's question do not commute (`Hardy.incompatible`).

THE LOGIC (Hardy's V, Fm, evalF, Refines, Hereditary). Atoms: 0 Wbar got okb, 1 S3, 2 F saw up, 3 S2,
4 Fbar saw t, 5 S1; W's chain is their conjunction.
  `expired_never_earns` THE THEOREM: for EVERY marking in which Fbar's record has expired (atom 4 is Z), the chain is
                        not earned — some refinement makes it F. No conclusion is earned through an expired record.
  `paradox_open`        the run as `fr.py` grounds it (record expired; S2, S1 tied to it): F now, yet not refuted —
                        OPEN, the verdict ZTL gave;
  `copy_refuted`        with the copy, S3 is F by the physics: the chain is F along every refinement — REFUTED;
  `control_earned`      Wbar reads the record in its own basis: nothing expires, the chain is T, hereditary — EARNED.

PREMISE, said: that a record measured in a non-commuting basis EXPIRES is the rule (as Hardy.lean's "unasked ↦ Z") —
read off the commutator, not derived from the logic; the integer arithmetic and the logic are checked.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace ZFrauchiger

open Hardy
open Hardy.V

/-! ## The physics, in integers -/

/-- Ψ over (r: false = h, true = t) × (z: false = dn, true = up), every row written out. -/
def psiFR : Bool → Bool → S
  | false, false => one
  | false, true  => zero
  | true,  false => one
  | true,  true  => one

/-- okb = |h⟩ − |t⟩ ; ok = |dn⟩ − |up⟩ (unnormalised, norm² 2 each). -/
def okb : Bool → S
  | false => one
  | true  => neg1

def ok : Bool → S
  | false => one
  | true  => neg1

def fail : Bool → S
  | false => one
  | true  => one

/-- ⟨okb ⊗ ok | Ψ⟩. -/
def ampOkOk : S :=
  sadd (sadd (smul (smul (okb false) (ok false)) (psiFR false false))
             (smul (smul (okb false) (ok true))  (psiFR false true)))
       (sadd (smul (smul (okb true)  (ok false)) (psiFR true false))
             (smul (smul (okb true)  (ok true))  (psiFR true true)))

/-- The contested run happens: amp = 1, P = 1/12. -/
theorem contradiction_run : seq ampOkOk one = true := by decide

/-- The state Wbar's okb leaves on L: post(z) = Σ_r okb(r) Ψ(r, z). -/
def post (z : Bool) : S := sadd (smul (okb false) (psiFR false z)) (smul (okb true) (psiFR true z))

/-- S3 there: no amplitude on dn, a nonzero one on up — z = up with certainty. -/
theorem s3_after_okb : seq (post false) zero = true ∧ seq (post true) zero = false := by decide

/-- Squared magnitude of a signed integer (as a natural: (p − n)² = p² + n² − 2pn, here never negative). -/
def sq (x : S) : Nat := x.1 * x.1 + x.2 * x.2 - 2 * x.1 * x.2

/-- S2 and S1 on that state hold with 1/2 only: |okb(t)|²·2 = ‖okb‖², |fail(up)|²·2 = ‖fail‖². -/
theorem s2_s1_after_okb :
    sq (okb true) * 2 = sq (okb false) + sq (okb true) ∧
    sq (fail true) * 2 = sq (fail false) + sq (fail true) := by decide

/-- Fbar's record copied to E (e = r): Ψ_C(r, e, z) = Ψ(r, z) when e = r, else 0. Given okb on Lbar alone:
post_C(e, z) = Σ_r okb(r) Ψ_C(r, e, z). -/
def psiC : Bool → Bool → Bool → S
  | false, false, z => psiFR false z
  | true,  true,  z => psiFR true z
  | false, true,  _ => zero
  | true,  false, _ => zero

def postC (e z : Bool) : S := sadd (smul (okb false) (psiC false e z)) (smul (okb true) (psiC true e z))

/-- With the copy, S3 holds with 1/3 only: the up part of post_C has weight 1 of a total 3. -/
theorem copy_s3 :
    3 * (sq (postC false true) + sq (postC true true)) =
      sq (postC false false) + sq (postC false true) + sq (postC true false) + sq (postC true true) ∧
    (sq (postC false true) + sq (postC true true)) = 1 := by decide

/-- The record's projector P(t) and twice Wbar's projector 2P(okb) do not commute: Hardy's matrices. -/
theorem record_erased : meq (mmul pZ1 pXm2) (mmul pXm2 pZ1) = false := incompatible

/-! ## The logic -/

def chainFR : Fm :=
  .conj (.atom 0) (.conj (.atom 1) (.conj (.atom 2) (.conj (.atom 3) (.conj (.atom 4) (.atom 5)))))

def chainV (a b c d e f : V) : V := zand a (zand b (zand c (zand d (zand e f))))

theorem chain_eval (m : Marking) : evalF m chainFR = chainV (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) := rfl

/-- `m` with atom 4 (Fbar's record) set to F — a refinement of any marking where it was Z. -/
def kill4 (m : Marking) : Marking := fun n => if n = 4 then V.F else m n

theorem kill4_refines (m : Marking) (h : m 4 = V.Z) : Refines (kill4 m) m := by
  intro n hn
  unfold kill4
  cases Nat.decEq n 4 with
  | isTrue e => subst e; exact absurd h hn
  | isFalse e => rw [if_neg e]

/-- A conjunction with an F conjunct is F, whatever the rest. -/
theorem chainV_F5 (a b c d f : V) : chainV a b c d V.F f = V.F := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases f <;> rfl

/-- THE THEOREM: no conclusion is earned through an expired record. Whenever atom 4 is Z, the chain is not
earned: either it is F already, or the refinement `kill4` turns it F. -/
theorem expired_never_earns (m : Marking) (h : m 4 = V.Z) :
    ¬ (evalF m chainFR = V.T ∧ Hereditary chainFR m) := by
  intro ⟨hT, hH⟩
  have e := hH (kill4 m) (kill4_refines m h)
  rw [chain_eval, chain_eval] at e
  have k4 : kill4 m 4 = V.F := rfl
  rw [k4, chainV_F5] at e
  rw [chain_eval] at hT
  rw [hT] at e
  exact V.noConfusion e

/-- The run `fr.py` grounds at tick 15: Wbar got okb (T), S3 (T), F saw up (T); Fbar's record, S2, S1 expired (Z). -/
def paradox : Marking := fun n =>
  if n = 0 then V.T else if n = 1 then V.T else if n = 2 then V.T else V.Z

/-- OPEN: F now, and not refuted — the refinement with every expired atom T makes the chain T. -/
theorem paradox_open :
    evalF paradox chainFR = V.F ∧
    evalF (fun _ => V.T) chainFR = V.T ∧ Refines (fun _ => V.T) paradox := by
  refine ⟨by decide, by decide, ?_⟩
  intro n hn
  unfold paradox at hn ⊢
  cases Nat.decEq n 0 with
  | isTrue e => subst e; rfl
  | isFalse e0 =>
    cases Nat.decEq n 1 with
    | isTrue e => subst e; rfl
    | isFalse e1 =>
      cases Nat.decEq n 2 with
      | isTrue e => subst e; rfl
      | isFalse e2 => rw [if_neg e0, if_neg e1, if_neg e2] at hn; exact absurd rfl hn

/-- With the copy: S3 is F by the physics (`copy_s3`), the record stands (T), the rest T. -/
def copyRun : Marking := fun n => if n = 1 then V.F else V.T

/-- REFUTED: F along every refinement (no atom is Z, so every refinement is the run itself). -/
theorem copy_refuted : evalF copyRun chainFR = V.F ∧ Hereditary chainFR copyRun := by
  refine ⟨by decide, ?_⟩
  intro m' h
  have : ∀ n, m' n = copyRun n := by
    intro n
    apply h n
    unfold copyRun
    cases Nat.decEq n 1 with
    | isTrue e => subst e; exact V.noConfusion
    | isFalse e => rw [if_neg e]; exact V.noConfusion
  rw [chain_eval, chain_eval, this 0, this 1, this 2, this 3, this 4, this 5]

/-- The control: Wbar reads the record in its own basis — nothing expires; W's chain (record T, S1 T) is earned. -/
def controlChain : Fm := .conj (.atom 4) (.atom 5)

theorem control_earned : evalF (fun _ => V.T) controlChain = V.T ∧ Hereditary controlChain (fun _ => V.T) := by
  refine ⟨by decide, ?_⟩
  intro m' h
  have h4 : m' 4 = V.T := h 4 V.noConfusion
  have h5 : m' 5 = V.T := h 5 V.noConfusion
  show zand (m' 4) (m' 5) = zand V.T V.T
  rw [h4, h5]

end ZFrauchiger

#print axioms ZFrauchiger.contradiction_run
#print axioms ZFrauchiger.s3_after_okb
#print axioms ZFrauchiger.s2_s1_after_okb
#print axioms ZFrauchiger.copy_s3
#print axioms ZFrauchiger.record_erased
#print axioms ZFrauchiger.kill4_refines
#print axioms ZFrauchiger.chainV_F5
#print axioms ZFrauchiger.expired_never_earns
#print axioms ZFrauchiger.paradox_open
#print axioms ZFrauchiger.copy_refuted
#print axioms ZFrauchiger.control_earned
