import ZComposition
/-!
# ZLegion — no promotion without a witness, for grounds that EXPIRE and grounds that come from MANY AGENTS

Asked 2026-10-05 by the curator for Arkady (DARPA LEGION/ERIS), items 1 and 2 of his list; built on
`ZComposition.lean` (holes, composition witness, `no_promotion_without_witness`).

1. TIME AND REVOCATION. A checked ground carries an expiry; past it (or revoked) it reads Z again.
   * `expired_link_never_promoted` — if a joining atom has expired at time t and no act can re-check it, a
     conclusion with no composition witness is EARNED in no reachable future, however true the other facts stay;
   * `earned_not_persistent` — EARNED now does not carry over to later by itself (a ground expires);
   * `earned_persists_if_no_expiry` — it DOES carry over when no atom of the conclusion changed: the runtime
     needs to re-check a conclusion only when one of ITS atoms expires.
2. MANY AGENTS. Each agent holds its own marking; they are merged atom by atom — a value one agent checked
   is taken, two agents disagreeing read Z (a conflict is not a verification).
   * `merge_invents_nothing` — an atom no agent checked is Z in the merge;
   * `distributed_no_promotion` — a joining atom no agent checked, outside the repertoire, blocks promotion of a
     conclusion with no composition witness — whatever each agent has earned locally;
   * `local_facts_global_link` — the example: agent A has X earned, agent B has Y earned, and X ∧ Y ∧ link, with
     the link checked by nobody, is EARNED in no reachable future.

Zero axioms, audited at the bottom.
-/

namespace ZLegion

open ZComposition (V Fm Marking evalF evalB Refines Hereditary Earned Reachable NoWitness
  no_promotion_without_witness)

/-! ## Agreement on the atoms of a formula is enough -/

def occ (a : Nat) : Fm → Bool
  | .atom n   => Nat.beq n a
  | .neg φ    => occ a φ
  | .conj φ ψ => occ a φ || occ a ψ
  | .disj φ ψ => occ a φ || occ a ψ
  | .imp φ ψ  => occ a φ || occ a ψ

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

theorem or_true_left {x y : Bool} (h : x = true) : (x || y) = true := by rw [h]; rfl
theorem or_true_right {x y : Bool} (h : y = true) : (x || y) = true := by cases x <;> rw [h] <;> rfl

theorem evalF_congr (m m' : Marking) : ∀ φ, (∀ n, occ n φ = true → m n = m' n) → evalF m φ = evalF m' φ := by
  intro φ
  induction φ with
  | atom n => intro h; exact h n (beq_self n)
  | neg φ ih =>
      intro h
      show V.znot (evalF m φ) = V.znot (evalF m' φ)
      rw [ih h]
  | conj φ ψ ih1 ih2 =>
      intro h
      show V.zand (evalF m φ) (evalF m ψ) = V.zand (evalF m' φ) (evalF m' ψ)
      rw [ih1 (fun n hn => h n (or_true_left hn)), ih2 (fun n hn => h n (or_true_right hn))]
  | disj φ ψ ih1 ih2 =>
      intro h
      show V.zor (evalF m φ) (evalF m ψ) = V.zor (evalF m' φ) (evalF m' ψ)
      rw [ih1 (fun n hn => h n (or_true_left hn)), ih2 (fun n hn => h n (or_true_right hn))]
  | imp φ ψ ih1 ih2 =>
      intro h
      show V.zimp (evalF m φ) (evalF m ψ) = V.zimp (evalF m' φ) (evalF m' ψ)
      rw [ih1 (fun n hn => h n (or_true_left hn)), ih2 (fun n hn => h n (or_true_right hn))]

/-- EARNED depends only on the conclusion's own atoms. -/
theorem earned_congr (φ : Fm) (m m' : Marking) (hag : ∀ n, occ n φ = true → m' n = m n)
    (he : Earned φ m) : Earned φ m' := by
  refine ⟨(evalF_congr m' m φ hag).trans he.1, ?_⟩
  intro m'' href
  -- carry the refinement back to m: φ's atoms from m'', the rest from m
  let k : Marking := fun n => if occ n φ = true then m'' n else m n
  have hk_ref : Refines k m := by
    intro n hn
    show (if occ n φ = true then m'' n else m n) = m n
    cases ho : occ n φ with
    | true =>
        rw [if_pos rfl]
        have hn' : m' n ≠ V.Z := by rw [hag n ho]; exact hn
        rw [href n hn', hag n ho]
    | false => rw [if_neg (fun e => Bool.noConfusion e)]
  have hk_ag : ∀ n, occ n φ = true → m'' n = k n := by
    intro n ho
    show m'' n = (if occ n φ = true then m'' n else m n)
    rw [if_pos ho]
  rw [evalF_congr m'' k φ hk_ag, he.2 k hk_ref]
  exact (evalF_congr m' m φ hag).symm

/-! ## 1. Time and revocation -/

/-- A checked ground: its value and the time it stops counting (expiry or revocation). -/
structure Ground where
  val    : V
  expiry : Nat

/-- The marking at time t: a ground counts while t < its expiry; otherwise (or never checked) Z. -/
def markAt (g : Nat → Option Ground) (t : Nat) : Marking := fun n =>
  match g n with
  | Option.none   => V.Z
  | Option.some r => if t < r.expiry then r.val else V.Z

/-- **An expired link blocks promotion.** At time t, with no composition witness (the expired, un-recheckable
links among the holes), the conclusion is EARNED in no reachable future. -/
theorem expired_link_never_promoted (g : Nat → Option Ground) (t : Nat) (R : Nat → Bool) (φ : Fm)
    (hnw : NoWitness R (markAt g t) φ) : ∀ m', Reachable R (markAt g t) m' → ¬ Earned φ m' :=
  no_promotion_without_witness R (markAt g t) φ hnw

/-- One ground X (atom 0), checked T, valid until time 1. -/
def gX : Nat → Option Ground := fun n => if n = 0 then Option.some ⟨V.T, 1⟩ else Option.none

/-- **EARNED now is not EARNED later by itself**: X is earned at time 0 and not at time 1, when its ground
expired. The runtime must re-check. -/
theorem earned_not_persistent : Earned (.atom 0) (markAt gX 0) ∧ ¬ Earned (.atom 0) (markAt gX 1) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro m' h
    exact h 0 (by decide)
  · intro he
    have h1 : evalF (markAt gX 1) (.atom 0) = V.Z := rfl
    have h2 := he.1
    rw [h1] at h2
    exact V.noConfusion h2

/-- **…and it persists when none of ITS atoms changed**: if the marking at a later time agrees with the
earlier one on the conclusion's atoms, EARNED carries over. Re-check only on expiry of the conclusion's
own atoms. -/
theorem earned_persists_if_no_expiry (g : Nat → Option Ground) (t t' : Nat) (φ : Fm)
    (hsame : ∀ n, occ n φ = true → markAt g t' n = markAt g t n) (he : Earned φ (markAt g t)) :
    Earned φ (markAt g t') :=
  earned_congr φ (markAt g t) (markAt g t') hsame he

/-! ## 2. Many agents -/

/-- Merging two agents' values: one checked, the other not — take it; both checked and agree — take it;
both checked and disagree — Z (a conflict is not a verification). -/
def comb : V → V → V
  | V.Z, b   => b
  | V.T, V.Z => V.T
  | V.T, V.T => V.T
  | V.T, V.F => V.Z
  | V.F, V.Z => V.F
  | V.F, V.F => V.F
  | V.F, V.T => V.Z

def merge : List Marking → Marking
  | []      => fun _ => V.Z
  | m :: ms => fun n => comb (m n) (merge ms n)

theorem comb_ZZ : comb V.Z V.Z = V.Z := rfl

/-- **The merge invents nothing**: an atom no agent checked is Z in the merge. -/
theorem merge_invents_nothing : ∀ (ms : List Marking) (n : Nat), (∀ m, m ∈ ms → m n = V.Z) → merge ms n = V.Z := by
  intro ms
  induction ms with
  | nil => intro n _; rfl
  | cons m ms ih =>
      intro n h
      show comb (m n) (merge ms n) = V.Z
      rw [h m (List.Mem.head ms), ih n (fun m' hm' => h m' (List.Mem.tail m hm'))]
      rfl

/-- **Distributed: no promotion across a link nobody checked.** Whatever each agent earned locally, a
conclusion with no composition witness over the merged marking is EARNED in no reachable future. -/
theorem distributed_no_promotion (ms : List Marking) (R : Nat → Bool) (φ : Fm)
    (hnw : NoWitness R (merge ms) φ) : ∀ m', Reachable R (merge ms) m' → ¬ Earned φ m' :=
  no_promotion_without_witness R (merge ms) φ hnw

/-- Agent A checked X (atom 0); agent B checked Y (atom 1); nobody checked the link (atom 2). -/
def agentA : Marking := fun n => if n = 0 then V.T else V.Z
def agentB : Marking := fun n => if n = 1 then V.T else V.Z
def noRecheck : Nat → Bool := fun _ => false
def joined : Fm := .conj (.atom 0) (.conj (.atom 1) (.atom 2))

theorem local_earned : Earned (.atom 0) agentA ∧ Earned (.atom 1) agentB := by
  refine ⟨⟨rfl, fun m' h => h 0 (by decide)⟩, ⟨rfl, fun m' h => h 1 (by decide)⟩⟩

theorem merged_link_unchecked : merge [agentA, agentB] 2 = V.Z := rfl

theorem joined_no_witness : NoWitness noRecheck (merge [agentA, agentB]) joined := by
  intro b _ _
  refine ⟨fun n => if n = 2 then false else b n, ?_, ?_⟩
  · intro n hn
    show (if n = 2 then false else b n) = b n
    cases h2 : decide (n = 2) with
    | true =>
        have e : n = 2 := of_decide_eq_true h2
        exact absurd ⟨by rw [e]; rfl, rfl⟩ hn
    | false => rw [if_neg (of_decide_eq_false h2)]
  · show ((if 0 = 2 then false else b 0) && ((if 1 = 2 then false else b 1) && (if 2 = 2 then false else b 2)))
        = false
    cases b 0 <;> cases b 1 <;> rfl

/-- **The example, end to end**: X earned by agent A, Y earned by agent B, and X ∧ Y ∧ link — the link checked
by nobody and not re-checkable — is EARNED in no reachable future of the merged state. -/
theorem local_facts_global_link :
    (Earned (.atom 0) agentA ∧ Earned (.atom 1) agentB) ∧
    ∀ m', Reachable noRecheck (merge [agentA, agentB]) m' → ¬ Earned joined m' :=
  ⟨local_earned, distributed_no_promotion [agentA, agentB] noRecheck joined joined_no_witness⟩

end ZLegion

#print axioms ZLegion.evalF_congr
#print axioms ZLegion.earned_congr
#print axioms ZLegion.expired_link_never_promoted
#print axioms ZLegion.earned_not_persistent
#print axioms ZLegion.earned_persists_if_no_expiry
#print axioms ZLegion.merge_invents_nothing
#print axioms ZLegion.distributed_no_promotion
#print axioms ZLegion.local_earned
#print axioms ZLegion.joined_no_witness
#print axioms ZLegion.local_facts_global_link
