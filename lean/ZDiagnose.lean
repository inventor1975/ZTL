import ZBackward

/-!
# ZDiagnose — `zdiagnose.py`: conflicts and diagnoses. Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема» (second hole after `ZBackward`).

`zdiagnose` asks which premises are suspect when a measurement refutes a law with stated inputs. Two families:

  CONFLICTS  the minimal sets of premises that, kept as stated, are refuted by the measurement. They are `fam conflict`
             of `ZBackward`, for the oracle "the numeric judge refutes the measurement on this box" — so soundness,
             antichain and completeness are `ZBackward.fam_sound / fam_antichain / exists_minimal`, for ANY oracle.
  DIAGNOSES  "every conflict has a false premise", written as the claim ⋀_c ⋁_{p∈c} ¬p over the premises as dirty atoms;
             its diagnoses are zbackward's POSSIBLE family for the target EARNED.

PROVED HERE: on that claim, a set H of premises can EARN it (some filling of H does) EXACTLY when H meets every conflict
(`possible_iff_hits`), so the diagnoses are the MINIMAL HITTING SETS of the conflicts (`diagnoses_are_hitting_sets`) —
Reiter's diagnoses (1987), here as a theorem about our encoding, not a runtime cross-check.

THE MODEL OF "EARNED" USED (`earnedW`): the claim is earned in a world iff every conflict has a premise FILLED false.
Why that is the judge's EARNED: a disjunct ¬p with p dirty is not forced (p read T makes it F) and a disjunct ¬p with p
filled T is F; only ¬p with p filled F is T, in every reading. That the Python judge agrees with `earnedW` is checked by
the kernel in `inventory/zbackward_lean_bridge.py` (the diagnoses part), not claimed here.
-/

namespace ZDiagnose
open ZBackward

/-- c and h share a checked position (masks of equal length; no overlapping wildcard — it brings `propext`). -/
def meets : List Bool → List Bool → Bool
  | [], [] => false
  | a :: c, b :: h => (a && b) || meets c h
  | [], _ :: _ => false
  | _ :: _, [] => false

/-- H is a hitting set: it meets every conflict. -/
def hitsAll (cs : List (List Bool)) (h : List Bool) : Bool := cs.all fun c => meets c h

/-- The conflict c has a premise filled false in the world w. -/
def hasF : List Bool → List (Option Bool) → Bool
  | [], [] => false
  | a :: c, x :: w => (a && x == some false) || hasF c w
  | [], _ :: _ => false
  | _ :: _, [] => false

/-- The claim ⋀_c ⋁_{p∈c} ¬p is earned in w: every conflict has a premise filled false. -/
def earnedW (cs : List (List Bool)) (w : List (Option Bool)) : Bool := cs.all fun c => hasF c w

/-- The all-false filling of h. -/
def allF : List Bool → List (Option Bool)
  | [] => []
  | false :: h => none :: allF h
  | true :: h => some false :: allF h

theorem allF_mem : ∀ h : List Bool, allF h ∈ fills h
  | [] => List.Mem.head _
  | false :: h => mem_map_of _ (allF_mem h)
  | true :: h => mem_append_l _ (mem_map_of _ (allF_mem h))

theorem or_split {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

/-- If c meets h, the all-false filling of h has a false premise in c. -/
theorem meets_hasF : ∀ (c h : List Bool), meets c h = true → hasF c (allF h) = true
  | [], [], e => Bool.noConfusion e
  | a :: c, b :: h, e => by
      have e1 : meets (a :: c) (b :: h) = ((a && b) || meets c h) := rfl
      rw [e1] at e
      cases b
      · have e2 : hasF (a :: c) (allF (false :: h)) = ((a && (none == some false)) || hasF c (allF h)) := rfl
        rw [e2]
        cases or_split e with
        | inl hab => cases a <;> exact Bool.noConfusion hab
        | inr hm => rw [meets_hasF c h hm]; cases a <;> rfl
      · have e2 : hasF (a :: c) (allF (true :: h)) = ((a && (some false == some false)) || hasF c (allF h)) := rfl
        rw [e2]
        cases or_split e with
        | inl hab => cases a
                     · exact Bool.noConfusion hab
                     · rfl
        | inr hm => rw [meets_hasF c h hm]; cases a <;> rfl
  | [], _ :: _, e => Bool.noConfusion e
  | _ :: _, [], e => Bool.noConfusion e

/-- A false premise of c in a filling of h lies in h. -/
theorem hasF_meets : ∀ (c h : List Bool) (w : List (Option Bool)), w ∈ fills h → hasF c w = true → meets c h = true
  | [], [], w, hw, e => by
      cases hw with
      | head => exact Bool.noConfusion e
      | tail _ t => nomatch t
  | a :: c, false :: h, w, hw, e => by
      obtain ⟨u, hu, rfl⟩ := mem_map_inv _ hw
      have e1 : hasF (a :: c) (none :: u) = ((a && (none == some false)) || hasF c u) := rfl
      rw [e1] at e
      have e3 : meets (a :: c) (false :: h) = ((a && false) || meets c h) := rfl
      rw [e3]
      cases or_split e with
      | inl hab => cases a <;> exact Bool.noConfusion hab
      | inr hm => rw [hasF_meets c h u hu hm]; cases a <;> rfl
  | a :: c, true :: h, w, hw, e => by
      have e3 : meets (a :: c) (true :: h) = ((a && true) || meets c h) := rfl
      rw [e3]
      cases mem_append_inv hw with
      | inl h1 =>
          obtain ⟨u, hu, rfl⟩ := mem_map_inv _ h1
          have e1 : hasF (a :: c) (some false :: u) = ((a && (some false == some false)) || hasF c u) := rfl
          rw [e1] at e
          cases a
          · rw [hasF_meets c h u hu e]; rfl
          · rfl
      | inr h1 =>
          obtain ⟨u, hu, rfl⟩ := mem_map_inv _ h1
          have e1 : hasF (a :: c) (some true :: u) = ((a && (some true == some false)) || hasF c u) := rfl
          rw [e1] at e
          have hm : hasF c u = true := by cases a <;> exact e
          rw [hasF_meets c h u hu hm]; cases a <;> rfl
  | [], false :: h, w, hw, e => by
      obtain ⟨u, _, rfl⟩ := mem_map_inv _ hw
      exact Bool.noConfusion e
  | [], true :: h, w, hw, e => by
      cases mem_append_inv hw with
      | inl h1 =>
          obtain ⟨u, _, rfl⟩ := mem_map_inv _ h1
          exact Bool.noConfusion e
      | inr h1 =>
          obtain ⟨u, _, rfl⟩ := mem_map_inv _ h1
          exact Bool.noConfusion e
  | _ :: _, [], w, hw, e => by
      cases hw with
      | head => exact Bool.noConfusion e
      | tail _ t => nomatch t

theorem all_true {α} (p : α → Bool) : ∀ (l : List α), (∀ x, x ∈ l → p x = true) → l.all p = true
  | [], _ => rfl
  | x :: l, h => by
      have e : (x :: l).all p = (p x && l.all p) := rfl
      rw [e, h x (List.Mem.head _), all_true p l (fun y hy => h y (List.Mem.tail _ hy))]; rfl

/-- (1) A set of premises can earn the claim iff it meets every conflict. -/
theorem possible_iff_hits (cs : List (List Bool)) (h : List Bool) :
    possibleB (earnedW cs) h = hitsAll cs h := by
  cases hh : hitsAll cs h
  · cases hp : possibleB (earnedW cs) h
    · rfl
    · obtain ⟨w, hw, he⟩ := any_exists _ _ hp
      have : hitsAll cs h = true :=
        all_true _ cs (fun c hc => hasF_meets c h w hw (all_of_mem (fun c => hasF c w) he hc))
      rw [hh] at this; exact Bool.noConfusion this
  · exact any_of_mem _ (allF_mem h) (all_true _ cs (fun c hc => meets_hasF c h (all_of_mem (fun c => meets c h) hh hc)))

theorem filter_congr {α} (p q : α → Bool) (e : ∀ x, p x = q x) : ∀ l : List α, l.filter p = l.filter q
  | [] => rfl
  | x :: l => by
      unfold List.filter
      rw [e x, filter_congr p q e l]

theorem any_congr {α} (p q : α → Bool) (e : ∀ x, p x = q x) : ∀ l : List α, l.any p = l.any q
  | [] => rfl
  | x :: l => by
      have e1 : (x :: l).any p = (p x || l.any p) := rfl
      have e2 : (x :: l).any q = (q x || l.any q) := rfl
      rw [e1, e2, e x, any_congr p q e l]

/-- The family depends only on the property, pointwise. -/
theorem fam_congr (P Q : List Bool → Bool) (n : Nat) (e : ∀ s, P s = Q s) : fam P n = fam Q n := by
  unfold fam
  apply filter_congr
  intro s
  unfold minimalB
  rw [e s, any_congr _ _ (fun t => by rw [e t]) (masks n)]

/-- (2) THE DIAGNOSES ARE THE MINIMAL HITTING SETS of the conflicts. -/
theorem diagnoses_are_hitting_sets (cs : List (List Bool)) (n : Nat) :
    fam (possibleB (earnedW cs)) n = fam (hitsAll cs) n :=
  fam_congr _ _ n (possible_iff_hits cs)

/-- All worlds of n grounds (each dirty, or filled false/true) — for the bridge. -/
def worlds : Nat → List (List (Option Bool))
  | 0 => [[]]
  | n + 1 => (worlds n).map (none :: ·) ++ (worlds n).map (some false :: ·) ++ (worlds n).map (some true :: ·)

end ZDiagnose

#print axioms ZDiagnose.allF_mem
#print axioms ZDiagnose.or_split
#print axioms ZDiagnose.all_true
#print axioms ZDiagnose.filter_congr
#print axioms ZDiagnose.any_congr
#print axioms ZDiagnose.meets_hasF
#print axioms ZDiagnose.hasF_meets
#print axioms ZDiagnose.possible_iff_hits
#print axioms ZDiagnose.fam_congr
#print axioms ZDiagnose.diagnoses_are_hitting_sets
