/-!
# ZBackward — the backward pass of `zbackward.py`: minimal sets of grounds. Zero axioms.

Written 2026-11-27 at the curator's word («Мы всегда делали ZTL судью так, что каждая его деталь теорема… пройдёмся,
проверим» → «Да» to starting with zbackward). Before this file `zbackward.py` had no Lean or Agda twin.

SETTING. The dirty grounds of a claim are numbered 0 … n-1. A SET of grounds is a mask `s : List Bool` of length n
(position i true = ground i is checked). A FILLING of s gives every checked ground a value T/F and leaves the others
dirty (`none`). The judge, read as an ORACLE `hits : List (Option Bool) → Bool`, says whether the target is reached in
the world of one filling; nothing here depends on what the oracle is.

  possible s   = SOME filling of s hits     «what to check so that the target becomes reachable»
  guaranteed s = EVERY filling of s hits    «what to check so that the target holds whatever the check shows»

The answer is the family of MINIMAL sets of a property P: P s, and no proper subset t ⊊ s has P t. `fam P n` is that
family by its definition — a filter of all 2^n masks. `zbackward.backward` computes it by a different route (sizes in
ascending order, a set kept when no smaller kept set lies inside it; or the tables, `zbackward_tree`); the two routes
are compared with `fam` by the kernel in `inventory/zbackward_lean_bridge.py`.

PROVED HERE:
1. `fam_antichain`        — no member of the family lies strictly inside another.
2. `fam_sound`            — every member has P and no proper subset with P (this is what "minimal" means).
3. `exists_minimal`       — every set with P CONTAINS a member of the family. So "the family is empty" means "no set
                            has P at all", and the size-ascending search is right to test only the kept sets: a proper
                            subset with P exists iff a kept one does. No monotonicity of P is needed — the judge's
                            outcome need not be monotone in the checks.
4. `guaranteed_possible`  — a guaranteed set is a possible one (a set has at least one filling).
   `guaranteed_has_possible` — so every minimal guaranteed set contains a minimal possible set.
5. `already_iff`          — if the empty set has P (the target is reached with no check), the family is exactly {∅}:
                            the Python answer "already, nothing to check".
6. `psub_iff`             — `psub` is proper inclusion: a subset with a strictly smaller count of checked grounds.

NOT CLAIMED: anything about the oracle — that `hits` is the judge is the bridge's job, not a theorem. Nor that the
search is fast (it is 3^n, `zbackward.CAP_*`).
-/

namespace ZBackward

/-- All masks of length n (2^n of them). -/
def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)

/-- s ⊆ t, pointwise, on masks of the same length. -/
def sub : List Bool → List Bool → Bool
  | [], [] => true
  | a :: s, b :: t => (!a || b) && sub s t
  | [], _ :: _ => false        -- no overlapping wildcard: it would compile with `propext` (SPEC, Lean pitfall)
  | _ :: _, [] => false

/-- How many grounds the mask checks. -/
def pop : List Bool → Nat
  | [] => 0
  | a :: s => (if a then 1 else 0) + pop s

/-- Proper inclusion: inside, and strictly fewer checked grounds (`psub_iff` shows it is t ⊊ s). -/
def psub (t s : List Bool) : Bool := sub t s && decide (pop t < pop s)

/-- s is minimal for P among the masks of length n. -/
def minimalB (P : List Bool → Bool) (n : Nat) (s : List Bool) : Bool :=
  P s && !((masks n).any fun t => psub t s && P t)

/-- THE FAMILY: the minimal sets of P, by definition. -/
def fam (P : List Bool → Bool) (n : Nat) : List (List Bool) := (masks n).filter (minimalB P n)

/-- The fillings of a mask: a value for every checked ground, `none` (dirty) elsewhere. -/
def fills : List Bool → List (List (Option Bool))
  | [] => [[]]
  | false :: s => (fills s).map (none :: ·)
  | true :: s => (fills s).map (some false :: ·) ++ (fills s).map (some true :: ·)

def possibleB (hits : List (Option Bool) → Bool) (s : List Bool) : Bool := (fills s).any hits
def guaranteedB (hits : List (Option Bool) → Bool) (s : List Bool) : Bool := (fills s).all hits

/-- The empty set of grounds, of length n. -/
def zeros : Nat → List Bool
  | 0 => []
  | n + 1 => false :: zeros n

/-! ## Bool and list bookkeeping, proved without `simp` (it pulls `propext`). -/

theorem and_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact ⟨rfl, rfl⟩

theorem any_exists {α} (p : α → Bool) : ∀ l : List α, l.any p = true → ∃ x, x ∈ l ∧ p x = true
  | [], h => Bool.noConfusion h
  | x :: l, h => by
      cases hx : p x
      · have h' : l.any p = true := by
          have e : (x :: l).any p = (p x || l.any p) := rfl
          rw [e, hx] at h; exact h
        obtain ⟨y, hy, py⟩ := any_exists p l h'
        exact ⟨y, List.Mem.tail _ hy, py⟩
      · exact ⟨x, List.Mem.head _, hx⟩

theorem any_of_mem {α} (p : α → Bool) {x : α} : ∀ {l : List α}, x ∈ l → p x = true → l.any p = true
  | _ :: l, List.Mem.head _, h => by
      have e : (x :: l).any p = (p x || l.any p) := rfl
      rw [e, h]; rfl
  | y :: l, List.Mem.tail _ hm, h => by
      have e : (y :: l).any p = (p y || l.any p) := rfl
      rw [e, any_of_mem p hm h]; cases p y <;> rfl

theorem all_of_mem {α} (p : α → Bool) {x : α} : ∀ {l : List α}, l.all p = true → x ∈ l → p x = true
  | y :: l, h, hm => by
      have e : (y :: l).all p = (p y && l.all p) := rfl
      rw [e] at h
      obtain ⟨h1, h2⟩ := and_split h
      cases hm with
      | head => exact h1
      | tail _ hm' => exact all_of_mem p h2 hm'

theorem mem_filter_l {α} (p : α → Bool) {x : α} : ∀ {l : List α}, x ∈ l.filter p → x ∈ l
  | y :: l, h => by
      unfold List.filter at h
      cases hy : p y
      · rw [hy] at h; exact List.Mem.tail _ (mem_filter_l p h)
      · rw [hy] at h
        cases h with
        | head => exact List.Mem.head _
        | tail _ h' => exact List.Mem.tail _ (mem_filter_l p h')

theorem mem_filter_p {α} (p : α → Bool) {x : α} : ∀ {l : List α}, x ∈ l.filter p → p x = true
  | y :: l, h => by
      unfold List.filter at h
      cases hy : p y
      · rw [hy] at h; exact mem_filter_p p h
      · rw [hy] at h
        cases h with
        | head => exact hy
        | tail _ h' => exact mem_filter_p p h'

theorem filter_of_mem {α} (p : α → Bool) {x : α} : ∀ {l : List α}, x ∈ l → p x = true → x ∈ l.filter p
  | y :: l, hm, hp => by
      unfold List.filter
      cases hy : p y
      · cases hm with
        | head => rw [hp] at hy; exact Bool.noConfusion hy
        | tail _ hm' => exact filter_of_mem p hm' hp
      · cases hm with
        | head => exact List.Mem.head _
        | tail _ hm' => exact List.Mem.tail _ (filter_of_mem p hm' hp)

theorem mem_append_l {α} {x : α} : ∀ {l₁ : List α} (l₂ : List α), x ∈ l₁ → x ∈ l₁ ++ l₂
  | _ :: _, _, List.Mem.head _ => List.Mem.head _
  | _ :: _, l₂, List.Mem.tail _ h => List.Mem.tail _ (mem_append_l l₂ h)

theorem mem_append_r {α} {x : α} : ∀ (l₁ : List α) {l₂ : List α}, x ∈ l₂ → x ∈ l₁ ++ l₂
  | [], _, h => h
  | _ :: l₁, _, h => List.Mem.tail _ (mem_append_r l₁ h)

theorem mem_map_of {α β} (f : α → β) {x : α} : ∀ {l : List α}, x ∈ l → f x ∈ l.map f
  | _ :: _, List.Mem.head _ => List.Mem.head _
  | _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_map_of f h)

/-- A member of `l.map f` is an image. -/
theorem mem_map_inv {α β} (f : α → β) {y : β} : ∀ {l : List α}, y ∈ l.map f → ∃ x, x ∈ l ∧ f x = y
  | x :: l, h => by
      cases h with
      | head => exact ⟨x, List.Mem.head _, rfl⟩
      | tail _ h' =>
          obtain ⟨z, hz, e⟩ := mem_map_inv f h'
          exact ⟨z, List.Mem.tail _ hz, e⟩

theorem mem_append_inv {α} {x : α} : ∀ {l₁ l₂ : List α}, x ∈ l₁ ++ l₂ → x ∈ l₁ ∨ x ∈ l₂
  | [], _, h => Or.inr h
  | _ :: _, _, List.Mem.head _ => Or.inl (List.Mem.head _)
  | _ :: l₁, _, List.Mem.tail _ h => by
      cases mem_append_inv (l₁ := l₁) h with
      | inl h' => exact Or.inl (List.Mem.tail _ h')
      | inr h' => exact Or.inr h'

/-! ## Inclusion -/

/-- Left cancellation, here because core's `Nat.add_left_cancel` carries `propext`. -/
theorem add_cancel : ∀ (k : Nat) {a b : Nat}, k + a = k + b → a = b
  | 0, a, b, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | k + 1, a, b, h => by
      rw [Nat.succ_add, Nat.succ_add] at h
      exact add_cancel k (Nat.succ.inj h)

theorem sub_refl : ∀ s : List Bool, sub s s = true
  | [] => rfl
  | a :: s => by
      show ((!a || a) && sub s s) = true
      rw [sub_refl s]; cases a <;> rfl

theorem sub_trans : ∀ (u t s : List Bool), sub u t = true → sub t s = true → sub u s = true
  | [], [], [], _, _ => rfl
  | a :: u, b :: t, c :: s, h1, h2 => by
      have e1 : sub (a :: u) (b :: t) = ((!a || b) && sub u t) := rfl
      have e2 : sub (b :: t) (c :: s) = ((!b || c) && sub t s) := rfl
      have e3 : sub (a :: u) (c :: s) = ((!a || c) && sub u s) := rfl
      rw [e1] at h1; rw [e2] at h2; rw [e3]
      obtain ⟨h1a, h1b⟩ := and_split h1
      obtain ⟨h2a, h2b⟩ := and_split h2
      rw [sub_trans u t s h1b h2b]
      cases a <;> cases b <;> cases c <;> first | rfl | exact Bool.noConfusion h1a | exact Bool.noConfusion h2a
  | [], [], _ :: _, _, h2 => Bool.noConfusion h2
  | [], _ :: _, _, h1, _ => Bool.noConfusion h1
  | _ :: _, [], _, h1, _ => Bool.noConfusion h1
  | _ :: _, _ :: _, [], _, h2 => Bool.noConfusion h2

theorem sub_pop_le : ∀ (t s : List Bool), sub t s = true → pop t ≤ pop s
  | [], [], _ => Nat.le_refl 0
  | a :: t, b :: s, h => by
      have e : sub (a :: t) (b :: s) = ((!a || b) && sub t s) := rfl
      rw [e] at h
      obtain ⟨ha, hb⟩ := and_split h
      have ih := sub_pop_le t s hb
      show (if a then 1 else 0) + pop t ≤ (if b then 1 else 0) + pop s
      cases a <;> cases b
      · exact Nat.add_le_add (Nat.le_refl 0) ih
      · exact Nat.add_le_add (Nat.zero_le 1) ih
      · exact Bool.noConfusion ha
      · exact Nat.add_le_add (Nat.le_refl 1) ih
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h

/-- Inside and the same count means equal. -/
theorem sub_pop_eq : ∀ (t s : List Bool), sub t s = true → pop t = pop s → t = s
  | [], [], _, _ => rfl
  | a :: t, b :: s, h, hp => by
      have e : sub (a :: t) (b :: s) = ((!a || b) && sub t s) := rfl
      rw [e] at h
      obtain ⟨ha, hb⟩ := and_split h
      have le := sub_pop_le t s hb
      have hp' : (if a then 1 else 0) + pop t = (if b then 1 else 0) + pop s := hp
      cases a <;> cases b
      · have := sub_pop_eq t s hb (add_cancel _ hp'); rw [this]
      · -- 0 + pop t = 1 + pop s with pop t ≤ pop s: impossible
        have h1 : 0 + pop t = 1 + pop s := hp'
        rw [Nat.zero_add, Nat.add_comm] at h1
        exact absurd (h1 ▸ le) (Nat.not_le_of_gt (Nat.lt_succ_self _))
      · exact Bool.noConfusion ha
      · have := sub_pop_eq t s hb (add_cancel _ hp'); rw [this]
  | [], _ :: _, h, _ => Bool.noConfusion h
  | _ :: _, [], h, _ => Bool.noConfusion h

/-- (6) `psub` is proper inclusion. -/
theorem psub_iff (t s : List Bool) : psub t s = true ↔ (sub t s = true ∧ t ≠ s) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := and_split h
    refine ⟨h1, fun e => ?_⟩
    rw [e] at h2
    exact Nat.lt_irrefl _ (of_decide_eq_true h2)
  · intro ⟨h1, hne⟩
    have le := sub_pop_le t s h1
    have lt : pop t < pop s := by
      cases Nat.lt_or_ge (pop t) (pop s) with
      | inl l => exact l
      | inr g => exact absurd (sub_pop_eq t s h1 (Nat.le_antisymm le g)) hne
    show (sub t s && decide (pop t < pop s)) = true
    rw [h1, decide_eq_true lt]; rfl

/-! ## The family -/

/-- (2) Members are minimal: P holds, and no proper subset among the masks has P. -/
theorem fam_sound (P : List Bool → Bool) (n : Nat) (s : List Bool) (h : s ∈ fam P n) :
    s ∈ masks n ∧ P s = true ∧ ∀ t, t ∈ masks n → psub t s = true → P t = false := by
  have hm := mem_filter_l _ h
  have hmin := mem_filter_p _ h
  have e : minimalB P n s = (P s && !((masks n).any fun t => psub t s && P t)) := rfl
  rw [e] at hmin
  obtain ⟨hP, hno⟩ := and_split hmin
  refine ⟨hm, hP, fun t ht hps => ?_⟩
  cases hPt : P t
  · rfl
  · have : ((masks n).any fun t => psub t s && P t) = true := by
      apply any_of_mem _ ht; rw [hps, hPt]; rfl
    rw [this] at hno; exact Bool.noConfusion hno

/-- (1) The family is an antichain. -/
theorem fam_antichain (P : List Bool → Bool) (n : Nat) (s t : List Bool)
    (hs : s ∈ fam P n) (ht : t ∈ fam P n) (hts : psub t s = true) : False := by
  obtain ⟨_, _, hno⟩ := fam_sound P n s hs
  obtain ⟨htm, hPt, _⟩ := fam_sound P n t ht
  rw [hno t htm hts] at hPt; exact Bool.noConfusion hPt

/-- (3) Every mask with P contains a member of the family. -/
theorem exists_minimal (P : List Bool → Bool) (n : Nat) :
    ∀ k s, pop s ≤ k → s ∈ masks n → P s = true → ∃ t, t ∈ fam P n ∧ sub t s = true := by
  intro k
  induction k with
  | zero =>
      intro s hk hm hP
      refine ⟨s, filter_of_mem _ hm ?_, sub_refl s⟩
      show (P s && !((masks n).any fun t => psub t s && P t)) = true
      rw [hP]
      cases hany : (masks n).any fun t => psub t s && P t
      · rfl
      · obtain ⟨t, _, ht⟩ := any_exists _ _ hany
        obtain ⟨hps, _⟩ := and_split ht
        obtain ⟨_, hlt⟩ := and_split hps
        exact absurd (Nat.lt_of_lt_of_le (of_decide_eq_true hlt) hk) (Nat.not_lt_zero _)
  | succ k ih =>
      intro s hk hm hP
      cases hmin : minimalB P n s
      · have e : minimalB P n s = (P s && !((masks n).any fun t => psub t s && P t)) := rfl
        rw [e, hP] at hmin
        have hany : ((masks n).any fun t => psub t s && P t) = true := by
          cases hh : (masks n).any fun t => psub t s && P t
          · rw [hh] at hmin; exact Bool.noConfusion hmin
          · rfl
        obtain ⟨t, htm, ht⟩ := any_exists _ _ hany
        obtain ⟨hps, hPt⟩ := and_split ht
        obtain ⟨hst, hlt⟩ := and_split hps
        have hk' : pop t ≤ k := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (of_decide_eq_true hlt) hk)
        obtain ⟨u, hu, hut⟩ := ih t hk' htm hPt
        exact ⟨u, hu, sub_trans u t s hut hst⟩
      · exact ⟨s, filter_of_mem _ hm hmin, sub_refl s⟩

/-- (3') The empty family means: no mask has P at all. -/
theorem fam_empty_none (P : List Bool → Bool) (n : Nat) (h : fam P n = []) :
    ∀ s, s ∈ masks n → P s = false := by
  intro s hm
  cases hP : P s
  · rfl
  · obtain ⟨t, ht, _⟩ := exists_minimal P n (pop s) s (Nat.le_refl _) hm hP
    rw [h] at ht; nomatch ht

/-! ## Possible and guaranteed -/

theorem fills_nonempty : ∀ s : List Bool, ∃ w, w ∈ fills s
  | [] => ⟨[], List.Mem.head _⟩
  | false :: s => by
      obtain ⟨w, hw⟩ := fills_nonempty s
      exact ⟨none :: w, mem_map_of _ hw⟩
  | true :: s => by
      obtain ⟨w, hw⟩ := fills_nonempty s
      exact ⟨some false :: w, mem_append_l _ (mem_map_of _ hw)⟩

/-- (4) A guaranteed set is a possible one. -/
theorem guaranteed_possible (hits : List (Option Bool) → Bool) (s : List Bool)
    (h : guaranteedB hits s = true) : possibleB hits s = true := by
  obtain ⟨w, hw⟩ := fills_nonempty s
  exact any_of_mem hits hw (all_of_mem hits h hw)

/-- (4') Every minimal guaranteed set contains a minimal possible set. -/
theorem guaranteed_has_possible (hits : List (Option Bool) → Bool) (n : Nat) (s : List Bool)
    (h : s ∈ fam (guaranteedB hits) n) : ∃ t, t ∈ fam (possibleB hits) n ∧ sub t s = true := by
  obtain ⟨hm, hg, _⟩ := fam_sound _ n s h
  exact exists_minimal (possibleB hits) n (pop s) s (Nat.le_refl _) hm (guaranteed_possible hits s hg)

/-! ## Already reached: the family is {∅} -/

theorem zeros_mem : ∀ n, zeros n ∈ masks n
  | 0 => List.Mem.head _
  | n + 1 => mem_append_l _ (mem_map_of _ (zeros_mem n))

theorem pop_zeros : ∀ n, pop (zeros n) = 0
  | 0 => rfl
  | n + 1 => by show 0 + pop (zeros n) = 0; rw [pop_zeros n]

theorem zeros_sub : ∀ n s, s ∈ masks n → sub (zeros n) s = true
  | 0, _, List.Mem.head _ => rfl
  | n + 1, s, h => by
      cases mem_append_inv h with
      | inl h' =>
          obtain ⟨t, ht, e⟩ := mem_map_inv _ h'
          rw [← e]; show ((!false || false) && sub (zeros n) t) = true; rw [zeros_sub n t ht]; rfl
      | inr h' =>
          obtain ⟨t, ht, e⟩ := mem_map_inv _ h'
          rw [← e]; show ((!false || true) && sub (zeros n) t) = true; rw [zeros_sub n t ht]; rfl

/-- (5) If the empty set already has P, the family is exactly {∅}. -/
theorem already_iff (P : List Bool → Bool) (n : Nat) (h0 : P (zeros n) = true) (s : List Bool) :
    s ∈ fam P n ↔ s = zeros n := by
  constructor
  · intro hs
    obtain ⟨hm, _, hno⟩ := fam_sound P n s hs
    have hsub := zeros_sub n s hm
    cases Nat.lt_or_ge 0 (pop s) with
    | inl hlt =>
        have hps : psub (zeros n) s = true := by
          show (sub (zeros n) s && decide (pop (zeros n) < pop s)) = true
          rw [hsub, pop_zeros n, decide_eq_true hlt]; rfl
        rw [hno (zeros n) (zeros_mem n) hps] at h0; exact Bool.noConfusion h0
    | inr hge =>
        exact (sub_pop_eq (zeros n) s hsub (by rw [pop_zeros n]; exact (Nat.le_antisymm hge (Nat.zero_le _)).symm)).symm
  · intro e
    rw [e]
    refine filter_of_mem _ (zeros_mem n) ?_
    show (P (zeros n) && !((masks n).any fun t => psub t (zeros n) && P t)) = true
    rw [h0]
    cases hany : (masks n).any fun t => psub t (zeros n) && P t
    · rfl
    · obtain ⟨t, _, ht⟩ := any_exists _ _ hany
      obtain ⟨hps, _⟩ := and_split ht
      obtain ⟨_, hlt⟩ := and_split hps
      have := of_decide_eq_true hlt
      rw [pop_zeros n] at this; exact absurd this (Nat.not_lt_zero _)

/-! ## The bridge's entry: families from an oracle given as a table. -/

/-- The oracle as data: the worlds where the target is hit (the bridge writes them from the Python judge). -/
def hitsOf (table : List (List (Option Bool))) (w : List (Option Bool)) : Bool := table.contains w

/-- The minimal sets as lists of ground indices, for printing. -/
def idx (s : List Bool) : List Nat := ((List.range s.length).zip s).filterMap fun p => if p.2 then some p.1 else none

def famIdx (P : List Bool → Bool) (n : Nat) : List (List Nat) := (fam P n).map idx

end ZBackward

open ZBackward in
example : famIdx (possibleB (hitsOf [[some true, some true]])) 2 = [[0, 1]] := by decide

#print axioms ZBackward.add_cancel
#print axioms ZBackward.and_split
#print axioms ZBackward.any_exists
#print axioms ZBackward.any_of_mem
#print axioms ZBackward.mem_filter_l
#print axioms ZBackward.mem_filter_p
#print axioms ZBackward.filter_of_mem
#print axioms ZBackward.sub_refl
#print axioms ZBackward.sub_trans
#print axioms ZBackward.sub_pop_le
#print axioms ZBackward.sub_pop_eq
#print axioms ZBackward.fam_sound
#print axioms ZBackward.fam_antichain
#print axioms ZBackward.exists_minimal
#print axioms ZBackward.fam_empty_none
#print axioms ZBackward.guaranteed_possible
#print axioms ZBackward.guaranteed_has_possible
#print axioms ZBackward.already_iff
#print axioms ZBackward.psub_iff
