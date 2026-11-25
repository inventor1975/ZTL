import ZSets

/-!
# ZCard — the cardinality interval is FORCED, not chosen. Zero axioms. (2026-11-25)

`ZSets` gives the cardinality of a collection with dirty identity as an interval: `k` verified, pairwise distinct
elements (the core) and `q` marked ones (identity unverified) have |S| = [cardLo k q, cardHi k q], with
cardLo = k (or min q 1 when k = 0) and cardHi = k + q.  There it is a DEFINITION with examples.

Here it is a theorem, in the shape of ZTL's generating principle (a verdict is what is forced under every reading).
A READING of the marked elements says what each of them really is: a label (a list `r` of length q); the core is
named by distinct labels.  The count under a reading is the number of distinct labels.

    card_sound     every reading gives a count inside [cardLo, cardHi];
    card_tight     every value in [cardLo, cardHi] is the count of some reading (both ends included);
    single_mark    |{Z}| = 1 under EVERY reading — the number is earned although no identity is
                   (`ZQuasi`: the count of acts against the count of objects);
    two_marks      |{Z, Z}| is 1 under one reading and 2 under another — "two" is not earned.

So the interval is exactly the set of counts the unverified identities leave open: nothing is added, nothing
excluded.  Reading for the propext line: cardinality is where classical mathematics uses extensionality to turn
"same members" into "same number".  With unverified identity the number does not collapse to Z — it is a
forced interval, and it collapses to a point exactly when the readings agree (q = 0, or k = 0 and q = 1).

NOT NEW MATHEMATICS: elementary counting.  New is only that ZSets' interval is now proved to be the forced
verdict, not a stipulation.
-/

namespace ZCard

/-- Membership of a label, by decidable equality (no Bool lemmas, no simp). -/
def memB (a : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => if a = x then true else memB a xs

/-- Number of distinct labels. -/
def ndist : List Nat → Nat
  | [] => 0
  | x :: xs => if memB x xs = true then ndist xs else ndist xs + 1

/-- Pairwise distinct labels. -/
def Nodup : List Nat → Prop
  | [] => True
  | x :: xs => memB x xs = false ∧ Nodup xs

theorem ndist_nodup : ∀ l : List Nat, Nodup l → ndist l = l.length
  | [], _ => rfl
  | x :: xs, ⟨h, hs⟩ => by
    show (if memB x xs = true then ndist xs else ndist xs + 1) = xs.length + 1
    rw [if_neg (fun e => Bool.noConfusion (h.symm.trans e)), ndist_nodup xs hs]

theorem ndist_cons_ge (x : Nat) (xs : List Nat) : ndist xs ≤ ndist (x :: xs) := by
  show ndist xs ≤ (if memB x xs = true then ndist xs else ndist xs + 1)
  by_cases h : memB x xs = true
  · rw [if_pos h]; exact Nat.le_refl _
  · rw [if_neg h]; exact Nat.le_succ _

theorem ndist_cons_le (x : Nat) (xs : List Nat) : ndist (x :: xs) ≤ ndist xs + 1 := by
  show (if memB x xs = true then ndist xs else ndist xs + 1) ≤ ndist xs + 1
  by_cases h : memB x xs = true
  · rw [if_pos h]; exact Nat.le_succ _
  · rw [if_neg h]; exact Nat.le_refl _

/-- A label that occurs means at least one distinct label. -/
theorem one_le_of_mem : ∀ (xs : List Nat) (x : Nat), memB x xs = true → 1 ≤ ndist xs
  | [], _, h => Bool.noConfusion h
  | y :: ys, _, _ => by
    show 1 ≤ (if memB y ys = true then ndist ys else ndist ys + 1)
    by_cases h : memB y ys = true
    · rw [if_pos h]; exact one_le_of_mem ys y h
    · rw [if_neg h]; exact Nat.succ_le_succ (Nat.zero_le _)

theorem one_le_cons (x : Nat) (xs : List Nat) : 1 ≤ ndist (x :: xs) := by
  show 1 ≤ (if memB x xs = true then ndist xs else ndist xs + 1)
  by_cases h : memB x xs = true
  · rw [if_pos h]; exact one_le_of_mem xs x h
  · rw [if_neg h]; exact Nat.succ_le_succ (Nat.zero_le _)

/-- Marked elements in front of the core never lower the count. -/
theorem ndist_append_ge : ∀ (r c : List Nat), ndist c ≤ ndist (r ++ c)
  | [], _ => Nat.le_refl _
  | x :: xs, c => Nat.le_trans (ndist_append_ge xs c) (ndist_cons_ge x (xs ++ c))

/-- …and raise it by at most one each. -/
theorem ndist_append_le : ∀ (r c : List Nat), ndist (r ++ c) ≤ r.length + ndist c
  | [], c => by show ndist c ≤ 0 + ndist c; rw [Nat.zero_add]; exact Nat.le_refl _
  | x :: xs, c => by
    show ndist (x :: (xs ++ c)) ≤ (xs.length + 1) + ndist c
    rw [Nat.add_right_comm]
    exact Nat.le_trans (ndist_cons_le x (xs ++ c)) (Nat.succ_le_succ (ndist_append_le xs c))

theorem min_succ_one (n : Nat) : min (n + 1) 1 ≤ 1 := by
  show (if n + 1 ≤ 1 then n + 1 else 1) ≤ 1
  by_cases h : n + 1 ≤ 1
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Nat.le_refl 1

/-- **Soundness**: under every reading `r` of the `q` marked elements, the count of `S = r ++ core` lies in
ZSets' interval. -/
theorem card_sound (c r : List Nat) (hc : Nodup c) :
    V.cardLo c.length r.length ≤ ndist (r ++ c) ∧ ndist (r ++ c) ≤ V.cardHi c.length r.length := by
  have hk : ndist c = c.length := ndist_nodup c hc
  refine ⟨?_, ?_⟩
  · cases c with
    | nil =>
      show (if 0 = 0 then min r.length 1 else 0) ≤ ndist (r ++ [])
      rw [if_pos rfl]
      cases r with
      | nil => exact Nat.zero_le _
      | cons x xs =>
        show min (xs.length + 1) 1 ≤ ndist (x :: (xs ++ []))
        exact Nat.le_trans (min_succ_one xs.length) (one_le_cons x (xs ++ []))
    | cons y ys =>
      show (if (ys.length + 1) = 0 then min r.length 1 else ys.length + 1) ≤ ndist (r ++ y :: ys)
      rw [if_neg (fun e => Nat.noConfusion e)]
      have := ndist_append_ge r (y :: ys)
      rw [hk] at this
      exact this
  · show ndist (r ++ c) ≤ c.length + r.length
    have := ndist_append_le r c
    rw [hk, Nat.add_comm] at this
    exact this

/-! ## Tightness, on the canonical core 0, 1, …, k−1 (labels are names; any core is a renaming of it) -/

/-- The core `[k−1, …, 1, 0]`. -/
def down : Nat → List Nat
  | 0 => []
  | n + 1 => n :: down n

/-- Fresh labels `[k+j−1, …, k]`. -/
def fresh (k : Nat) : Nat → List Nat
  | 0 => []
  | j + 1 => (k + j) :: fresh k j

theorem length_down : ∀ n, (down n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (length_down n)

theorem length_fresh (k : Nat) : ∀ j, (fresh k j).length = j
  | 0 => rfl
  | j + 1 => congrArg Nat.succ (length_fresh k j)

theorem fresh_down (k : Nat) : ∀ j, fresh k j ++ down k = down (k + j)
  | 0 => rfl
  | j + 1 => congrArg ((k + j) :: ·) (fresh_down k j)

/-- Labels at or above `n` are not in `down n`. -/
theorem memB_down_ge : ∀ (n m : Nat), n ≤ m → memB m (down n) = false
  | 0, _, _ => rfl
  | n + 1, m, h => by
    show (if m = n then true else memB m (down n)) = false
    rw [if_neg (fun e => Nat.lt_irrefl n (by rw [e] at h; exact h)), memB_down_ge n m (Nat.le_of_succ_le h)]

theorem nodup_down : ∀ n, Nodup (down n)
  | 0 => trivial
  | n + 1 => ⟨memB_down_ge n n (Nat.le_refl n), nodup_down n⟩

theorem memB_zero_down : ∀ n, memB 0 (down (n + 1)) = true
  | 0 => rfl
  | n + 1 => by
    show (if 0 = n + 1 then true else memB 0 (down (n + 1))) = true
    rw [if_neg (fun e => Nat.noConfusion e), memB_zero_down n]

def rep (a : Nat) : Nat → List Nat
  | 0 => []
  | m + 1 => a :: rep a m

theorem length_rep (a : Nat) : ∀ m, (rep a m).length = m
  | 0 => rfl
  | m + 1 => congrArg Nat.succ (length_rep a m)

/-- Copies of an existing label do not change the count. -/
theorem ndist_rep {a : Nat} {l : List Nat} : ∀ m, memB a l = true → ndist (rep a m ++ l) = ndist l
  | 0, _ => rfl
  | m + 1, h => by
    have hm : memB a (rep a m ++ l) = true := by
      cases m with
      | zero => exact h
      | succ m' =>
        show (if a = a then true else memB a (rep a m' ++ l)) = true
        rw [if_pos rfl]
    show (if memB a (rep a m ++ l) = true then ndist (rep a m ++ l) else ndist (rep a m ++ l) + 1) = ndist l
    rw [if_pos hm, ndist_rep m h]

theorem append_assoc' : ∀ (a b c : List Nat), (a ++ b) ++ c = a ++ (b ++ c)
  | [], _, _ => rfl
  | x :: xs, b, c => congrArg (x :: ·) (append_assoc' xs b c)

theorem length_append' : ∀ (a b : List Nat), (a ++ b).length = a.length + b.length
  | [], b => by show b.length = 0 + b.length; rw [Nat.zero_add]
  | x :: xs, b => by
    show (xs ++ b).length + 1 = (xs.length + 1) + b.length
    rw [length_append' xs b, Nat.add_right_comm]

/-- **Tightness**: with `k` core and `q = m + j` marked elements, the count `k + j` is attained by a reading —
`j` marked ones are new, the other `m` are the core's first element (or, when the core is empty, one of the new
ones: the side condition `m = 0 ∨ 1 ≤ k + j` says there is something to be identified with). -/
theorem card_tight (k m j : Nat) (h : m = 0 ∨ 1 ≤ k + j) :
    ∃ r : List Nat, r.length = m + j ∧ ndist (r ++ down k) = k + j := by
  refine ⟨rep 0 m ++ fresh k j, ?_, ?_⟩
  · rw [length_append', length_rep, length_fresh]
  · rw [append_assoc', fresh_down]
    have hd : ndist (down (k + j)) = k + j := by
      rw [ndist_nodup _ (nodup_down _), length_down]
    cases h with
    | inl hm => subst hm; exact hd
    | inr hp =>
      cases hkj : k + j with
      | zero => rw [hkj] at hp; exact absurd hp (Nat.not_succ_le_zero 0)
      | succ n =>
        rw [ndist_rep m (memB_zero_down n), ← hkj]
        exact hd

/-- Both ends of the interval are attained: the top (every marked element new)… -/
theorem card_hi_attained (k q : Nat) : ∃ r : List Nat, r.length = q ∧ ndist (r ++ down k) = V.cardHi k q := by
  obtain ⟨r, hl, hn⟩ := card_tight k 0 q (.inl rfl)
  exact ⟨r, by rw [hl, Nat.zero_add], hn⟩

/-- …and the bottom with a nonempty core (every marked element one of the core). -/
theorem card_lo_attained (k q : Nat) (hk : 1 ≤ k) :
    ∃ r : List Nat, r.length = q ∧ ndist (r ++ down k) = V.cardLo k q := by
  obtain ⟨r, hl, hn⟩ := card_tight k q 0 (.inr hk)
  refine ⟨r, hl, ?_⟩
  cases k with
  | zero => exact absurd hk (Nat.not_succ_le_zero 0)
  | succ k' =>
    show ndist (r ++ down (k' + 1)) = (if k' + 1 = 0 then min q 1 else k' + 1)
    rw [if_neg (fun e => Nat.noConfusion e)]
    exact hn

/-- **|{Z}| = 1 under every reading**: one unverified element is one, whatever it is. The number is earned
although its identity is not. -/
theorem single_mark (r : List Nat) (h : r.length = 1) : ndist r = 1 := by
  cases r with
  | nil => exact Nat.noConfusion h
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => exact absurd (Nat.succ.inj h) (fun e => Nat.noConfusion e)

/-- **|{Z, Z}| is not earned**: one reading counts one, another counts two. -/
theorem two_marks : ndist [0, 0] = 1 ∧ ndist [1, 0] = 2 := ⟨rfl, rfl⟩

end ZCard

#print axioms ZCard.ndist_nodup
#print axioms ZCard.ndist_append_ge
#print axioms ZCard.ndist_append_le
#print axioms ZCard.min_succ_one
#print axioms ZCard.card_sound
#print axioms ZCard.nodup_down
#print axioms ZCard.ndist_rep
#print axioms ZCard.card_tight
#print axioms ZCard.card_hi_attained
#print axioms ZCard.card_lo_attained
#print axioms ZCard.single_mark
#print axioms ZCard.two_marks
