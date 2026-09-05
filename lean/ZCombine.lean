/-
  ZCombine.lean — E39: COMBINATION IS INTERSECTION, AND ZADEH IS A THEOREM.

  §20 states three things and measures them on worked scenarios. Here they
  are proved.

    1. COMBINATION IS INTERSECTION, and VERIFICATION IS A SPECIAL CASE of it —
       checking a value against prior evidence is combining with the singleton
       [v,v]. One operation, not two. The honest side effect §20 names follows
       at once: the act of checking can itself EARN a conflict, when the
       checked value lies outside what was already known.

    2. AN EMPTY INTERSECTION IS AN EARNED CONTRADICTION OF SOURCES, not noise
       to be normalised away. Proved in the form that makes "earned" mean
       something: if the meet is empty then NO value whatever satisfies both
       constraints — the refutation holds under every reading, which is
       exactly soundness.

    3. ZADEH'S PARADOX (1984), AS A THEOREM RATHER THAN AN ANECDOTE. Two
       doctors each give a tumour one part in a hundred and disagree entirely
       about the rest. Dempster's rule discards the conflict and renormalises;
       what survives is one part in ten thousand, on the tumour alone. By the
       threshold theorem of `ZDempster` — OUR theorem, applied to THEIR
       combined mass — the verdict is then T. An unshakable certainty
       manufactured from two one-percent opinions, and the machine says so.

       Our side retains the conflict instead of dividing it away, and the
       retained assignment is then IMPROPER — the conflict sits on the empty
       focal, `m(∅) = 9999` of 10000. That is proved too, and it is the
       refusal: no verdict is issued, and the reason is exhibited rather than
       normalised.

  WHY 3 IS WORTH THE TROUBLE. It is not a criticism of Dempster from outside.
  The certainty is derived INSIDE our own machinery, from their rule, by the
  theorem we proved for their theory an hour earlier. A twin that can be
  turned against its own worked example is a twin that was formalised, not
  admired.

  ФОРМА. Никаких дробей: пороги масштабно-свободны, поэтому веса — целые, и
  нормировка Демпстера выражается ОТБРАСЫВАНИЕМ конфликтной массы, а не
  делением. Развилки по `Nat.beq`, не по образцам с подстановочным `_`.
-/
import ZDempster

namespace ZCombine

open V

/-! ### 1. Constraints, and combination as their meet -/

structure Iv where
  lo : Nat
  hi : Nat

def inIv (a : Iv) (v : Nat) : Prop := a.lo ≤ v ∧ v ≤ a.hi

def mx (a b : Nat) : Nat := match Nat.ble a b with | true => b | false => a
def mn (a b : Nat) : Nat := match Nat.ble a b with | true => a | false => b

/-- Combination of two pieces of evidence about one value: the intersection
of the constraints, or nothing when they cannot both hold. -/
def meet (a b : Iv) : Option Iv :=
  match Nat.ble (mx a.lo b.lo) (mn a.hi b.hi) with
  | true  => some ⟨mx a.lo b.lo, mn a.hi b.hi⟩
  | false => none

theorem le_of_ble : ∀ (a b : Nat), Nat.ble a b = true → a ≤ b
  | 0,     b,     _ => Nat.zero_le b
  | _ + 1, 0,     h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (le_of_ble a b h)

theorem lt_of_ble_false : ∀ (a b : Nat), Nat.ble a b = false → b < a
  | 0,     _,     h => Bool.noConfusion h
  | _ + 1, 0,     _ => Nat.succ_le_succ (Nat.zero_le _)
  | a + 1, b + 1, h => Nat.succ_le_succ (lt_of_ble_false a b h)

theorem ble_false_of_lt : ∀ (a b : Nat), b < a → Nat.ble a b = false
  | 0,     _,     h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0,     _ => rfl
  | a + 1, b + 1, h => ble_false_of_lt a b (Nat.lt_of_succ_lt_succ h)

theorem ble_true_of_le : ∀ (a b : Nat), a ≤ b → Nat.ble a b = true
  | 0,     _,     _ => rfl
  | a + 1, 0,     h => absurd h (Nat.not_succ_le_zero a)
  | a + 1, b + 1, h => ble_true_of_le a b (Nat.le_of_succ_le_succ h)

theorem mx_le : ∀ (a b c : Nat), a ≤ c → b ≤ c → mx a b ≤ c := by
  intro a b c ha hb
  show (match Nat.ble a b with | true => b | false => a) ≤ c
  cases Nat.ble a b with
  | true  => exact hb
  | false => exact ha

theorem le_mx_left (a b : Nat) : a ≤ mx a b := by
  show a ≤ (match Nat.ble a b with | true => b | false => a)
  cases h : Nat.ble a b with
  | true  => exact le_of_ble a b h
  | false => exact Nat.le_refl a

theorem le_mx_right (a b : Nat) : b ≤ mx a b := by
  show b ≤ (match Nat.ble a b with | true => b | false => a)
  cases h : Nat.ble a b with
  | true  => exact Nat.le_refl b
  | false => exact Nat.le_of_lt (lt_of_ble_false a b h)

theorem mn_le_left (a b : Nat) : mn a b ≤ a := by
  show (match Nat.ble a b with | true => a | false => b) ≤ a
  cases h : Nat.ble a b with
  | true  => exact Nat.le_refl a
  | false => exact Nat.le_of_lt (lt_of_ble_false a b h)

theorem mn_le_right (a b : Nat) : mn a b ≤ b := by
  show (match Nat.ble a b with | true => a | false => b) ≤ b
  cases h : Nat.ble a b with
  | true  => exact le_of_ble a b h
  | false => exact Nat.le_refl b

theorem le_mn : ∀ (a b c : Nat), c ≤ a → c ≤ b → c ≤ mn a b := by
  intro a b c ha hb
  show c ≤ (match Nat.ble a b with | true => a | false => b)
  cases Nat.ble a b with
  | true  => exact ha
  | false => exact hb

/-- **COMBINATION IS INTERSECTION.** When the meet exists, its members are
exactly the values both sources allow. -/
theorem meet_is_intersection (a b c : Iv) (h : meet a b = some c) :
    ∀ v, inIv c v ↔ (inIv a v ∧ inIv b v) := by
  have hc : c = ⟨mx a.lo b.lo, mn a.hi b.hi⟩ := by
    unfold meet at h
    cases hb : Nat.ble (mx a.lo b.lo) (mn a.hi b.hi) with
    | true =>
        rw [hb] at h
        exact (Option.some.inj h).symm
    | false =>
        rw [hb] at h
        cases h
  intro v
  rw [hc]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨⟨Nat.le_trans (le_mx_left a.lo b.lo) h1,
            Nat.le_trans h2 (mn_le_left a.hi b.hi)⟩,
           ⟨Nat.le_trans (le_mx_right a.lo b.lo) h1,
            Nat.le_trans h2 (mn_le_right a.hi b.hi)⟩⟩
  · intro ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
    exact ⟨mx_le a.lo b.lo v ha1 hb1, le_mn a.hi b.hi v ha2 hb2⟩

/-- **AN EMPTY MEET IS AN EARNED CONTRADICTION.** Not a default deny: NO
value whatever satisfies both sources, so the refutation holds under every
reading. -/
theorem meet_none_is_earned (a b : Iv) (h : meet a b = none) :
    ∀ v, ¬(inIv a v ∧ inIv b v) := by
  intro v ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
  have hlt : mn a.hi b.hi < mx a.lo b.lo := by
    unfold meet at h
    cases hb : Nat.ble (mx a.lo b.lo) (mn a.hi b.hi) with
    | true =>
        rw [hb] at h
        cases h
    | false => exact lt_of_ble_false _ _ hb
  exact absurd (Nat.le_trans (mx_le a.lo b.lo v ha1 hb1)
                             (le_mn a.hi b.hi v ha2 hb2))
    (Nat.not_le_of_gt hlt)

/-- **VERIFICATION IS COMBINATION WITH A SINGLETON** — one operation, not
two. Checking `v` against prior evidence `a` confirms exactly `v` when `v`
was possible, and EARNS A CONFLICT when it was not. -/
theorem verify_is_meet (a : Iv) (v : Nat) (hv : inIv a v) :
    meet a ⟨v, v⟩ = some ⟨v, v⟩ := by
  have hlo : mx a.lo v = v := by
    show (match Nat.ble a.lo v with | true => v | false => a.lo) = v
    rw [ble_true_of_le a.lo v hv.1]
  have hhi : mn a.hi v = v := by
    show (match Nat.ble a.hi v with | true => a.hi | false => v) = v
    cases hb : Nat.ble a.hi v with
    | true  => exact Nat.le_antisymm (le_of_ble a.hi v hb) hv.2
    | false => rfl
  unfold meet
  rw [hlo, hhi, ble_true_of_le v v (Nat.le_refl v)]

/-- And the check itself can earn the conflict: a value outside the prior
evidence refutes the pair. -/
theorem verify_can_conflict (a : Iv) (v : Nat) (h : a.hi < v) :
    meet a ⟨v, v⟩ = none := by
  unfold meet
  have : Nat.ble (mx a.lo v) (mn a.hi v) = false :=
    ble_false_of_lt _ _
      (Nat.lt_of_le_of_lt (mn_le_left a.hi v)
        (Nat.lt_of_lt_of_le h (le_mx_right a.lo v)))
  rw [this]

/-! ### 3. Zadeh's paradox, as a theorem

    Two doctors, three diagnoses. Each gives the tumour one part in a hundred
    and puts the rest elsewhere — and they disagree about where. Dempster's
    rule combines by intersecting focal elements, DISCARDS whatever intersects
    to nothing, and renormalises. Weights here are integers: a threshold is
    scale-free, so discarding is all the normalisation there is. -/

def frame : List Nat := [0, 1, 2]

def tumour     : ZDempster.Sub := fun n => Nat.beq n 0
def meningitis : ZDempster.Sub := fun n => Nat.beq n 1
def concussion : ZDempster.Sub := fun n => Nat.beq n 2
def emptySet   : ZDempster.Sub := fun _ => false

def doc1 : ZDempster.Mass := [⟨meningitis, 99⟩, ⟨tumour, 1⟩]
def doc2 : ZDempster.Mass := [⟨concussion, 99⟩, ⟨tumour, 1⟩]

/-- The four pairwise products. Three intersect to nothing. -/
def conflictWeight  : Nat := 99 * 99 + 99 * 1 + 1 * 99
def survivingWeight : Nat := 1 * 1

theorem zadeh_arithmetic : conflictWeight = 9999 ∧ survivingWeight = 1 :=
  ⟨rfl, rfl⟩

/-- What Dempster keeps: one part in ten thousand, on the tumour alone. -/
def dempsterKept : ZDempster.Mass := [⟨tumour, 1⟩]

theorem dempsterKept_proper : ZDempster.allOk frame dempsterKept :=
  ⟨⟨Nat.zero_lt_one, rfl⟩, trivial⟩

/-- **ZADEH'S CERTAINTY, DERIVED INSIDE OUR OWN MACHINERY.** After the
discard the verdict for the tumour is T — an unshakable diagnosis
manufactured from two one-percent opinions. -/
theorem zadeh_dempster_says_certain :
    ZDempster.verdict frame tumour dempsterKept = T := rfl

/-- And that certainty IS full belief, by the threshold theorem proved for
their own theory. The paradox is not criticised from outside; it is derived
with their rule and our theorem. -/
theorem zadeh_belief_is_full :
    ZDempster.bel frame tumour dempsterKept = ZDempster.total dempsterKept :=
  ((ZDempster.verdict_is_threshold frame tumour ⟨tumour, 1⟩ []
      dempsterKept_proper).1).mp zadeh_dempster_says_certain

/-- **OUR SIDE RETAINS THE CONFLICT**, and the retained assignment is then
IMPROPER — the mass sits on the empty focal, 9999 parts of 10000. No verdict
is issued, and the reason is exhibited rather than divided away. That is the
refusal §20 describes, and it is a theorem about the precondition of
`verdict_is_threshold` rather than a further verdict. -/
def retained : ZDempster.Mass := [⟨emptySet, conflictWeight⟩, ⟨tumour, survivingWeight⟩]

theorem zadeh_retained_is_improper : ¬ ZDempster.allOk frame retained := by
  intro h
  exact Bool.noConfusion (h.1.2 : ZDempster.anyOn emptySet frame = true)

/-- The two readings side by side, in one statement: discard and you get
certainty; retain and you get no verdict at all, with the conflict visible. -/
theorem zadeh_two_readings :
    ZDempster.verdict frame tumour dempsterKept = T
  ∧ conflictWeight = 9999
  ∧ ¬ ZDempster.allOk frame retained :=
  ⟨zadeh_dempster_says_certain, rfl, zadeh_retained_is_improper⟩

end ZCombine

#print axioms ZCombine.meet_is_intersection
#print axioms ZCombine.meet_none_is_earned
#print axioms ZCombine.verify_is_meet
#print axioms ZCombine.verify_can_conflict
#print axioms ZCombine.zadeh_dempster_says_certain
#print axioms ZCombine.zadeh_belief_is_full
#print axioms ZCombine.zadeh_retained_is_improper
#print axioms ZCombine.zadeh_two_readings
