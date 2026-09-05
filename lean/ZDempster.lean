/-
  ZDempster.lean — E35: THE VERDICT IS THE {0,1}-THRESHOLD OF BELIEF.

  WHAT §16 CLAIMED, AND HOW. "On masses m({a}) = m({a,b,c}) = 1/2 it is
  measured that the ZTL verdict of an event is the threshold of belief
  functions: T ⟺ Bel = 1, F ⟺ Pl = 0, else Z." One mass assignment, checked.
  §27 asks for a tradition's own semantics formalised and mapped in; this
  does it for the fifth twin — Dempster–Shafer, and with it Walley's
  imprecise probabilities, whose lower/upper pair is exactly Bel/Pl.

  THE ENCODING IS THEIRS, NOT OURS. A mass assignment is a list of focal
  elements, each a subset of a finite frame carrying a positive weight.
  Bel(A) sums the weights of the focals lying INSIDE A; Pl(A) sums the
  weights of those MEETING A. Both are the textbook definitions. Weights are
  natural numbers rather than fractions on purpose: the thresholds are
  Bel = total and Pl = 0, and a threshold is scale-free, so nothing is lost
  and no rational arithmetic is imported.

  OUR VERDICT IS DEFINED SEPARATELY, by the generating principle, and only
  then compared. A reading of the ignorance places each focal's mass at some
  world inside it. The event is forced true when every reading lands in A,
  forced false when no reading can, and marked otherwise. Nothing about Bel
  or Pl enters that definition — which is the whole point, since a
  correspondence proved by defining one side out of the other proves
  nothing.

  WHAT IS PROVED (empty axiom list): the two agree, in all three cells, for
  EVERY finite frame, EVERY mass assignment with positive weights and EVERY
  event. What §16 checked on one assignment holds on all of them.

  ЧТО СБОРКА ВСКРЫЛА В МОЕЙ ЖЕ ФОРМУЛИРОВКЕ. Первая редакция требовала от масс
  только ПОЛОЖИТЕЛЬНОСТИ весов — и была ложной. На пустом наборе масс вердикт
  выходит T (всё вложено вакуумно), а Pl = 0, и клетка «F ⟺ Pl = 0» падает; то
  же ломает фокальный элемент, равный пустому множеству. Это не мелочь
  формализации, а СТАНДАРТНОЕ УСЛОВИЕ Демпстера–Шейфера, `m(∅) = 0`, которое я
  пропустил, потому что на одном промеренном распределении оно выполнялось само
  собой. Ровно то, ради чего теорема и пишется вместо промера.

  ФОРМА. Арифметика по `Nat` ведётся руками, БЕЗ `omega`: промерено сегодня —
  `omega` тянет `propext` и `Quot.sound` (хотя `Classical.choice` не тянет).
  Списки — своя структурная рекурсия, не ядровые `List.all`/`any`: та тоже
  промерена и тоже тянет. Развилки — по неперекрывающимся образцам.
-/
import ZTL

namespace ZDempster

open V

/-- A subset of the frame, as its characteristic function. -/
def Sub := Nat → Bool

/-- A focal element: a subset with a weight. -/
structure Focal where
  set : Sub
  w   : Nat

/-- A mass assignment. -/
def Mass := List Focal

/-! ### Set operations over a finite frame, on our own recursion -/

def allOn (p : Nat → Bool) : List Nat → Bool
  | []     => true
  | x :: r => p x && allOn p r

def anyOn (p : Nat → Bool) : List Nat → Bool
  | []     => false
  | x :: r => p x || anyOn p r

/-- `A ⊆ B` over the frame. -/
def subsetOn (frame : List Nat) (A B : Sub) : Bool :=
  allOn (fun x => match A x with
                  | true  => B x
                  | false => true) frame

/-- `A ∩ B ≠ ∅` over the frame. -/
def meetsOn (frame : List Nat) (A B : Sub) : Bool :=
  anyOn (fun x => match A x with
                  | true  => B x
                  | false => false) frame

/-! ### Dempster–Shafer, as they define it -/

def total : Mass → Nat
  | []     => 0
  | f :: r => f.w + total r

def bel (frame : List Nat) (A : Sub) : Mass → Nat
  | []     => 0
  | f :: r => (match subsetOn frame f.set A with
               | true  => f.w
               | false => 0) + bel frame A r

def pl (frame : List Nat) (A : Sub) : Mass → Nat
  | []     => 0
  | f :: r => (match meetsOn frame f.set A with
               | true  => f.w
               | false => 0) + pl frame A r

/-- Every weight is positive — the standing condition on focal elements. -/
def positive : Mass → Prop
  | []     => True
  | f :: r => 0 < f.w ∧ positive r

/-! ### Our verdict, defined by the generating principle alone -/

/-- Every reading lands inside A. -/
def allIn (frame : List Nat) (A : Sub) : Mass → Bool
  | []     => true
  | f :: r => subsetOn frame f.set A && allIn frame A r

/-- No reading can land in A. -/
def noneMeets (frame : List Nat) (A : Sub) : Mass → Bool
  | []     => true
  | f :: r => (match meetsOn frame f.set A with
               | true  => false
               | false => true) && noneMeets frame A r

/-- T if forced under all readings, F if excluded by all, else Z. Bel and Pl
do not appear here. -/
def verdict (frame : List Nat) (A : Sub) (m : Mass) : V :=
  match allIn frame A m with
  | true  => T
  | false => match noneMeets frame A m with
             | true  => F
             | false => Z

/-! ### The arithmetic, by hand -/

/-- Cancellation, hand-rolled. `Nat.add_left_cancel` from core carries
`propext` — measured, and that is the whole reason this is here. `Nat.add`
recurses on its SECOND argument, so right-cancellation reduces structurally
and needs no lemma at all; left-cancellation follows by commutativity, which
is itself clean. -/
theorem addRightCancel : ∀ (b c a : Nat), b + a = c + a → b = c
  | _, _, 0,     h => h
  | b, c, a + 1, h => addRightCancel b c a (Nat.succ.inj h)

theorem addLeftCancel (a b c : Nat) (h : a + b = a + c) : b = c :=
  addRightCancel b c a (by rw [Nat.add_comm b a, Nat.add_comm c a]; exact h)

theorem bel_le_total (frame : List Nat) (A : Sub) :
    ∀ m : Mass, bel frame A m ≤ total m
  | []     => Nat.le_refl 0
  | f :: r => by
      show ((match subsetOn frame f.set A with
             | true => f.w | false => 0) + bel frame A r) ≤ f.w + total r
      cases subsetOn frame f.set A with
      | true  => exact Nat.add_le_add_left (bel_le_total frame A r) f.w
      | false =>
          exact Nat.le_trans
            (Nat.add_le_add (Nat.zero_le f.w) (bel_le_total frame A r))
            (Nat.le_refl _)

/-- A focal element is proper when it carries weight and is not empty over
the frame — `m(∅) = 0` in the textbook's phrasing. -/
def okFocal (frame : List Nat) (f : Focal) : Prop :=
  0 < f.w ∧ anyOn f.set frame = true

def allOk (frame : List Nat) : Mass → Prop
  | []     => True
  | f :: r => okFocal frame f ∧ allOk frame r

theorem allOk_positive (frame : List Nat) : ∀ m : Mass, allOk frame m → positive m
  | [],     _  => trivial
  | _ :: r, ho => ⟨ho.1.1, allOk_positive frame r ho.2⟩

/-- A NON-EMPTY subset of A meets A. This is the step the first version
skipped, and skipping it made the theorem false. -/
theorem subset_nonempty_meets (A B : Sub) : ∀ frame : List Nat,
    subsetOn frame A B = true → anyOn A frame = true → meetsOn frame A B = true
  | [],     _,  he => Bool.noConfusion he
  | x :: r, hs, he => by
      show ((match A x with | true => B x | false => false) || meetsOn r A B) = true
      cases hax : A x with
      | true =>
          have hb : B x = true := by
            have : ((match A x with | true => B x | false => true) && allOn
                     (fun y => match A y with | true => B y | false => true) r) = true := hs
            rw [hax] at this
            cases hbx : B x with
            | true  => rfl
            | false => rw [hbx] at this; exact Bool.noConfusion this
          rw [hb]; rfl
      | false =>
          have hrest : anyOn A r = true := by
            have : (A x || anyOn A r) = true := he
            rw [hax] at this; exact this
          have hsub : subsetOn r A B = true := by
            have : ((match A x with | true => B x | false => true) && allOn
                     (fun y => match A y with | true => B y | false => true) r) = true := hs
            rw [hax] at this; exact this
          rw [subset_nonempty_meets A B r hsub hrest]
          exact Bool.or_true _

/-- Forcedness and exclusion cannot hold together on a proper, non-empty mass
assignment — so the three cells really are three. -/
theorem forced_not_excluded (frame : List Nat) (A : Sub) :
    ∀ (f : Focal) (r : Mass), allOk frame (f :: r) →
      allIn frame A (f :: r) = true → noneMeets frame A (f :: r) = false := by
  intro f r ho ha
  have hsub : subsetOn frame f.set A = true := by
    have : (subsetOn frame f.set A && allIn frame A r) = true := ha
    cases hs : subsetOn frame f.set A with
    | true  => rfl
    | false => rw [hs] at this; exact Bool.noConfusion this
  have hm : meetsOn frame f.set A = true :=
    subset_nonempty_meets f.set A frame hsub ho.1.2
  show ((match meetsOn frame f.set A with | true => false | false => true)
          && noneMeets frame A r) = false
  rw [hm]; rfl

/-! ### The bridge, cell by cell -/

/-- **T ⟺ Bel = total.** Full belief is exactly forcedness. -/
theorem bel_full_iff (frame : List Nat) (A : Sub) :
    ∀ m : Mass, positive m → (bel frame A m = total m ↔ allIn frame A m = true)
  | [],     _  => ⟨fun _ => rfl, fun _ => rfl⟩
  | f :: r, hp => by
      show ((match subsetOn frame f.set A with
             | true => f.w | false => 0) + bel frame A r = f.w + total r)
         ↔ (subsetOn frame f.set A && allIn frame A r) = true
      cases hs : subsetOn frame f.set A with
      | true =>
          constructor
          · intro h
            have h2 : bel frame A r = total r := addLeftCancel _ _ _ h
            have := (bel_full_iff frame A r hp.2).mp h2
            show (true && allIn frame A r) = true
            rw [this]; rfl
          · intro h
            have h2 : allIn frame A r = true := by
              show allIn frame A r = true
              cases ha : allIn frame A r with
              | true  => rfl
              | false => rw [ha] at h; exact Bool.noConfusion h
            rw [(bel_full_iff frame A r hp.2).mpr h2]
      | false =>
          constructor
          · intro h
            have hlt : bel frame A r < f.w + total r :=
              Nat.lt_of_le_of_lt (bel_le_total frame A r)
                (Nat.lt_add_of_pos_left hp.1)
            exact absurd h (Nat.ne_of_lt (by
              show 0 + bel frame A r < f.w + total r
              rw [Nat.zero_add]; exact hlt))
          · intro h
            show (0 + bel frame A r) = f.w + total r
            exact absurd h (by rw [Bool.false_and]; exact Bool.noConfusion)

/-- **F ⟺ Pl = 0.** Zero plausibility is exactly exclusion by all readings. -/
theorem pl_zero_iff (frame : List Nat) (A : Sub) :
    ∀ m : Mass, positive m → (pl frame A m = 0 ↔ noneMeets frame A m = true)
  | [],     _  => ⟨fun _ => rfl, fun _ => rfl⟩
  | f :: r, hp => by
      show ((match meetsOn frame f.set A with
             | true => f.w | false => 0) + pl frame A r = 0)
         ↔ ((match meetsOn frame f.set A with
             | true => false | false => true) && noneMeets frame A r) = true
      cases hm : meetsOn frame f.set A with
      | true =>
          constructor
          · intro h
            exact absurd (Nat.eq_zero_of_add_eq_zero_right h) (Nat.ne_of_gt hp.1)
          · intro h
            exact absurd h (by rw [Bool.false_and]; exact Bool.noConfusion)
      | false =>
          constructor
          · intro h
            have h0 : pl frame A r = 0 := by
              show pl frame A r = 0
              rw [Nat.zero_add] at h; exact h
            show (true && noneMeets frame A r) = true
            rw [(pl_zero_iff frame A r hp.2).mp h0]; rfl
          · intro h
            have h2 : noneMeets frame A r = true := by
              cases hn : noneMeets frame A r with
              | true  => rfl
              | false => rw [hn] at h; exact Bool.noConfusion h
            show (0 + pl frame A r) = 0
            rw [Nat.zero_add, (pl_zero_iff frame A r hp.2).mpr h2]

/-! ### The embedding -/

/-- **THE THRESHOLD THEOREM.** For every finite frame, every PROPER mass
assignment — positive weights, no empty focal, at least one focal — and every
event: our verdict is T exactly when belief is full, F exactly when
plausibility is nil, and Z in between. What §16 measured on a single mass
assignment holds on all of them.

The properness condition is not decoration. Drop "no empty focal" or allow the
empty assignment and the F-cell is FALSE: the verdict comes out T vacuously
while Pl = 0. That is Dempster–Shafer's own `m(∅) = 0`, and the first draft of
this file omitted it. -/
theorem verdict_is_threshold (frame : List Nat) (A : Sub)
    (f : Focal) (r : Mass) (ho : allOk frame (f :: r)) :
    (verdict frame A (f :: r) = T ↔ bel frame A (f :: r) = total (f :: r))
  ∧ (verdict frame A (f :: r) = F ↔ pl frame A (f :: r) = 0)
  ∧ (verdict frame A (f :: r) = Z ↔
       (bel frame A (f :: r) ≠ total (f :: r) ∧ pl frame A (f :: r) ≠ 0)) := by
  have hp : positive (f :: r) := allOk_positive frame (f :: r) ho
  unfold verdict
  cases ha : allIn frame A (f :: r) with
  | true =>
      have hb : bel frame A (f :: r) = total (f :: r) :=
        (bel_full_iff frame A (f :: r) hp).mpr ha
      have hne : noneMeets frame A (f :: r) = false :=
        forced_not_excluded frame A f r ho ha
      have hz : pl frame A (f :: r) ≠ 0 := fun h =>
        Bool.noConfusion (hne ▸ (pl_zero_iff frame A (f :: r) hp).mp h)
      exact ⟨⟨fun _ => hb, fun _ => rfl⟩,
             ⟨fun h => V.noConfusion h, fun h => absurd h hz⟩,
             ⟨fun h => V.noConfusion h, fun h => absurd hb h.1⟩⟩
  | false =>
      have hb : bel frame A (f :: r) ≠ total (f :: r) := fun h =>
        Bool.noConfusion (ha ▸ (bel_full_iff frame A (f :: r) hp).mp h)
      cases hn : noneMeets frame A (f :: r) with
      | true =>
          have hz : pl frame A (f :: r) = 0 :=
            (pl_zero_iff frame A (f :: r) hp).mpr hn
          exact ⟨⟨fun h => V.noConfusion h, fun h => absurd h hb⟩,
                 ⟨fun _ => hz, fun _ => rfl⟩,
                 ⟨fun h => V.noConfusion h, fun h => absurd hz h.2⟩⟩
      | false =>
          have hz : pl frame A (f :: r) ≠ 0 := fun h =>
            Bool.noConfusion (hn ▸ (pl_zero_iff frame A (f :: r) hp).mp h)
          exact ⟨⟨fun h => V.noConfusion h, fun h => absurd h hb⟩,
                 ⟨fun h => V.noConfusion h, fun h => absurd h hz⟩,
                 ⟨fun _ => ⟨hb, hz⟩, fun _ => rfl⟩⟩

end ZDempster

#print axioms ZDempster.bel_le_total
#print axioms ZDempster.bel_full_iff
#print axioms ZDempster.pl_zero_iff
#print axioms ZDempster.verdict_is_threshold
#print axioms ZDempster.subset_nonempty_meets
#print axioms ZDempster.forced_not_excluded
#print axioms ZDempster.addLeftCancel
