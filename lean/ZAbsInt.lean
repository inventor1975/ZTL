/-
  ZAbsInt.lean — E37: ABSTRACT INTERPRETATION, AND WHERE OUR VERDICT IS EXACT.

  THE TRADITION. Cousot & Cousot, 1977: a concrete domain of value sets, an
  abstract domain (here intervals), a Galois connection α ⊣ γ between them,
  and abstract operations that over-approximate the concrete ones. §15 lists
  it as the fourth twin — "interval value analysis plus assertion checking" —
  and §1's claim ceiling says plainly that a reproduced case is not an
  embedding. This file formalises their connection and proves what our
  verdict is with respect to it.

  WHAT IS PROVED (empty axiom list).

    1. THE GALOIS CONNECTION ITSELF: with `Abstracts S lo hi` saying that
       [lo,hi] is the best interval abstraction of the value set S — both
       endpoints attained, which is exactly α(S) = [lo,hi] — we have
       α(S) ⊑ [a,b] ⟺ S ⊆ γ([a,b]), in both directions.

    2. OUR VERDICT IS NOT MERELY SOUND ON THE ABSTRACT VALUE, IT IS EXACT.
       For a threshold atom, the verdict computed from the interval alone
       equals the verdict computed over the whole concrete value set —
       T, F and Z all three. Abstract interpretation normally buys soundness
       and pays precision; at this atom nothing is paid.

    3. AND THE PRECISION IS PAID EXACTLY WHERE §15 SAID IT WAS. The moment
       one variable occurs twice the exactness is gone: on S = [1,3] every
       concrete `v - v` is 0, so the concrete verdict of "v - v < 1" is T,
       while the interval computation gives [0,2] and returns Z. That is the
       decorrelation of §15 — here as the named boundary of theorem 2 rather
       than as a separate observation.

  SO THE SHAPE IS THE SAME AS FOR PROVENANCE AND DEMPSTER–SHAFER: their
  construction formalised as they state it, our verdict placed inside it by
  theorem, and the boundary named in the same file rather than left for a
  reader to find.

  WHAT IS NOT DONE: the abstract-interpretation FRAMEWORK — widening,
  narrowing, fixpoint transfer — is not formalised. One atom over one
  abstract domain is mapped, not the method. Third algebraic core, not third
  tradition.

  ФОРМА. Мостики Bool↔порядок написаны свои: ядровая `Nat.ble_eq` тянет
  propext (промерено), тогда как Prop-уровневые `Nat.le_trans`,
  `Nat.lt_of_le_of_lt`, `Nat.not_lt`, `Nat.le_of_not_lt` чисты.
-/
import ZTL

namespace ZAbsInt

open V

/-! ### Bool ↔ order, hand-rolled -/

theorem le_of_ble : ∀ (a b : Nat), Nat.ble a b = true → a ≤ b
  | 0,     b,     _ => Nat.zero_le b
  | _ + 1, 0,     h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (le_of_ble a b h)

theorem ble_of_le : ∀ (a b : Nat), a ≤ b → Nat.ble a b = true
  | 0,     _,     _ => rfl
  | a + 1, 0,     h => absurd h (Nat.not_succ_le_zero a)
  | a + 1, b + 1, h => ble_of_le a b (Nat.le_of_succ_le_succ h)

theorem ble_false_of_lt : ∀ (a b : Nat), b < a → Nat.ble a b = false
  | 0,     _,     h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0,     _ => rfl
  | a + 1, b + 1, h => ble_false_of_lt a b (Nat.lt_of_succ_lt_succ h)

theorem lt_of_ble_false : ∀ (a b : Nat), Nat.ble a b = false → b < a
  | 0,     _,     h => Bool.noConfusion h
  | _ + 1, 0,     _ => Nat.succ_le_succ (Nat.zero_le _)
  | a + 1, b + 1, h => Nat.succ_le_succ (lt_of_ble_false a b h)

/-! ### The two domains and the connection -/

/-- `[lo,hi]` is the BEST interval abstraction of the value set `S`: it
contains S and both endpoints are attained. That is α(S) = [lo,hi]. -/
structure Abstracts (S : List Nat) (lo hi : Nat) : Prop where
  low_mem  : lo ∈ S
  high_mem : hi ∈ S
  bounded  : ∀ v, v ∈ S → lo ≤ v ∧ v ≤ hi

/-- γ: a value is in the concretization of `[a,b]`. -/
def inGamma (a b v : Nat) : Prop := a ≤ v ∧ v ≤ b

/-- **THE GALOIS CONNECTION.** α(S) ⊑ [a,b] ⟺ S ⊆ γ([a,b]). Their defining
adjunction, in both directions. -/
theorem galois (S : List Nat) (lo hi a b : Nat) (hA : Abstracts S lo hi) :
    (a ≤ lo ∧ hi ≤ b) ↔ (∀ v, v ∈ S → inGamma a b v) := by
  constructor
  · intro ⟨hal, hhb⟩ v hv
    exact ⟨Nat.le_trans hal (hA.bounded v hv).1,
           Nat.le_trans (hA.bounded v hv).2 hhb⟩
  · intro h
    exact ⟨(h _ hA.low_mem).1, (h _ hA.high_mem).2⟩

/-! ### The atom, both sides -/

/-- The verdict of `x < c` computed from the INTERVAL alone. -/
def absLt (lo hi c : Nat) : V :=
  match Nat.ble (hi + 1) c with
  | true  => T
  | false => match Nat.ble c lo with
             | true  => F
             | false => Z

def allLt (c : Nat) : List Nat → Bool
  | []     => true
  | v :: r => Nat.ble (v + 1) c && allLt c r

def noneLt (c : Nat) : List Nat → Bool
  | []     => true
  | v :: r => (match Nat.ble (v + 1) c with
               | true  => false
               | false => true) && noneLt c r

/-- The verdict of `x < c` computed over the WHOLE concrete value set, by the
generating principle: T if forced by every value, F if excluded by every
value, else Z. -/
def conLt (c : Nat) (S : List Nat) : V :=
  match allLt c S with
  | true  => T
  | false => match noneLt c S with
             | true  => F
             | false => Z

/-! ### The four list lemmas -/

theorem allLt_true (c : Nat) : ∀ S : List Nat, (∀ v, v ∈ S → v < c) →
    allLt c S = true
  | [],     _ => rfl
  | v :: r, h => by
      show (Nat.ble (v + 1) c && allLt c r) = true
      rw [ble_of_le (v + 1) c (h v (List.Mem.head r)),
          allLt_true c r (fun x hx => h x (List.Mem.tail v hx))]
      rfl

theorem allLt_false (c : Nat) : ∀ (S : List Nat) (v : Nat), v ∈ S → c ≤ v →
    allLt c S = false
  | [],     _, hv, _  => nomatch hv
  | w :: r, v, hv, hc => by
      show (Nat.ble (w + 1) c && allLt c r) = false
      cases hv with
      | head =>
          rw [ble_false_of_lt (w + 1) c (Nat.lt_succ_of_le hc)]
          rfl
      | tail _ ht =>
          rw [allLt_false c r v ht hc]
          exact Bool.and_false _

theorem noneLt_true (c : Nat) : ∀ S : List Nat, (∀ v, v ∈ S → c ≤ v) →
    noneLt c S = true
  | [],     _ => rfl
  | v :: r, h => by
      show ((match Nat.ble (v + 1) c with | true => false | false => true)
              && noneLt c r) = true
      rw [ble_false_of_lt (v + 1) c (Nat.lt_succ_of_le (h v (List.Mem.head r))),
          noneLt_true c r (fun x hx => h x (List.Mem.tail v hx))]
      rfl

theorem noneLt_false (c : Nat) : ∀ (S : List Nat) (v : Nat), v ∈ S → v < c →
    noneLt c S = false
  | [],     _, hv, _  => nomatch hv
  | w :: r, v, hv, hc => by
      show ((match Nat.ble (w + 1) c with | true => false | false => true)
              && noneLt c r) = false
      cases hv with
      | head =>
          rw [ble_of_le (w + 1) c hc]
          rfl
      | tail _ ht =>
          rw [noneLt_false c r v ht hc]
          exact Bool.and_false _

/-! ### Exactness -/

/-- **THE VERDICT IS EXACT ON THE ABSTRACT VALUE.** For a threshold atom, what
the interval says and what the whole value set says are the same verdict —
in all three cells. Abstraction costs nothing here. -/
theorem verdict_exact (S : List Nat) (lo hi c : Nat) (hA : Abstracts S lo hi) :
    absLt lo hi c = conLt c S := by
  unfold absLt conLt
  cases h1 : Nat.ble (hi + 1) c with
  | true =>
      have hall : allLt c S = true :=
        allLt_true c S (fun v hv =>
          Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (hA.bounded v hv).2)
            (le_of_ble (hi + 1) c h1))
      rw [hall]
  | false =>
      have hhi : c ≤ hi := Nat.le_of_lt_succ (lt_of_ble_false (hi + 1) c h1)
      have hallF : allLt c S = false := allLt_false c S hi hA.high_mem hhi
      rw [hallF]
      cases h2 : Nat.ble c lo with
      | true =>
          have hnone : noneLt c S = true :=
            noneLt_true c S (fun v hv =>
              Nat.le_trans (le_of_ble c lo h2) (hA.bounded v hv).1)
          rw [hnone]
      | false =>
          have hlo : lo < c := lt_of_ble_false c lo h2
          have hnoneF : noneLt c S = false := noneLt_false c S lo hA.low_mem hlo
          rw [hnoneF]

/-! ### And the boundary, in the same file -/

/-- Interval subtraction, decorrelated: each occurrence chooses its value
independently. This is the standard abstract operation, not ours. -/
def subI (lo₁ hi₁ lo₂ hi₂ : Nat) : Nat × Nat := (lo₁ - hi₂, hi₁ - lo₂)

/-- The concrete set of `v - v` over [1,3] — every element is 0. -/
theorem concrete_self_sub : List.map (fun v => v - v) [1, 3] = [0, 0] := rfl

/-- The abstract interval for `x - x` on [1,3] — width 2, decorrelated. -/
theorem abstract_self_sub : subI 1 3 1 3 = (0, 2) := rfl

/-- **EXACTNESS ENDS WHERE A VARIABLE REPEATS.** On the value set [1,3] every
concrete `v - v` is 0, so the concrete verdict of `v - v < 1` is T; the
interval computation of `x - x` on [1,3] gives [0,2] and returns Z. This is
§15's decorrelation, stated here as the price of theorem `verdict_exact`
rather than as a separate observation. -/
theorem not_exact_on_repeated_variable :
    conLt 1 (List.map (fun v => v - v) [1, 3]) = T
  ∧ absLt (subI 1 3 1 3).1 (subI 1 3 1 3).2 1 = Z := ⟨rfl, rfl⟩

end ZAbsInt

#print axioms ZAbsInt.le_of_ble
#print axioms ZAbsInt.ble_of_le
#print axioms ZAbsInt.galois
#print axioms ZAbsInt.allLt_true
#print axioms ZAbsInt.noneLt_false
#print axioms ZAbsInt.verdict_exact
#print axioms ZAbsInt.not_exact_on_repeated_variable
#print axioms ZAbsInt.concrete_self_sub
#print axioms ZAbsInt.abstract_self_sub
