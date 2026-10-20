import Hardy

/-!
# Agrippa — the trilemma on a finite justification base, kernel-checked. Zero axioms.

2026-10-20 (the curator's "Один Агриппа чего стоит" and "Мы расщепили третий рог, в нем вилка"). The measured
stands are `dilemmas/agrippa.py` (F1–F7) and `dilemmas/agrippa_nullary.py` (the third horn split); this file puts
their core under the kernel.

THE MODEL. A justification system gives every statement x one of two kinds of support:
  `ground b`   — a nullary ground: x is settled as b and asks for nothing further (the FORCED stop);
  `ref j s`    — x holds iff (s ⊕) j holds: x rests on j, with s = true meaning "on j's negation".
A chosen stop "p because p" is `ref p false` — a self-reference, NOT a ground. That is the split of the third horn.
A READING of x's chain is a valuation obeying every support met when following x's reasons (`Reading`).

THE THEOREMS.
  `no_regress`     on a closed base of n statements, the chain of reasons from any statement repeats within n steps
                   (pigeonhole, `pigeon`): an infinite regress of distinct reasons needs infinitely many statements.
  `chain_value`    along any reading, x's value is its parity of negations ⊕ the value reached.
  `forced_one`     the chain reaches a ground: exactly one reading value (exists, and all readings agree).
  `odd_zero`       the chain enters a loop with an odd number of negations: NO reading at all — the paradox.
  `even_two`       the chain enters a loop whose every return is even: two readings that disagree on x — the fork.
  With Bool values "two that disagree" is "exactly two". So ONE criterion, the number of readings, sorts every
  horn: 1 = forced stop, 2 = fork, 0 = paradox; and regress is not a fourth case on a finite base.
  `dogma_two`, `circle_two`, `twoneg_two`  the chosen stop f := f (with p := f), the circle a := b, b := a, and the
                   circle a := ¬b, b := ¬a all read twice: DOGMA AND THE EVEN CIRCLE ARE ONE PLACE.
  `nullary_one`    the forced stop (a ground) reads once — the other half of the split horn.
  `liar_zero`      x := ¬x reads never.
THE SKEPTIC (Hardy's three-valued V, greedy lifts; atoms j, k, ra, rb, rc as in agrippa.py):
  `skeptic_earned` F1 — (bridges ∧ j ∧ (ra ∨ rb ∨ rc)) → ¬k is T at EVERY marking, partial or total: the
                   trilemma's logic is earned outright.
  `lethality_on_j` F2 — grant everything but j: F now, T when j := T, F when j := F — OPEN, the weak link j alone.

SCOPE, said. The counts are for x's chain (its cone of reasons), not for a whole system: a system with several
components multiplies their counts, and one odd loop anywhere makes the whole system unreadable while x's own chain
may still read. Parts are known mathematics (kernels of digraphs — Walicki; parity of feedback circuits — Thomas;
the truth-teller as ungrounded but not paradoxical — Kripke 1975; odd attack cycles — Dung): what this file
states is the reading of Agrippa's horns by one count. Logic programming's stable semantics gives `p ← p` ONE model
(p false, by minimality); ZTL counts both, since minimality is itself a chosen stop.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace Agrippa

/-! ## Bool lemmas, by cases -/

theorem fx (b : Bool) : xor false b = b := by cases b <;> rfl
theorem xf (b : Bool) : xor b false = b := by cases b <;> rfl
theorem xx (b : Bool) : xor b b = false := by cases b <;> rfl
theorem xa (a b c : Bool) : xor a (xor b c) = xor (xor a b) c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem xc (a b : Bool) : xor a b = xor b a := by cases a <;> cases b <;> rfl

/-! ## Justification systems -/

inductive Just where
  | ground : Bool → Just
  | ref : Nat → Bool → Just

abbrev Sys := Nat → Just

/-- The reason x rests on (a ground rests on itself: the chain stops there). -/
def step (J : Sys) (x : Nat) : Nat :=
  match J x with
  | .ground _ => x
  | .ref j _ => j

/-- Whether x rests on its reason's negation. -/
def sign (J : Sys) (x : Nat) : Bool :=
  match J x with
  | .ground _ => false
  | .ref _ s => s

/-- What x's support demands of x under v. -/
def val (J : Sys) (v : Nat → Bool) (x : Nat) : Bool :=
  match J x with
  | .ground b => b
  | .ref j s => xor s (v j)

def Holds (J : Sys) (v : Nat → Bool) (x : Nat) : Prop := v x = val J v x

/-- The chain of reasons from x. -/
def path (J : Sys) (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => step J (path J x k)

/-- The parity of the negations met on the first k links. -/
def par (J : Sys) (x : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => xor (par J x k) (sign J (path J x k))

/-- v reads x's chain: every support met along it holds. -/
def Reading (J : Sys) (x : Nat) (v : Nat → Bool) : Prop := ∀ k, Holds J v (path J x k)

/-- A base of n statements: reasons of the first n statements are among them. -/
def Closed (J : Sys) (n : Nat) : Prop := ∀ x, x < n → step J x < n

theorem step_ground {J : Sys} {x : Nat} {b : Bool} (h : J x = .ground b) : step J x = x := by
  unfold step; rw [h]
theorem step_ref {J : Sys} {x j : Nat} {s : Bool} (h : J x = .ref j s) : step J x = j := by
  unfold step; rw [h]
theorem sign_ground {J : Sys} {x : Nat} {b : Bool} (h : J x = .ground b) : sign J x = false := by
  unfold sign; rw [h]
theorem sign_ref {J : Sys} {x j : Nat} {s : Bool} (h : J x = .ref j s) : sign J x = s := by
  unfold sign; rw [h]
theorem val_ground {J : Sys} {v : Nat → Bool} {x : Nat} {b : Bool} (h : J x = .ground b) : val J v x = b := by
  unfold val; rw [h]
theorem val_ref {J : Sys} {v : Nat → Bool} {x j : Nat} {s : Bool} (h : J x = .ref j s) :
    val J v x = xor s (v j) := by
  unfold val; rw [h]

/-! ## No regress: pigeonhole -/

/-- Values c is hit among g 0 … g m, or missed by all of them. -/
theorem hit_or_miss (g : Nat → Nat) (c : Nat) :
    ∀ m, (∃ k, k ≤ m ∧ g k = c) ∨ (∀ k, k ≤ m → g k ≠ c)
  | 0 => by
    cases Nat.decEq (g 0) c with
    | isTrue e => exact Or.inl ⟨0, Nat.le_refl 0, e⟩
    | isFalse e =>
      refine Or.inr ?_
      intro k hk
      have k0 : k = 0 := Nat.eq_zero_of_le_zero hk
      rw [k0]; exact e
  | m + 1 => by
    cases hit_or_miss g c m with
    | inl h =>
      obtain ⟨k, hk, e⟩ := h
      exact Or.inl ⟨k, Nat.le_succ_of_le hk, e⟩
    | inr h =>
      cases Nat.decEq (g (m + 1)) c with
      | isTrue e => exact Or.inl ⟨m + 1, Nat.le_refl _, e⟩
      | isFalse e =>
        refine Or.inr ?_
        intro k hk
        cases Nat.decEq k (m + 1) with
        | isTrue ek => rw [ek]; exact e
        | isFalse ek => exact h k (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hk ek))

/-- n + 1 values below n: two of them coincide. -/
theorem pigeon : ∀ (n : Nat) (g : Nat → Nat), (∀ k, k ≤ n → g k < n) →
    ∃ a b, a < b ∧ b ≤ n ∧ g a = g b
  | 0, _, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | n + 1, g, h => by
    cases hit_or_miss g (g (n + 1)) n with
    | inl hc =>
      obtain ⟨k, hk, e⟩ := hc
      exact ⟨k, n + 1, Nat.lt_succ_of_le hk, Nat.le_refl _, e⟩
    | inr hm =>
      -- no collision with g (n+1) = c: send the value n to c, the rest stay — all below n now
      let c := g (n + 1)
      let g' : Nat → Nat := fun k => if g k = n then c else g k
      have hc : c < n + 1 := h (n + 1) (Nat.le_refl _)
      have h' : ∀ k, k ≤ n → g' k < n := by
        intro k hk
        have gk : g k < n + 1 := h k (Nat.le_succ_of_le hk)
        have nc : g k ≠ c := hm k hk
        show (if g k = n then c else g k) < n
        cases Nat.decEq (g k) n with
        | isTrue e =>
          rw [if_pos e]
          have cn : c ≠ n := fun ec => nc (Eq.trans e ec.symm)
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hc) cn
        | isFalse e =>
          rw [if_neg e]
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ gk) e
      obtain ⟨a, b, hab, hb, e⟩ := pigeon n g' h'
      refine ⟨a, b, hab, Nat.le_succ_of_le hb, ?_⟩
      have ea : g' a = (if g a = n then c else g a) := rfl
      have eb : g' b = (if g b = n then c else g b) := rfl
      rw [ea, eb] at e
      cases Nat.decEq (g a) n with
      | isTrue na =>
        cases Nat.decEq (g b) n with
        | isTrue nb => exact Eq.trans na nb.symm
        | isFalse nb =>
          rw [if_pos na, if_neg nb] at e
          exact absurd e.symm (hm b hb)
      | isFalse na =>
        cases Nat.decEq (g b) n with
        | isTrue nb =>
          rw [if_neg na, if_pos nb] at e
          exact absurd e (hm a (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hab (Nat.le_succ_of_le hb))))
        | isFalse nb =>
          rw [if_neg na, if_neg nb] at e
          exact e

theorem path_lt (J : Sys) (n : Nat) (hc : Closed J n) (x : Nat) (hx : x < n) : ∀ k, path J x k < n
  | 0 => hx
  | k + 1 => hc _ (path_lt J n hc x hx k)

/-- THE REGRESS HORN ON A FINITE BASE: within n steps the chain of reasons repeats a statement. -/
theorem no_regress (J : Sys) (n : Nat) (hc : Closed J n) (x : Nat) (hx : x < n) :
    ∃ a b, a < b ∧ b ≤ n ∧ path J x a = path J x b :=
  pigeon n (path J x) (fun k _ => path_lt J n hc x hx k)

/-! ## Chains: paths and parities -/

theorem path_succ' (J : Sys) : ∀ (x d : Nat), path J x (d + 1) = path J (step J x) d
  | _, 0 => rfl
  | x, d + 1 => by
    show step J (path J x (d + 1)) = step J (path J (step J x) d)
    rw [path_succ' J x d]

theorem path_add (J : Sys) (x m : Nat) : ∀ d, path J x (m + d) = path J (path J x m) d
  | 0 => rfl
  | d + 1 => by
    show step J (path J x (m + d)) = step J (path J (path J x m) d)
    rw [path_add J x m d]

theorem par_front (J : Sys) : ∀ (x d : Nat), par J x (d + 1) = xor (sign J x) (par J (step J x) d)
  | x, 0 => by
    show xor false (sign J x) = xor (sign J x) false
    rw [fx, xf]
  | x, d + 1 => by
    show xor (par J x (d + 1)) (sign J (path J x (d + 1))) =
      xor (sign J x) (xor (par J (step J x) d) (sign J (path J (step J x) d)))
    rw [par_front J x d, path_succ' J x d, xa]

/-- Any support, read: x's value is its sign ⊕ its reason's value (a ground: x = x). -/
theorem link {J : Sys} {v : Nat → Bool} {x : Nat} (h : Holds J v x) : v x = xor (sign J x) (v (step J x)) := by
  cases hJ : J x with
  | ground b => rw [sign_ground hJ, step_ground hJ, fx]
  | ref j s =>
    rw [sign_ref hJ, step_ref hJ]
    unfold Holds at h
    rw [val_ref hJ] at h
    exact h

/-- Along a reading, x's value = parity of the first k links ⊕ the value reached. -/
theorem chain_value {J : Sys} {x : Nat} {v : Nat → Bool} (hv : Reading J x v) :
    ∀ k, v x = xor (par J x k) (v (path J x k))
  | 0 => (fx _).symm
  | k + 1 => by
    show v x = xor (xor (par J x k) (sign J (path J x k))) (v (step J (path J x k)))
    rw [← xa, ← link (hv k)]
    exact chain_value hv k

theorem reading_shift {J : Sys} {x : Nat} {v : Nat → Bool} (hv : Reading J x v) (a : Nat) :
    Reading J (path J x a) v := by
  intro k
  rw [← path_add]
  exact hv (a + k)

/-! ## The three counts -/

/-- THE PARADOX: the chain enters a loop (p returns to itself after r links) with odd parity — no reading. -/
theorem odd_zero (J : Sys) (x a r : Nat) (hr : path J (path J x a) r = path J x a)
    (hodd : par J (path J x a) r = true) : ¬ ∃ v, Reading J x v := by
  intro ⟨v, hv⟩
  have e := chain_value (reading_shift hv a) r
  rw [hr, hodd] at e
  cases h : v (path J x a) with
  | false => rw [h] at e; exact Bool.noConfusion e
  | true => rw [h] at e; exact Bool.noConfusion e

/-- Reaching p within f links. -/
def Within (J : Sys) (x p f : Nat) : Prop := ∃ d, d ≤ f ∧ path J x d = p

/-- Parity from x to the first arrival at p, with fuel f. -/
def pt (J : Sys) (p : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | x, f + 1 => if x = p then false else xor (sign J x) (pt J p (step J x) f)

/-- The reading the existence theorems build: β at p, and parity-to-p ⊕ β elsewhere. -/
def build (J : Sys) (p : Nat) (β : Bool) (f : Nat) (x : Nat) : Bool := xor (pt J p x f) β

theorem within_zero {J : Sys} {x p : Nat} (h : Within J x p 0) : x = p := by
  obtain ⟨d, hd, e⟩ := h
  have d0 : d = 0 := Nat.eq_zero_of_le_zero hd
  rw [d0] at e; exact e

theorem within_step {J : Sys} {x p f : Nat} (h : Within J x p (f + 1)) (hx : x ≠ p) :
    Within J (step J x) p f := by
  obtain ⟨d, hd, e⟩ := h
  cases d with
  | zero => exact absurd e hx
  | succ d' =>
    rw [path_succ'] at e
    exact ⟨d', Nat.le_of_succ_le_succ hd, e⟩

/-- Once p is within reach, more fuel changes nothing. -/
theorem pt_stable (J : Sys) (p : Nat) : ∀ (f x : Nat), Within J x p f → pt J p x f = pt J p x (f + 1)
  | 0, x, h => by
    show false = (if x = p then false else xor (sign J x) (pt J p (step J x) 0))
    rw [if_pos (within_zero h)]
  | f + 1, x, h => by
    show (if x = p then false else xor (sign J x) (pt J p (step J x) f)) =
      (if x = p then false else xor (sign J x) (pt J p (step J x) (f + 1)))
    cases Nat.decEq x p with
    | isTrue e => rw [if_pos e, if_pos e]
    | isFalse e => rw [if_neg e, if_neg e, pt_stable J p f (step J x) (within_step h e)]

/-- The fuelled parity is the parity of an actual arrival at p. -/
theorem pt_is_par (J : Sys) (p : Nat) : ∀ (f y : Nat), Within J y p f →
    ∃ d, path J y d = p ∧ pt J p y f = par J y d
  | 0, y, h => ⟨0, within_zero h, rfl⟩
  | f + 1, y, h => by
    cases Nat.decEq y p with
    | isTrue e =>
      refine ⟨0, e, ?_⟩
      show (if y = p then false else xor (sign J y) (pt J p (step J y) f)) = false
      rw [if_pos e]
    | isFalse e =>
      obtain ⟨d, hd, hp⟩ := pt_is_par J p f (step J y) (within_step h e)
      refine ⟨d + 1, ?_, ?_⟩
      · rw [path_succ']; exact hd
      · show (if y = p then false else xor (sign J y) (pt J p (step J y) f)) = par J y (d + 1)
        rw [if_neg e, hp, par_front]

theorem path_fixed {J : Sys} {x : Nat} (h : step J x = x) : ∀ d, path J x d = x
  | 0 => rfl
  | d + 1 => by
    show step J (path J x d) = x
    rw [path_fixed h d]; exact h

/-- Away from p, the built valuation obeys every support. -/
theorem build_off (J : Sys) (p : Nat) (β : Bool) (f x : Nat) (hx : x ≠ p) (hw : Within J x p (f + 1)) :
    Holds J (build J p β (f + 1)) x := by
  cases hJ : J x with
  | ground b =>
    obtain ⟨d, _, e⟩ := hw
    rw [path_fixed (step_ground hJ) d] at e
    exact absurd e hx
  | ref j s =>
    unfold Holds
    rw [val_ref hJ]
    have hj : step J x = j := step_ref hJ
    have w := within_step hw hx
    rw [hj] at w
    show xor (if x = p then false else xor (sign J x) (pt J p (step J x) f)) β =
      xor s (xor (pt J p j (f + 1)) β)
    rw [if_neg hx, sign_ref hJ, hj, ← pt_stable J p f j w, xa]

/-- Every statement on x's chain reaches p (the chain reaches p after a links; p returns after L + 1). -/
theorem chain_within (J : Sys) (x a L : Nat) (hr : path J (path J x a) (L + 1) = path J x a) :
    ∀ k, Within J (path J x k) (path J x a) (a + (L + 1))
  | 0 => ⟨a, Nat.le_add_right a _, rfl⟩
  | k + 1 => by
    obtain ⟨d, hd, e⟩ := chain_within J x a L hr k
    cases d with
    | zero =>
      refine ⟨L, Nat.le_trans (Nat.le_succ L) (Nat.le_add_left (L + 1) a), ?_⟩
      show path J (step J (path J x k)) L = path J x a
      have e0 : path J x k = path J x a := e
      rw [e0, ← path_succ']; exact hr
    | succ d' =>
      refine ⟨d', Nat.le_of_succ_le hd, ?_⟩
      show path J (step J (path J x k)) d' = path J x a
      rw [← path_succ']; exact e

/-- The built valuation reads x's chain, provided it holds at p itself. -/
theorem build_reads (J : Sys) (x a L : Nat) (β : Bool)
    (hr : path J (path J x a) (L + 1) = path J x a)
    (hp : Holds J (build J (path J x a) β (a + L + 1)) (path J x a)) :
    Reading J x (build J (path J x a) β (a + L + 1)) := by
  intro k
  cases Nat.decEq (path J x k) (path J x a) with
  | isTrue e => rw [e]; exact hp
  | isFalse e => exact build_off J _ β (a + L) _ e (chain_within J x a L hr k)

theorem build_p (J : Sys) (p : Nat) (β : Bool) (f : Nat) : build J p β (f + 1) p = β := by
  show xor (if p = p then false else xor (sign J p) (pt J p (step J p) f)) β = β
  rw [if_pos rfl, fx]

/-- THE FORCED STOP: the chain reaches a ground — one reading value, and it exists. -/
theorem forced_one (J : Sys) (x a : Nat) (c : Bool) (hg : J (path J x a) = .ground c) :
    (∃ v, Reading J x v) ∧ ∀ v w, Reading J x v → Reading J x w → v x = w x := by
  have hs : step J (path J x a) = path J x a := step_ground hg
  have hr : path J (path J x a) (0 + 1) = path J x a := hs
  refine ⟨⟨_, build_reads J x a 0 c hr ?_⟩, ?_⟩
  · unfold Holds
    rw [val_ground hg]
    exact build_p J _ c (a + 0)
  · intro v w hv hw
    have ev := chain_value hv a
    have ew := chain_value hw a
    have gv : v (path J x a) = c := by
      have h := hv a; unfold Holds at h; rw [val_ground hg] at h; exact h
    have gw : w (path J x a) = c := by
      have h := hw a; unfold Holds at h; rw [val_ground hg] at h; exact h
    rw [ev, ew, gv, gw]

/-- THE FORK: the chain enters a loop (p a reason, returning after L + 1) whose every return is even —
two readings, disagreeing on x. With Bool values: exactly two. -/
theorem even_two (J : Sys) (x a L j : Nat) (s : Bool) (hp : J (path J x a) = .ref j s)
    (hr : path J (path J x a) (L + 1) = path J x a)
    (hev : ∀ r, path J (path J x a) r = path J x a → par J (path J x a) r = false) :
    ∃ v w, Reading J x v ∧ Reading J x w ∧ v x ≠ w x := by
  have holds : ∀ β, Holds J (build J (path J x a) β (a + L + 1)) (path J x a) := by
    intro β
    unfold Holds
    rw [val_ref hp, build_p]
    have hj : step J (path J x a) = j := step_ref hp
    -- j reaches p in L links
    have wj : Within J j (path J x a) (a + L) := by
      refine ⟨L, Nat.le_add_left L a, ?_⟩
      rw [← hj, ← path_succ']; exact hr
    obtain ⟨d, hd, e⟩ := pt_is_par J (path J x a) (a + L) j wj
    show β = xor s (xor (pt J (path J x a) j (a + L + 1)) β)
    rw [← pt_stable J _ (a + L) j wj, e, xa]
    have ret : path J (path J x a) (d + 1) = path J x a := by rw [path_succ', hj]; exact hd
    have pe := hev (d + 1) ret
    rw [par_front, sign_ref hp, hj] at pe
    rw [pe, fx]
  refine ⟨_, _, build_reads J x a L false hr (holds false), build_reads J x a L true hr (holds true), ?_⟩
  intro e
  have ef := chain_value (build_reads J x a L false hr (holds false)) a
  have et := chain_value (build_reads J x a L true hr (holds true)) a
  rw [build_p] at ef et
  rw [ef, et] at e
  cases h : par J x a with
  | false => rw [h] at e; exact Bool.noConfusion e
  | true => rw [h] at e; exact Bool.noConfusion e

/-! ## The horns, as instances -/

/-- The forced stop: ∅ is a nullary ground (VR's ∅ = the nullary operation), p := ∅. -/
def nullary : Sys := fun n => if n = 0 then .ground true else .ref 0 false

theorem nullary_one : (∃ v, Reading nullary 1 v) ∧ ∀ v w, Reading nullary 1 v → Reading nullary 1 w → v 1 = w 1 :=
  forced_one nullary 1 1 true rfl

/-- The chosen stop, dogma: f := f, p := f. -/
def dogma : Sys := fun n => if n = 0 then .ref 0 false else .ref 0 false

theorem dogma_path : ∀ r, path dogma 0 r = 0
  | 0 => rfl
  | r + 1 => by show step dogma (path dogma 0 r) = 0; rw [dogma_path r]; rfl

theorem dogma_par : ∀ r, par dogma 0 r = false
  | 0 => rfl
  | r + 1 => by
    show xor (par dogma 0 r) (sign dogma (path dogma 0 r)) = false
    rw [dogma_par r, dogma_path r]; rfl

theorem dogma_two : ∃ v w, Reading dogma 1 v ∧ Reading dogma 1 w ∧ v 1 ≠ w 1 :=
  even_two dogma 1 1 0 0 false rfl (dogma_path 1) (fun r _ => dogma_par r)

/-- The circle a := b, b := a (and p := a). -/
def circle : Sys := fun n => if n = 0 then .ref 1 false else if n = 1 then .ref 0 false else .ref 0 false

/-- The circle a := ¬b, b := ¬a (and p := a). -/
def twoneg : Sys := fun n => if n = 0 then .ref 1 true else if n = 1 then .ref 0 true else .ref 0 false

theorem circle_state : ∀ r, (path circle 0 r = 0 ∧ par circle 0 r = false) ∨
    (path circle 0 r = 1 ∧ par circle 0 r = false)
  | 0 => Or.inl ⟨rfl, rfl⟩
  | r + 1 => by
    cases circle_state r with
    | inl h =>
      refine Or.inr ⟨?_, ?_⟩
      · show step circle (path circle 0 r) = 1; rw [h.1]; rfl
      · show xor (par circle 0 r) (sign circle (path circle 0 r)) = false; rw [h.1, h.2]; rfl
    | inr h =>
      refine Or.inl ⟨?_, ?_⟩
      · show step circle (path circle 0 r) = 0; rw [h.1]; rfl
      · show xor (par circle 0 r) (sign circle (path circle 0 r)) = false; rw [h.1, h.2]; rfl

theorem circle_two : ∃ v w, Reading circle 2 v ∧ Reading circle 2 w ∧ v 2 ≠ w 2 :=
  even_two circle 2 1 1 1 false rfl rfl (fun r _ => by
    cases circle_state r with
    | inl h => exact h.2
    | inr h => exact h.2)

theorem twoneg_state : ∀ r, (path twoneg 0 r = 0 ∧ par twoneg 0 r = false) ∨
    (path twoneg 0 r = 1 ∧ par twoneg 0 r = true)
  | 0 => Or.inl ⟨rfl, rfl⟩
  | r + 1 => by
    cases twoneg_state r with
    | inl h =>
      refine Or.inr ⟨?_, ?_⟩
      · show step twoneg (path twoneg 0 r) = 1; rw [h.1]; rfl
      · show xor (par twoneg 0 r) (sign twoneg (path twoneg 0 r)) = true; rw [h.1, h.2]; rfl
    | inr h =>
      refine Or.inl ⟨?_, ?_⟩
      · show step twoneg (path twoneg 0 r) = 0; rw [h.1]; rfl
      · show xor (par twoneg 0 r) (sign twoneg (path twoneg 0 r)) = false; rw [h.1, h.2]; rfl

/-- Every return of a to itself is even (an odd number of links ends at b, not a). -/
theorem twoneg_two : ∃ v w, Reading twoneg 2 v ∧ Reading twoneg 2 w ∧ v 2 ≠ w 2 :=
  even_two twoneg 2 1 1 1 true rfl rfl (fun r hr => by
    cases twoneg_state r with
    | inl h => exact h.2
    | inr h =>
      have hr' : path twoneg 0 r = 0 := hr
      rw [hr'] at h; exact absurd h.1 (fun e => Nat.noConfusion e))

/-- The liar: x := ¬x. -/
def liar : Sys := fun _ => .ref 0 true

theorem liar_zero : ¬ ∃ v, Reading liar 0 v := odd_zero liar 0 0 1 rfl rfl

/-! ## The skeptic's engine, in Hardy's three values (agrippa.py F1, F2) -/

section Skeptic
open Hardy
open Hardy.V

def zor : V → V → V := lift2 (fun a b => a || b)

/-- (j ∧ r) → ¬k : the bridge carrying a horn's lethality. -/
def bridge (j k r : V) : V := zimp (zand j r) (znot k)

/-- F1's formula: (bridge_a ∧ bridge_b ∧ bridge_c ∧ j ∧ ((ra ∨ rb) ∨ rc)) → ¬k, greedy lifts throughout. -/
def skeptic (j k ra rb rc : V) : V :=
  zimp (zand (bridge j k ra) (zand (bridge j k rb) (zand (bridge j k rc) (zand j (zor (zor ra rb) rc)))))
    (znot k)

/-- F1: T at every marking — every refinement of every marking included: EARNED, hereditary. -/
theorem skeptic_earned (j k ra rb rc : V) : skeptic j k ra rb rc = T := by
  cases j <;> cases k <;> cases ra <;> cases rb <;> cases rc <;> rfl

/-- F2's package: ((j ∧ rc) → ¬k) ∧ j ∧ rc ∧ ¬k. -/
def package (j k rc : V) : V := zand (bridge j k rc) (zand j (zand rc (znot k)))

/-- F2: everything granted but j (rc = T, k = F): F now, T when j := T, F when j := F — OPEN on j alone. -/
theorem lethality_on_j : package Z F T = F ∧ package T F T = T ∧ package F F T = F := ⟨rfl, rfl, rfl⟩

end Skeptic

end Agrippa

#print axioms Agrippa.pigeon
#print axioms Agrippa.no_regress
#print axioms Agrippa.chain_value
#print axioms Agrippa.odd_zero
#print axioms Agrippa.forced_one
#print axioms Agrippa.even_two
#print axioms Agrippa.nullary_one
#print axioms Agrippa.dogma_two
#print axioms Agrippa.circle_two
#print axioms Agrippa.twoneg_two
#print axioms Agrippa.liar_zero
#print axioms Agrippa.skeptic_earned
#print axioms Agrippa.lethality_on_j
