import ZTopology
/-!
# ZRuntimeGate — a runtime gate that checks admissibility in linear time, without enumerating worlds

Asked 2026-10-05 by the curator for Arkady (DARPA LEGION/ERIS): "prove that the system can check the
admissibility of a composition at runtime without enumerating all possible worlds". The honest form:

* EXACT "is this conclusion EARNED?" is NOT linear in general — in `ZHeredTaut.lean` the hereditary grade is
  shown equivalent to tautology (`hereditary_iff_taut`), a coNP-hard question. No gate can decide it exactly
  in linear time unless P = NP.
* A SOUND gate is linear: evaluate once in the lazy (strong Kleene) register; pass iff the value is T.
  `ZTopology.kleene_sub_earned` already proves that a pass is EARNED. This file adds:

  1. `gate_sound`        — a pass is EARNED (no false pass);
  2. `gateC_steps`       — the gate's cost is exactly the formula's size: one step per node, the same for every
                           marking — independent of how many atoms are unverified (no 2^k search);
  3. `gate_incomplete`   — the price: ¬(a ∧ ¬a) on no data is EARNED and the gate does not pass it; such cases
                           go to a hold / to a human, never to a false pass;
  4. `kevalF_frozen`     — after one atom changes, every subformula that does not mention it keeps its value;
  5. `reval_correct`, `reval_cost` — the incremental re-check: with the previous evaluation cached node by
                           node, re-checking after a change of atom `a` rebuilds only the nodes that mention `a`
                           (cost = `touched a φ` ≤ size φ) and gives exactly the full re-evaluation.

Cost model: one unit per formula node (an atom lookup counts one). Wall-clock latency is a measurement, not a
theorem. The composition WITNESS of `ZComposition.lean` enters as data: the checked values of the joining atoms
are part of the marking, so checking with a witness is the same single pass.

Zero axioms, audited at the bottom.
-/

namespace ZRuntimeGate

open V
open ZTopology

/-! ## The gate and its cost -/

def isT : V → Bool
  | T => true
  | F => false
  | Z => false

/-- THE GATE: one pass in the lazy register; pass iff T. -/
def gate (v : Nat → V) (φ : Fm) : Bool := isT (kevalF v φ)

/-- 1. **No false pass**: what the gate passes is EARNED (T now and after any further data). -/
theorem gate_sound {v : Nat → V} {φ : Fm} (h : gate v φ = true) : earned φ v := by
  unfold gate at h
  cases hk : kevalF v φ with
  | T => exact kleene_sub_earned hk
  | F => rw [hk] at h; exact Bool.noConfusion h
  | Z => rw [hk] at h; exact Bool.noConfusion h

/-- The size of a formula: its number of nodes. -/
def size : Fm → Nat
  | .atom _   => 1
  | .top      => 1
  | .bot      => 1
  | .neg φ    => size φ + 1
  | .conj φ ψ => size φ + size ψ + 1
  | .disj φ ψ => size φ + size ψ + 1
  | .imp φ ψ  => size φ + size ψ + 1
  | .xor φ ψ  => size φ + size ψ + 1
  | .xnor φ ψ => size φ + size ψ + 1

/-- The lazy evaluation with an explicit step counter: one step per node. -/
def kevalC (v : Nat → V) : Fm → V × Nat
  | .atom n   => (v n, 1)
  | .top      => (T, 1)
  | .bot      => (F, 1)
  | .neg φ    => (knot (kevalC v φ).1, (kevalC v φ).2 + 1)
  | .conj φ ψ => (kand (kevalC v φ).1 (kevalC v ψ).1, (kevalC v φ).2 + (kevalC v ψ).2 + 1)
  | .disj φ ψ => (kor (kevalC v φ).1 (kevalC v ψ).1, (kevalC v φ).2 + (kevalC v ψ).2 + 1)
  | .imp φ ψ  => (kimp (kevalC v φ).1 (kevalC v ψ).1, (kevalC v φ).2 + (kevalC v ψ).2 + 1)
  | .xor φ ψ  => (kxor (kevalC v φ).1 (kevalC v ψ).1, (kevalC v φ).2 + (kevalC v ψ).2 + 1)
  | .xnor φ ψ => (kxnor (kevalC v φ).1 (kevalC v ψ).1, (kevalC v φ).2 + (kevalC v ψ).2 + 1)

theorem kevalC_value (v : Nat → V) : ∀ φ, (kevalC v φ).1 = kevalF v φ := by
  intro φ
  induction φ with
  | atom n => rfl
  | top => rfl
  | bot => rfl
  | neg φ ih => show knot (kevalC v φ).1 = knot (kevalF v φ); rw [ih]
  | conj φ ψ ih1 ih2 => show kand (kevalC v φ).1 (kevalC v ψ).1 = kand (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | disj φ ψ ih1 ih2 => show kor (kevalC v φ).1 (kevalC v ψ).1 = kor (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | imp φ ψ ih1 ih2 => show kimp (kevalC v φ).1 (kevalC v ψ).1 = kimp (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | xor φ ψ ih1 ih2 => show kxor (kevalC v φ).1 (kevalC v ψ).1 = kxor (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | xnor φ ψ ih1 ih2 => show kxnor (kevalC v φ).1 (kevalC v ψ).1 = kxnor (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]

/-- The step count is exactly the size — whatever the marking. -/
theorem kevalC_steps (v : Nat → V) : ∀ φ, (kevalC v φ).2 = size φ := by
  intro φ
  induction φ with
  | atom n => rfl
  | top => rfl
  | bot => rfl
  | neg φ ih => show (kevalC v φ).2 + 1 = size φ + 1; rw [ih]
  | conj φ ψ ih1 ih2 => show (kevalC v φ).2 + (kevalC v ψ).2 + 1 = size φ + size ψ + 1; rw [ih1, ih2]
  | disj φ ψ ih1 ih2 => show (kevalC v φ).2 + (kevalC v ψ).2 + 1 = size φ + size ψ + 1; rw [ih1, ih2]
  | imp φ ψ ih1 ih2 => show (kevalC v φ).2 + (kevalC v ψ).2 + 1 = size φ + size ψ + 1; rw [ih1, ih2]
  | xor φ ψ ih1 ih2 => show (kevalC v φ).2 + (kevalC v ψ).2 + 1 = size φ + size ψ + 1; rw [ih1, ih2]
  | xnor φ ψ ih1 ih2 => show (kevalC v φ).2 + (kevalC v ψ).2 + 1 = size φ + size ψ + 1; rw [ih1, ih2]

/-- The gate with its cost. -/
def gateC (v : Nat → V) (φ : Fm) : Bool × Nat := (isT (kevalC v φ).1, (kevalC v φ).2)

/-- 2. **Linear, no enumeration**: the gate's answer is the gate, and its cost is the formula's size — the same
for every marking, however many atoms are unverified. -/
theorem gateC_steps (v : Nat → V) (φ : Fm) : gateC v φ = (gate v φ, size φ) := by
  show (isT (kevalC v φ).1, (kevalC v φ).2) = (isT (kevalF v φ), size φ)
  rw [kevalC_value, kevalC_steps]

/-- 3. **The price, stated**: ¬(a ∧ ¬a) on no data is EARNED, and the gate does not pass it. Incomplete, never
unsound: what it cannot certify goes to a hold, not to a false pass. -/
theorem gate_incomplete : gate blank nonContradiction = false ∧ earned nonContradiction blank :=
  ⟨rfl, not_a_and_not_a_earned⟩

/-! ## Incremental re-checking -/

/-- Does atom `a` occur in φ. -/
def occ (a : Nat) : Fm → Bool
  | .atom n   => Nat.beq n a
  | .top      => false
  | .bot      => false
  | .neg φ    => occ a φ
  | .conj φ ψ => occ a φ || occ a ψ
  | .disj φ ψ => occ a φ || occ a ψ
  | .imp φ ψ  => occ a φ || occ a ψ
  | .xor φ ψ  => occ a φ || occ a ψ
  | .xnor φ ψ => occ a φ || occ a ψ

/-- `Nat.beq n n = true`, proved here: the library's `Nat.beq_refl` pulls propext (measured on this file). -/
theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

theorem or_false_left {x y : Bool} (h : (x || y) = false) : x = false := by
  cases x
  · rfl
  · exact Bool.noConfusion h

theorem or_false_right {x y : Bool} (h : (x || y) = false) : y = false := by
  cases x
  · exact h
  · exact Bool.noConfusion h

/-- 4. **Frozen**: if `v` and `w` differ only at atom `a`, every subformula not mentioning `a` has the same lazy
value under both — its cached value stays valid. -/
theorem kevalF_frozen (a : Nat) (v w : Nat → V) (h : ∀ n, n ≠ a → v n = w n) :
    ∀ φ, occ a φ = false → kevalF v φ = kevalF w φ := by
  intro φ
  induction φ with
  | atom n =>
      intro ho
      show v n = w n
      apply h n
      intro e
      rw [e] at ho
      exact Bool.noConfusion (ho.symm.trans (beq_self a))
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih => intro ho; show knot (kevalF v φ) = knot (kevalF w φ); rw [ih ho]
  | conj φ ψ ih1 ih2 =>
      intro ho
      show kand (kevalF v φ) (kevalF v ψ) = kand (kevalF w φ) (kevalF w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | disj φ ψ ih1 ih2 =>
      intro ho
      show kor (kevalF v φ) (kevalF v ψ) = kor (kevalF w φ) (kevalF w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | imp φ ψ ih1 ih2 =>
      intro ho
      show kimp (kevalF v φ) (kevalF v ψ) = kimp (kevalF w φ) (kevalF w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | xor φ ψ ih1 ih2 =>
      intro ho
      show kxor (kevalF v φ) (kevalF v ψ) = kxor (kevalF w φ) (kevalF w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | xnor φ ψ ih1 ih2 =>
      intro ho
      show kxnor (kevalF v φ) (kevalF v ψ) = kxnor (kevalF w φ) (kevalF w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]

/-- A cached evaluation: the formula's tree with the lazy value stored at every node. -/
inductive CT where
  | leaf : V → CT
  | un   : V → CT → CT
  | bin  : V → CT → CT → CT

def CT.val : CT → V
  | .leaf x    => x
  | .un x _    => x
  | .bin x _ _ => x

def CT.left : CT → CT
  | .leaf x    => .leaf x
  | .un _ c    => c
  | .bin _ l _ => l

def CT.right : CT → CT
  | .leaf x    => .leaf x
  | .un _ c    => c
  | .bin _ _ r => r

/-- Build the cache from scratch: every node evaluated once. -/
def build (v : Nat → V) : Fm → CT
  | .atom n   => .leaf (v n)
  | .top      => .leaf T
  | .bot      => .leaf F
  | .neg φ    => .un (knot (build v φ).val) (build v φ)
  | .conj φ ψ => .bin (kand (build v φ).val (build v ψ).val) (build v φ) (build v ψ)
  | .disj φ ψ => .bin (kor (build v φ).val (build v ψ).val) (build v φ) (build v ψ)
  | .imp φ ψ  => .bin (kimp (build v φ).val (build v ψ).val) (build v φ) (build v ψ)
  | .xor φ ψ  => .bin (kxor (build v φ).val (build v ψ).val) (build v φ) (build v ψ)
  | .xnor φ ψ => .bin (kxnor (build v φ).val (build v ψ).val) (build v φ) (build v ψ)

theorem build_val (v : Nat → V) : ∀ φ, (build v φ).val = kevalF v φ := by
  intro φ
  induction φ with
  | atom n => rfl
  | top => rfl
  | bot => rfl
  | neg φ ih => show knot (build v φ).val = knot (kevalF v φ); rw [ih]
  | conj φ ψ ih1 ih2 => show kand (build v φ).val (build v ψ).val = kand (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | disj φ ψ ih1 ih2 => show kor (build v φ).val (build v ψ).val = kor (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | imp φ ψ ih1 ih2 => show kimp (build v φ).val (build v ψ).val = kimp (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | xor φ ψ ih1 ih2 => show kxor (build v φ).val (build v ψ).val = kxor (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]
  | xnor φ ψ ih1 ih2 => show kxnor (build v φ).val (build v ψ).val = kxnor (kevalF v φ) (kevalF v ψ); rw [ih1, ih2]

/-- The number of nodes that mention atom `a` — what an incremental re-check must touch. -/
def touched (a : Nat) : Fm → Nat
  | .atom n   => if Nat.beq n a then 1 else 0
  | .top      => 0
  | .bot      => 0
  | .neg φ    => if occ a φ then touched a φ + 1 else 0
  | .conj φ ψ => if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0
  | .disj φ ψ => if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0
  | .imp φ ψ  => if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0
  | .xor φ ψ  => if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0
  | .xnor φ ψ => if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0

/-- THE INCREMENTAL RE-CHECK after atom `a` changed (new marking `w`): a node not mentioning `a` is reused from
the cache at no cost; a node mentioning `a` is recomputed from its (recursively re-checked) children, cost 1. -/
def reval (a : Nat) (w : Nat → V) : Fm → CT → CT × Nat
  | .atom n, c   => if Nat.beq n a then (.leaf (w n), 1) else (c, 0)
  | .top, c      => (c, 0)
  | .bot, c      => (c, 0)
  | .neg φ, c    =>
      if occ a φ then
        (.un (knot (reval a w φ c.left).1.val) (reval a w φ c.left).1, (reval a w φ c.left).2 + 1)
      else (c, 0)
  | .conj φ ψ, c => if occ a φ || occ a ψ then
        (.bin (kand (reval a w φ c.left).1.val (reval a w ψ c.right).1.val)
              (reval a w φ c.left).1 (reval a w ψ c.right).1,
         (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1) else (c, 0)
  | .disj φ ψ, c => if occ a φ || occ a ψ then
        (.bin (kor (reval a w φ c.left).1.val (reval a w ψ c.right).1.val)
              (reval a w φ c.left).1 (reval a w ψ c.right).1,
         (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1) else (c, 0)
  | .imp φ ψ, c  => if occ a φ || occ a ψ then
        (.bin (kimp (reval a w φ c.left).1.val (reval a w ψ c.right).1.val)
              (reval a w φ c.left).1 (reval a w ψ c.right).1,
         (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1) else (c, 0)
  | .xor φ ψ, c  => if occ a φ || occ a ψ then
        (.bin (kxor (reval a w φ c.left).1.val (reval a w ψ c.right).1.val)
              (reval a w φ c.left).1 (reval a w ψ c.right).1,
         (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1) else (c, 0)
  | .xnor φ ψ, c => if occ a φ || occ a ψ then
        (.bin (kxnor (reval a w φ c.left).1.val (reval a w ψ c.right).1.val)
              (reval a w φ c.left).1 (reval a w ψ c.right).1,
         (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1) else (c, 0)

/-- A subformula not mentioning `a` builds the same cache under `v` and `w`. -/
theorem build_frozen (a : Nat) (v w : Nat → V) (h : ∀ n, n ≠ a → v n = w n) :
    ∀ φ, occ a φ = false → build v φ = build w φ := by
  intro φ
  induction φ with
  | atom n =>
      intro ho
      show CT.leaf (v n) = CT.leaf (w n)
      have hn : n ≠ a := by
        intro e; rw [e] at ho; exact Bool.noConfusion (ho.symm.trans (beq_self a))
      rw [h n hn]
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih => intro ho; show CT.un _ (build v φ) = CT.un _ (build w φ); rw [ih ho]
  | conj φ ψ ih1 ih2 =>
      intro ho
      show CT.bin _ (build v φ) (build v ψ) = CT.bin _ (build w φ) (build w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | disj φ ψ ih1 ih2 =>
      intro ho
      show CT.bin _ (build v φ) (build v ψ) = CT.bin _ (build w φ) (build w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | imp φ ψ ih1 ih2 =>
      intro ho
      show CT.bin _ (build v φ) (build v ψ) = CT.bin _ (build w φ) (build w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | xor φ ψ ih1 ih2 =>
      intro ho
      show CT.bin _ (build v φ) (build v ψ) = CT.bin _ (build w φ) (build w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]
  | xnor φ ψ ih1 ih2 =>
      intro ho
      show CT.bin _ (build v φ) (build v ψ) = CT.bin _ (build w φ) (build w ψ)
      rw [ih1 (or_false_left ho), ih2 (or_false_right ho)]

/-- 5. **The incremental re-check is exact**: starting from the cache of `v`, re-checking after atom `a`
changed gives exactly the cache a full evaluation under `w` would build. -/
theorem reval_correct (a : Nat) (v w : Nat → V) (h : ∀ n, n ≠ a → v n = w n) :
    ∀ φ, (reval a w φ (build v φ)).1 = build w φ := by
  intro φ
  induction φ with
  | atom n =>
      show (if Nat.beq n a then (CT.leaf (w n), 1) else (CT.leaf (v n), 0)).1 = CT.leaf (w n)
      cases hb : Nat.beq n a with
      | true => rfl
      | false =>
          have hn : n ≠ a := by intro e; rw [e, beq_self] at hb; exact Bool.noConfusion hb
          show CT.leaf (v n) = CT.leaf (w n)
          rw [h n hn]
  | top => rfl
  | bot => rfl
  | neg φ ih =>
      show (if occ a φ then _ else (build v (.neg φ), 0)).1 = build w (.neg φ)
      cases ho : occ a φ with
      | true =>
          show CT.un (knot (reval a w φ (build v φ)).1.val) (reval a w φ (build v φ)).1 = build w (.neg φ)
          rw [ih]; rfl
      | false => exact build_frozen a v w h (.neg φ) ho
  | conj φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then _ else (build v (.conj φ ψ), 0)).1 = build w (.conj φ ψ)
      cases ho : (occ a φ || occ a ψ) with
      | true =>
          show CT.bin (kand (reval a w φ (build v φ)).1.val (reval a w ψ (build v ψ)).1.val)
            (reval a w φ (build v φ)).1 (reval a w ψ (build v ψ)).1 = build w (.conj φ ψ)
          rw [ih1, ih2]; rfl
      | false => exact build_frozen a v w h (.conj φ ψ) ho
  | disj φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then _ else (build v (.disj φ ψ), 0)).1 = build w (.disj φ ψ)
      cases ho : (occ a φ || occ a ψ) with
      | true =>
          show CT.bin (kor (reval a w φ (build v φ)).1.val (reval a w ψ (build v ψ)).1.val)
            (reval a w φ (build v φ)).1 (reval a w ψ (build v ψ)).1 = build w (.disj φ ψ)
          rw [ih1, ih2]; rfl
      | false => exact build_frozen a v w h (.disj φ ψ) ho
  | imp φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then _ else (build v (.imp φ ψ), 0)).1 = build w (.imp φ ψ)
      cases ho : (occ a φ || occ a ψ) with
      | true =>
          show CT.bin (kimp (reval a w φ (build v φ)).1.val (reval a w ψ (build v ψ)).1.val)
            (reval a w φ (build v φ)).1 (reval a w ψ (build v ψ)).1 = build w (.imp φ ψ)
          rw [ih1, ih2]; rfl
      | false => exact build_frozen a v w h (.imp φ ψ) ho
  | xor φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then _ else (build v (.xor φ ψ), 0)).1 = build w (.xor φ ψ)
      cases ho : (occ a φ || occ a ψ) with
      | true =>
          show CT.bin (kxor (reval a w φ (build v φ)).1.val (reval a w ψ (build v ψ)).1.val)
            (reval a w φ (build v φ)).1 (reval a w ψ (build v ψ)).1 = build w (.xor φ ψ)
          rw [ih1, ih2]; rfl
      | false => exact build_frozen a v w h (.xor φ ψ) ho
  | xnor φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then _ else (build v (.xnor φ ψ), 0)).1 = build w (.xnor φ ψ)
      cases ho : (occ a φ || occ a ψ) with
      | true =>
          show CT.bin (kxnor (reval a w φ (build v φ)).1.val (reval a w ψ (build v ψ)).1.val)
            (reval a w φ (build v φ)).1 (reval a w ψ (build v ψ)).1 = build w (.xnor φ ψ)
          rw [ih1, ih2]; rfl
      | false => exact build_frozen a v w h (.xnor φ ψ) ho

/-- 5'. **Its cost is the touched part only**: the re-check recomputes exactly `touched a φ` nodes — the nodes
that mention the changed atom — and reuses everything else. -/
theorem reval_cost (a : Nat) (w : Nat → V) : ∀ φ c, (reval a w φ c).2 = touched a φ := by
  intro φ
  induction φ with
  | atom n =>
      intro c
      show (if Nat.beq n a then (CT.leaf (w n), 1) else (c, 0)).2 = (if Nat.beq n a then 1 else 0)
      cases Nat.beq n a <;> rfl
  | top => intro c; rfl
  | bot => intro c; rfl
  | neg φ ih =>
      intro c
      show (if occ a φ then _ else (c, 0)).2 = (if occ a φ then touched a φ + 1 else 0)
      cases occ a φ with
      | true => show (reval a w φ c.left).2 + 1 = touched a φ + 1; rw [ih]
      | false => rfl
  | conj φ ψ ih1 ih2 =>
      intro c
      show (if occ a φ || occ a ψ then _ else (c, 0)).2 =
           (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0)
      cases (occ a φ || occ a ψ) with
      | true => show (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1 = _; rw [ih1, ih2]; rfl
      | false => rfl
  | disj φ ψ ih1 ih2 =>
      intro c
      show (if occ a φ || occ a ψ then _ else (c, 0)).2 =
           (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0)
      cases (occ a φ || occ a ψ) with
      | true => show (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1 = _; rw [ih1, ih2]; rfl
      | false => rfl
  | imp φ ψ ih1 ih2 =>
      intro c
      show (if occ a φ || occ a ψ then _ else (c, 0)).2 =
           (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0)
      cases (occ a φ || occ a ψ) with
      | true => show (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1 = _; rw [ih1, ih2]; rfl
      | false => rfl
  | xor φ ψ ih1 ih2 =>
      intro c
      show (if occ a φ || occ a ψ then _ else (c, 0)).2 =
           (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0)
      cases (occ a φ || occ a ψ) with
      | true => show (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1 = _; rw [ih1, ih2]; rfl
      | false => rfl
  | xnor φ ψ ih1 ih2 =>
      intro c
      show (if occ a φ || occ a ψ then _ else (c, 0)).2 =
           (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0)
      cases (occ a φ || occ a ψ) with
      | true => show (reval a w φ c.left).2 + (reval a w ψ c.right).2 + 1 = _; rw [ih1, ih2]; rfl
      | false => rfl

/-- And the touched part is never more than the whole. -/
theorem touched_le_size (a : Nat) : ∀ φ, touched a φ ≤ size φ := by
  intro φ
  induction φ with
  | atom n =>
      show (if Nat.beq n a then 1 else 0) ≤ 1
      cases Nat.beq n a
      · exact Nat.zero_le 1
      · exact Nat.le_refl 1
  | top => exact Nat.zero_le 1
  | bot => exact Nat.zero_le 1
  | neg φ ih =>
      show (if occ a φ then touched a φ + 1 else 0) ≤ size φ + 1
      cases occ a φ
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ ih
  | conj φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0) ≤ size φ + size ψ + 1
      cases (occ a φ || occ a ψ)
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (Nat.add_le_add ih1 ih2)
  | disj φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0) ≤ size φ + size ψ + 1
      cases (occ a φ || occ a ψ)
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (Nat.add_le_add ih1 ih2)
  | imp φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0) ≤ size φ + size ψ + 1
      cases (occ a φ || occ a ψ)
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (Nat.add_le_add ih1 ih2)
  | xor φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0) ≤ size φ + size ψ + 1
      cases (occ a φ || occ a ψ)
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (Nat.add_le_add ih1 ih2)
  | xnor φ ψ ih1 ih2 =>
      show (if occ a φ || occ a ψ then touched a φ + touched a ψ + 1 else 0) ≤ size φ + size ψ + 1
      cases (occ a φ || occ a ψ)
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (Nat.add_le_add ih1 ih2)

/-- The gate after a change, read off the re-checked cache: the same answer as a full pass. -/
theorem gate_after_change (a : Nat) (v w : Nat → V) (h : ∀ n, n ≠ a → v n = w n) (φ : Fm) :
    isT (reval a w φ (build v φ)).1.val = gate w φ := by
  rw [reval_correct a v w h φ, build_val]; rfl

end ZRuntimeGate

#print axioms ZRuntimeGate.gate_sound
#print axioms ZRuntimeGate.kevalC_value
#print axioms ZRuntimeGate.kevalC_steps
#print axioms ZRuntimeGate.gateC_steps
#print axioms ZRuntimeGate.gate_incomplete
#print axioms ZRuntimeGate.kevalF_frozen
#print axioms ZRuntimeGate.build_val
#print axioms ZRuntimeGate.build_frozen
#print axioms ZRuntimeGate.reval_correct
#print axioms ZRuntimeGate.reval_cost
#print axioms ZRuntimeGate.touched_le_size
#print axioms ZRuntimeGate.gate_after_change
