/-
  ZSwarmBounds.lean — what a swarm of judges guarantees when HOW they fail together is not known.

  WHY (2026-11-05). `ztlnetwork.py` reported that below p = 1/3 more judges make the consensus layer sharply
  safer — computed with INDEPENDENT compromises, never declared. ZTL's degrees say the joint of the judges'
  compromises is the dirty parameter: any joint keeping each judge's own probability p is allowed. Under that
  reading the guarantee is Markov's bound, and it does not grow with the number of judges. This file proves the
  bound, its attainment, and the same bound for the tree of triples of `ZMajority`.

  THE ENCODING (as in ZDempster, E35). A joint distribution is a list of worlds with natural-number weights; the
  probabilities are ratios of weights, and every statement below is scale-free, so no rational arithmetic is
  imported. A judge network's world is a list of flags (judge i compromised or not); a tree's world is a tree
  whose leaves say T, F or Z.

  PROVED, on the empty axiom list:
  1. `markov` — a general weighted Markov inequality: if c ≤ g wherever P holds, then
     c · (weight of P) ≤ Σ weight · g.
  2. `expected_count` — linearity of expectation for the flags: Σ weight · (number compromised) is the sum over
     judges of each judge's own compromised weight. With each judge's share p of the total, that sum is N·p·total.
  3. `network_bound` — so (f+1) · weight(more than f compromised) ≤ Σ_i (judge i's weight): P(the network
     fails) ≤ N·p/(f+1), i.e. P(it holds) ≥ 1 − N·p/(f+1), for EVERY joint. No independence assumed.
  4. `attained_4`, `attained_30`, `attained_90` — and it is attained: at p = 1/10, the joint putting weight on
     "f+1 consecutive judges, cyclically" (each start equally) and the rest on "none" gives every judge exactly
     share 1/10 and makes the bound an equality — P(holds) = 0.8 at N = 4, 0.7 at N = 30 and at N = 90.
  5. `tree_bound` — the tree of triples (`ZMajority`): with `lie_needs` (a depth-d tree says F only with at
     least 2^d lying leaves), 2^d · weight(the tree says F) ≤ Σ weight · (lying leaves): P(capture) ≤
     E[lies]/2^d = 3^d·p/2^d for EVERY joint of the liars — about 5·p at 81 seats.
  6. `unanimous_bound` (2026-11-06, Logik2's note) — admitting only on every judge's T: P(all N wrong together) ≤
     P(judge i wrong) for each i, for EVERY joint — falsely admitted with probability at most the least p_i. More
     judges never make that worse; they cost only availability (a majority rule has no such floor: 1 − N·p/(f+1)).

  NOT PROVED HERE: that the tree bound is ATTAINED (computed, at depth 3, in `zswarm_bounds.py`); how much seats
  drawn at random improve on it — that depends on the liars' joint and on the adversary NOT seeing the draw, and is
  computed exactly in `zswarm_bounds.py` (0.16 against 0.506 at p = 0.1, 81 seats); and the linearity of
  expectation for the tree's leaves (proved here for the flag encoding; for the tree it is the same sum, stated).

  FORM. Arithmetic by hand: `Nat.add_mul` and `Nat.mul_assoc` carry propext on this toolchain (probed), so only
  `Nat.mul_add`, `Nat.mul_comm`, `Nat.add_assoc`, `Nat.add_left_comm`, `Nat.add_comm`, `Nat.add_le_add`,
  `Nat.mul_le_mul_left`, all clean. Predicates are Bool-valued, so no Decidable instance enters.
-/
import ZMajority

namespace ZSwarmBounds

open V

/-! ### Weighted worlds and the Markov inequality -/

/-- The weight of the worlds where `P` holds. -/
def wsumP {α : Type} (P : α → Bool) : List (α × Nat) → Nat
  | [] => 0
  | (x, m) :: r => (match P x with | true => m | false => 0) + wsumP P r

/-- Σ weight · g. -/
def wexp {α : Type} (g : α → Nat) : List (α × Nat) → Nat
  | [] => 0
  | (x, m) :: r => m * g x + wexp g r

/-- The total weight. -/
def wtotal {α : Type} : List (α × Nat) → Nat
  | [] => 0
  | (_, m) :: r => m + wtotal r

theorem markov {α : Type} (P : α → Bool) (g : α → Nat) (c : Nat)
    (h : ∀ x, P x = true → c ≤ g x) : ∀ ws : List (α × Nat), c * wsumP P ws ≤ wexp g ws
  | [] => Nat.le_refl 0
  | (x, m) :: r => by
      show c * ((match P x with | true => m | false => 0) + wsumP P r) ≤ m * g x + wexp g r
      rw [Nat.mul_add]
      apply Nat.add_le_add _ (markov P g c h r)
      cases hp : P x with
      | true =>
          show c * m ≤ m * g x
          rw [Nat.mul_comm c m]
          exact Nat.mul_le_mul_left m (h x hp)
      | false =>
          show c * 0 ≤ m * g x
          rw [Nat.mul_zero]
          exact Nat.zero_le _

/-- Σ weight · (g + h) = Σ weight · g + Σ weight · h. -/
theorem wexp_add {α : Type} (g h : α → Nat) :
    ∀ ws : List (α × Nat), wexp (fun x => g x + h x) ws = wexp g ws + wexp h ws
  | [] => rfl
  | (x, m) :: r => by
      show m * (g x + h x) + wexp (fun x => g x + h x) r = (m * g x + wexp g r) + (m * h x + wexp h r)
      rw [Nat.mul_add, wexp_add g h r, Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm (m * h x)]

/-! ### The judge network -/

/-- A flag as a number. -/
def bit : Bool → Nat
  | true => 1
  | false => 0

/-- The `i`-th flag, a missing one reading "no" — by hand: core's `List.getD` carries propext (probed). -/
def nth : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: r, n + 1 => nth r n

/-- Is judge `i` compromised in world `w`. -/
def flag (w : List Bool) (i : Nat) : Nat := bit (nth w i)

/-- The number of compromised judges among the first `n`. -/
def cnt : Nat → List Bool → Nat
  | 0, _ => 0
  | n + 1, w => cnt n w + flag w n

/-- Judge `i`'s own compromised weight (its probability times the total). -/
def marg (ws : List (List Bool × Nat)) (i : Nat) : Nat := wexp (fun w => flag w i) ws

/-- The sum of the first `n` judges' compromised weights. -/
def sumMarg (ws : List (List Bool × Nat)) : Nat → Nat
  | 0 => 0
  | n + 1 => sumMarg ws n + marg ws n

theorem wexp_zero {α : Type} : ∀ ws : List (α × Nat), wexp (fun _ => 0) ws = 0
  | [] => rfl
  | (_, m) :: r => by
      show m * 0 + wexp (fun _ => 0) r = 0
      rw [Nat.mul_zero, wexp_zero r]

/-- Linearity of expectation: the expected number compromised is the sum of the judges' own probabilities. -/
theorem expected_count (ws : List (List Bool × Nat)) : ∀ n, wexp (cnt n) ws = sumMarg ws n
  | 0 => wexp_zero ws
  | n + 1 => (wexp_add (cnt n) (fun w => flag w n) ws).trans
      (congrArg (fun s => s + marg ws n) (expected_count ws n))

/-- "More than f of the N judges are compromised". -/
def broken (N f : Nat) (w : List Bool) : Bool := Nat.ble (f + 1) (cnt N w)

/-- THE BOUND. For every joint of the compromises: (f+1) · P(more than f compromised) ≤ Σ_i P(judge i
compromised) — i.e. P(the network holds) ≥ 1 − N·p/(f+1) when every judge has share p. -/
theorem network_bound (N f : Nat) (ws : List (List Bool × Nat)) :
    (f + 1) * wsumP (broken N f) ws ≤ sumMarg ws N := by
  exact (expected_count ws N) ▸ markov (broken N f) (cnt N) (f + 1) (fun _ h => Nat.le_of_ble_eq_true h) ws

/-! ### Unanimity: admitting only on every judge's T (Logik2's note, 2026-11-06) -/

/-- "All of the first `n` judges are compromised". -/
def allF : Nat → List Bool → Bool
  | 0, _ => true
  | n + 1, w => allF n w && nth w n

theorem allF_nth : ∀ (n : Nat) (w : List Bool) (i : Nat), i < n → allF n w = true → nth w i = true
  | 0, _, i, h, _ => absurd h (Nat.not_lt_zero i)
  | n + 1, w, i, h, ha => by
      have split : ∀ x y : Bool, (x && y) = true → x = true ∧ y = true := by decide
      have hn : allF n w = true ∧ nth w n = true := split _ _ ha
      cases Nat.lt_or_ge i n with
      | inl hlt => exact allF_nth n w i hlt hn.1
      | inr hge =>
          have hi : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
          rw [hi]; exact hn.2

/-- For EVERY joint: P(all N judges wrong together) ≤ P(judge i wrong), for each i < N — so a verdict admitted only
on unanimity is falsely admitted with probability at most the least p_i, whatever the judges' correlation. More
judges never make it worse; they cost only availability. -/
theorem unanimous_bound (N : Nat) (ws : List (List Bool × Nat)) (i : Nat) (hi : i < N) :
    wsumP (allF N) ws ≤ marg ws i := by
  have h := markov (allF N) (fun w => flag w i) 1 (fun w hw => by
    show 1 ≤ bit (nth w i)
    rw [allF_nth N w i hi hw]; exact Nat.le_refl 1) ws
  rw [Nat.one_mul] at h
  exact h

/-! ### Attained: f+1 consecutive judges, cyclically -/

/-- World "judges k, k+1, ..., k+f (mod N) compromised". -/
def window (N f k : Nat) : List Bool :=
  (List.range N).map (fun i => Nat.blt ((i + N - k) % N) (f + 1))

/-- Every window once with weight 1, and "none compromised" with weight `w0`. -/
def cyclic (N f w0 : Nat) : List (List Bool × Nat) :=
  (List.replicate N false, w0) :: (List.range N).map (fun k => (window N f k, 1))

/-- N = 4, f = 1, p = 1/10: every judge has weight 2 of 20; the failing worlds weigh 4 of 20, and the bound
(f+1)·4 = 8 = Σ_i 2 holds with EQUALITY: P(holds) = 16/20 = 0.8 = 1 − 4·(1/10)/2. -/
theorem attained_4 :
    (List.range 4).map (marg (cyclic 4 1 16)) = List.replicate 4 2 ∧
    wtotal (cyclic 4 1 16) = 20 ∧
    wsumP (broken 4 1) (cyclic 4 1 16) = 4 ∧
    (1 + 1) * wsumP (broken 4 1) (cyclic 4 1 16) = sumMarg (cyclic 4 1 16) 4 := by
  decide

/-- N = 30, f = 9, p = 1/10: weight 10 of 100 per judge; failing worlds 30 of 100; P(holds) = 0.7, equality. -/
theorem attained_30 :
    (List.range 30).map (marg (cyclic 30 9 70)) = List.replicate 30 10 ∧
    wtotal (cyclic 30 9 70) = 100 ∧
    wsumP (broken 30 9) (cyclic 30 9 70) = 30 ∧
    (9 + 1) * wsumP (broken 30 9) (cyclic 30 9 70) = sumMarg (cyclic 30 9 70) 30 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- N = 90, f = 29, p = 1/10: weight 30 of 300 per judge; failing worlds 90 of 300; P(holds) = 0.7, equality. -/
theorem attained_90 :
    (List.range 90).map (marg (cyclic 90 29 210)) = List.replicate 90 30 ∧
    wtotal (cyclic 90 29 210) = 300 ∧
    wsumP (broken 90 29) (cyclic 90 29 210) = 90 ∧
    (29 + 1) * wsumP (broken 90 29) (cyclic 90 29 210) = sumMarg (cyclic 90 29 210) 90 := by
  decide +kernel

/-! ### The tree of triples -/

/-- "The tree says F". -/
def saysF {d : Nat} (t : ZMajority.Tree d) : Bool :=
  match t.fold with
  | T => false
  | F => true
  | Z => false

/-- For every joint of the liars: 2^d · P(the tree says F) ≤ E[lying leaves] — so P(capture) ≤ 3^d·p / 2^d
when every seat lies with probability p (linearity of expectation over the 3^d seats). -/
theorem tree_bound (d : Nat) (ws : List (ZMajority.Tree d × Nat)) :
    ZMajority.pow2 d * wsumP saysF ws ≤ wexp ZMajority.Tree.lies ws := by
  apply markov saysF ZMajority.Tree.lies (ZMajority.pow2 d)
  intro t h
  apply ZMajority.lie_needs t
  revert h
  unfold saysF
  cases t.fold with
  | T => intro h; cases h
  | F => intro _; rfl
  | Z => intro h; cases h

end ZSwarmBounds

#print axioms ZSwarmBounds.markov
#print axioms ZSwarmBounds.wexp_add
#print axioms ZSwarmBounds.expected_count
#print axioms ZSwarmBounds.network_bound
#print axioms ZSwarmBounds.attained_4
#print axioms ZSwarmBounds.attained_30
#print axioms ZSwarmBounds.attained_90
#print axioms ZSwarmBounds.tree_bound
#print axioms ZSwarmBounds.allF_nth
#print axioms ZSwarmBounds.unanimous_bound
