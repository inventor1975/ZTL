import ZMajority

/-!
# CHSH — the CHSH game through the ZTL lens. Zero axioms.

Clauser, Horne, Shimony and Holt (1969); in game form, Cleve, Høyer, Toner and Watrous (2004). Written 2026-11-26 at the
curator's word («Беремся»), after the cake-and-drinks case. Twin of VR-ZTL's `ZTL/CHSH.agda`; the judge's run is in
VR-ZTL's `research/chsh/`.

THE GAME. Alice gets x ∈ {0,1}, Bob gets y ∈ {0,1}. They answer a, b ∈ {0,1} without talking and win iff a ⊕ b = x ∧ y.

PROVED HERE:
1. Classical. A deterministic strategy is four pre-written answers a0 a1 b0 b1 (sealed envelopes).
   * Each of the 16 wins 1 or 3 of the 4 rounds, never 0, 2 or 4 (`wins_odd`), so at most 3 (`wins_le_three`).
   * Shared randomness is a weighted list of strategies: total score ≤ 3 · total weight (`mixture_le`). So envelopes,
     socks and coins tossed at the meeting win at most 3/4.
2. Quantum, exact, in integers. Φ⁺ unnormalised (|00⟩+|11⟩, ⟨Φ|Φ⟩ = 2); Alice A0 = Z, A1 = X; Bob B'0 = Z+X, B'1 = Z−X,
   with B'² = 2I, so Bob's real observables are B'/√2.
   * The correlators ⟨Φ|A_x⊗B'_y|Φ⟩ are 2, 2, 2, −2, and S' = 8.
   * The real CHSH value S = S'/(⟨Φ|Φ⟩·√2) has S² = 64/8 = 8 (`tsirelson`): S = 2√2 > 2. With P(win) = 1/2 + S/8,
     quantum wins with (2+√2)/4 ≈ 0.854.
   * Every one-sided correlator is 0: each side alone is a fair coin, so there is no signalling.
3. The judge. With the answers as four unverified atoms, "win all four rounds" is REFUTED IF STABLE (`chsh_stable`) and
   not REFUTED (`chsh_not_refuted`); "not all four" is EARNED IF STABLE. A played round is EARNED. So the envelope bound IS
   the judge's stability condition: each pre-written answer has one value in both rounds it plays in.

WHAT THIS ADDS to `dilemmas/bell.py` (2026-10-02). Its B4 recorded a limit: "(PI ∧ OI ∧ MI) → CHSH ≤ 2" is only on credit,
because the kernel sees PI, OI, MI as independent atoms. With the ANSWERS as atoms instead of the premises, the kernel
does see the bound. bell.py's 2√2 was a Monte-Carlo float; here it is exact.

LIMIT. The two readings bracket the game. Stable allows at most 3/4; occurrence by occurrence allows 4/4, the level of a
Popescu–Rohrlich box (1994). Quantum, (2+√2)/4, lies strictly between, and neither reading locates it: the 2√2
(Tsirelson 1980) comes from the Hilbert-space arithmetic, not from the logic.

NOT CLAIMED: new physics. Every physical number here is textbook.
-/

namespace CHSH

open V ZTopology

/-! ## Classical strategies -/

structure Strat where
  a0 : Bool
  a1 : Bool
  b0 : Bool
  b1 : Bool

def ans : Bool → Bool → Bool → Bool
  | false, p, _ => p
  | true, _, q => q

def xorB : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

def eqB : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

/-- Round (x, y) is won iff a_x ⊕ b_y = x ∧ y. -/
def won (s : Strat) (x y : Bool) : Bool := eqB (xorB (ans x s.a0 s.a1) (ans y s.b0 s.b1)) (x && y)

def one : Bool → Nat
  | true => 1
  | false => 0

def wins (s : Strat) : Nat :=
  one (won s false false) + one (won s false true) + one (won s true false) + one (won s true true)

def oddW : Nat → Bool
  | 1 => true
  | 3 => true
  | _ => false

/-- Every deterministic strategy wins 1 or 3 rounds: never 0, 2 or 4. -/
theorem wins_odd : ∀ p q r t : Bool, oddW (wins ⟨p, q, r, t⟩) = true := by decide

/-- At most 3… -/
theorem wins_le_three : ∀ p q r t : Bool, wins ⟨p, q, r, t⟩ ≤ 3 := by decide

/-- …and 3 is reached (always answer 0). -/
theorem three_reached : wins ⟨false, false, false, false⟩ = 3 := rfl

theorem wins_le (s : Strat) : wins s ≤ 3 := wins_le_three s.a0 s.a1 s.b0 s.b1

/-- Shared randomness: a weighted list of deterministic strategies. -/
def weight : List (Nat × Strat) → Nat
  | [] => 0
  | (w, _) :: m => w + weight m

def score : List (Nat × Strat) → Nat
  | [] => 0
  | (w, s) :: m => w * wins s + score m

/-- Total score ≤ 3 · total weight: shared randomness wins at most 3/4 of the rounds. -/
theorem mixture_le : ∀ m : List (Nat × Strat), score m ≤ 3 * weight m
  | [] => Nat.le_refl 0
  | (w, s) :: m => by
    show w * wins s + score m ≤ 3 * (w + weight m)
    rw [Nat.left_distrib]
    exact Nat.add_le_add (Nat.mul_comm 3 w ▸ Nat.mul_le_mul_left w (wins_le s)) (mixture_le m)

/-! ## Quantum, exact -/

/-- 2×2 integer matrices, indexed by Bool. -/
abbrev M := Bool → Bool → Int

def Id : M
  | false, false => 1
  | false, true => 0
  | true, false => 0
  | true, true => 1

def Zm : M
  | false, false => 1
  | false, true => 0
  | true, false => 0
  | true, true => -1

def Xm : M
  | false, false => 0
  | false, true => 1
  | true, false => 1
  | true, true => 0

def madd (A B : M) : M := fun i j => A i j + B i j
def msub (A B : M) : M := fun i j => A i j - B i j
def mmul (A B : M) : M := fun i j => A i false * B false j + A i true * B true j

/-- Bob's integer observables: √2 times the real ones. -/
def B0' : M := madd Zm Xm
def B1' : M := msub Zm Xm

def sumB (f : Bool → Int) : Int := f false + f true

/-- Φ⁺, unnormalised. -/
def phi : Bool → Bool → Int
  | false, false => 1
  | false, true => 0
  | true, false => 0
  | true, true => 1

/-- ⟨Φ|A⊗B|Φ⟩. -/
def corr (A B : M) : Int :=
  sumB fun i => sumB fun j => sumB fun k => sumB fun l => phi i j * A i k * B j l * phi k l

/-- ⟨Φ|Φ⟩ = 2. -/
theorem norm_phi : corr Id Id = 2 := rfl

/-- B'² = 2I: Bob's real observables are B'/√2, with eigenvalues ±1. -/
theorem B0'_sq : ∀ i j : Bool, mmul B0' B0' i j = 2 * Id i j := by decide
theorem B1'_sq : ∀ i j : Bool, mmul B1' B1' i j = 2 * Id i j := by decide

/-- The four correlators. -/
theorem correlators : corr Zm B0' = 2 ∧ corr Zm B1' = 2 ∧ corr Xm B0' = 2 ∧ corr Xm B1' = -2 := ⟨rfl, rfl, rfl, rfl⟩

def S' : Int := corr Zm B0' + corr Zm B1' + corr Xm B0' - corr Xm B1'

theorem S'_eq : S' = 8 := rfl

/-- S² = S'²/(⟨Φ|Φ⟩²·2) = 64/8 = 8: S = 2√2. -/
theorem tsirelson : S' * S' = 8 * (corr Id Id * corr Id Id * 2) := rfl

/-- No signalling: every one-sided correlator is 0. -/
theorem marginals : corr Zm Id = 0 ∧ corr Xm Id = 0 ∧ corr Id B0' = 0 ∧ corr Id B1' = 0 := ⟨rfl, rfl, rfl, rfl⟩

/-! ## The ZTL reading (measured with zfl.run, 2026-11-26: VR-ZTL research/chsh/judge_output.txt) -/

/-- Atoms: 0 = a0, 1 = a1, 2 = b0, 3 = b1 (pre-written answers). -/
def allFour : Fm :=
  .conj (.conj (.conj (.neg (.xor (.atom 0) (.atom 2))) (.neg (.xor (.atom 0) (.atom 3))))
    (.neg (.xor (.atom 1) (.atom 2)))) (.xor (.atom 1) (.atom 3))

def unverified : Nat → V := fun _ => Z

theorem four : ∀ p q r t : Bool, (((!(p != r) && !(p != t)) && !(q != r)) && (q != t)) = false := by decide

/-- REFUTED IF STABLE: false in every cleaning, i.e. each pre-written answer has one value in both rounds it plays in. -/
theorem chsh_stable : stableF unverified allFour := fun c _ => four (c 0) (c 1) (c 2) (c 3)

/-- "Not all four": EARNED IF STABLE. This is the envelope bound as the judge's disposition. -/
theorem chsh_bound_stable : stableT unverified (.neg allFour) := fun c h => by
  show (!clEval c allFour) = true
  rw [chsh_stable c h]; rfl

/-- …and NOT refuted: occurrence by occurrence, where an answer may depend on the partner's question, all four can be won. -/
theorem chsh_not_refuted : ¬ refutedR unverified allFour :=
  fun h => absurd (show (rd unverified allFour).1 = false from h) (by decide)

/-- A played round, x = 0 and y = 1: a0 and b1 measured (both 1); a1 and b0 never asked. -/
def played : Nat → V
  | 0 => T
  | 1 => Z
  | 2 => Z
  | _ => T

/-- "This round was won" (a0 ⊕ b1 = 0 = 0 ∧ 1): EARNED. -/
theorem round_earned : earned (.neg (.xor (.atom 0) (.atom 3))) played := forced_sub_earned rfl

/-- **THE THEOREM.** Envelopes win at most 3/4: every strategy wins 1 or 3 rounds, and mixtures win ≤ 3/4. The singlet with
the CHSH settings has S² = 8, so S = 2√2 > 2, and it wins with (2+√2)/4 without signalling. The judge reads the envelope
bound as stability: "all four" is REFUTED IF STABLE, not REFUTED, and a played round is EARNED. -/
theorem chsh_verdict :
    (∀ p q r t : Bool, wins ⟨p, q, r, t⟩ ≤ 3) ∧ (∀ m : List (Nat × Strat), score m ≤ 3 * weight m) ∧
    S' = 8 ∧ S' * S' = 8 * (corr Id Id * corr Id Id * 2) ∧
    corr Zm Id = 0 ∧ corr Id B0' = 0 ∧ corr Id B1' = 0 ∧
    stableF unverified allFour ∧ stableT unverified (.neg allFour) ∧ ¬ refutedR unverified allFour ∧
    earned (.neg (.xor (.atom 0) (.atom 3))) played :=
  ⟨wins_le_three, mixture_le, S'_eq, tsirelson, marginals.1, marginals.2.2.1, marginals.2.2.2,
   chsh_stable, chsh_bound_stable, chsh_not_refuted, round_earned⟩

end CHSH

#print axioms CHSH.wins_odd
#print axioms CHSH.wins_le_three
#print axioms CHSH.three_reached
#print axioms CHSH.wins_le
#print axioms CHSH.mixture_le
#print axioms CHSH.norm_phi
#print axioms CHSH.B0'_sq
#print axioms CHSH.B1'_sq
#print axioms CHSH.correlators
#print axioms CHSH.S'_eq
#print axioms CHSH.tsirelson
#print axioms CHSH.marginals
#print axioms CHSH.four
#print axioms CHSH.chsh_stable
#print axioms CHSH.chsh_bound_stable
#print axioms CHSH.chsh_not_refuted
#print axioms CHSH.round_earned
#print axioms CHSH.chsh_verdict
