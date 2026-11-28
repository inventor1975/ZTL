import ZTL
import ZRead

/-!
# QZCtx — Kochen–Specker contextuality is a refutation that needs the stable reading. Zero axioms.

(2026-11-28, Logik2, at the curator's word "если есть, что можешь сам написать в леан то сделай". Written with AI.
The word-first statement is T2 in QZ/THEOREMS-WORDFIRST.md; the measurements are FINDINGS F2 and calib/.)

A family of contexts is a list of bases, each a list of atoms (one atom per ray). `ctx B` says "in every basis
exactly one atom is true": a disjunction of the atoms and every pair excluded, ¬(a ∧ b) (classically this is the
Sasaki form ¬a ∨ (a ∧ ¬b) the lattice needs; here only classical readings are used).

  `exOne_eval`, `ctx_eval`   classically, `ctx B` is true exactly when every basis has exactly one true atom
  `stableF_ctx_iff`          with every atom dirty, the kernel's REFUTED IF STABLE (`stableF`) holds for `ctx B`
                             exactly when the family has NO assignment with exactly one true atom per basis — i.e.
                             when it is Kochen–Specker uncolourable
  `ctx_not_refuted`          but the kernel's strict REFUTED (`refutedR`: no reading of the OCCURRENCES makes it
                             true) never holds for it, if every basis is non-empty: read occurrence by occurrence,
                             each basis is satisfied on its own
  `ks18_refuted_if_stable`   the Cabello–Estebaranz–García-Alcaine 18-vector set (quant-ph/9706009, eqs. (1)–(9)):
                             REFUTED IF STABLE, and not REFUTED — the kernel's own reading of the KS theorem

So non-contextuality is exactly the kernel's stability assumption (one value per question, whatever it is asked
with), and the classical Kochen–Specker contradiction is a refutation that needs it.
Not here: the quantum side — that the same formula is TRUE in the lattice of subspaces (measured, calib/ks18_lattice.py;
in an ortholattice it is the short lemma x ≤ ¬y → ¬x ∨ (x ∧ ¬y) = 1, not written); that the QZ judge withdraws the
stable verdict (QZ4 Splits fails for non-commuting rays; a corollary of QZ9's split_comm, sketched in the word-first
page, not written).
-/

namespace QZCtx
open V

/-- `a₁ ∨ a₂ ∨ …` (⊥ for no atom) -/
def bigOr : List Nat → Fm
  | [] => .bot
  | a :: as => .disj (.atom a) (bigOr as)

/-- `¬(a ∧ b)` for every `b` of the list -/
def allNot (a : Nat) : List Nat → Fm
  | [] => .top
  | b :: bs => .conj (.neg (.conj (.atom a) (.atom b))) (allNot a bs)

/-- every pair of the list excluded -/
def excl : List Nat → Fm
  | [] => .top
  | a :: as => .conj (allNot a as) (excl as)

/-- exactly one atom of the basis -/
def exOne (b : List Nat) : Fm := .conj (bigOr b) (excl b)

/-- the family of contexts -/
def ctx : List (List Nat) → Fm
  | [] => .top
  | b :: bs => .conj (exOne b) (ctx bs)

/-! ### counting, without the library's arithmetic -/

def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

def isOne : Nat → Bool
  | 0 => false
  | n + 1 => isZero n

/-- how many atoms of the list `c` makes true (with multiplicity) -/
def cnt (c : Nat → Bool) : List Nat → Nat
  | [] => 0
  | a :: as => cnt c as + cond (c a) 1 0

theorem absorb : ∀ x y : Bool, (x && (x || y)) = x := by decide

theorem one_of : ∀ n, (!(isZero n) && (isZero n || isOne n)) = isOne n
  | 0 => rfl
  | _ + 1 => rfl

theorem bigOr_eval (c : Nat → Bool) : ∀ b, clEval c (bigOr b) = !(isZero (cnt c b))
  | [] => rfl
  | a :: as => by
    show (c a || clEval c (bigOr as)) = !(isZero (cnt c as + cond (c a) 1 0))
    rw [bigOr_eval c as]
    cases c a <;> rfl

theorem allNot_eval (c : Nat → Bool) (a : Nat) : ∀ bs, clEval c (allNot a bs) = (!(c a) || isZero (cnt c bs))
  | [] => by
    show true = (!(c a) || true)
    cases c a <;> rfl
  | b :: bs => by
    show (!(c a && c b) && clEval c (allNot a bs)) = (!(c a) || isZero (cnt c bs + cond (c b) 1 0))
    rw [allNot_eval c a bs]
    cases c a <;> cases c b <;> rfl

/-- at most one -/
theorem excl_eval (c : Nat → Bool) : ∀ b, clEval c (excl b) = (isZero (cnt c b) || isOne (cnt c b))
  | [] => rfl
  | a :: as => by
    show (clEval c (allNot a as) && clEval c (excl as)) =
      (isZero (cnt c as + cond (c a) 1 0) || isOne (cnt c as + cond (c a) 1 0))
    rw [allNot_eval c a as, excl_eval c as]
    cases c a
    · rfl
    · exact absorb (isZero (cnt c as)) (isOne (cnt c as))

/-- CLASSICALLY, "exactly one" is exactly one -/
theorem exOne_eval (c : Nat → Bool) (b : List Nat) : clEval c (exOne b) = isOne (cnt c b) := by
  show (clEval c (bigOr b) && clEval c (excl b)) = isOne (cnt c b)
  rw [bigOr_eval c b, excl_eval c b]
  exact one_of (cnt c b)

/-- every basis has exactly one true atom -/
def allOne (c : Nat → Bool) : List (List Nat) → Bool
  | [] => true
  | b :: bs => isOne (cnt c b) && allOne c bs

theorem ctx_eval (c : Nat → Bool) : ∀ B, clEval c (ctx B) = allOne c B
  | [] => rfl
  | b :: bs => by
    show (clEval c (exOne b) && clEval c (ctx bs)) = (isOne (cnt c b) && allOne c bs)
    rw [exOne_eval c b, ctx_eval c bs]

/-! ### the kernel's two readings of `ctx B`, every atom dirty -/

theorem cleans_all {v : Nat → V} (hv : ∀ n, v n = Z) (c : Nat → Bool) : cleans v c := by
  intro n
  rw [hv n]
  cases c n <;> rfl

/-- REFUTED IF STABLE ⟺ KOCHEN–SPECKER UNCOLOURABLE: false in every cleaning exactly when no assignment gives every
basis exactly one true atom -/
theorem stableF_ctx_iff {v : Nat → V} (hv : ∀ n, v n = Z) (B : List (List Nat)) :
    stableF v (ctx B) ↔ ∀ c : Nat → Bool, allOne c B = false := by
  constructor
  · intro h c
    have e := h c (cleans_all hv c)
    rw [ctx_eval c B] at e
    exact e
  · intro h c _
    rw [ctx_eval c B]
    exact h c

theorem rd_atom {v : Nat → V} (hv : ∀ n, v n = Z) (n : Nat) : rd v (.atom n) = (true, true) := by
  show ((subs (v n)).contains true, (subs (v n)).contains false) = (true, true)
  rw [hv n]
  rfl

theorem comb_and_fst (p q : Bool × Bool) (hp : p.1 = true) (hq : q.1 = true) :
    (comb (fun a b => a && b) p q).1 = true := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases hp
  cases hq
  rfl

theorem rd_negpair {v : Nat → V} (hv : ∀ n, v n = Z) (a b : Nat) :
    rd v (.neg (.conj (.atom a) (.atom b))) = (true, true) := by
  show ((rd v (.conj (.atom a) (.atom b))).2, (rd v (.conj (.atom a) (.atom b))).1) = (true, true)
  show ((comb (fun x y => x && y) (rd v (.atom a)) (rd v (.atom b))).2,
        (comb (fun x y => x && y) (rd v (.atom a)) (rd v (.atom b))).1) = (true, true)
  rw [rd_atom hv a, rd_atom hv b]
  rfl

theorem allNot_fst {v : Nat → V} (hv : ∀ n, v n = Z) (a : Nat) : ∀ bs, (rd v (allNot a bs)).1 = true
  | [] => rfl
  | b :: bs => by
    show (comb (fun x y => x && y) (rd v (.neg (.conj (.atom a) (.atom b)))) (rd v (allNot a bs))).1 = true
    rw [rd_negpair hv a b]
    exact comb_and_fst _ _ rfl (allNot_fst hv a bs)

theorem excl_fst {v : Nat → V} (hv : ∀ n, v n = Z) : ∀ b, (rd v (excl b)).1 = true
  | [] => rfl
  | a :: as => comb_and_fst _ _ (allNot_fst hv a as) (excl_fst hv as)

/-- the dirty reading of a disjunction of atoms: some reading true, or (for no atom) some reading false -/
theorem bigOr_some {v : Nat → V} (hv : ∀ n, v n = Z) : ∀ b, ((rd v (bigOr b)).1 || (rd v (bigOr b)).2) = true
  | [] => rfl
  | a :: as => by
    show ((comb (fun x y => x || y) (rd v (.atom a)) (rd v (bigOr as))).1 ||
          (comb (fun x y => x || y) (rd v (.atom a)) (rd v (bigOr as))).2) = true
    have ih := bigOr_some hv as
    rw [rd_atom hv a]
    revert ih
    cases rd v (bigOr as) with
    | mk q1 q2 => cases q1 <;> cases q2 <;> intro ih <;> first | rfl | exact absurd ih (by decide)

theorem bigOr_fst {v : Nat → V} (hv : ∀ n, v n = Z) (a : Nat) (as : List Nat) :
    (rd v (bigOr (a :: as))).1 = true := by
  show (comb (fun x y => x || y) (rd v (.atom a)) (rd v (bigOr as))).1 = true
  have ih := bigOr_some hv as
  rw [rd_atom hv a]
  revert ih
  cases rd v (bigOr as) with
  | mk q1 q2 => cases q1 <;> cases q2 <;> intro ih <;> first | rfl | exact absurd ih (by decide)

/-- every basis non-empty -/
def NonEmpty : List (List Nat) → Prop
  | [] => True
  | b :: bs => b ≠ [] ∧ NonEmpty bs

theorem ctx_fst {v : Nat → V} (hv : ∀ n, v n = Z) : ∀ B, NonEmpty B → (rd v (ctx B)).1 = true
  | [], _ => rfl
  | [] :: _, ⟨hb, _⟩ => absurd rfl hb
  | (a :: as) :: bs, ⟨_, hbs⟩ =>
    comb_and_fst _ _ (comb_and_fst _ _ (bigOr_fst hv a as) (excl_fst hv (a :: as))) (ctx_fst hv bs hbs)

/-- BUT NEVER STRICTLY REFUTED: some reading of the occurrences makes `ctx B` true -/
theorem ctx_not_refuted {v : Nat → V} (hv : ∀ n, v n = Z) (B : List (List Nat)) (hB : NonEmpty B) :
    ¬ refutedR v (ctx B) := by
  intro h
  have e : (rd v (ctx B)).1 = true := ctx_fst hv B hB
  unfold refutedR at h
  rw [e] at h
  exact nomatch h

/-! ### the 18-vector set (Cabello, Estebaranz, García-Alcaine 1996, quant-ph/9706009, eqs. (1)-(9))

Rays numbered as in calib/ks18_set.py (sign-normalised, sorted), generated:
0 (0,0,0,1) 1 (0,0,1,0) 2 (0,0,1,1) 3 (0,1,-1,0) 4 (0,1,0,-1) 5 (0,1,0,0) 6 (1,-1,-1,-1) 7 (1,-1,-1,1) 8 (1,-1,0,0) 9 (1,-1,1,-1) 10 (1,0,-1,0) 11 (1,0,0,-1) 12 (1,0,0,1) 13 (1,0,1,0) 14 (1,1,-1,1) 15 (1,1,0,0) 16 (1,1,1,-1) 17 (1,1,1,1)
(the basis lists below are generated from that file, and its orthogonality check is the tie). -/
def ks18 : List (List Nat) := [[0, 1, 15, 8], [0, 5, 13, 10], [9, 7, 15, 2], [9, 17, 10, 4], [1, 5, 12, 11], [7, 17, 11, 3], [14, 16, 8, 2], [14, 6, 13, 4], [16, 6, 12, 3]]

/-- the 18 truth values of an assignment, read from a list -/
def nthB : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: l, n + 1 => nthB l n

-- own lookup: core's List.getD carries propext (MEASURED 28.11)
def fromBits (l : List Bool) (n : Nat) : Bool := nthB l n

/-- every assignment of the next `k` rays, after the ones in `acc`, fails some basis — by enumeration -/
def go : Nat → List Bool → Bool
  | 0, acc => !(allOne (fromBits acc) ks18)
  | k + 1, acc => go k (acc ++ [true]) && go k (acc ++ [false])

-- own list lemmas: core's List.append_nil / List.append_assoc carry propext (MEASURED 28.11, #print axioms)
theorem app_nil : ∀ l : List Bool, l ++ [] = l
  | [] => rfl
  | a :: l => congrArg (a :: ·) (app_nil l)

theorem app_assoc : ∀ a b c : List Bool, (a ++ b) ++ c = a ++ (b ++ c)
  | [], _, _ => rfl
  | x :: a, b, c => congrArg (x :: ·) (app_assoc a b c)

theorem and_l : ∀ x y : Bool, (x && y) = true → x = true := by decide
theorem and_r : ∀ x y : Bool, (x && y) = true → y = true := by decide
theorem not_t : ∀ x : Bool, (!x) = true → x = false := by decide

theorem go_step (k : Nat) (acc : List Bool) (h : go (k + 1) acc = true) : ∀ b : Bool, go k (acc ++ [b]) = true
  | true => and_l (go k (acc ++ [true])) (go k (acc ++ [false])) h
  | false => and_r (go k (acc ++ [true])) (go k (acc ++ [false])) h

theorem go_sound : ∀ (k : Nat) (acc : List Bool), go k acc = true →
    ∀ l : List Bool, l.length = k → allOne (fromBits (acc ++ l)) ks18 = false
  | 0, acc, h, [], _ => by
    rw [app_nil acc]
    exact not_t _ h
  | k + 1, acc, h, b :: l, hl => by
    have r := go_sound k (acc ++ [b]) (go_step k acc h b) l (Nat.succ.inj hl)
    rw [app_assoc acc [b] l] at r
    exact r

/-- THE ENUMERATION, by the kernel: all 2^18 assignments of the 18 rays -/
theorem go_of (k : Nat) (acc : List Bool) (h1 : go k (acc ++ [true]) = true) (h2 : go k (acc ++ [false]) = true) :
    go (k + 1) acc = true := by
  show (go k (acc ++ [true]) && go k (acc ++ [false])) = true
  rw [h1, h2]; rfl

/-! The enumeration in 64 pieces of 2^12 assignments each (one piece of all 2^18 in one declaration ran the kernel out
of memory: MEASURED 12.9 GB; a piece of 2^12: 2.1 GB, seconds), joined by `go_of`. -/

theorem g_111111 : go 12 [true, true, true, true, true, true] = true := by decide +kernel
theorem g_111110 : go 12 [true, true, true, true, true, false] = true := by decide +kernel
theorem g_111101 : go 12 [true, true, true, true, false, true] = true := by decide +kernel
theorem g_111100 : go 12 [true, true, true, true, false, false] = true := by decide +kernel
theorem g_111011 : go 12 [true, true, true, false, true, true] = true := by decide +kernel
theorem g_111010 : go 12 [true, true, true, false, true, false] = true := by decide +kernel
theorem g_111001 : go 12 [true, true, true, false, false, true] = true := by decide +kernel
theorem g_111000 : go 12 [true, true, true, false, false, false] = true := by decide +kernel
theorem g_110111 : go 12 [true, true, false, true, true, true] = true := by decide +kernel
theorem g_110110 : go 12 [true, true, false, true, true, false] = true := by decide +kernel
theorem g_110101 : go 12 [true, true, false, true, false, true] = true := by decide +kernel
theorem g_110100 : go 12 [true, true, false, true, false, false] = true := by decide +kernel
theorem g_110011 : go 12 [true, true, false, false, true, true] = true := by decide +kernel
theorem g_110010 : go 12 [true, true, false, false, true, false] = true := by decide +kernel
theorem g_110001 : go 12 [true, true, false, false, false, true] = true := by decide +kernel
theorem g_110000 : go 12 [true, true, false, false, false, false] = true := by decide +kernel
theorem g_101111 : go 12 [true, false, true, true, true, true] = true := by decide +kernel
theorem g_101110 : go 12 [true, false, true, true, true, false] = true := by decide +kernel
theorem g_101101 : go 12 [true, false, true, true, false, true] = true := by decide +kernel
theorem g_101100 : go 12 [true, false, true, true, false, false] = true := by decide +kernel
theorem g_101011 : go 12 [true, false, true, false, true, true] = true := by decide +kernel
theorem g_101010 : go 12 [true, false, true, false, true, false] = true := by decide +kernel
theorem g_101001 : go 12 [true, false, true, false, false, true] = true := by decide +kernel
theorem g_101000 : go 12 [true, false, true, false, false, false] = true := by decide +kernel
theorem g_100111 : go 12 [true, false, false, true, true, true] = true := by decide +kernel
theorem g_100110 : go 12 [true, false, false, true, true, false] = true := by decide +kernel
theorem g_100101 : go 12 [true, false, false, true, false, true] = true := by decide +kernel
theorem g_100100 : go 12 [true, false, false, true, false, false] = true := by decide +kernel
theorem g_100011 : go 12 [true, false, false, false, true, true] = true := by decide +kernel
theorem g_100010 : go 12 [true, false, false, false, true, false] = true := by decide +kernel
theorem g_100001 : go 12 [true, false, false, false, false, true] = true := by decide +kernel
theorem g_100000 : go 12 [true, false, false, false, false, false] = true := by decide +kernel
theorem g_011111 : go 12 [false, true, true, true, true, true] = true := by decide +kernel
theorem g_011110 : go 12 [false, true, true, true, true, false] = true := by decide +kernel
theorem g_011101 : go 12 [false, true, true, true, false, true] = true := by decide +kernel
theorem g_011100 : go 12 [false, true, true, true, false, false] = true := by decide +kernel
theorem g_011011 : go 12 [false, true, true, false, true, true] = true := by decide +kernel
theorem g_011010 : go 12 [false, true, true, false, true, false] = true := by decide +kernel
theorem g_011001 : go 12 [false, true, true, false, false, true] = true := by decide +kernel
theorem g_011000 : go 12 [false, true, true, false, false, false] = true := by decide +kernel
theorem g_010111 : go 12 [false, true, false, true, true, true] = true := by decide +kernel
theorem g_010110 : go 12 [false, true, false, true, true, false] = true := by decide +kernel
theorem g_010101 : go 12 [false, true, false, true, false, true] = true := by decide +kernel
theorem g_010100 : go 12 [false, true, false, true, false, false] = true := by decide +kernel
theorem g_010011 : go 12 [false, true, false, false, true, true] = true := by decide +kernel
theorem g_010010 : go 12 [false, true, false, false, true, false] = true := by decide +kernel
theorem g_010001 : go 12 [false, true, false, false, false, true] = true := by decide +kernel
theorem g_010000 : go 12 [false, true, false, false, false, false] = true := by decide +kernel
theorem g_001111 : go 12 [false, false, true, true, true, true] = true := by decide +kernel
theorem g_001110 : go 12 [false, false, true, true, true, false] = true := by decide +kernel
theorem g_001101 : go 12 [false, false, true, true, false, true] = true := by decide +kernel
theorem g_001100 : go 12 [false, false, true, true, false, false] = true := by decide +kernel
theorem g_001011 : go 12 [false, false, true, false, true, true] = true := by decide +kernel
theorem g_001010 : go 12 [false, false, true, false, true, false] = true := by decide +kernel
theorem g_001001 : go 12 [false, false, true, false, false, true] = true := by decide +kernel
theorem g_001000 : go 12 [false, false, true, false, false, false] = true := by decide +kernel
theorem g_000111 : go 12 [false, false, false, true, true, true] = true := by decide +kernel
theorem g_000110 : go 12 [false, false, false, true, true, false] = true := by decide +kernel
theorem g_000101 : go 12 [false, false, false, true, false, true] = true := by decide +kernel
theorem g_000100 : go 12 [false, false, false, true, false, false] = true := by decide +kernel
theorem g_000011 : go 12 [false, false, false, false, true, true] = true := by decide +kernel
theorem g_000010 : go 12 [false, false, false, false, true, false] = true := by decide +kernel
theorem g_000001 : go 12 [false, false, false, false, false, true] = true := by decide +kernel
theorem g_000000 : go 12 [false, false, false, false, false, false] = true := by decide +kernel
theorem g_11111 : go 13 [true, true, true, true, true] = true := go_of 12 [true, true, true, true, true] g_111111 g_111110
theorem g_11110 : go 13 [true, true, true, true, false] = true := go_of 12 [true, true, true, true, false] g_111101 g_111100
theorem g_11101 : go 13 [true, true, true, false, true] = true := go_of 12 [true, true, true, false, true] g_111011 g_111010
theorem g_11100 : go 13 [true, true, true, false, false] = true := go_of 12 [true, true, true, false, false] g_111001 g_111000
theorem g_11011 : go 13 [true, true, false, true, true] = true := go_of 12 [true, true, false, true, true] g_110111 g_110110
theorem g_11010 : go 13 [true, true, false, true, false] = true := go_of 12 [true, true, false, true, false] g_110101 g_110100
theorem g_11001 : go 13 [true, true, false, false, true] = true := go_of 12 [true, true, false, false, true] g_110011 g_110010
theorem g_11000 : go 13 [true, true, false, false, false] = true := go_of 12 [true, true, false, false, false] g_110001 g_110000
theorem g_10111 : go 13 [true, false, true, true, true] = true := go_of 12 [true, false, true, true, true] g_101111 g_101110
theorem g_10110 : go 13 [true, false, true, true, false] = true := go_of 12 [true, false, true, true, false] g_101101 g_101100
theorem g_10101 : go 13 [true, false, true, false, true] = true := go_of 12 [true, false, true, false, true] g_101011 g_101010
theorem g_10100 : go 13 [true, false, true, false, false] = true := go_of 12 [true, false, true, false, false] g_101001 g_101000
theorem g_10011 : go 13 [true, false, false, true, true] = true := go_of 12 [true, false, false, true, true] g_100111 g_100110
theorem g_10010 : go 13 [true, false, false, true, false] = true := go_of 12 [true, false, false, true, false] g_100101 g_100100
theorem g_10001 : go 13 [true, false, false, false, true] = true := go_of 12 [true, false, false, false, true] g_100011 g_100010
theorem g_10000 : go 13 [true, false, false, false, false] = true := go_of 12 [true, false, false, false, false] g_100001 g_100000
theorem g_01111 : go 13 [false, true, true, true, true] = true := go_of 12 [false, true, true, true, true] g_011111 g_011110
theorem g_01110 : go 13 [false, true, true, true, false] = true := go_of 12 [false, true, true, true, false] g_011101 g_011100
theorem g_01101 : go 13 [false, true, true, false, true] = true := go_of 12 [false, true, true, false, true] g_011011 g_011010
theorem g_01100 : go 13 [false, true, true, false, false] = true := go_of 12 [false, true, true, false, false] g_011001 g_011000
theorem g_01011 : go 13 [false, true, false, true, true] = true := go_of 12 [false, true, false, true, true] g_010111 g_010110
theorem g_01010 : go 13 [false, true, false, true, false] = true := go_of 12 [false, true, false, true, false] g_010101 g_010100
theorem g_01001 : go 13 [false, true, false, false, true] = true := go_of 12 [false, true, false, false, true] g_010011 g_010010
theorem g_01000 : go 13 [false, true, false, false, false] = true := go_of 12 [false, true, false, false, false] g_010001 g_010000
theorem g_00111 : go 13 [false, false, true, true, true] = true := go_of 12 [false, false, true, true, true] g_001111 g_001110
theorem g_00110 : go 13 [false, false, true, true, false] = true := go_of 12 [false, false, true, true, false] g_001101 g_001100
theorem g_00101 : go 13 [false, false, true, false, true] = true := go_of 12 [false, false, true, false, true] g_001011 g_001010
theorem g_00100 : go 13 [false, false, true, false, false] = true := go_of 12 [false, false, true, false, false] g_001001 g_001000
theorem g_00011 : go 13 [false, false, false, true, true] = true := go_of 12 [false, false, false, true, true] g_000111 g_000110
theorem g_00010 : go 13 [false, false, false, true, false] = true := go_of 12 [false, false, false, true, false] g_000101 g_000100
theorem g_00001 : go 13 [false, false, false, false, true] = true := go_of 12 [false, false, false, false, true] g_000011 g_000010
theorem g_00000 : go 13 [false, false, false, false, false] = true := go_of 12 [false, false, false, false, false] g_000001 g_000000
theorem g_1111 : go 14 [true, true, true, true] = true := go_of 13 [true, true, true, true] g_11111 g_11110
theorem g_1110 : go 14 [true, true, true, false] = true := go_of 13 [true, true, true, false] g_11101 g_11100
theorem g_1101 : go 14 [true, true, false, true] = true := go_of 13 [true, true, false, true] g_11011 g_11010
theorem g_1100 : go 14 [true, true, false, false] = true := go_of 13 [true, true, false, false] g_11001 g_11000
theorem g_1011 : go 14 [true, false, true, true] = true := go_of 13 [true, false, true, true] g_10111 g_10110
theorem g_1010 : go 14 [true, false, true, false] = true := go_of 13 [true, false, true, false] g_10101 g_10100
theorem g_1001 : go 14 [true, false, false, true] = true := go_of 13 [true, false, false, true] g_10011 g_10010
theorem g_1000 : go 14 [true, false, false, false] = true := go_of 13 [true, false, false, false] g_10001 g_10000
theorem g_0111 : go 14 [false, true, true, true] = true := go_of 13 [false, true, true, true] g_01111 g_01110
theorem g_0110 : go 14 [false, true, true, false] = true := go_of 13 [false, true, true, false] g_01101 g_01100
theorem g_0101 : go 14 [false, true, false, true] = true := go_of 13 [false, true, false, true] g_01011 g_01010
theorem g_0100 : go 14 [false, true, false, false] = true := go_of 13 [false, true, false, false] g_01001 g_01000
theorem g_0011 : go 14 [false, false, true, true] = true := go_of 13 [false, false, true, true] g_00111 g_00110
theorem g_0010 : go 14 [false, false, true, false] = true := go_of 13 [false, false, true, false] g_00101 g_00100
theorem g_0001 : go 14 [false, false, false, true] = true := go_of 13 [false, false, false, true] g_00011 g_00010
theorem g_0000 : go 14 [false, false, false, false] = true := go_of 13 [false, false, false, false] g_00001 g_00000
theorem g_111 : go 15 [true, true, true] = true := go_of 14 [true, true, true] g_1111 g_1110
theorem g_110 : go 15 [true, true, false] = true := go_of 14 [true, true, false] g_1101 g_1100
theorem g_101 : go 15 [true, false, true] = true := go_of 14 [true, false, true] g_1011 g_1010
theorem g_100 : go 15 [true, false, false] = true := go_of 14 [true, false, false] g_1001 g_1000
theorem g_011 : go 15 [false, true, true] = true := go_of 14 [false, true, true] g_0111 g_0110
theorem g_010 : go 15 [false, true, false] = true := go_of 14 [false, true, false] g_0101 g_0100
theorem g_001 : go 15 [false, false, true] = true := go_of 14 [false, false, true] g_0011 g_0010
theorem g_000 : go 15 [false, false, false] = true := go_of 14 [false, false, false] g_0001 g_0000
theorem g_11 : go 16 [true, true] = true := go_of 15 [true, true] g_111 g_110
theorem g_10 : go 16 [true, false] = true := go_of 15 [true, false] g_101 g_100
theorem g_01 : go 16 [false, true] = true := go_of 15 [false, true] g_011 g_010
theorem g_00 : go 16 [false, false] = true := go_of 15 [false, false] g_001 g_000
theorem g_1 : go 17 [true] = true := go_of 16 [true] g_11 g_10
theorem g_0 : go 17 [false] = true := go_of 16 [false] g_01 g_00
theorem g_root : go 18 [] = true := go_of 17 [] g_1 g_0
theorem go18 : go 18 [] = true := g_root

theorem ks18_uncolourable (c : Nat → Bool) : allOne c ks18 = false :=
  go_sound 18 [] go18 [c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7, c 8, c 9, c 10, c 11, c 12, c 13, c 14, c 15, c 16, c 17] rfl

/-- THE KERNEL'S READING OF THE KOCHEN–SPECKER THEOREM: the 18-vector contexts are REFUTED IF STABLE, and not
REFUTED — the contradiction needs one value per ray -/
theorem ks18_refuted_if_stable {v : Nat → V} (hv : ∀ n, v n = Z) :
    stableF v (ctx ks18) ∧ ¬ refutedR v (ctx ks18) :=
  ⟨(stableF_ctx_iff hv ks18).2 ks18_uncolourable,
   ctx_not_refuted hv ks18 ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
     by decide, trivial⟩⟩

end QZCtx

#print axioms QZCtx.exOne_eval
#print axioms QZCtx.ctx_eval
#print axioms QZCtx.stableF_ctx_iff
#print axioms QZCtx.ctx_not_refuted
#print axioms QZCtx.go_sound
#print axioms QZCtx.go18
#print axioms QZCtx.ks18_uncolourable
#print axioms QZCtx.ks18_refuted_if_stable
