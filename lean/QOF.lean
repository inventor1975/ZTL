import ZRankMany
import ZNet

/-!
# QOF — the kernel's ordered field `ZNet.OF`, BUILT on the empty axiom list, and it COMPUTES. Written with AI (Logik2),
2026-11-28, at the curator's word «Дай Л2 строить» (via Logik1, 01:52).

Every theorem "for any `F : OF α`" (ZNet, ZRound, ZStability, ZHigham, ZChi, ZFloatPath, ZEnergy, ZHypercircle,
QZ8, QZ10) was conditional on such a field existing (Logik1 found no instance, 2026-11-28). `qOF : OF QC` is one:
  * `QC` — VR's pre-rationals that are their own CANONICAL REPRESENTATIVE; Lean's `=` on `QC` is the number's equality;
  * the representative is the FIRST HIT of a fixed enumeration `±k/(d+1)` over growing squares (Part A), so it depends
    only on the number (`norm_canon`: `qEq x y → norm x = norm y`) — no gcd, no quotient, no division algorithm;
  * every law of `OF` is carried over from VR's laws on pre-rationals (`q_ring`, `rat_linarith`, Part C).
MEASURED (`#print axioms`): `qOF`, `qOF_nontrivial` (0 ≠ 1), `decEqC` (decidable `=`), `cmul_inv` (the inverse), `le_mn`,
`mx_le` (QZ8.MinMax's laws) and three computed examples (`decide +kernel`) — NO axioms. A false example is refused.
Traps met: core `Rat`/`Nat.gcd`/`Nat.mul_assoc` carry axioms (RatOF.lean, MEASURED); `unfold` under `∃` pulls
`Quot.sound` (funext) — `rw [f.eq_2]` does not; `norm` is `irreducible` for elaboration (whnf on a symbolic search
timed out), the kernel still evaluates it.
COST: the search is linear in the components' size (unary VR numerals): small fractions only.
-/

/-!
# QSearch — the first hit of a fixed enumeration, independent of the search bound. Zero axioms. Written with AI.

Items `(d, k, s)`; the enumeration runs over growing squares `d ≤ L, k ≤ L`. If two predicates agree pointwise and
each has a hit somewhere, their first hits (searched with any bounds that reach a hit) are THE SAME item.
-/
namespace QSearch

abbrev Item := Nat × Nat × Bool

def tryK (p : Item → Bool) (d k : Nat) : Option Item :=
  cond (p (d, k, true)) (some (d, k, true)) (cond (p (d, k, false)) (some (d, k, false)) none)

def scanK (p : Item → Bool) (d : Nat) : Nat → Option Item
  | 0 => tryK p d 0
  | K + 1 => match scanK p d K with
    | some r => some r
    | none => tryK p d (K + 1)

def scanD (p : Item → Bool) (K : Nat) : Nat → Option Item
  | 0 => scanK p 0 K
  | D + 1 => match scanD p K D with
    | some r => some r
    | none => scanK p (D + 1) K

def search (p : Item → Bool) : Nat → Option Item
  | 0 => scanD p 0 0
  | L + 1 => match search p L with
    | some r => some r
    | none => scanD p (L + 1) (L + 1)

theorem some_inj {a b : Item} (h : some a = some b) : a = b := by injection h

theorem none_ne_some {a : Item} (h : (none : Option Item) = some a) : False := by cases h

/-! ## soundness: a hit satisfies the predicate -/

theorem tryK_sound {p : Item → Bool} {d k : Nat} {r : Item} (h : tryK p d k = some r) : p r = true := by
  unfold tryK at h
  cases h1 : p (d, k, true) with
  | true => rw [h1] at h; have e := some_inj h; rw [← e]; exact h1
  | false =>
    rw [h1] at h
    cases h2 : p (d, k, false) with
    | true => rw [h2] at h; have e := some_inj h; rw [← e]; exact h2
    | false => rw [h2] at h; exact (none_ne_some h).elim

theorem scanK_sound {p : Item → Bool} {d : Nat} : ∀ {K : Nat} {r : Item}, scanK p d K = some r → p r = true
  | 0, _, h => tryK_sound h
  | K + 1, r, h => by
    unfold scanK at h
    cases e : scanK p d K with
    | some r' => rw [e] at h; have := some_inj h; rw [← this]; exact scanK_sound e
    | none => rw [e] at h; exact tryK_sound h

theorem scanD_sound {p : Item → Bool} {K : Nat} : ∀ {D : Nat} {r : Item}, scanD p K D = some r → p r = true
  | 0, _, h => scanK_sound h
  | D + 1, r, h => by
    unfold scanD at h
    cases e : scanD p K D with
    | some r' => rw [e] at h; have := some_inj h; rw [← this]; exact scanD_sound e
    | none => rw [e] at h; exact scanK_sound h

theorem search_sound {p : Item → Bool} : ∀ {L : Nat} {r : Item}, search p L = some r → p r = true
  | 0, _, h => scanD_sound h
  | L + 1, r, h => by
    unfold search at h
    cases e : search p L with
    | some r' => rw [e] at h; have := some_inj h; rw [← this]; exact search_sound e
    | none => rw [e] at h; exact scanD_sound h

/-! ## completeness: an item in the square is reached -/

theorem tryK_some {p : Item → Bool} {d k : Nat} {s : Bool} (h : p (d, k, s) = true) : ∃ r, tryK p d k = some r := by
  unfold tryK
  cases h1 : p (d, k, true) with
  | true => exact ⟨_, rfl⟩
  | false =>
    cases s with
    | true => rw [h1] at h; cases h
    | false => rw [h]; exact ⟨_, rfl⟩

theorem le_cases {k K : Nat} (h : k ≤ K + 1) : k ≤ K ∨ k = K + 1 := by
  cases Nat.lt_or_ge k (K + 1) with
  | inl hl => exact Or.inl (Nat.le_of_lt_succ hl)
  | inr hg => exact Or.inr (Nat.le_antisymm h hg)

theorem scanK_some {p : Item → Bool} {d k : Nat} {s : Bool} (hp : p (d, k, s) = true) (K : Nat) (hk : k ≤ K) :
    ∃ r, scanK p d K = some r := by
  induction K with
  | zero =>
    have e : k = 0 := Nat.le_antisymm hk (Nat.zero_le k)
    rw [e] at hp; exact tryK_some hp
  | succ K ih =>
    rw [scanK.eq_2]
    cases e : scanK p d K with
    | some r => exact ⟨r, rfl⟩
    | none =>
      cases le_cases hk with
      | inl h => obtain ⟨r, hr⟩ := ih h; rw [e] at hr; exact (none_ne_some hr).elim
      | inr h => rw [h] at hp; exact tryK_some hp

theorem scanD_some {p : Item → Bool} {d k K : Nat} {s : Bool} (hp : p (d, k, s) = true) (hk : k ≤ K) (D : Nat)
    (hd : d ≤ D) : ∃ r, scanD p K D = some r := by
  induction D with
  | zero =>
    have e : d = 0 := Nat.le_antisymm hd (Nat.zero_le d)
    rw [e] at hp; exact scanK_some hp K hk
  | succ D ih =>
    rw [scanD.eq_2]
    cases e : scanD p K D with
    | some r => exact ⟨r, rfl⟩
    | none =>
      cases le_cases hd with
      | inl h => obtain ⟨r, hr⟩ := ih h; rw [e] at hr; exact (none_ne_some hr).elim
      | inr h => rw [h] at hp; exact scanK_some hp K hk

theorem search_some {p : Item → Bool} {d k : Nat} {s : Bool} (hp : p (d, k, s) = true) :
    ∀ {L : Nat}, d ≤ L → k ≤ L → ∃ r, search p L = some r
  | 0, hd, hk => scanD_some hp hk 0 hd
  | L + 1, hd, hk => by
    rw [search.eq_2]
    cases e : search p L with
    | some r => exact ⟨r, rfl⟩
    | none => exact scanD_some hp hk (L + 1) hd

/-! ## monotone in the bound, and congruent in the predicate -/

theorem search_succ {p : Item → Bool} {L : Nat} {r : Item} (h : search p L = some r) : search p (L + 1) = some r := by
  unfold search; rw [h]

theorem search_mono {p : Item → Bool} {L : Nat} {r : Item} (h : search p L = some r) :
    ∀ {L' : Nat}, L ≤ L' → search p L' = some r := by
  intro L' hl
  induction hl with
  | refl => exact h
  | step _ ih => exact search_succ ih

theorem tryK_congr {p q : Item → Bool} (h : ∀ i, p i = q i) (d k : Nat) : tryK p d k = tryK q d k := by
  unfold tryK; rw [h (d, k, true), h (d, k, false)]

theorem scanK_congr {p q : Item → Bool} (h : ∀ i, p i = q i) (d : Nat) : ∀ K, scanK p d K = scanK q d K
  | 0 => tryK_congr h d 0
  | K + 1 => by unfold scanK; rw [scanK_congr h d K, tryK_congr h d (K + 1)]

theorem scanD_congr {p q : Item → Bool} (h : ∀ i, p i = q i) (K : Nat) : ∀ D, scanD p K D = scanD q K D
  | 0 => scanK_congr h 0 K
  | D + 1 => by unfold scanD; rw [scanD_congr h K D, scanK_congr h (D + 1) K]

theorem search_congr {p q : Item → Bool} (h : ∀ i, p i = q i) : ∀ L, search p L = search q L
  | 0 => scanD_congr h 0 0
  | L + 1 => by unfold search; rw [search_congr h L, scanD_congr h (L + 1) (L + 1)]

/-- THE FIRST HIT IS CANONICAL: agreeing predicates, any bounds that reach a hit — the same item. -/
theorem first_hit_unique {p q : Item → Bool} (h : ∀ i, p i = q i) {L1 L2 : Nat} {r1 r2 : Item}
    (h1 : search p L1 = some r1) (h2 : search q L2 = some r2) : r1 = r2 := by
  have a := search_mono h1 (Nat.le_add_right L1 L2)
  have b := search_mono h2 (Nat.le_add_left L2 L1)
  rw [search_congr h] at a
  rw [a] at b
  exact some_inj b

end QSearch


/-! # Part B: the canonical representative of a pre-rational -/
namespace QOF
open VR VR.Numbers QSearch

theorem O_inv_vadd (u v : VRObj) : O_inv (vadd u v) = O_inv u + O_inv v := by
  have h : vadd u v = O (O_inv u + O_inv v) := by rw [O_add, O_right_inv, O_right_inv]
  rw [h, O_left_inv]

theorem den_pos_of (d : Nat) : intPos (IntExpr.mk (VRObj.succ (O d)) VRObj.base) :=
  (intPos_iff _).mpr ⟨O d, intEq_refl _⟩

/-- The item `(d, k, s)` read as the pre-rational `±k / (d + 1)`. -/
def toQ (i : Item) : QExpr :=
  ⟨cond i.2.2 (IntExpr.mk (O i.2.1) VRObj.base) (IntExpr.mk VRObj.base (O i.2.1)),
   IntExpr.mk (VRObj.succ (O i.1)) VRObj.base, den_pos_of i.1⟩

/-- The predicate searched for `x`: the item names the same number. -/
def hit (x : QExpr) (i : Item) : Bool := decide (qEq x (toQ i))

/-- A bound that reaches a hit: the sum of the four components. -/
def bnd (x : QExpr) : Nat :=
  match x.num, x.den with
  | .mk a b, .mk c e => O_inv a + O_inv b + O_inv c + O_inv e

def norm (x : QExpr) : QExpr :=
  match search (hit x) (bnd x) with
  | some i => toQ i
  | none => x

theorem qEq_parts {x : QExpr} {n dd : IntExpr} (hd : intPos dd) (hn : intEq x.num n) (hdd : intEq x.den dd) :
    qEq x ⟨n, dd, hd⟩ := by
  show intEq (imul x.num dd) (imul n x.den)
  exact intEq_trans _ _ _ (imul_congr_left hn) (intEq_symm _ _ (imul_congr_right hdd))

theorem le4a (a b c e : Nat) : a ≤ a + b + c + e :=
  Nat.le_trans (Nat.le_add_right a b) (Nat.le_trans (Nat.le_add_right _ c) (Nat.le_add_right _ e))
theorem le4b (a b c e : Nat) : b ≤ a + b + c + e :=
  Nat.le_trans (Nat.le_add_left b a) (Nat.le_trans (Nat.le_add_right _ c) (Nat.le_add_right _ e))
theorem le4c (a b c e : Nat) : c ≤ a + b + c + e :=
  Nat.le_trans (Nat.le_add_left c (a + b)) (Nat.le_add_right _ e)

/-- A hit exists below the bound. -/
theorem hit_exists (x : QExpr) : ∃ d k s, hit x (d, k, s) = true ∧ d ≤ bnd x ∧ k ≤ bnd x := by
  obtain ⟨num, den, hpos⟩ := x
  cases num with
  | mk a b =>
  cases den with
  | mk c e =>
  obtain ⟨m, hm⟩ := (intPos_iff _).mp hpos
  have hm' : vadd c VRObj.base = vadd e (VRObj.succ m) := hm
  have hc : O_inv c = O_inv e + O_inv m + 1 := by
    have : c = VRObj.succ (vadd e m) := hm'
    rw [this]; show O_inv (vadd e m) + 1 = _; rw [O_inv_vadd]
  have hdle : O_inv m ≤ O_inv a + O_inv b + O_inv c + O_inv e := by
    refine Nat.le_trans ?_ (le4c _ _ _ _)
    rw [hc]; exact Nat.le_trans (Nat.le_add_left _ (O_inv e)) (Nat.le_add_right _ 1)
  have hden : intEq (IntExpr.mk c e) (IntExpr.mk (VRObj.succ (O (O_inv m))) VRObj.base) := by
    rw [O_right_inv]; exact hm
  cases canonical_form (IntExpr.mk a b) with
  | inl h =>
    obtain ⟨n, hn⟩ := h
    have hn' : vadd a VRObj.base = vadd b n := hn
    have ha : O_inv a = O_inv b + O_inv n := by
      have : a = vadd b n := hn'
      rw [this, O_inv_vadd]
    refine ⟨O_inv m, O_inv n, true, ?_, hdle, ?_⟩
    · apply decide_eq_true
      apply qEq_parts (den_pos_of _) _ hden
      show intEq (IntExpr.mk a b) (IntExpr.mk (O (O_inv n)) VRObj.base)
      rw [O_right_inv]; exact hn
    · refine Nat.le_trans ?_ (le4a _ _ _ _)
      rw [ha]; exact Nat.le_add_left _ _
  | inr h =>
    obtain ⟨n, hn⟩ := h
    have hn' : vadd a n = vadd b VRObj.base := hn
    have hb : O_inv b = O_inv a + O_inv n := by
      have : b = vadd a n := hn'.symm
      rw [this, O_inv_vadd]
    refine ⟨O_inv m, O_inv n, false, ?_, hdle, ?_⟩
    · apply decide_eq_true
      apply qEq_parts (den_pos_of _) _ hden
      show intEq (IntExpr.mk a b) (IntExpr.mk VRObj.base (O (O_inv n)))
      rw [O_right_inv]; exact hn
    · refine Nat.le_trans ?_ (le4b _ _ _ _)
      rw [hb]; exact Nat.le_add_left _ _

theorem search_hits (x : QExpr) : ∃ i, search (hit x) (bnd x) = some i := by
  obtain ⟨d, k, s, h, hd, hk⟩ := hit_exists x
  exact search_some h hd hk

/-- N1: the representative is the same number. -/
theorem norm_eq (x : QExpr) : qEq (norm x) x := by
  obtain ⟨i, hi⟩ := search_hits x
  have hs := search_sound hi
  show qEq (match search (hit x) (bnd x) with | some i => toQ i | none => x) x
  rw [hi]
  exact qEq_symm (of_decide_eq_true hs)

theorem hit_congr {x y : QExpr} (h : qEq x y) (i : Item) : hit x i = hit y i := by
  unfold hit
  cases h1 : decide (qEq x (toQ i)) with
  | true =>
    have a := of_decide_eq_true h1
    exact (decide_eq_true (qEq_trans (qEq_symm h) a)).symm
  | false =>
    cases h2 : decide (qEq y (toQ i)) with
    | true => exact absurd (qEq_trans h (of_decide_eq_true h2)) (of_decide_eq_false h1)
    | false => rfl

/-- N2: equal numbers have the IDENTICAL representative. -/
theorem norm_canon {x y : QExpr} (h : qEq x y) : norm x = norm y := by
  obtain ⟨i, hi⟩ := search_hits x
  obtain ⟨j, hj⟩ := search_hits y
  have e : i = j := first_hit_unique (hit_congr h) hi hj
  show (match search (hit x) (bnd x) with | some i => toQ i | none => x) =
    (match search (hit y) (bnd y) with | some i => toQ i | none => y)
  rw [hi, hj, e]

theorem norm_idem (x : QExpr) : norm (norm x) = norm x := norm_canon (norm_eq x)

/-- The representative IS an explicit fraction `±k/(d+1)`. -/
theorem norm_is (x : QExpr) : ∃ i, norm x = toQ i := by
  obtain ⟨i, hi⟩ := search_hits x
  refine ⟨i, ?_⟩
  show (match search (hit x) (bnd x) with | some i => toQ i | none => x) = toQ i
  rw [hi]

-- elaboration must never try to evaluate the search on a symbolic argument (the kernel still computes it)
attribute [irreducible] norm

end QOF


/-! # Part C: the canonical rationals as the kernel's ordered field `ZNet.OF` -/
namespace QOF
open VR VR.Numbers ZExp ZNet

/-- The carrier: pre-rationals that are their own representative. Lean's `=` on it is the number's equality. -/
def QC : Type := {x : QExpr // norm x = x}

def mk' (x : QExpr) : QC := ⟨norm x, norm_idem x⟩
theorem valC (x : QExpr) : qEq (mk' x).1 x := norm_eq x
theorem eqC {a b : QC} (h : qEq a.1 b.1) : a = b := Subtype.ext (a.2.symm.trans ((norm_canon h).trans b.2))
theorem ceq {x y : QExpr} (h : qEq x y) : mk' x = mk' y := eqC (qEq_trans (valC x) (qEq_trans h (qEq_symm (valC y))))
theorem selfC (a : QC) : mk' a.1 = a := Subtype.ext a.2
theorem valE {a b : QC} (h : a = b) : qEq a.1 b.1 := by rw [h]; exact qEq_refl _
/-- every element of the carrier is an explicit fraction -/
theorem rep (a : QC) : ∃ i, a.1 = QOF.toQ i := by
  obtain ⟨i, h⟩ := norm_is a.1
  exact ⟨i, a.2.symm.trans h⟩

def czero : QC := mk' qzero
def cone : QC := mk' qone
def cadd (a b : QC) : QC := mk' (qadd a.1 b.1)
def cmul (a b : QC) : QC := mk' (qmul a.1 b.1)
def cneg (a : QC) : QC := mk' (qneg a.1)
def cle (a b : QC) : Prop := qle a.1 b.1

/-- |x| on pre-rationals, by the decided sign. -/
def qabs (x : QExpr) : QExpr := if qle qzero x then x else qneg x
def cabs (a : QC) : QC := mk' (qabs a.1)

theorem qabs_pos {x : QExpr} (h : qle qzero x) : qabs x = x := if_pos h
theorem qabs_neg' {x : QExpr} (h : ¬ qle qzero x) : qabs x = qneg x := if_neg h

theorem nonpos_of_not {x : QExpr} (h : ¬ qle qzero x) : qle x qzero := by
  cases qle_total qzero x with
  | inl h' => exact absurd h' h
  | inr h' => exact h'

theorem qabs_nonneg (x : QExpr) : qle qzero (qabs x) := by
  cases qle.decidable qzero x with
  | isTrue h => rw [qabs_pos h]; exact h
  | isFalse h => rw [qabs_neg' h]; have := nonpos_of_not h; rat_linarith

theorem le_qabs (x : QExpr) : qle x (qabs x) := by
  cases qle.decidable qzero x with
  | isTrue h => rw [qabs_pos h]; exact qle_refl _
  | isFalse h => rw [qabs_neg' h]; have := nonpos_of_not h; rat_linarith

theorem neg_le_qabs (x : QExpr) : qle (qneg x) (qabs x) := by
  cases qle.decidable qzero x with
  | isTrue h => rw [qabs_pos h]; rat_linarith
  | isFalse h => rw [qabs_neg' h]; exact qle_refl _

theorem qabs_cases (x : QExpr) : qEq (qabs x) x ∨ qEq (qabs x) (qneg x) := by
  cases qle.decidable qzero x with
  | isTrue h => rw [qabs_pos h]; exact Or.inl (qEq_refl _)
  | isFalse h => rw [qabs_neg' h]; exact Or.inr (qEq_refl _)

/-- |x| is the largest of x, −x: any u ≥ x, u ≥ −x with u ∈ {x, −x} equals |x|. -/
theorem qabs_eq_of {x u : QExpr} (h1 : qle x u) (h2 : qle (qneg x) u) (h3 : qEq u x ∨ qEq u (qneg x)) :
    qEq (qabs x) u := by
  have a := le_qabs x
  have b := neg_le_qabs x
  have c := qabs_cases x
  cases h3 with
  | inl e => cases c with
    | inl e' => exact qEq_trans e' (qEq_symm e)
    | inr e' => exact qle_antisymm (by have := qle_respects e' (qEq_refl _) (qle_refl _); rat_linarith)
                  (by have := qle_respects (qEq_refl _) e (qle_refl _); rat_linarith)
  | inr e => cases c with
    | inl e' => exact qle_antisymm (by have := qle_respects e' (qEq_refl _) (qle_refl _); rat_linarith)
                  (by have := qle_respects (qEq_refl _) e (qle_refl _); rat_linarith)
    | inr e' => exact qEq_trans e' (qEq_symm e)

theorem qabs_respects {x y : QExpr} (h : qEq x y) : qEq (qabs x) (qabs y) := by
  have a := le_qabs y
  have b := neg_le_qabs y
  refine qabs_eq_of (qle_respects (qEq_symm h) (qEq_refl _) a) (qle_respects (qneg_respects (qEq_symm h)) (qEq_refl _) b) ?_
  cases qabs_cases y with
  | inl e => exact Or.inl (qEq_trans e (qEq_symm h))
  | inr e => exact Or.inr (qEq_trans e (qneg_respects (qEq_symm h)))

theorem qabs_neg_eq (x : QExpr) : qEq (qabs (qneg x)) (qabs x) := by
  have a := le_qabs x
  have b := neg_le_qabs x
  refine qabs_eq_of b (by have e : qEq (qneg (qneg x)) x := by q_ring
                          exact qle_respects (qEq_symm e) (qEq_refl _) a) ?_
  cases qabs_cases x with
  | inl e => exact Or.inr (qEq_trans e (by q_ring))
  | inr e => exact Or.inl e

theorem qabs_mul (x y : QExpr) : qEq (qabs (qmul x y)) (qmul (qabs x) (qabs y)) := by
  have ax := qabs_nonneg x
  have ay := qabs_nonneg y
  have p := qmul_nonneg ax ay
  refine qabs_eq_of ?_ ?_ ?_
  · cases qabs_cases x with
    | inl ex => cases qabs_cases y with
      | inl ey => exact qle_respects (qEq_refl _) (qmul_respects (qEq_symm ex) (qEq_symm ey)) (qle_refl _)
      | inr ey =>
        have hy : qle y qzero := by have := qle_respects (qEq_refl _) ey ay; rat_linarith
        have hx : qle qzero x := qle_respects (qEq_refl _) ex ax
        have n := qmul_nonneg hx (by rat_linarith : qle qzero (qneg y))
        have e : qEq (qmul x (qneg y)) (qneg (qmul x y)) := by q_ring
        have n' := qle_respects (qEq_refl _) e n
        rat_linarith
    | inr ex => cases qabs_cases y with
      | inl ey =>
        have hx : qle x qzero := by have := qle_respects (qEq_refl _) ex ax; rat_linarith
        have hy : qle qzero y := qle_respects (qEq_refl _) ey ay
        have n := qmul_nonneg (by rat_linarith : qle qzero (qneg x)) hy
        have e : qEq (qmul (qneg x) y) (qneg (qmul x y)) := by q_ring
        have n' := qle_respects (qEq_refl _) e n
        rat_linarith
      | inr ey =>
        have e : qEq (qmul (qneg x) (qneg y)) (qmul x y) := by q_ring
        exact qle_respects e (qmul_respects (qEq_symm ex) (qEq_symm ey)) (qle_refl _)
  · cases qabs_cases x with
    | inl ex => cases qabs_cases y with
      | inl ey =>
        have hx : qle qzero x := qle_respects (qEq_refl _) ex ax
        have hy : qle qzero y := qle_respects (qEq_refl _) ey ay
        have n := qmul_nonneg hx hy
        have q := qle_respects (qEq_refl _) (qmul_respects ex ey) p
        rat_linarith
      | inr ey =>
        have e : qEq (qneg (qmul x y)) (qmul x (qneg y)) := by q_ring
        exact qle_respects (qEq_symm e) (qmul_respects (qEq_symm ex) (qEq_symm ey)) (qle_refl _)
    | inr ex => cases qabs_cases y with
      | inl ey =>
        have e : qEq (qneg (qmul x y)) (qmul (qneg x) y) := by q_ring
        exact qle_respects (qEq_symm e) (qmul_respects (qEq_symm ex) (qEq_symm ey)) (qle_refl _)
      | inr ey =>
        have hx : qle x qzero := by have := qle_respects (qEq_refl _) ex ax; rat_linarith
        have hy : qle y qzero := by have := qle_respects (qEq_refl _) ey ay; rat_linarith
        have n := qmul_nonneg (by rat_linarith : qle qzero (qneg x)) (by rat_linarith : qle qzero (qneg y))
        have e : qEq (qmul (qneg x) (qneg y)) (qmul x y) := by q_ring
        have n' := qle_respects (qEq_refl _) e n
        have q := qle_respects (qEq_refl _) (qmul_respects ex ey) p
        have e2 : qEq (qmul (qneg x) (qneg y)) (qmul x y) := by q_ring
        have q' := qle_respects (qEq_refl _) e2 q
        rat_linarith
  · cases qabs_cases x with
    | inl ex => cases qabs_cases y with
      | inl ey => exact Or.inl (qmul_respects ex ey)
      | inr ey => exact Or.inr (qEq_trans (qmul_respects ex ey) (by q_ring))
    | inr ex => cases qabs_cases y with
      | inl ey => exact Or.inr (qEq_trans (qmul_respects ex ey) (by q_ring))
      | inr ey => exact Or.inl (qEq_trans (qmul_respects ex ey) (by q_ring))

theorem zle {a : QC} (h : cle czero a) : qle qzero a.1 := qle_respects (valC _) (qEq_refl _) h
theorem lez {a : QC} (h : cle a czero) : qle a.1 qzero := qle_respects (qEq_refl _) (valC _) h

/-- THE KERNEL'S ORDERED FIELD, BUILT: canonical fractions over VR's pre-rationals. -/
def qOF : OF QC where
  zero := czero
  one := cone
  add := cadd
  mul := cmul
  neg := cneg
  le := cle
  add_comm a b := ceq (by q_ring)
  add_assoc a b c := ceq (qEq_trans (qadd_respects (valC _) (qEq_refl _)) (qEq_trans (by q_ring) (qadd_respects (qEq_refl _) (qEq_symm (valC _)))))
  add_zero a := (ceq (qEq_trans (qadd_respects (qEq_refl _) (valC _)) (by q_ring))).trans (selfC a)
  add_neg a := ceq (qEq_trans (qadd_respects (qEq_refl _) (valC _)) (by q_ring))
  mul_comm a b := ceq (by q_ring)
  mul_assoc a b c := ceq (qEq_trans (qmul_respects (valC _) (qEq_refl _)) (qEq_trans (by q_ring) (qmul_respects (qEq_refl _) (qEq_symm (valC _)))))
  mul_one a := (ceq (qEq_trans (qmul_respects (qEq_refl _) (valC _)) (by q_ring))).trans (selfC a)
  mul_zero a := ceq (qEq_trans (qmul_respects (qEq_refl _) (valC _)) (by q_ring))
  mul_add a b c := ceq (qEq_trans (qmul_respects (qEq_refl _) (valC _)) (qEq_trans (by q_ring) (qadd_respects (qEq_symm (valC _)) (qEq_symm (valC _)))))
  neg_mul a b := ceq (qEq_trans (qmul_respects (valC _) (qEq_refl _)) (qEq_trans (by q_ring) (qneg_respects (qEq_symm (valC _)))))
  neg_neg a := (ceq (qEq_trans (qneg_respects (valC _)) (by q_ring))).trans (selfC a)
  le_refl a := qle_refl a.1
  le_trans h1 h2 := qle_trans h1 h2
  add_le_add := fun {a b c d} h1 h2 => qle_respects (qEq_symm (valC _)) (qEq_symm (valC _))
      (by have h1' : qle a.1 b.1 := h1; have h2' : qle c.1 d.1 := h2; rat_linarith)
  mul_le_mul_left := fun {a b c} hc h => by
    have hc' := zle hc
    have h' : qle a.1 b.1 := h
    have hd : qle qzero (qsub b.1 a.1) := by unfold qsub; rat_linarith
    have m := qmul_nonneg hc' hd
    have e : qEq (qmul c.1 (qsub b.1 a.1)) (qsub (qmul c.1 b.1) (qmul c.1 a.1)) := by unfold qsub; q_ring
    have m' := qle_respects (qEq_refl _) e m
    exact qle_respects (qEq_symm (valC _)) (qEq_symm (valC _)) (by unfold qsub at m'; rat_linarith)
  mul_nonneg := fun {a b} ha hb => qle_respects (qEq_symm (valC _)) (qEq_symm (valC _)) (qmul_nonneg (zle ha) (zle hb))
  sq_nonneg a := qle_respects (qEq_symm (valC _)) (qEq_symm (valC _)) (qmul_self_nonneg a.1)
  nonpos_mul := fun {a b} ha hb => by
    have ha' := lez ha
    have hb' := zle hb
    have m := qmul_nonneg (by rat_linarith : qle qzero (qneg a.1)) hb'
    have e : qEq (qmul (qneg a.1) b.1) (qneg (qmul a.1 b.1)) := by q_ring
    have m' := qle_respects (qEq_refl _) e m
    exact qle_respects (qEq_symm (valC _)) (qEq_symm (valC _)) (by rat_linarith)
  le_of_double := fun {a b} h => by
    have h' := qle_respects (valC _) (valC _) h
    show qle a.1 b.1
    rat_linarith
  le_total a b := qle_total a.1 b.1
  le_antisymm := fun h1 h2 => eqC (qle_antisymm h1 h2)
  mul_eq_zero := fun {a b} h => by
    have hq : qEq (qmul a.1 b.1) qzero := qEq_trans (qEq_symm (valC _)) (qEq_trans (valE h) (valC _))
    cases qEq.decidable a.1 qzero with
    | isTrue ha => exact Or.inl (eqC (qEq_trans ha (qEq_symm (valC _))))
    | isFalse ha =>
      cases qEq.decidable b.1 qzero with
      | isTrue hb => exact Or.inr (eqC (qEq_trans hb (qEq_symm (valC _))))
      | isFalse hb => exact absurd hq (ZRankMany.mul_ne_zero ha hb)
  abs := cabs
  abs_mul a b := ceq (qEq_trans (qabs_respects (valC _)) (qEq_trans (qabs_mul a.1 b.1) (qmul_respects (qEq_symm (valC _)) (qEq_symm (valC _)))))
  abs_add a b := by
    have e1 : qEq (mk' (qabs (mk' (qadd a.1 b.1)).1)).1 (qabs (qadd a.1 b.1)) :=
      qEq_trans (valC (qabs (mk' (qadd a.1 b.1)).1)) (qabs_respects (valC (qadd a.1 b.1)))
    have e2 : qEq (mk' (qadd (mk' (qabs a.1)).1 (mk' (qabs b.1)).1)).1 (qadd (qabs a.1) (qabs b.1)) :=
      qEq_trans (valC (qadd (mk' (qabs a.1)).1 (mk' (qabs b.1)).1)) (qadd_respects (valC (qabs a.1)) (valC (qabs b.1)))
    refine qle_respects (qEq_symm e1) (qEq_symm e2) ?_
    have la := le_qabs a.1
    have lb := le_qabs b.1
    have na := neg_le_qabs a.1
    have nb := neg_le_qabs b.1
    cases qabs_cases (qadd a.1 b.1) with
    | inl e => have := qle_respects (qEq_symm e) (qEq_refl _) (qle_refl (qadd a.1 b.1)); rat_linarith
    | inr e => have := qle_respects (qEq_symm e) (qEq_refl _) (qle_refl (qneg (qadd a.1 b.1))); rat_linarith
  abs_zero := ceq (qEq_trans (qabs_respects (valC _)) (by rw [qabs_pos (qle_refl qzero)]; exact qEq_refl _))
  abs_nonneg a := qle_respects (qEq_symm (valC _)) (qEq_symm (valC _)) (qabs_nonneg a.1)
  abs_of_nonneg := fun {a} h => (ceq (by rw [qabs_pos (zle h)]; exact qEq_refl _)).trans (selfC a)
  abs_neg a := ceq (qEq_trans (qabs_respects (valC _)) (qabs_neg_eq a.1))


/-- NONTRIVIAL: 0 ≠ 1 (the laws of `OF` alone admit a one-element type). -/
theorem qOF_nontrivial : qOF.zero ≠ qOF.one := fun h =>
  absurd (qEq_trans (qEq_symm (valC qzero)) (qEq_trans (valE h) (valC qone))) (by decide)

/-- Equality is DECIDABLE, by the number's equality (no structural equality on the carrier needed). -/
instance decEqC : DecidableEq QC := fun a b =>
  match qEq.decidable a.1 b.1 with
  | isTrue h => isTrue (eqC h)
  | isFalse h => isFalse (fun e => h (valE e))

/-- The inverse (not a field of `OF`; for Gram–Schmidt and QZ10's `c·⟨v,v⟩ = 1`). -/
def cinv (a : QC) : QC := mk' (qinv' a.1)
theorem cmul_inv {a : QC} (h : a ≠ qOF.zero) : qOF.mul a (cinv a) = qOF.one := by
  have ha : ¬ qEq a.1 qzero := fun e => h (eqC (qEq_trans e (qEq_symm (valC qzero))))
  exact ceq (qEq_trans (qmul_respects (qEq_refl _) (valC _)) (qmul_inv'_cancel ha))

/-- min / max with the laws QZ8.MinMax asks for. -/
def cmn (x y : QC) : QC := if qle x.1 y.1 then x else y
def cmx (x y : QC) : QC := if qle x.1 y.1 then y else x
theorem le_mn {a x y : QC} (h1 : qOF.le a x) (h2 : qOF.le a y) : qOF.le a (cmn x y) := by
  unfold cmn; cases qle.decidable x.1 y.1 with
  | isTrue h => rw [if_pos h]; exact h1
  | isFalse h => rw [if_neg h]; exact h2
theorem mx_le {a x y : QC} (h1 : qOF.le x a) (h2 : qOF.le y a) : qOF.le (cmx x y) a := by
  unfold cmx; cases qle.decidable x.1 y.1 with
  | isTrue h => rw [if_pos h]; exact h2
  | isFalse h => rw [if_neg h]; exact h1

/-- A number from an integer numerator and a positive denominator `d + 1`. -/
def frac (k : Nat) (neg : Bool) (d : Nat) : QC := mk' (QOF.toQ (d, k, !neg))

end QOF

/-! It COMPUTES: examples checked by the kernel's evaluation (`decide`). -/
open QOF in
/-- 1/2 + (1/3)·(−3/4) = 1/4 -/
theorem ex_add : qOF.add (frac 1 false 1) (qOF.mul (frac 1 false 2) (frac 3 true 3)) = frac 1 false 3 := by decide +kernel
open QOF in
/-- 1/3 + 1/3 ≠ 1/2 -/
theorem ex_ne : qOF.add (frac 1 false 2) (frac 1 false 2) ≠ frac 1 false 1 := by decide +kernel
open QOF in
/-- (2/3)·(2/3)⁻¹ = 1 -/
theorem ex_inv : qOF.mul (frac 2 false 2) (cinv (frac 2 false 2)) = qOF.one := by decide +kernel

#print axioms QOF.norm_eq
#print axioms QOF.norm_canon
#print axioms QOF.qOF
#print axioms QOF.qOF_nontrivial
#print axioms QOF.decEqC
#print axioms QOF.cmul_inv
#print axioms QOF.le_mn
#print axioms QOF.mx_le
#print axioms QOF.rep
#print axioms ex_add
#print axioms ex_ne
#print axioms ex_inv
