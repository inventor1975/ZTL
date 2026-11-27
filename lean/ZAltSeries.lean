import ZExpAdd2

/-!
# ZAltSeries — the bracket `zseries.point` returns: an alternating series with decreasing terms. Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема». `zseries` (Bessel J0, J1, Kelvin ber, bei and
their derivatives) brackets f(x) at a rational x between the partial sums before and after the term t_k at which the
terms have begun to decrease for good: the value lies between S_k and S_{k+1}. Until today a stated premise.

PROVED HERE, over VR's pre-rationals:
  `alt_bracket`  if from index k on the terms alternate in sign and do not grow in size, every later partial sum
                 S_m (m ≥ k) lies between S_k and S_{k+1} — the brackets NEST, so the limit, where it exists, does too
                 (`limit_in_bracket`, VR's reals);
  `ratio_decreasing`  the terms do not grow from k on when |t_{j+1}| = |t_j|·ρ_j with 0 ≤ ρ_{j+1} ≤ ρ_j and ρ_k ≤ 1 —
                 the condition zseries checks at k ("the ratio below 1 and below the previous one") plus the family's
                 ratio decreasing in j (each family's ρ_j is X divided by a product increasing in j).
-/

namespace ZAltSeries
open VR VR.Numbers ZExp ZExpAdd2

/-- t_j and t_{j+1}: opposite signs (weakly), and the second no larger in size. -/
def AltStep (a b : QExpr) : Prop :=
  (qle qzero a → qle b qzero ∧ qle (qneg b) a) ∧ (qle a qzero → qle qzero b ∧ qle b (qneg a))

/-- x lies between u and u + d (d of either sign). -/
def Btw (x u d : QExpr) : Prop :=
  (qle qzero d → qle u x ∧ qle x (qadd u d)) ∧ (qle d qzero → qle (qadd u d) x ∧ qle x u)

/-- The nested step: if S lies between u + d and (u + d) + e, with d, e an AltStep, it lies between u and u + d. -/
theorem nest {x u d e : QExpr} (hs : AltStep d e) (h : Btw x (qadd u d) e) : Btw x u d := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · obtain ⟨he, hed⟩ := hs1 hd
    obtain ⟨b1, b2⟩ := h2 he
    constructor <;> rat_linarith
  · obtain ⟨he, hed⟩ := hs2 hd
    obtain ⟨b1, b2⟩ := h1 he
    constructor <;> rat_linarith

theorem btw_self (u d : QExpr) : Btw (qadd u d) u d := by
  refine ⟨fun hd => ⟨?_, qle_refl _⟩, fun hd => ⟨qle_refl _, ?_⟩⟩ <;> rat_linarith

/-- **THE BRACKET.** If the terms are an AltStep at every index from k on, every S_{k+1+j} lies between S_k and
S_{k+1} = S_k + t_k. -/
theorem alt_bracket (t : Nat → QExpr) (k : Nat) (h : ∀ j, k ≤ j → AltStep (t j) (t (j + 1))) :
    ∀ j, Btw (sumTo t (k + 1 + j)) (sumTo t k) (t k) := by
  -- by induction on j, for every start n ≥ k
  have key : ∀ j n, k ≤ n → Btw (sumTo t (n + 1 + j)) (sumTo t n) (t n) := by
    intro j
    induction j with
    | zero => intro n _; exact btw_self _ _
    | succ j ih =>
        intro n hn
        have hnext := ih (n + 1) (Nat.le_trans hn (Nat.le_succ n))
        have e : n + 1 + (j + 1) = n + 1 + 1 + j := by rw [Nat.add_succ, Nat.add_right_comm (n + 1) 1 j]
        rw [e]
        exact nest (h n hn) hnext
  intro j; exact key j k (Nat.le_refl k)

/-- The limit, where the partial sums converge, lies in the bracket too. -/
theorem limit_in_bracket (t : Nat → QExpr) (k : Nat) (h : ∀ j, k ≤ j → AltStep (t j) (t (j + 1)))
    (L : RExpr) (hL : ∀ n, L.seq n = sumTo t n) (hpos : qle qzero (t k)) :
    rle (rofQ (sumTo t k)) L ∧ rle L (rofQ (qadd (sumTo t k) (t k))) := by
  have hb := alt_bracket t k h
  refine ⟨ZExp.rle_of_eventually (k + 1) (fun n hn => ?_), ZExp.rle_of_eventually (k + 1) (fun n hn => ?_)⟩
  · obtain ⟨j, rfl⟩ := ZExp.le_ex hn
    show qle (sumTo t k) (L.seq (k + 1 + j))
    rw [hL]; exact ((hb j).1 hpos).1
  · obtain ⟨j, rfl⟩ := ZExp.le_ex hn
    show qle (L.seq (k + 1 + j)) (qadd (sumTo t k) (t k))
    rw [hL]; exact ((hb j).1 hpos).2

/-- The terms do not grow: size_{j+1} = size_j · ρ_j, 0 ≤ ρ, ρ decreasing, ρ_k ≤ 1 ⇒ size_{j+1} ≤ size_j for j ≥ k. -/
theorem ratio_decreasing (a ρ : Nat → QExpr) (k : Nat) (ha : ∀ j, qle qzero (a j))
    (hrec : ∀ j, qEq (a (j + 1)) (qmul (a j) (ρ j))) (hρ0 : ∀ j, qle qzero (ρ j))
    (hdec : ∀ j, k ≤ j → qle (ρ (j + 1)) (ρ j)) (hk : qle (ρ k) qone) :
    ∀ j, k ≤ j → qle (a (j + 1)) (a j) := by
  have hle : ∀ d, qle (ρ (k + d)) qone := by
    intro d
    induction d with
    | zero => exact hk
    | succ d ih => exact qle_trans (hdec (k + d) (Nat.le_add_right k d)) ih
  intro j hj
  obtain ⟨d, rfl⟩ := ZExp.le_ex hj
  have h1 := hle d
  have h2 := ha (k + d)
  have hm := ZExp.scale_l h1 h2      -- a·ρ ≤ a·1
  refine qle_respects (qEq_symm (hrec (k + d))) (qmul_one _) hm

end ZAltSeries

#print axioms ZAltSeries.nest
#print axioms ZAltSeries.btw_self
#print axioms ZAltSeries.alt_bracket
#print axioms ZAltSeries.limit_in_bracket
#print axioms ZAltSeries.ratio_decreasing
