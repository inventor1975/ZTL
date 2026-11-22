import ZTL
/-! # ZRead — the dirty reading: EARNED / REFUTED / IF STABLE from ZTL alone. Zero axioms.

Pure branch (curator 2026-11-22: "only ZTL, from the tables"). No Kleene table is used or defined here.

Z is a dirty parameter: not ours, its owner may change it between two reads, so EACH OCCURRENCE is read
on its own. `rd v φ = (t, f)`: under some reading of the occurrences φ is true (t), resp. false (f).
Readings of a compound are the products of the readings of its parts — that is what "each occurrence on
its own" means — so `rd` is computed connective by connective, in one pass (this IS the fast count; it
needs no third value: "both reachable" is the pair (true, true)).

Dispositions, in the curator's words (2026-11-22):
  * EARNED   — T under every reading of every occurrence: forced.      `earnedR v φ`  ⇔ (rd v φ).2 = false
  * REFUTED  — F under every reading of every occurrence: forced.      `refutedR v φ` ⇔ (rd v φ).1 = false
  * IF STABLE — classically true (false) — one value per atom, every completion — but not forced:
               `stableT v φ` / `stableF v φ` over `Frame.beval`-style completions, below.
The lines from `ok` to `over_grant` are moved verbatim from ZDirty.lean (2026-10-28), where they were
proved first. -/

namespace V

/-- is the classical value a among the reachable ones? -/
def ok (a : Bool) (p : Bool × Bool) : Bool := if a then p.1 else p.2

def comb (g : Bool → Bool → Bool) (p q : Bool × Bool) : Bool × Bool :=
  ([true, false].any (fun a => [true, false].any (fun c => ok a p && ok c q && g a c)),
   [true, false].any (fun a => [true, false].any (fun c => ok a p && ok c q && !(g a c))))

def rd (v : Nat → V) : Fm → Bool × Bool
  | .atom n    => ((subs (v n)).contains true, (subs (v n)).contains false)
  | .top       => (true, false)
  | .bot       => (false, true)
  | .neg φ     => ((rd v φ).2, (rd v φ).1)
  | .conj φ ψ  => comb (fun a b => a && b) (rd v φ) (rd v ψ)
  | .disj φ ψ  => comb (fun a b => a || b) (rd v φ) (rd v ψ)
  | .imp φ ψ   => comb (fun a b => !a || b) (rd v φ) (rd v ψ)
  | .xor φ ψ   => comb (fun a b => a != b) (rd v φ) (rd v ψ)
  | .xnor φ ψ  => comb (fun a b => a == b) (rd v φ) (rd v ψ)

/-- every classical reading of the value x is reachable -/
def covers (x : V) (p : Bool × Bool) : Bool := (subs x).all (fun a => ok a p)

theorem stepNot : ∀ (x : V) (a b : Bool), covers x (a, b) = true → covers (znot x) (b, a) = true := by
  intro x a b; cases x <;> cases a <;> cases b <;> decide

theorem stepBin (g : Bool → Bool → Bool)
    (hg : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
      covers (lift2 g x y) (comb g (a, b) (c, d)) = true)
    (x y : V) (p q : Bool × Bool) (hx : covers x p = true) (hy : covers y q = true) :
    covers (lift2 g x y) (comb g p q) = true := by
  cases p; cases q; exact hg _ _ _ _ _ _ hx hy

theorem hAnd : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a && b) x y) (comb (fun a b => a && b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hOr : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a || b) x y) (comb (fun a b => a || b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hImp : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => !a || b) x y) (comb (fun a b => !a || b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hXor : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a != b) x y) (comb (fun a b => a != b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hXnor : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a == b) x y) (comb (fun a b => a == b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Every classical reading of the ZTL value is reached by some reading of the occurrences. -/
theorem covers_rd (v : Nat → V) : ∀ φ : Fm, covers (evalF v φ) (rd v φ) = true
  | .atom n => by
      show covers (v n) ((subs (v n)).contains true, (subs (v n)).contains false) = true
      cases v n <;> decide
  | .top => rfl
  | .bot => rfl
  | .neg φ => by
      have h := covers_rd v φ
      show covers (znot (evalF v φ)) ((rd v φ).2, (rd v φ).1) = true
      revert h; cases rd v φ; exact stepNot _ _ _
  | .conj φ ψ => stepBin _ hAnd _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .disj φ ψ => stepBin _ hOr _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .imp φ ψ  => stepBin _ hImp _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .xor φ ψ  => stepBin _ hXor _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .xnor φ ψ => stepBin _ hXnor _ _ _ _ (covers_rd v φ) (covers_rd v ψ)

/-- Every refusal is witnessed by a dirty reading: if ZTL says F, some reading of the occurrences is false. -/
theorem refusal_witnessed (v : Nat → V) (φ : Fm) (h : evalF v φ = F) : (rd v φ).2 = true := by
  have c := covers_rd v φ
  rw [h] at c
  revert c; cases rd v φ with
  | mk t f => cases t <;> cases f <;> decide

/-- Never stricter than the dirty reading: true under every reading of the occurrences ⇒ ZTL grants T. -/
theorem never_stricter (v : Nat → V) (φ : Fm) (h : (rd v φ).2 = false) : evalF v φ = T := by
  have c := covers_rd v φ
  revert c; cases e : evalF v φ with
  | T => intro _; rfl
  | F => intro c; have w := refusal_witnessed v φ e; rw [h] at w; exact absurd w (by decide)
  | Z => revert h; cases rd v φ with
    | mk t f => cases t <;> cases f <;> decide

/-- The converse fails: ¬¬p is granted on a dirty p, though a reading of its one occurrence is false. -/
theorem over_grant : evalF (fun _ => Z) (.neg (.neg (.atom 0))) = T ∧
    (rd (fun _ => Z) (.neg (.neg (.atom 0)))).2 = true := by decide


/-! ## The mirror of `never_stricter`: false under every reading ⇒ ZTL refuses. -/

/-- Never laxer than the dirty reading: false under every reading of the occurrences ⇒ ZTL says F. -/
theorem never_laxer (v : Nat → V) (φ : Fm) (h : (rd v φ).1 = false) : evalF v φ = F := by
  have c := covers_rd v φ
  revert c; cases e : evalF v φ with
  | F => intro _; rfl
  | T => intro c; revert c h; cases rd v φ with
    | mk t f => cases t <;> cases f <;> decide
  | Z => intro c; revert c h; cases rd v φ with
    | mk t f => cases t <;> cases f <;> decide

/-! ## The dispositions EARNED / REFUTED, defined by the readings -/

/-- EARNED: no reading of the occurrences makes φ false. -/
def earnedR (v : Nat → V) (φ : Fm) : Prop := (rd v φ).2 = false
/-- REFUTED: no reading of the occurrences makes φ true. -/
def refutedR (v : Nat → V) (φ : Fm) : Prop := (rd v φ).1 = false

theorem earnedR_verdict {v : Nat → V} {φ : Fm} (h : earnedR v φ) : evalF v φ = T := never_stricter v φ h
theorem refutedR_verdict {v : Nat → V} {φ : Fm} (h : refutedR v φ) : evalF v φ = F := never_laxer v φ h

/-! ## More data only narrows the readings (monotonicity, without any third value) -/

/-- `w` knows at least what `v` knows: a checked atom stays as checked. -/
def refinesR (v w : Nat → V) : Prop := ∀ n, v n ≠ Z → w n = v n

/-- pair inclusion: every reading reachable at `q` is reachable at `p` -/
def sub2 (q p : Bool × Bool) : Bool := (!q.1 || p.1) && (!q.2 || p.2)

theorem sub2_atom (a b : V) (h : a ≠ Z → b = a) :
    sub2 ((subs b).contains true, (subs b).contains false) ((subs a).contains true, (subs a).contains false) = true := by
  cases a <;> cases b <;> first | decide | exact absurd (h (by decide)) (by decide)

theorem sub2_neg (q p : Bool × Bool) (h : sub2 q p = true) : sub2 (q.2, q.1) (p.2, p.1) = true := by
  obtain ⟨a, b⟩ := q; obtain ⟨c, d⟩ := p
  revert h; cases a <;> cases b <;> cases c <;> cases d <;> decide

set_option maxHeartbeats 4000000 in
theorem sub2_comb (g : Bool → Bool → Bool) (q p q' p' : Bool × Bool)
    (h1 : sub2 q p = true) (h2 : sub2 q' p' = true) : sub2 (comb g q q') (comb g p p') = true := by
  obtain ⟨a, b⟩ := q; obtain ⟨c, d⟩ := p; obtain ⟨e, f⟩ := q'; obtain ⟨i, j⟩ := p'
  revert h1 h2
  dsimp only [sub2, comb, ok, List.any]
  generalize g true true = w1
  generalize g true false = w2
  generalize g false true = w3
  generalize g false false = w4
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases i <;> cases j <;>
    cases w1 <;> cases w2 <;> cases w3 <;> cases w4 <;> decide

theorem rd_mono {v w : Nat → V} (hr : refinesR v w) : ∀ φ : Fm, sub2 (rd w φ) (rd v φ) = true
  | .atom n    => sub2_atom (v n) (w n) (hr n)
  | .top       => rfl
  | .bot       => rfl
  | .neg φ     => sub2_neg _ _ (rd_mono hr φ)
  | .conj φ ψ  => sub2_comb _ _ _ _ _ (rd_mono hr φ) (rd_mono hr ψ)
  | .disj φ ψ  => sub2_comb _ _ _ _ _ (rd_mono hr φ) (rd_mono hr ψ)
  | .imp φ ψ   => sub2_comb _ _ _ _ _ (rd_mono hr φ) (rd_mono hr ψ)
  | .xor φ ψ   => sub2_comb _ _ _ _ _ (rd_mono hr φ) (rd_mono hr ψ)
  | .xnor φ ψ  => sub2_comb _ _ _ _ _ (rd_mono hr φ) (rd_mono hr ψ)

theorem sub2_false2 (q p : Bool × Bool) (h : sub2 q p = true) (hp : p.2 = false) : q.2 = false := by
  obtain ⟨a, b⟩ := q; obtain ⟨c, d⟩ := p
  revert h hp; cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem sub2_false1 (q p : Bool × Bool) (h : sub2 q p = true) (hp : p.1 = false) : q.1 = false := by
  obtain ⟨a, b⟩ := q; obtain ⟨c, d⟩ := p
  revert h hp; cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- EARNED is hereditary: new data never overturns it. -/
theorem earnedR_open {v w : Nat → V} {φ : Fm} (hr : refinesR v w) (h : earnedR v φ) : earnedR w φ :=
  sub2_false2 _ _ (rd_mono hr φ) h
/-- REFUTED is hereditary. -/
theorem refutedR_open {v w : Nat → V} {φ : Fm} (hr : refinesR v w) (h : refutedR v φ) : refutedR w φ :=
  sub2_false1 _ _ (rd_mono hr φ) h

/-! ## IF STABLE: one value per atom (a completion) — classical truth over every cleaning -/

/-- classical evaluation under one value per atom -/
def clEval (c : Nat → Bool) : Fm → Bool
  | .atom n    => c n
  | .top       => true
  | .bot       => false
  | .neg φ     => !(clEval c φ)
  | .conj φ ψ  => clEval c φ && clEval c ψ
  | .disj φ ψ  => clEval c φ || clEval c ψ
  | .imp φ ψ   => !(clEval c φ) || clEval c ψ
  | .xor φ ψ   => clEval c φ != clEval c ψ
  | .xnor φ ψ  => clEval c φ == clEval c ψ

/-- `c` cleans `v`: a checked atom keeps its value, a dirty one gets either. -/
def cleans (v : Nat → V) (c : Nat → Bool) : Prop := ∀ n, (subs (v n)).contains (c n) = true

/-- classically true in every cleaning (the judge's EARNED IF STABLE, when not EARNED) -/
def stableT (v : Nat → V) (φ : Fm) : Prop := ∀ c, cleans v c → clEval c φ = true
/-- classically false in every cleaning (REFUTED IF STABLE, when not REFUTED) -/
def stableF (v : Nat → V) (φ : Fm) : Prop := ∀ c, cleans v c → clEval c φ = false

theorem ok_atom (x : V) (b : Bool) (h : (subs x).contains b = true) :
    ok b ((subs x).contains true, (subs x).contains false) = true := by
  revert h; cases x <;> cases b <;> decide

theorem ok_neg (b : Bool) (p : Bool × Bool) (h : ok b p = true) : ok (!b) (p.2, p.1) = true := by
  obtain ⟨t, f⟩ := p; revert h; cases b <;> cases t <;> cases f <;> decide

theorem ok_comb (g : Bool → Bool → Bool) (a c : Bool) (p q : Bool × Bool)
    (ha : ok a p = true) (hc : ok c q = true) : ok (g a c) (comb g p q) = true := by
  obtain ⟨t, f⟩ := p; obtain ⟨t', f'⟩ := q
  revert ha hc
  cases a <;> cases c <;>
  (dsimp only [comb, ok, List.any]
   generalize g true true = w1
   generalize g true false = w2
   generalize g false true = w3
   generalize g false false = w4
   cases t <;> cases f <;> cases t' <;> cases f' <;> cases w1 <;> cases w2 <;> cases w3 <;> cases w4 <;> decide)

/-- a cleaning is one reading (every occurrence of an atom read alike): its value is reachable -/
theorem cleaning_is_reading {v : Nat → V} {c : Nat → Bool} (hc : cleans v c) :
    ∀ φ : Fm, ok (clEval c φ) (rd v φ) = true
  | .atom n    => ok_atom (v n) (c n) (hc n)
  | .top       => rfl
  | .bot       => rfl
  | .neg φ     => ok_neg _ _ (cleaning_is_reading hc φ)
  | .conj φ ψ => ok_comb (fun a b => a && b) _ _ _ _ (cleaning_is_reading hc φ) (cleaning_is_reading hc ψ)
  | .disj φ ψ => ok_comb (fun a b => a || b) _ _ _ _ (cleaning_is_reading hc φ) (cleaning_is_reading hc ψ)
  | .imp φ ψ => ok_comb (fun a b => !a || b) _ _ _ _ (cleaning_is_reading hc φ) (cleaning_is_reading hc ψ)
  | .xor φ ψ => ok_comb (fun a b => a != b) _ _ _ _ (cleaning_is_reading hc φ) (cleaning_is_reading hc ψ)
  | .xnor φ ψ => ok_comb (fun a b => a == b) _ _ _ _ (cleaning_is_reading hc φ) (cleaning_is_reading hc ψ)

/-- EARNED ⇒ EARNED IF STABLE: forced truth is classical truth in every cleaning. -/
theorem earnedR_stable {v : Nat → V} {φ : Fm} (h : earnedR v φ) : stableT v φ := by
  intro c hc
  have k := cleaning_is_reading hc φ
  revert k; unfold earnedR at h; cases e : clEval c φ with
  | true => intro _; rfl
  | false => intro k; change (rd v φ).2 = true at k; rw [h] at k; exact Bool.noConfusion k

/-- REFUTED ⇒ REFUTED IF STABLE. -/
theorem refutedR_stable {v : Nat → V} {φ : Fm} (h : refutedR v φ) : stableF v φ := by
  intro c hc
  have k := cleaning_is_reading hc φ
  revert k; unfold refutedR at h; cases e : clEval c φ with
  | false => intro _; rfl
  | true => intro k; change (rd v φ).1 = true at k; rw [h] at k; exact Bool.noConfusion k

/-! ## The strict case the curator named: x ↔ x is classically true, not forced -/

def blankR : Nat → V := fun _ => Z
def selfEq : Fm := .xnor (.atom 0) (.atom 0)

theorem selfEq_not_forced : ¬ earnedR blankR selfEq := by
  unfold earnedR; intro h; exact absurd h (by decide)

theorem selfEq_stable : stableT blankR selfEq := by
  intro c _; show (c 0 == c 0) = true; cases c 0 <;> rfl

end V

#print axioms V.covers_rd
#print axioms V.refusal_witnessed
#print axioms V.never_stricter
#print axioms V.never_laxer
#print axioms V.over_grant
#print axioms V.rd_mono
#print axioms V.earnedR_open
#print axioms V.refutedR_open
#print axioms V.cleaning_is_reading
#print axioms V.earnedR_stable
#print axioms V.refutedR_stable
#print axioms V.selfEq_not_forced
#print axioms V.selfEq_stable
