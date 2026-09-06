import LabelExact

/-!
# The exact receipt is NP-hard to know — E59. Zero axioms.

`receipt_complete` (Receipt.lean) says the label is never too small;
`label_exact_linear` (LabelExact.lean) says that on a linear claim it is never
too large; `clash_names_an_idle_atom` says that without linearity it can be —
`p ∧ ¬p` names an atom no reading moves. What remained open was the BOUNDARY:
is there a cheap exact rule — a class wider than linearity, a repair of `labF`
— that names an atom exactly when the answer is waiting on it? This file says
no cheap rule exists at all: deciding whether a named atom is idle is deciding
satisfiability.

THE WITNESS. For a formula ψ that does not read the atom `a` and carries no
constant, put

    R_ψ := (a ∨ (ψ ∧ ¬ψ)) ∧ ψ

`ψ ∧ ¬ψ` is the false that keeps the mark: F wherever ψ is settled, Z
wherever ψ still waits (`kand Z Z = Z`). At the all-marked start everything
is Z, the claim is pending, and the receipt names `a` (`named`) — by its own
rule, since neither branch of the outer conjunction is settled.

Whether `a` was worth naming (`pivotal`, LabelExact.lean: a reading of the
other unverified grounds — possibly partial — under which `a := T` and
`a := F` give different verdicts) is then exactly whether ψ has a classical
point. With `a := T` the claim reads `ψ`; with `a := F` it reads `ψ ∧ ¬ψ`,
which is Z where ψ is Z and F where ψ is settled; the two differ precisely
where ψ reads T (`sides_ne`). A partial reading on which ψ reads T lies
below a classical one, and the lazy register is monotone (`evalK_mono`), so
the classical point reads T as well.

    named            :  labF allZ R_ψ a = true
    pivotal_iff_sat  :  pivotal allZ R_ψ a  ↔  ∃ c classical, evalK c ψ = T

(Only `named` needs ψ constant-free — the receipt names `a` only while the
claim is pending; the equivalence itself needs just that `a` is not read by ψ.)

WHY NOT THE SIMPLER `a ∧ ψ`. Under a reading that leaves ψ's atoms marked,
`a := T` gives Z and `a := F` gives F — different, so `a` is pivotal
whatever ψ is (`conj_always_pivotal`, the negative control, proved so that
the shape of the witness is seen to be forced rather than chosen). The
reduction needs the false that keeps the mark, so that both sides wait
together.

WHAT FOLLOWS, in prose since complexity classes are not formalised here:
R_ψ has the size of three copies of ψ plus a constant, so a procedure that
decides in polynomial time whether a named atom is idle decides SAT(ψ). The
exact receipt is therefore NP-HARD — that is the claim, and the reduction
above is its whole content.

CLAIM GRADE. NP-hard is the claim. Membership in NP (a pair of readings as a
certificate, checked by two evaluations) is an argument in prose that
nothing here formalises; it is not claimed, so "NP-complete" is not said.
Hence `labF` — the cheap candidate list, complete by `receipt_complete`,
exact on linear claims by `label_exact_linear` — is the forced cut, as
`joint` is for the width (E58). With E57 and E58 this makes three grades
the judge does not compute, and they are the three it cannot compute
cheaply: hereditary (coNP-hard), exact width (NP-hard), exact receipt
(NP-hard).

MEASURED FIRST (`zreceipthard.py`: the judge's own `_lazy`, and `pivotal`
read literally, partial readings included). On all 2906 formulas ψ of depth
≤ 2 over two atoms, `a` is named on every one and "pivotal ⟺ satisfiable"
holds on every one; `a ∧ ψ` is pivotal on every one. A note the measurement
forced on §19's prose: `pivotal` quantifies over readings that may leave
other grounds marked, while the paper said "a definite reading". On 48,759
pending linear cells the two notions agree on every named atom (57,969 of
them), but the theorem proves the weaker one, and the paper now says what
the theorem says.
-/

namespace V

/-- Every ground still unverified. -/
def allZ : Nat → V := fun _ => Z

/-- No `⊤`/`⊥` inside — what keeps a formula at Z while every atom is Z. -/
def constFree : Fm → Bool
  | .atom _ => true
  | .top => false
  | .bot => false
  | .neg φ => constFree φ
  | .conj φ ψ => constFree φ && constFree ψ
  | .disj φ ψ => constFree φ && constFree ψ
  | .imp φ ψ => constFree φ && constFree ψ
  | .xor φ ψ => constFree φ && constFree ψ
  | .xnor φ ψ => constFree φ && constFree ψ

theorem and_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => exact Bool.noConfusion h

theorem and_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- A constant-free claim waits while every ground waits. -/
theorem evalK_allZ : ∀ φ : Fm, constFree φ = true → evalK allZ φ = Z := by
  intro φ
  induction φ with
  | atom n => intro _; rfl
  | top => intro h; exact Bool.noConfusion h
  | bot => intro h; exact Bool.noConfusion h
  | neg φ ih =>
      intro h
      show knot (evalK allZ φ) = Z
      rw [ih h]; rfl
  | conj φ ψ ihφ ihψ =>
      intro h
      show kand (evalK allZ φ) (evalK allZ ψ) = Z
      rw [ihφ (and_true_left h), ihψ (and_true_right h)]; rfl
  | disj φ ψ ihφ ihψ =>
      intro h
      show kor (evalK allZ φ) (evalK allZ ψ) = Z
      rw [ihφ (and_true_left h), ihψ (and_true_right h)]; rfl
  | imp φ ψ ihφ ihψ =>
      intro h
      show kimp (evalK allZ φ) (evalK allZ ψ) = Z
      rw [ihφ (and_true_left h), ihψ (and_true_right h)]; rfl
  | xor φ ψ ihφ ihψ =>
      intro h
      show kxor (evalK allZ φ) (evalK allZ ψ) = Z
      rw [ihφ (and_true_left h), ihψ (and_true_right h)]; rfl
  | xnor φ ψ ihφ ihψ =>
      intro h
      show kxnor (evalK allZ φ) (evalK allZ ψ) = Z
      rw [ihφ (and_true_left h), ihψ (and_true_right h)]; rfl

/-! ## The witness -/

/-- `ψ ∧ ¬ψ`: F wherever ψ is settled, Z wherever ψ still waits. -/
def zfalse (ψ : Fm) : Fm := Fm.conj ψ (Fm.neg ψ)

/-- `(a ∨ (ψ ∧ ¬ψ)) ∧ ψ`. -/
def witnessR (a : Nat) (ψ : Fm) : Fm := Fm.conj (Fm.disj (Fm.atom a) (zfalse ψ)) ψ

/-- With `a := T` the witness reads ψ; with `a := F` it reads `ψ ∧ ¬ψ`; the two
differ exactly where ψ reads T. -/
theorem sides_ne : ∀ x : V,
    kand (kor T (kand x (knot x))) x ≠ kand (kor F (kand x (knot x))) x → x = T := by
  intro x h
  cases x with
  | T => rfl
  | F => exact absurd (by decide) h
  | Z => exact absurd (by decide) h

/-- At the all-marked start the receipt names `a`. -/
theorem named (a : Nat) (ψ : Fm) (hc : constFree ψ = true) :
    labF allZ (witnessR a ψ) a = true := by
  have hψ : evalK allZ ψ = Z := evalK_allZ ψ hc
  have hz : evalK allZ (zfalse ψ) = Z := by
    show kand (evalK allZ ψ) (knot (evalK allZ ψ)) = Z
    rw [hψ]; rfl
  have hd : evalK allZ (Fm.disj (Fm.atom a) (zfalse ψ)) = Z := by
    show kor (evalK allZ (Fm.atom a)) (evalK allZ (zfalse ψ)) = Z
    rw [hz]; rfl
  have ha : labF allZ (Fm.atom a) a = true := by
    show decide (a = a) = true
    exact decide_eq_true rfl
  have hl : labF allZ (Fm.disj (Fm.atom a) (zfalse ψ)) a = true := by
    show disjL (evalK allZ (Fm.atom a)) (evalK allZ (zfalse ψ))
           (labF allZ (Fm.atom a) a) (labF allZ (zfalse ψ) a) = true
    rw [hz, ha]
    show disjL Z Z true (labF allZ (zfalse ψ) a) = true
    cases hb : labF allZ (zfalse ψ) a with
    | true => rfl
    | false => rfl
  show conjL (evalK allZ (Fm.disj (Fm.atom a) (zfalse ψ))) (evalK allZ ψ)
         (labF allZ (Fm.disj (Fm.atom a) (zfalse ψ)) a) (labF allZ ψ a) = true
  rw [hd, hψ, hl]
  show (true || labF allZ ψ a) = true
  rfl

/-! ## Readings: keep a classical point on ψ's atoms, mark the rest; settle a partial reading upward -/

/-- Keep `c` on the atoms of ψ, mark everything else. -/
def restrict (ψ : Fm) (c : Nat → V) : Nat → V :=
  fun n => match occurs n ψ with
    | true => c n
    | false => Z

theorem restrict_occ (ψ : Fm) (c : Nat → V) (n : Nat) (h : occurs n ψ = true) :
    restrict ψ c n = c n := by
  show (match occurs n ψ with | true => c n | false => Z) = c n
  rw [h]

theorem restrict_nocc (ψ : Fm) (c : Nat → V) (n : Nat) (h : occurs n ψ = false) :
    restrict ψ c n = Z := by
  show (match occurs n ψ with | true => c n | false => Z) = Z
  rw [h]

/-- Settle every waiting ground to T: a classical point above the reading. -/
def fillT (w : Nat → V) : Nat → V :=
  fun n => match w n with
    | T => T
    | F => F
    | Z => T

theorem fillT_ne_Z (w : Nat → V) : ∀ n, fillT w n ≠ Z := by
  intro n
  show (match w n with | T => T | F => F | Z => T) ≠ Z
  cases w n <;> decide

theorem leqb_fillT (w : Nat → V) : ∀ n, leqb (w n) (fillT w n) = true := by
  intro n
  show leqb (w n) (match w n with | T => T | F => F | Z => T) = true
  cases w n <;> decide

theorem leqb_T_eq : ∀ y : V, leqb T y = true → y = T := by
  intro y h
  cases y with
  | T => rfl
  | F => exact absurd h (by decide)
  | Z => exact absurd h (by decide)

/-! ## The theorem: a named atom is worth naming exactly when ψ is satisfiable -/

theorem pivotal_iff_sat (a : Nat) (ψ : Fm) (hocc : occurs a ψ = false) :
    pivotal allZ (witnessR a ψ) a ↔ ∃ c : Nat → V, (∀ n, c n ≠ Z) ∧ evalK c ψ = T := by
  constructor
  · intro hp
    obtain ⟨w1, w2, _, _, ha1, ha2, hd, hne⟩ := hp
    have hx : evalK w1 ψ = evalK w2 ψ :=
      evalK_congr w1 w2 ψ (fun n hn => hd n (fun he => by
        rw [he, hocc] at hn; exact Bool.noConfusion hn))
    have hne' : kand (kor (w1 a) (kand (evalK w1 ψ) (knot (evalK w1 ψ)))) (evalK w1 ψ)
              ≠ kand (kor (w2 a) (kand (evalK w2 ψ) (knot (evalK w2 ψ)))) (evalK w2 ψ) := hne
    rw [ha1, ha2, ← hx] at hne'
    have hT : evalK w1 ψ = T := sides_ne (evalK w1 ψ) hne'
    refine ⟨fillT w1, fillT_ne_Z w1, ?_⟩
    have hm := evalK_mono (leqb_fillT w1) ψ
    rw [hT] at hm
    exact leqb_T_eq _ hm
  · intro hs
    obtain ⟨c, _, hcT⟩ := hs
    have hfill : ∀ x : V, fills allZ (setA a x (restrict ψ c)) (witnessR a ψ) := by
      intro x
      refine ⟨fun n h => absurd rfl h, ?_⟩
      intro n ho
      have ho' : ((decide (a = n) || (occurs n ψ || occurs n ψ)) || occurs n ψ) = false := ho
      cases hna : decide (a = n) with
      | true =>
          rw [hna] at ho'
          have h2 : true = false := ho'
          exact Bool.noConfusion h2
      | false =>
          cases hψ : occurs n ψ with
          | true =>
              rw [hna, hψ] at ho'
              have h2 : true = false := ho'
              exact Bool.noConfusion h2
          | false =>
              rw [setA_other x (restrict ψ c) (fun he => of_decide_eq_false hna he.symm)]
              exact restrict_nocc ψ c n hψ
    have hagree : ∀ x : V, evalK (setA a x (restrict ψ c)) ψ = T := by
      intro x
      have hag : ∀ n, occurs n ψ = true → setA a x (restrict ψ c) n = c n := by
        intro n hn
        have hna : n ≠ a := fun he => by rw [he, hocc] at hn; exact Bool.noConfusion hn
        rw [setA_other x (restrict ψ c) hna]
        exact restrict_occ ψ c n hn
      rw [evalK_congr _ c ψ hag, hcT]
    refine ⟨setA a T (restrict ψ c), setA a F (restrict ψ c), hfill T, hfill F,
            setA_self a T _, setA_self a F _, ?_, ?_⟩
    · intro n hn
      rw [setA_other T (restrict ψ c) hn, setA_other F (restrict ψ c) hn]
    · have e1 := hagree T
      have e2 := hagree F
      show kand (kor (setA a T (restrict ψ c) a)
                     (kand (evalK (setA a T (restrict ψ c)) ψ)
                           (knot (evalK (setA a T (restrict ψ c)) ψ))))
                (evalK (setA a T (restrict ψ c)) ψ)
         ≠ kand (kor (setA a F (restrict ψ c) a)
                     (kand (evalK (setA a F (restrict ψ c)) ψ)
                           (knot (evalK (setA a F (restrict ψ c)) ψ))))
                (evalK (setA a F (restrict ψ c)) ψ)
      rw [setA_self, setA_self, e1, e2]
      decide

/-! ## The negative control: why the witness is not simply `a ∧ ψ` -/

/-- `a ∧ ψ` is no reduction: under a reading that leaves ψ waiting, `a := T`
gives Z and `a := F` gives F, so `a` is pivotal whatever ψ is. -/
theorem conj_always_pivotal (a : Nat) (ψ : Fm) (hc : constFree ψ = true)
    (hocc : occurs a ψ = false) :
    pivotal allZ (Fm.conj (Fm.atom a) ψ) a := by
  have hfill : ∀ x : V, fills allZ (setA a x allZ) (Fm.conj (Fm.atom a) ψ) := by
    intro x
    refine ⟨fun n h => absurd rfl h, ?_⟩
    intro n ho
    have ho' : (decide (a = n) || occurs n ψ) = false := ho
    cases hna : decide (a = n) with
    | true =>
        rw [hna] at ho'
        have h2 : true = false := ho'
        exact Bool.noConfusion h2
    | false => exact setA_other x allZ (fun he => of_decide_eq_false hna he.symm)
  have hZ : ∀ x : V, evalK (setA a x allZ) ψ = Z := by
    intro x
    rw [evalK_congr (setA a x allZ) allZ ψ (fun n hn =>
          setA_other x allZ (fun he => by rw [he, hocc] at hn; exact Bool.noConfusion hn))]
    exact evalK_allZ ψ hc
  refine ⟨setA a T allZ, setA a F allZ, hfill T, hfill F,
          setA_self a T allZ, setA_self a F allZ, ?_, ?_⟩
  · intro n hn
    rw [setA_other T allZ hn, setA_other F allZ hn]
  · show kand (setA a T allZ a) (evalK (setA a T allZ) ψ)
         ≠ kand (setA a F allZ a) (evalK (setA a F allZ) ψ)
    rw [setA_self, setA_self, hZ T, hZ F]
    decide

#print axioms evalK_allZ
#print axioms sides_ne
#print axioms named
#print axioms leqb_T_eq
#print axioms pivotal_iff_sat
#print axioms conj_always_pivotal

end V
