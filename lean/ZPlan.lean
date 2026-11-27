import ZTL
import ZRead
/-!
# ZPlan — THE CHEAPEST PLAN OF CHECKS THAT SETTLES A CLAIM WHATEVER THE CHECKS SHOW. Zero axioms.

(2026-11-27, the curator: "Строй в ЗТЛ правь ядро"; "для судьи нужно делать оптимально, так как мы только теоремы там
принимаем".) Written with AI.

THE QUESTION. A claim is not settled: some of its grounds are dirty. Checking a ground costs something and cleans it —
it comes out true or false, and nobody knows which beforehand. In what order should the grounds be checked so that the
verdict becomes final (EARNED or REFUTED, in the kernel's own sense: `earnedR` / `refutedR` of ZRead) at the least cost
that is GUARANTEED, whatever the checks show?

A PLAN is a tree: settle now (`done`), or check one dirty ground and go on by its answer (`ask n yes no`). It is VALID
when every branch ends settled and only dirty grounds are checked. Its WORST cost is the dearest branch.
The backward pass already in the kernel (zbackward: POSSIBILITY / GUARANTEE, lean/ZBackward.lean) names SETS of
grounds to check together. A plan is finer: what is checked next depends on what was found. For
(a ∧ b) ∨ (¬a ∧ c) the least guaranteeing set is {a, b, c}; the plan "a, then b or c" never checks all three.

`opt` is the plain recursion: nothing to do if settled; else, over every dirty ground, its cost plus the worse of the
two continuations — the least of these.

THEOREMS.
  `opt_le`        no valid plan is cheaper in the worst case than `opt` says              (a lower bound, any fuel)
  `opt_attained`  with fuel for every dirty ground, some valid plan costs no more than `opt`
  `optimal`       hence a valid plan exists whose worst cost is `opt` and is least among ALL valid plans

WHAT IS NOT CLAIMED. "Cheapest on average" is not here and cannot be without a premise: it needs the chances of the
answers and how the checks hang together, and how grounds hang together is the dirty parameter. The recursion is
exponential in the number of dirty grounds; the kernel computes it up to a stated cap and refuses beyond (zplan.py).
-/

namespace ZPlan
open V

/-! ### a ground cleaned by a check -/

def upd (v : Nat → V) (n : Nat) (x : V) : Nat → V := fun m => if m = n then x else v m

theorem upd_same (v : Nat → V) (n : Nat) (x : V) : upd v n x n = x := if_pos rfl
theorem upd_other (v : Nat → V) (n : Nat) (x : V) {m : Nat} (h : m ≠ n) : upd v n x m = v m := if_neg h

/-- settled in the kernel's sense: EARNED or REFUTED by the dirty reading -/
def decided (φ : Fm) (v : Nat → V) : Bool := !(rd v φ).2 || !(rd v φ).1

theorem decided_earned {φ : Fm} {v : Nat → V} (h : earnedR v φ) : decided φ v = true := by
  show (!(rd v φ).2 || !(rd v φ).1) = true
  have e : (rd v φ).2 = false := h
  rw [e]; rfl
theorem decided_refuted {φ : Fm} {v : Nat → V} (h : refutedR v φ) : decided φ v = true := by
  show (!(rd v φ).2 || !(rd v φ).1) = true
  have e : (rd v φ).1 = false := h
  rw [e]; exact Bool.or_true _
theorem or_not_cases : ∀ a b : Bool, (!b || !a) = true → b = false ∨ a = false := by decide
/-- a settled claim is EARNED or REFUTED -/
theorem decided_means {φ : Fm} {v : Nat → V} (h : decided φ v = true) : earnedR v φ ∨ refutedR v φ :=
  or_not_cases _ _ h

/-! ### plans -/

inductive Plan
  | done
  | ask (n : Nat) (yes no : Plan)

def Valid (φ : Fm) : Plan → (Nat → V) → Prop
  | .done, v => decided φ v = true
  | .ask n y no, v => v n = Z ∧ Valid φ y (upd v n T) ∧ Valid φ no (upd v n F)

/-- the larger of two, written out -/
def mx (a b : Nat) : Nat := if a ≤ b then b else a

theorem le_mx_l (a b : Nat) : a ≤ mx a b := by
  unfold mx
  cases Nat.decLe a b with
  | isTrue h => rw [if_pos h]; exact h
  | isFalse h => rw [if_neg h]; exact Nat.le_refl a
theorem le_mx_r (a b : Nat) : b ≤ mx a b := by
  unfold mx
  cases Nat.decLe a b with
  | isTrue h => rw [if_pos h]; exact Nat.le_refl b
  | isFalse h => rw [if_neg h]; exact Nat.le_of_lt (Nat.gt_of_not_le h)
theorem mx_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : mx a b ≤ c := by
  unfold mx
  cases Nat.decLe a b with
  | isTrue h => rw [if_pos h]; exact hb
  | isFalse h => rw [if_neg h]; exact ha
theorem mx_mono {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : mx a b ≤ mx c d :=
  mx_le (Nat.le_trans h1 (le_mx_l c d)) (Nat.le_trans h2 (le_mx_r c d))

/-- the cost of a plan's dearest branch -/
def worst (cost : Nat → Nat) : Plan → Nat
  | .done => 0
  | .ask n y no => cost n + mx (worst cost y) (worst cost no)

/-! ### lists of grounds, written out (no library lemma, no axiom) -/

def In (n : Nat) : List Nat → Prop
  | [] => False
  | k :: r => n = k ∨ In n r

/-- the list without a ground -/
def rem (n : Nat) : List Nat → List Nat
  | [] => []
  | k :: r => if k = n then rem n r else k :: rem n r

theorem in_rem {n m : Nat} (hne : m ≠ n) : ∀ {l : List Nat}, In m l → In m (rem n l)
  | [], h => h
  | k :: r, h => by
    cases Nat.decEq k n with
    | isTrue e =>
      show In m (if k = n then rem n r else k :: rem n r)
      rw [if_pos e]
      cases h with
      | inl h1 => exact absurd (h1.trans e) hne
      | inr h2 => exact in_rem hne h2
    | isFalse e =>
      show In m (if k = n then rem n r else k :: rem n r)
      rw [if_neg e]
      cases h with
      | inl h1 => exact Or.inl h1
      | inr h2 => exact Or.inr (in_rem hne h2)

theorem rem_in {n m : Nat} : ∀ {l : List Nat}, In m (rem n l) → In m l ∧ m ≠ n
  | [], h => False.elim h
  | k :: r, h => by
    cases Nat.decEq k n with
    | isTrue e =>
      have h' : In m (rem n r) := by
        have : In m (if k = n then rem n r else k :: rem n r) := h
        rw [if_pos e] at this; exact this
      exact ⟨Or.inr (rem_in h').1, (rem_in h').2⟩
    | isFalse e =>
      have h' : In m (k :: rem n r) := by
        have : In m (if k = n then rem n r else k :: rem n r) := h
        rw [if_neg e] at this; exact this
      cases h' with
      | inl h1 => exact ⟨Or.inl h1, fun e2 => e (h1 ▸ e2)⟩
      | inr h2 => exact ⟨Or.inr (rem_in h2).1, (rem_in h2).2⟩

theorem rem_len_le (n : Nat) : ∀ l : List Nat, (rem n l).length ≤ l.length
  | [] => Nat.le_refl 0
  | k :: r => by
    cases Nat.decEq k n with
    | isTrue e =>
      show (if k = n then rem n r else k :: rem n r).length ≤ r.length + 1
      rw [if_pos e]; exact Nat.le_succ_of_le (rem_len_le n r)
    | isFalse e =>
      show (if k = n then rem n r else k :: rem n r).length ≤ r.length + 1
      rw [if_neg e]; exact Nat.succ_le_succ (rem_len_le n r)

/-- removing a ground that is in the list makes it shorter -/
theorem rem_len_lt {n : Nat} : ∀ {l : List Nat}, In n l → (rem n l).length < l.length
  | [], h => False.elim h
  | k :: r, h => by
    cases Nat.decEq k n with
    | isTrue e =>
      show (if k = n then rem n r else k :: rem n r).length < r.length + 1
      rw [if_pos e]; exact Nat.lt_succ_of_le (rem_len_le n r)
    | isFalse e =>
      show (if k = n then rem n r else k :: rem n r).length < r.length + 1
      rw [if_neg e]
      cases h with
      | inl h1 => exact absurd h1.symm e
      | inr h2 => exact Nat.succ_lt_succ (rem_len_lt h2)

/-- the least value of f over a list (0 for the empty list) -/
def least (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | k :: r => match r with
    | [] => f k
    | _ :: _ => if f k ≤ least f r then f k else least f r

theorem least_le (f : Nat → Nat) : ∀ {l : List Nat} {n : Nat}, In n l → least f l ≤ f n
  | [], _, h => False.elim h
  | [k], n, h => by
    cases h with
    | inl h1 => rw [h1]; exact Nat.le_refl _
    | inr h2 => exact False.elim h2
  | k :: j :: r, n, h => by
    show (if f k ≤ least f (j :: r) then f k else least f (j :: r)) ≤ f n
    cases Nat.decLe (f k) (least f (j :: r)) with
    | isTrue hle =>
      rw [if_pos hle]
      cases h with
      | inl h1 => rw [h1]; exact Nat.le_refl _
      | inr h2 => exact Nat.le_trans hle (least_le f h2)
    | isFalse hle =>
      rw [if_neg hle]
      cases h with
      | inl h1 => rw [h1]; exact Nat.le_of_lt (Nat.gt_of_not_le hle)
      | inr h2 => exact least_le f h2

theorem least_attained (f : Nat → Nat) : ∀ (k : Nat) (r : List Nat), ∃ n, In n (k :: r) ∧ least f (k :: r) = f n
  | k, [] => ⟨k, Or.inl rfl, rfl⟩
  | k, j :: r => by
    obtain ⟨n, hin, he⟩ := least_attained f j r
    cases Nat.decLe (f k) (least f (j :: r)) with
    | isTrue hle =>
      refine ⟨k, Or.inl rfl, ?_⟩
      show (if f k ≤ least f (j :: r) then f k else least f (j :: r)) = f k
      rw [if_pos hle]
    | isFalse hle =>
      refine ⟨n, Or.inr hin, ?_⟩
      show (if f k ≤ least f (j :: r) then f k else least f (j :: r)) = f n
      rw [if_neg hle]; exact he

/-! ### the recursion -/

variable (cost : Nat → Nat) (φ : Fm)

/-- the step of the recursion at one ground: its cost and the worse of the two continuations -/
def step (rec : List Nat → (Nat → V) → Nat) (ds : List Nat) (v : Nat → V) (n : Nat) : Nat :=
  cost n + mx (rec (rem n ds) (upd v n T)) (rec (rem n ds) (upd v n F))

/-- the least guaranteed cost of settling the claim, with `fuel` checks at most -/
def opt : Nat → List Nat → (Nat → V) → Nat
  | 0, _, _ => 0
  | k + 1, ds, v => cond (decided φ v) 0 (least (step cost (opt k) ds v) ds)

theorem opt_settled (k : Nat) (ds : List Nat) (v : Nat → V) (h : decided φ v = true) : opt cost φ (k + 1) ds v = 0 := by
  show cond (decided φ v) 0 _ = 0
  rw [h]; rfl
theorem opt_open (k : Nat) (ds : List Nat) (v : Nat → V) (h : decided φ v = false) :
    opt cost φ (k + 1) ds v = least (step cost (opt cost φ k) ds v) ds := by
  show cond (decided φ v) 0 _ = _
  rw [h]; rfl

/-- **No valid plan is cheaper in the worst case than `opt` says** — with any fuel. `ds` lists every dirty ground. -/
theorem opt_le : ∀ (p : Plan) (k : Nat) (ds : List Nat) (v : Nat → V), (∀ n, v n = Z → In n ds) → Valid φ p v →
    opt cost φ k ds v ≤ worst cost p
  | .done, 0, _, _, _, _ => Nat.le_refl 0
  | .done, k + 1, ds, v, _, hv => by rw [opt_settled cost φ k ds v hv]; exact Nat.le_refl 0
  | .ask _ _ _, 0, _, _, _, _ => Nat.zero_le _
  | .ask n y no, k + 1, ds, v, hd, hv => by
    obtain ⟨hz, vy, vn⟩ := hv
    cases hdec : decided φ v with
    | true => rw [opt_settled cost φ k ds v hdec]; exact Nat.zero_le _
    | false =>
      rw [opt_open cost φ k ds v hdec]
      have dirty : ∀ (x : V), x ≠ Z → ∀ m, upd v n x m = Z → In m (rem n ds) := by
        intro x hx m hm
        cases Nat.decEq m n with
        | isTrue e => rw [e, upd_same] at hm; exact absurd hm hx
        | isFalse e => rw [upd_other v n x e] at hm; exact in_rem e (hd m hm)
      have iy := opt_le y k (rem n ds) (upd v n T) (dirty T (fun e => V.noConfusion e)) vy
      have ino := opt_le no k (rem n ds) (upd v n F) (dirty F (fun e => V.noConfusion e)) vn
      exact Nat.le_trans (least_le (step cost (opt cost φ k) ds v) (hd n hz))
        (Nat.add_le_add_left (mx_mono iy ino) _)

/-! ### with no dirty ground left the claim is settled -/

theorem atom_def : ∀ x : V, x ≠ Z → (subs x).contains false = !((subs x).contains true) := by decide
theorem n_neg : ∀ a b : Bool, b = !a → a = !b := by decide
theorem n_and : ∀ a b c d : Bool, b = !a → d = !c →
    (comb (fun x y => x && y) (a, b) (c, d)).2 = !(comb (fun x y => x && y) (a, b) (c, d)).1 := by decide
theorem n_or : ∀ a b c d : Bool, b = !a → d = !c →
    (comb (fun x y => x || y) (a, b) (c, d)).2 = !(comb (fun x y => x || y) (a, b) (c, d)).1 := by decide
theorem n_imp : ∀ a b c d : Bool, b = !a → d = !c →
    (comb (fun x y => !x || y) (a, b) (c, d)).2 = !(comb (fun x y => !x || y) (a, b) (c, d)).1 := by decide
theorem n_xor : ∀ a b c d : Bool, b = !a → d = !c →
    (comb (fun x y => x != y) (a, b) (c, d)).2 = !(comb (fun x y => x != y) (a, b) (c, d)).1 := by decide
theorem n_xnor : ∀ a b c d : Bool, b = !a → d = !c →
    (comb (fun x y => x == y) (a, b) (c, d)).2 = !(comb (fun x y => x == y) (a, b) (c, d)).1 := by decide

/-- with every ground clean, exactly one of "can be true", "can be false" holds -/
theorem definite (v : Nat → V) (h : ∀ n, v n ≠ Z) : ∀ φ : Fm, (rd v φ).2 = !(rd v φ).1
  | .atom n => atom_def (v n) (h n)
  | .top => rfl
  | .bot => rfl
  | .neg φ => n_neg _ _ (definite v h φ)
  | .conj φ ψ => n_and _ _ _ _ (definite v h φ) (definite v h ψ)
  | .disj φ ψ => n_or _ _ _ _ (definite v h φ) (definite v h ψ)
  | .imp φ ψ => n_imp _ _ _ _ (definite v h φ) (definite v h ψ)
  | .xor φ ψ => n_xor _ _ _ _ (definite v h φ) (definite v h ψ)
  | .xnor φ ψ => n_xnor _ _ _ _ (definite v h φ) (definite v h ψ)

theorem dec_of_def : ∀ a b : Bool, b = !a → (!b || !a) = true := by decide
theorem settled_when_clean (v : Nat → V) (h : ∀ n, v n ≠ Z) : decided φ v = true :=
  dec_of_def _ _ (definite v h φ)

/-- **With fuel for every dirty ground, some valid plan costs no more than `opt`.** `ds` lists exactly the dirty
grounds. -/
theorem opt_attained : ∀ (k : Nat) (ds : List Nat) (v : Nat → V), ds.length ≤ k → (∀ n, v n = Z → In n ds) →
    (∀ n, In n ds → v n = Z) → ∃ p, Valid φ p v ∧ worst cost p ≤ opt cost φ k ds v
  | 0, ds, v, hl, hd, _ => by
    cases ds with
    | nil => exact ⟨.done, settled_when_clean φ v (fun n e => hd n e), Nat.le_refl 0⟩
    | cons a r => exact absurd hl (Nat.not_succ_le_zero _)
  | k + 1, ds, v, hl, hd, hz => by
    cases hdec : decided φ v with
    | true => exact ⟨.done, hdec, Nat.zero_le _⟩
    | false =>
      cases ds with
      | nil =>
        have := settled_when_clean φ v (fun n e => hd n e)
        rw [hdec] at this; exact Bool.noConfusion this
      | cons a r =>
        obtain ⟨n, hin, he⟩ := least_attained (step cost (opt cost φ k) (a :: r) v) a r
        have zn : v n = Z := hz n hin
        have len : (rem n (a :: r)).length ≤ k := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (rem_len_lt hin) hl)
        have dirty : ∀ (x : V), x ≠ Z → ∀ m, upd v n x m = Z → In m (rem n (a :: r)) := by
          intro x hx m hm
          cases Nat.decEq m n with
          | isTrue e => rw [e, upd_same] at hm; exact absurd hm hx
          | isFalse e => rw [upd_other v n x e] at hm; exact in_rem e (hd m hm)
        have listed : ∀ (x : V) m, In m (rem n (a :: r)) → upd v n x m = Z := by
          intro x m hm
          have := rem_in hm
          rw [upd_other v n x this.2]; exact hz m this.1
        obtain ⟨py, vy, wy⟩ := opt_attained k (rem n (a :: r)) (upd v n T) len (dirty T (fun e => V.noConfusion e)) (listed T)
        obtain ⟨pn, vn, wn⟩ := opt_attained k (rem n (a :: r)) (upd v n F) len (dirty F (fun e => V.noConfusion e)) (listed F)
        refine ⟨.ask n py pn, ⟨zn, vy, vn⟩, ?_⟩
        rw [opt_open cost φ k (a :: r) v hdec, he]
        exact Nat.add_le_add_left (mx_mono wy wn) _

/-- **The optimum.** If `ds` lists exactly the dirty grounds and the fuel covers them, there is a valid plan whose
worst cost is `opt`, and no valid plan has a smaller worst cost. -/
theorem optimal (k : Nat) (ds : List Nat) (v : Nat → V) (hl : ds.length ≤ k) (hd : ∀ n, v n = Z → In n ds)
    (hz : ∀ n, In n ds → v n = Z) :
    ∃ p, Valid φ p v ∧ worst cost p = opt cost φ k ds v ∧ ∀ q, Valid φ q v → worst cost p ≤ worst cost q := by
  obtain ⟨p, vp, wp⟩ := opt_attained cost φ k ds v hl hd hz
  have lo := opt_le cost φ p k ds v hd vp
  exact ⟨p, vp, Nat.le_antisymm wp lo, fun q vq => Nat.le_trans wp (opt_le cost φ q k ds v hd vq)⟩

/-! ### the example of the header: a plan beats every set -/

/-- (a ∧ b) ∨ (¬a ∧ c), the grounds a, b, c numbered 0, 1, 2 -/
def ex : Fm := .disj (.conj (.atom 0) (.atom 1)) (.conj (.neg (.atom 0)) (.atom 2))
def blank : Nat → V := fun _ => Z
def unit : Nat → Nat := fun _ => 1

/-- "check a, then b or c": valid, and its dearest branch costs 2 — never all three grounds. -/
theorem ex_plan : Valid ex (.ask 0 (.ask 1 .done .done) (.ask 2 .done .done)) blank ∧
    worst unit (.ask 0 (.ask 1 .done .done) (.ask 2 .done .done)) = 2 :=
  ⟨⟨rfl,
    ⟨(by decide : upd blank 0 T 1 = Z), (by decide : decided ex (upd (upd blank 0 T) 1 T) = true),
      (by decide : decided ex (upd (upd blank 0 T) 1 F) = true)⟩,
    ⟨(by decide : upd blank 0 F 2 = Z), (by decide : decided ex (upd (upd blank 0 F) 2 T) = true),
      (by decide : decided ex (upd (upd blank 0 F) 2 F) = true)⟩⟩, by decide⟩
/-- the set way: a, b and c all checked costs 3 — and no two of them guarantee a verdict (b and c known true, a
dirty: the claim is still open) -/
theorem ex_set_needs_three : decided ex (upd (upd blank 1 T) 2 T) = false ∧ worst unit (.ask 0 (.ask 1 (.ask 2 .done .done) .done) .done) = 3 := by decide
/-- and 2 is the optimum there: the recursion says 2 -/
theorem ex_opt : opt unit ex 3 [0, 1, 2] blank = 2 := by decide

end ZPlan

#print axioms ZPlan.opt_le
#print axioms ZPlan.opt_attained
#print axioms ZPlan.optimal
#print axioms ZPlan.ex_plan
#print axioms ZPlan.ex_opt
#print axioms ZPlan.ex_set_needs_three
