import ZNumBin
/-!
# ZPoly — polynomial identities with integer coefficients, decided by the kernel. Zero axioms.

Module 3 of the Lean-checked `check_none` (curator, 2026-11-07: "Б"). The chart nodes and the excluded leaves
of a `check_none` certificate rest on polynomial IDENTITIES (`E(φ) = rᵐ·G`, `N ≡ 0`). Here an expression is
normalised into a sorted list of TERMS — a sorted list of variable indices with a signed binary coefficient
(`ZNumBin.BZ`) — equal monomials MERGED by adding coefficients and a zero sum DROPPED (cancellation, which
VR's `CSR.norm` deliberately lacks); `norm_sound` proves, from the ring laws alone, that the normal form has
the expression's value in every `OH`. An identity is checked by the normal form of the difference being empty
(`identity_sound`) — a Boolean the kernel evaluates; no decidable equality on lists is needed.

The design follows VR's `Meta/CSRNorm.lean` (lists, insertion, `cond` instead of overlapping matches, which
reach `propext` through their splitters), with coefficients added.
-/

namespace ZPoly
open VR.CSR ZNumBin

/-- Polynomial expressions over variables numbered by `Nat`, with integer constants. -/
inductive PE where
  | var : Nat → PE
  | cst : D → PE
  | add : PE → PE → PE
  | sub : PE → PE → PE
  | mul : PE → PE → PE
  | pow : PE → Nat → PE

variable {α : Type} (S : OH α)

def powS (x : α) : Nat → α
  | 0 => S.one
  | n + 1 => S.mul x (powS x n)

/-- Value at a point. -/
def eval (env : Nat → α) : PE → α
  | .var i => env i
  | .cst c => dv S c
  | .add p q => S.add (eval env p) (eval env q)
  | .sub p q => S.add (eval env p) (S.neg (eval env q))
  | .mul p q => S.mul (eval env p) (eval env q)
  | .pow p n => powS S (eval env p) n

/-- Substitution of expressions for variables. -/
def PE.subst (σ : Nat → PE) : PE → PE
  | .var i => σ i
  | .cst c => .cst c
  | .add p q => .add (p.subst σ) (q.subst σ)
  | .sub p q => .sub (p.subst σ) (q.subst σ)
  | .mul p q => .mul (p.subst σ) (q.subst σ)
  | .pow p n => .pow (p.subst σ) n

theorem powS_congr {x y : α} (h : S.r x y) : ∀ n, S.r (powS S x n) (powS S y n)
  | 0 => S.refl _
  | n + 1 => S.mul_congr h (powS_congr h n)

theorem eval_subst (env : Nat → α) (σ : Nat → PE) :
    ∀ e : PE, S.r (eval S env (e.subst σ)) (eval S (fun i => eval S env (σ i)) e)
  | .var _ => S.refl _
  | .cst _ => S.refl _
  | .add p q => S.add_congr (eval_subst env σ p) (eval_subst env σ q)
  | .sub p q => S.add_congr (eval_subst env σ p) (S.neg_congr (eval_subst env σ q))
  | .mul p q => S.mul_congr (eval_subst env σ p) (eval_subst env σ q)
  | .pow p n => powS_congr S (eval_subst env σ p) n

/-! ## Terms and their order -/

/-- A term: a sorted list of variable indices (a monomial) and its dyadic coefficient. -/
abbrev Term := List Nat × D

def evalA (env : Nat → α) : List Nat → α
  | [] => S.one
  | i :: m => S.mul (env i) (evalA env m)

def evalT (env : Nat → α) (t : Term) : α := S.mul (dv S t.2) (evalA S env t.1)

def evalP (env : Nat → α) : List Term → α
  | [] => S.zero
  | t :: p => S.add (evalT S env t) (evalP env p)

/-- The monomial order: lexicographic on sorted index lists, a PREFIX counting as LARGER — the reverse of
lexicographic order on exponent vectors, so it is kept by multiplication with a common monomial (plain
lexicographic order with "shorter is smaller" is NOT: `[1] < [1, 2]` but `[1, 3] > [1, 2, 3]` — measured
2026-11-08, a true identity was refused). `cond`, no overlapping matches. -/
def leA : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => true
  | i :: m, j :: n => cond (Nat.blt i j) true (cond (Nat.blt j i) false (leA m n))

/-- Equality of monomials, as a Boolean the kernel evaluates. -/
def eqA : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | i :: m, j :: n => cond (Nat.beq i j) (eqA m n) false

theorem eqA_eq : ∀ {m n : List Nat}, eqA m n = true → m = n
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | i :: m, j :: n, h => by
      cases hb : Nat.beq i j with
      | false => rw [eqA, hb] at h; exact Bool.noConfusion h
      | true =>
          rw [eqA, hb] at h
          rw [Nat.eq_of_beq_eq_true hb, eqA_eq h]

/-- A coefficient that is zero: both parts of the (normalised) numerator zero. -/
def isZ (c : D) : Bool := Nat.beq c.m.p 0 && Nat.beq c.m.n 0
/-- Normalise a dyadic's numerator. -/
def dnorm (d : D) : D := ⟨znorm d.m, d.e⟩

theorem dv_dnorm (d : D) : S.r (dv S (dnorm d)) (dv S d) := S.mul_congr (zv_norm S d.m) (S.refl _)

theorem zv_isZ {c : D} (h : isZ c = true) : S.r (dv S c) S.zero := by
  have h' := and_true_split h
  have e1 := Nat.eq_of_beq_eq_true h'.1
  have e2 := Nat.eq_of_beq_eq_true h'.2
  show S.r (S.mul (S.add (nI S c.m.p) (S.neg (nI S c.m.n))) (hp S c.e)) S.zero
  rw [e1, e2]
  show S.r (S.mul (S.add S.zero (S.neg S.zero)) (hp S c.e)) S.zero
  cr_ring S.toCR

/-- Insert a term: before a larger monomial, MERGED into an equal one (zero sum dropped). -/
def insertT (t : Term) : List Term → List Term
  | [] => [t]
  | t' :: p =>
      cond (eqA t.1 t'.1)
        (let c := dnorm (dadd t.2 t'.2); cond (isZ c) p ((t'.1, c) :: p))
        (cond (leA t.1 t'.1) (t :: t' :: p) (t' :: insertT t p))

/-- One step of the merge: `t :: p` against `q`, with `mp` the merge of `p` (structural in both lists). -/
def mergeAux (t : Term) (p : List Term) (mp : List Term → List Term) : List Term → List Term
  | [] => t :: p
  | u :: q => cond (eqA t.1 u.1)
      (let c := dnorm (dadd t.2 u.2); cond (isZ c) (mp q) ((u.1, c) :: mp q))
      (cond (leA t.1 u.1) (t :: mp (u :: q)) (u :: mergeAux t p mp q))

/-- The MERGE of two sorted lists of terms, equal monomials combined (linear, not quadratic). -/
def addP : List Term → List Term → List Term
  | [], q => q
  | t :: p, q => mergeAux t p (addP p) q

def insertA (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: m => cond (Nat.ble i j) (i :: j :: m) (j :: insertA i m)

def mergeA : List Nat → List Nat → List Nat
  | [], n => n
  | i :: m, n => insertA i (mergeA m n)

def mulT (t u : Term) : Term := (mergeA t.1 u.1, dnorm (dmul t.2 u.2))

/-- A term times a list: the monomial order is kept by a common factor, so no re-sorting (were it not,
only cancellations would be missed — the test would refuse, never accept wrongly). -/
def mulTP (t : Term) : List Term → List Term
  | [] => []
  | u :: q => mulT t u :: mulTP t q

def mulP : List Term → List Term → List Term
  | [], _ => []
  | t :: p, q => addP (mulTP t q) (mulP p q)

def negP : List Term → List Term
  | [] => []
  | t :: p => (t.1, dneg t.2) :: negP p

def powP (p : List Term) : Nat → List Term
  | 0 => [([], ⟨⟨1, 0⟩, 0⟩)]
  | n + 1 => mulP p (powP p n)

def norm : PE → List Term
  | .var i => [([i], ⟨⟨1, 0⟩, 0⟩)]
  | .cst c => let c' := dnorm c; cond (isZ c') [] [([], c')]
  | .add p q => addP (norm p) (norm q)
  | .sub p q => addP (norm p) (negP (norm q))
  | .mul p q => mulP (norm p) (norm q)
  | .pow p n => powP (norm p) n

/-- The kernel's identity test: the normal form of `e₁ − e₂` is empty. -/
def ident (e₁ e₂ : PE) : Bool := (norm (.sub e₁ e₂)).isEmpty

/-! ## Soundness, from the ring laws alone -/

variable (env : Nat → α)

theorem insertT_sound (t : Term) :
    ∀ p : List Term, S.r (evalP S env (insertT t p)) (S.add (evalT S env t) (evalP S env p))
  | [] => S.refl _
  | t' :: p => by
      cases he : eqA t.1 t'.1 with
      | true =>
          have ea := eqA_eq he
          have hc := dv_dnorm S (dadd t.2 t'.2)
          have hs := dv_add S t.2 t'.2
          -- t + t' = (c_t + c_t')·A
          have merge : S.r (S.mul (dv S (dnorm (dadd t.2 t'.2))) (evalA S env t'.1))
              (S.add (evalT S env t) (evalT S env t')) := by
            unfold evalT; rw [ea]
            refine S.trans (S.mul_congr (S.trans hc hs) (S.refl _)) ?_
            cr_ring S.toCR
          rw [insertT, he]
          show S.r (evalP S env (cond (isZ (dnorm (dadd t.2 t'.2))) p ((t'.1, dnorm (dadd t.2 t'.2)) :: p))) _
          cases hz : isZ (dnorm (dadd t.2 t'.2)) with
          | true =>
              show S.r (evalP S env p) (S.add (evalT S env t) (S.add (evalT S env t') (evalP S env p)))
              have z0 : S.r (S.mul (dv S (dnorm (dadd t.2 t'.2))) (evalA S env t'.1)) S.zero :=
                S.trans (S.mul_congr (zv_isZ S hz) (S.refl _)) (S.zero_mul _)
              have m0 := S.trans (S.symm merge) z0
              refine S.trans ?_ (S.add_assoc _ _ _)
              exact S.trans (S.symm (S.zero_add _)) (S.add_congr (S.symm m0) (S.refl _))
          | false =>
              show S.r (S.add (S.mul (dv S (dnorm (dadd t.2 t'.2))) (evalA S env t'.1)) (evalP S env p))
                (S.add (evalT S env t) (S.add (evalT S env t') (evalP S env p)))
              exact S.trans (S.add_congr merge (S.refl _)) (S.add_assoc _ _ _)
      | false =>
          rw [insertT, he]
          show S.r (evalP S env (cond (leA t.1 t'.1) (t :: t' :: p) (t' :: insertT t p))) _
          cases hl : leA t.1 t'.1 with
          | true =>
              show S.r (S.add (evalT S env t) (S.add (evalT S env t') (evalP S env p)))
                (S.add (evalT S env t) (S.add (evalT S env t') (evalP S env p)))
              exact S.refl _
          | false =>
              show S.r (S.add (evalT S env t') (evalP S env (insertT t p)))
                (S.add (evalT S env t) (S.add (evalT S env t') (evalP S env p)))
              exact S.trans (S.add_congr (S.refl _) (insertT_sound t p))
                (S.add_left_comm (evalT S env t') (evalT S env t) (evalP S env p))

theorem mergeAux_sound (t : Term) (p : List Term) (mp : List Term → List Term)
    (hmp : ∀ q, S.r (evalP S env (mp q)) (S.add (evalP S env p) (evalP S env q))) :
    ∀ q, S.r (evalP S env (mergeAux t p mp q)) (S.add (S.add (evalT S env t) (evalP S env p)) (evalP S env q))
  | [] => S.symm (S.trans (S.add_congr (S.refl _) (S.refl _)) (by
      show S.r (S.add (S.add (evalT S env t) (evalP S env p)) S.zero) (S.add (evalT S env t) (evalP S env p))
      cr_ring S.toCR))
  | u :: q => by
      cases he : eqA t.1 u.1 with
      | true =>
          rw [mergeAux, he]
          have ea := eqA_eq he
          have merge : S.r (S.mul (dv S (dnorm (dadd t.2 u.2))) (evalA S env u.1)) (S.add (evalT S env t) (evalT S env u)) := by
            unfold evalT; rw [ea]
            refine S.trans (S.mul_congr (S.trans (dv_dnorm S _) (dv_add S t.2 u.2)) (S.refl _)) ?_
            cr_ring S.toCR
          show S.r (evalP S env (cond (isZ (dnorm (dadd t.2 u.2))) (mp q) ((u.1, dnorm (dadd t.2 u.2)) :: mp q))) _
          cases hz : isZ (dnorm (dadd t.2 u.2)) with
          | true =>
              show S.r (evalP S env (mp q)) (S.add (S.add (evalT S env t) (evalP S env p)) (S.add (evalT S env u) (evalP S env q)))
              have z0 : S.r (S.mul (dv S (dnorm (dadd t.2 u.2))) (evalA S env u.1)) S.zero :=
                S.trans (S.mul_congr (zv_isZ S hz) (S.refl _)) (S.zero_mul _)
              have m0 := S.trans (S.symm merge) z0
              refine S.trans (hmp q) ?_
              have k : S.r (S.add (S.add (evalT S env t) (evalP S env p)) (S.add (evalT S env u) (evalP S env q)))
                  (S.add (S.add (evalT S env t) (evalT S env u)) (S.add (evalP S env p) (evalP S env q))) := by cr_ring S.toCR
              refine S.symm (S.trans k (S.trans (S.add_congr m0 (S.refl _)) (S.zero_add _)))
          | false =>
              show S.r (S.add (S.mul (dv S (dnorm (dadd t.2 u.2))) (evalA S env u.1)) (evalP S env (mp q)))
                (S.add (S.add (evalT S env t) (evalP S env p)) (S.add (evalT S env u) (evalP S env q)))
              refine S.trans (S.add_congr merge (hmp q)) ?_
              cr_ring S.toCR
      | false =>
          rw [mergeAux, he]
          show S.r (evalP S env (cond (leA t.1 u.1) (t :: mp (u :: q)) (u :: mergeAux t p mp q))) _
          cases hl : leA t.1 u.1 with
          | true =>
              show S.r (S.add (evalT S env t) (evalP S env (mp (u :: q)))) _
              exact S.trans (S.add_congr (S.refl _) (hmp (u :: q))) (S.symm (S.add_assoc _ _ _))
          | false =>
              show S.r (S.add (evalT S env u) (evalP S env (mergeAux t p mp q)))
                (S.add (S.add (evalT S env t) (evalP S env p)) (S.add (evalT S env u) (evalP S env q)))
              refine S.trans (S.add_congr (S.refl _) (mergeAux_sound t p mp hmp q)) ?_
              cr_ring S.toCR

theorem addP_sound :
    ∀ p q : List Term, S.r (evalP S env (addP p q)) (S.add (evalP S env p) (evalP S env q))
  | [], q => S.symm (S.zero_add _)
  | t :: p, q => mergeAux_sound S env t p (addP p) (addP_sound p) q

theorem insertA_sound (i : Nat) :
    ∀ m : List Nat, S.r (evalA S env (insertA i m)) (S.mul (env i) (evalA S env m))
  | [] => S.refl _
  | j :: m => by
      cases h : Nat.ble i j with
      | true => rw [insertA, h]; exact S.refl _
      | false =>
          rw [insertA, h]
          show S.r (S.mul (env j) (evalA S env (insertA i m))) _
          exact S.trans (S.mul_congr (S.refl (env j)) (insertA_sound i m)) (S.mul_left_comm _ _ _)

theorem mergeA_sound :
    ∀ m n : List Nat, S.r (evalA S env (mergeA m n)) (S.mul (evalA S env m) (evalA S env n))
  | [], n => S.symm (S.one_mul _)
  | i :: m, n =>
      S.trans (insertA_sound S env i (mergeA m n))
        (S.trans (S.mul_congr (S.refl (env i)) (mergeA_sound m n)) (S.symm (S.mul_assoc _ _ _)))

theorem mulT_sound (t u : Term) :
    S.r (evalT S env (mulT t u)) (S.mul (evalT S env t) (evalT S env u)) := by
  unfold evalT mulT
  refine S.trans (S.mul_congr (S.trans (dv_dnorm S _) (dv_mul S _ _)) (mergeA_sound S env _ _)) ?_
  cr_ring S.toCR

theorem mulTP_sound (t : Term) :
    ∀ q : List Term, S.r (evalP S env (mulTP t q)) (S.mul (evalT S env t) (evalP S env q))
  | [] => S.symm (S.mul_zero _)
  | u :: q =>
      S.trans (S.add_congr (mulT_sound S env t u) (mulTP_sound t q)) (S.symm (S.mul_add _ _ _))

theorem mulP_sound :
    ∀ p q : List Term, S.r (evalP S env (mulP p q)) (S.mul (evalP S env p) (evalP S env q))
  | [], q => S.symm (S.zero_mul _)
  | t :: p, q =>
      S.trans (addP_sound S env (mulTP t q) (mulP p q))
        (S.trans (S.add_congr (mulTP_sound S env t q) (mulP_sound p q)) (S.symm (S.add_mul _ _ _)))

theorem negP_sound : ∀ p : List Term, S.r (evalP S env (negP p)) (S.neg (evalP S env p))
  | [] => S.symm S.neg_zero
  | t :: p => by
      show S.r (S.add (S.mul (dv S (dneg t.2)) (evalA S env t.1)) (evalP S env (negP p)))
        (S.neg (S.add (S.mul (dv S t.2) (evalA S env t.1)) (evalP S env p)))
      refine S.trans (S.add_congr (S.mul_congr (dv_neg S t.2) (S.refl _)) (negP_sound p)) ?_
      cr_ring S.toCR

theorem powP_sound (p : List Term) :
    ∀ n, S.r (evalP S env (powP p n)) (powS S (evalP S env p) n)
  | 0 => by
      show S.r (S.add (S.mul (dv S ⟨⟨1, 0⟩, 0⟩) S.one) S.zero) S.one
      show S.r (S.add (S.mul (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) S.one) S.zero) S.one
      cr_ring S.toCR
  | n + 1 => S.trans (mulP_sound S env p (powP p n)) (S.mul_congr (S.refl _) (powP_sound p n))

theorem norm_sound : ∀ e : PE, S.r (evalP S env (norm e)) (eval S env e)
  | .var i => by
      show S.r (S.add (S.mul (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) (S.mul (env i) S.one)) S.zero) (env i)
      cr_ring S.toCR
  | .cst c => by
      show S.r (evalP S env (cond (isZ (dnorm c)) [] [([], dnorm c)])) (dv S c)
      cases hz : isZ (dnorm c) with
      | true => exact S.symm (S.trans (S.symm (dv_dnorm S c)) (zv_isZ S hz))
      | false =>
          show S.r (S.add (S.mul (dv S (dnorm c)) S.one) S.zero) (dv S c)
          exact S.trans (by cr_ring S.toCR) (dv_dnorm S c)
  | .add p q => S.trans (addP_sound S env _ _) (S.add_congr (norm_sound p) (norm_sound q))
  | .sub p q => S.trans (addP_sound S env _ _) (S.add_congr (norm_sound p)
      (S.trans (negP_sound S env _) (S.neg_congr (norm_sound q))))
  | .mul p q => S.trans (mulP_sound S env _ _) (S.mul_congr (norm_sound p) (norm_sound q))
  | .pow p n => S.trans (powP_sound S env _ n) (powS_congr S (norm_sound p) n)

theorem isEmpty_nil {p : List Term} (h : p.isEmpty = true) : p = [] := by
  cases p with
  | nil => rfl
  | cons _ _ => exact Bool.noConfusion h

/-- **THE IDENTITY TEST IS SOUND**: an accepted identity holds at every point, in every `OH`. -/
theorem identity_sound {e₁ e₂ : PE} (h : ident e₁ e₂ = true) : S.r (eval S env e₁) (eval S env e₂) := by
  have hn := norm_sound S env (.sub e₁ e₂)
  rw [isEmpty_nil h] at hn
  -- 0 ≈ e₁ − e₂
  have hd : S.r S.zero (S.add (eval S env e₁) (S.neg (eval S env e₂))) := hn
  have e : S.r (eval S env e₁) (S.add (S.add (eval S env e₁) (S.neg (eval S env e₂))) (eval S env e₂)) := by
    cr_ring S.toCR
  exact S.trans e (S.trans (S.add_congr (S.symm hd) (S.refl _)) (S.zero_add _))

end ZPoly

namespace ZPoly
/-! The kernel, both ways: `(x + y)² = x² + 2xy + y²` is accepted, `(x + y)² = x² + y²` is not. -/
private def X : PE := .var 0
private def Y : PE := .var 1
example : ident (.pow (.add X Y) 2) (.add (.add (.pow X 2) (.mul (.cst ⟨⟨2, 0⟩, 0⟩) (.mul X Y))) (.pow Y 2)) = true := by decide
example : ident (.pow (.add X Y) 2) (.add (.pow X 2) (.pow Y 2)) = false := by decide
/-- Cancellation with large coefficients: `(3⁴⁰·x − y)·(3⁴⁰·x + y) = 3⁸⁰·x² − y²`. -/
example : ident (.mul (.sub (.mul (.cst ⟨⟨3 ^ 40, 0⟩, 0⟩) X) Y) (.add (.mul (.cst ⟨⟨3 ^ 40, 0⟩, 0⟩) X) Y))
    (.sub (.mul (.cst ⟨⟨3 ^ 80, 0⟩, 0⟩) (.pow X 2)) (.pow Y 2)) = true := by decide
end ZPoly

#print axioms ZPoly.eval_subst
#print axioms ZPoly.eqA_eq
#print axioms ZPoly.insertT_sound
#print axioms ZPoly.mulP_sound
#print axioms ZPoly.norm_sound
#print axioms ZPoly.identity_sound
