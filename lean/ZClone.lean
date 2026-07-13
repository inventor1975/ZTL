import ZTL

/-!
# ZClone: single-operator completeness under zero trust. Zero axioms.

The Lean half of expedition E23 §4 (measured in `zzhegalkin.py`).
Classically, Sheffer's stroke (NAND) and Peirce's arrow (NOR) are each
functionally complete alone. Under the zero-trust lift both lose
completeness — kernel-checked here by the CERTIFICATE method: we
exhibit an explicit 18-table set, prove it contains the generators and
is closed under the lifted operator (a finite `decide`), so the whole
reachable clone lives inside it; conjunction and disjunction are not
among the 18. Strikingly, NAND and NOR stall in the SAME 18-table
cage — and both still reach negation (x↑x = ¬x survives verbatim),
yet neither can rebuild its own De Morgan partner.

The sole surviving solo basis is NONIMPLICATION ↛ (p ∧ ¬q, the refusal
connective): explicit witness terms, extracted from the measured
search and re-checked cell by cell by the kernel, reach ¬, ∧ and ∨ —
the full canonical basis of ZTL.

    ¬x   = ⊤ ↛ x
    x∧y  = x ↛ (x ↛ (y ↛ ⊥))
    x∨y  = ⊤ ↛ ((⊤ ↛ (x ↛ ⊥)) ↛ (y ↛ ⊥))

(Note `y ↛ ⊥` is the truth detector J_T(y).)

VR discipline: `#print axioms` at the bottom — the whole module must
stand on the empty axiom list.
-/

open V

/-- The three lifted single-operator candidates. -/
def znand : V → V → V := V.lift2 (fun a b => !(a && b))
def znor  : V → V → V := V.lift2 (fun a b => !(a || b))
def znimp : V → V → V := V.lift2 (fun a b => a && !b)

/-- A binary operation as a finite table: the nine cells in the row
order (T,T),(T,F),(T,Z),(F,T),(F,F),(F,Z),(Z,T),(Z,F),(Z,Z). Data,
not a function — so equality is decidable and no `funext` is needed. -/
structure Tbl where
  c1 : V
  c2 : V
  c3 : V
  c4 : V
  c5 : V
  c6 : V
  c7 : V
  c8 : V
  c9 : V
deriving DecidableEq, Repr

/-- The table of a binary operation. -/
def ofOp (f : V → V → V) : Tbl :=
  ⟨f T T, f T F, f T Z, f F T, f F F, f F Z, f Z T, f Z F, f Z Z⟩

/-- Pointwise application of an operation to two tables. -/
def map2 (g : V → V → V) (a b : Tbl) : Tbl :=
  ⟨g a.c1 b.c1, g a.c2 b.c2, g a.c3 b.c3,
   g a.c4 b.c4, g a.c5 b.c5, g a.c6 b.c6,
   g a.c7 b.c7, g a.c8 b.c8, g a.c9 b.c9⟩

def projX : Tbl := ⟨T, T, T, F, F, F, Z, Z, Z⟩
def projY : Tbl := ⟨T, F, Z, T, F, Z, T, F, Z⟩
def cnstT : Tbl := ⟨T, T, T, T, T, T, T, T, T⟩
def cnstF : Tbl := ⟨F, F, F, F, F, F, F, F, F⟩

/-- The clone reachable from the projections and constants by the
single operator `g`, composed pointwise. -/
inductive Reach (g : V → V → V) : Tbl → Prop
  | fst   : Reach g projX
  | snd   : Reach g projY
  | top   : Reach g cnstT
  | bot   : Reach g cnstF
  | app {a b : Tbl} : Reach g a → Reach g b → Reach g (map2 g a b)

-- ============================================================
-- §1.  The 18-table cage (one certificate serves both champions)
-- ============================================================

/-- The certificate: an explicit 18-table set. MEASURED first
(`zzhegalkin.py`), then kernel-verified: it contains the generators
and is closed under BOTH lifted champions. -/
def cage : List Tbl := [
  ⟨F, F, F, F, F, F, F, F, F⟩,
  ⟨F, F, F, F, T, F, F, F, F⟩,
  ⟨F, F, F, T, F, T, F, F, F⟩,
  ⟨F, F, F, T, T, T, F, F, F⟩,
  ⟨F, T, F, F, F, F, F, T, F⟩,
  ⟨F, T, F, F, T, F, F, T, F⟩,
  ⟨F, T, F, T, F, T, F, T, F⟩,
  ⟨F, T, F, T, T, T, F, T, F⟩,
  ⟨T, F, T, F, F, F, T, F, T⟩,
  ⟨T, F, T, F, T, F, T, F, T⟩,
  ⟨T, F, T, T, F, T, T, F, T⟩,
  ⟨T, F, T, T, T, T, T, F, T⟩,
  ⟨T, F, Z, T, F, Z, T, F, Z⟩,
  ⟨T, T, T, F, F, F, T, T, T⟩,
  ⟨T, T, T, F, F, F, Z, Z, Z⟩,
  ⟨T, T, T, F, T, F, T, T, T⟩,
  ⟨T, T, T, T, F, T, T, T, T⟩,
  ⟨T, T, T, T, T, T, T, T, T⟩
]

/-- Boolean membership by own recursion. The core decidability of
`List.Mem` is propext-tainted (house pitfall #5 in the ledger), so the
whole negative side runs on `Bool` with induction bridges. -/
def memb (t : Tbl) : List Tbl → Bool
  | [] => false
  | h :: r => if t = h then true else memb t r

theorem andEqTrueC : ∀ a b : Bool, (a && b) = true ↔ (a = true ∧ b = true) := by
  decide

/-- The whole closure check as one Bool. -/
def closedUnder (g : V → V → V) (l : List Tbl) : Bool :=
  l.all fun a => l.all fun b => memb (map2 g a b) l

theorem cage_closed_nand : closedUnder znand cage = true := by decide

theorem cage_closed_nor : closedUnder znor cage = true := by decide

/-- Bridge: a true `List.all` holds at every Bool-member. -/
theorem all_at_memb {p : Tbl → Bool} :
    ∀ (l : List Tbl), l.all p = true → ∀ t, memb t l = true → p t = true := by
  intro l
  induction l with
  | nil => intro _ t ht; exact nomatch ht
  | cons h r ih =>
      intro hall t ht
      have hsplit : p h = true ∧ r.all p = true := (andEqTrueC _ _).mp hall
      cases htd : decide (t = h) with
      | true =>
          have he : t = h := of_decide_eq_true htd
          subst he; exact hsplit.1
      | false =>
          have hne : ¬ t = h := of_decide_eq_false htd
          rw [memb, if_neg hne] at ht
          exact ih hsplit.2 t ht

/-- Closure, in usable form. -/
theorem closed_at {g : V → V → V} {l : List Tbl}
    (hcl : closedUnder g l = true) :
    ∀ a, memb a l = true → ∀ b, memb b l = true →
      memb (map2 g a b) l = true := by
  intro a ha b hb
  exact all_at_memb l (all_at_memb l hcl a ha) b hb

/-- Everything NAND reaches lives in the cage. -/
theorem reach_nand_in_cage {t : Tbl} (h : Reach znand t) :
    memb t cage = true := by
  induction h with
  | fst => decide
  | snd => decide
  | top => decide
  | bot => decide
  | app _ _ iha ihb => exact closed_at cage_closed_nand _ iha _ ihb

/-- Everything NOR reaches lives in the same cage. -/
theorem reach_nor_in_cage {t : Tbl} (h : Reach znor t) :
    memb t cage = true := by
  induction h with
  | fst => decide
  | snd => decide
  | top => decide
  | bot => decide
  | app _ _ iha ihb => exact closed_at cage_closed_nor _ iha _ ihb

/-- **Sheffer's stroke cannot rebuild conjunction** under zero trust. -/
theorem nand_cannot_and : ¬ Reach znand (ofOp zand) := by
  intro h
  exact absurd (reach_nand_in_cage h) (by decide)

/-- ...nor disjunction. -/
theorem nand_cannot_or : ¬ Reach znand (ofOp zor) := by
  intro h
  exact absurd (reach_nand_in_cage h) (by decide)

/-- **Peirce's arrow cannot rebuild conjunction** either. -/
theorem nor_cannot_and : ¬ Reach znor (ofOp zand) := by
  intro h
  exact absurd (reach_nor_in_cage h) (by decide)

theorem nor_cannot_or : ¬ Reach znor (ofOp zor) := by
  intro h
  exact absurd (reach_nor_in_cage h) (by decide)

/-- The irony intact: both champions still NEGATE (x↑x = ¬x = x↓x,
verbatim) — they lose the partner, not the flip. -/
def notTbl : Tbl := ofOp (fun x _ => znot x)

theorem nand_reaches_not : Reach znand notTbl := by
  have h := Reach.app (g := znand) Reach.fst Reach.fst
  exact (show map2 znand projX projX = notTbl by decide) ▸ h

theorem nor_reaches_not : Reach znor notTbl := by
  have h := Reach.app (g := znor) Reach.fst Reach.fst
  exact (show map2 znor projX projX = notTbl by decide) ▸ h

-- ============================================================
-- §2.  Nonimplication: the sole surviving solo basis
-- ============================================================

/-- ¬x = ⊤ ↛ x. -/
theorem nimp_reaches_not : Reach znimp notTbl := by
  have h := Reach.app (g := znimp) Reach.top Reach.fst
  exact (show map2 znimp cnstT projX = notTbl by decide) ▸ h

/-- x∧y = x ↛ (x ↛ (y ↛ ⊥)).  (`y ↛ ⊥` is the detector J_T.) -/
theorem nimp_reaches_and : Reach znimp (ofOp zand) := by
  have h := Reach.app (g := znimp) Reach.fst
    (Reach.app Reach.fst (Reach.app Reach.snd Reach.bot))
  exact (show map2 znimp projX
      (map2 znimp projX (map2 znimp projY cnstF)) = ofOp zand
    by decide) ▸ h

/-- x∨y = ⊤ ↛ ((⊤ ↛ (x ↛ ⊥)) ↛ (y ↛ ⊥)). -/
theorem nimp_reaches_or : Reach znimp (ofOp zor) := by
  have h := Reach.app (g := znimp) Reach.top
    (Reach.app
      (Reach.app Reach.top (Reach.app Reach.fst Reach.bot))
      (Reach.app Reach.snd Reach.bot))
  exact (show map2 znimp cnstT
      (map2 znimp
        (map2 znimp cnstT (map2 znimp projX cnstF))
        (map2 znimp projY cnstF)) = ofOp zor
    by decide) ▸ h

-- ============================================================
-- §3.  The splice: clone equalities, entirely in the kernel
-- ============================================================

/-- Pointwise unary application. -/
def map1 (u : V → V) (a : Tbl) : Tbl :=
  ⟨u a.c1, u a.c2, u a.c3, u a.c4, u a.c5, u a.c6, u a.c7, u a.c8, u a.c9⟩

/-- Table extensionality, cell by cell — data, no `funext`. -/
theorem tbl_eq_of_cells {s t : Tbl}
    (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2) (h3 : s.c3 = t.c3)
    (h4 : s.c4 = t.c4) (h5 : s.c5 = t.c5) (h6 : s.c6 = t.c6)
    (h7 : s.c7 = t.c7) (h8 : s.c8 = t.c8) (h9 : s.c9 = t.c9) : s = t := by
  cases s; cases t
  cases h1; cases h2; cases h3; cases h4; cases h5
  cases h6; cases h7; cases h8; cases h9
  rfl

/-- The clone of the canonical basis {¬, ∧, ∨} (+ constants). -/
inductive ReachC : Tbl → Prop
  | fst : ReachC projX
  | snd : ReachC projY
  | top : ReachC cnstT
  | bot : ReachC cnstF
  | nots {a : Tbl} : ReachC a → ReachC (map1 znot a)
  | ands {a b : Tbl} : ReachC a → ReachC b → ReachC (map2 zand a b)
  | ors  {a b : Tbl} : ReachC a → ReachC b → ReachC (map2 zor a b)

/-- The clone of the Zhegalkin pair {∧, ⊕} (+ constants). -/
inductive ReachZh : Tbl → Prop
  | fst : ReachZh projX
  | snd : ReachZh projY
  | top : ReachZh cnstT
  | bot : ReachZh cnstF
  | ands {a b : Tbl} : ReachZh a → ReachZh b → ReachZh (map2 zand a b)
  | xors {a b : Tbl} : ReachZh a → ReachZh b → ReachZh (map2 zxor a b)

/-! Cell identities — each kernel-checked over all 3 or 9 value pairs. -/

theorem cell_not_nimp : ∀ v, znimp V.T v = znot v := by decide
theorem cell_and_nimp :
    ∀ x y, znimp x (znimp x (znimp y V.F)) = zand x y := by decide
theorem cell_or_nimp :
    ∀ x y, znimp V.T (znimp (znimp V.T (znimp x V.F)) (znimp y V.F))
      = zor x y := by decide
theorem cell_nimp_canon : ∀ x y, zand x (znot y) = znimp x y := by decide
theorem cell_not_zh : ∀ v, zxor v V.T = znot v := by decide
theorem cell_or_zh :
    ∀ x y, zxor (zand x x) (zxor y (zand x y)) = zor x y := by decide
theorem cell_xor_canon :
    ∀ x y, zor (zand x (znot y)) (zand (znot x) y) = zxor x y := by decide

/-- **Nonimplication subsumes the canonical basis**: everything {¬,∧,∨}
reach, ↛ reaches alone. -/
theorem nimp_subsumes_canon {t : Tbl} (h : ReachC t) : Reach znimp t := by
  induction h with
  | fst => exact .fst
  | snd => exact .snd
  | top => exact .top
  | bot => exact .bot
  | nots _ ih =>
      rename_i a _
      have key : map2 znimp cnstT a = map1 znot a :=
        tbl_eq_of_cells (cell_not_nimp _) (cell_not_nimp _) (cell_not_nimp _)
          (cell_not_nimp _) (cell_not_nimp _) (cell_not_nimp _)
          (cell_not_nimp _) (cell_not_nimp _) (cell_not_nimp _)
      exact key ▸ Reach.app Reach.top ih
  | ands _ _ iha ihb =>
      rename_i a b _ _
      have key : map2 znimp a (map2 znimp a (map2 znimp b cnstF))
          = map2 zand a b :=
        tbl_eq_of_cells (cell_and_nimp _ _) (cell_and_nimp _ _)
          (cell_and_nimp _ _) (cell_and_nimp _ _) (cell_and_nimp _ _)
          (cell_and_nimp _ _) (cell_and_nimp _ _) (cell_and_nimp _ _)
          (cell_and_nimp _ _)
      exact key ▸ Reach.app iha (Reach.app iha (Reach.app ihb Reach.bot))
  | ors _ _ iha ihb =>
      rename_i a b _ _
      have key : map2 znimp cnstT
          (map2 znimp (map2 znimp cnstT (map2 znimp a cnstF))
            (map2 znimp b cnstF)) = map2 zor a b :=
        tbl_eq_of_cells (cell_or_nimp _ _) (cell_or_nimp _ _)
          (cell_or_nimp _ _) (cell_or_nimp _ _) (cell_or_nimp _ _)
          (cell_or_nimp _ _) (cell_or_nimp _ _) (cell_or_nimp _ _)
          (cell_or_nimp _ _)
      exact key ▸ Reach.app Reach.top
        (Reach.app
          (Reach.app Reach.top (Reach.app iha Reach.bot))
          (Reach.app ihb Reach.bot))

/-- ...and conversely (↛ = p ∧ ¬q is canonical), so the clones are EQUAL. -/
theorem canon_subsumes_nimp {t : Tbl} (h : Reach znimp t) : ReachC t := by
  induction h with
  | fst => exact .fst
  | snd => exact .snd
  | top => exact .top
  | bot => exact .bot
  | app _ _ iha ihb =>
      rename_i a b _ _
      have key : map2 zand a (map1 znot b) = map2 znimp a b :=
        tbl_eq_of_cells (cell_nimp_canon _ _) (cell_nimp_canon _ _)
          (cell_nimp_canon _ _) (cell_nimp_canon _ _) (cell_nimp_canon _ _)
          (cell_nimp_canon _ _) (cell_nimp_canon _ _) (cell_nimp_canon _ _)
          (cell_nimp_canon _ _)
      exact key ▸ ReachC.ands iha (ReachC.nots ihb)

/-- **Kernel clone equality**: nonimplication alone generates exactly the
canonical clone — its completeness, with no measured step left. -/
theorem nimp_clone_eq : ∀ t, Reach znimp t ↔ ReachC t :=
  fun _ => ⟨canon_subsumes_nimp, nimp_subsumes_canon⟩

/-- **The Zhegalkin pair subsumes the canonical basis** (¬x = x⊕⊤;
x∨y = J_T(x) ⊕ y ⊕ (x∧y) — the detector repairs the classical
polynomial). -/
theorem zh_subsumes_canon {t : Tbl} (h : ReachC t) : ReachZh t := by
  induction h with
  | fst => exact .fst
  | snd => exact .snd
  | top => exact .top
  | bot => exact .bot
  | nots _ ih =>
      rename_i a _
      have key : map2 zxor a cnstT = map1 znot a :=
        tbl_eq_of_cells (cell_not_zh _) (cell_not_zh _) (cell_not_zh _)
          (cell_not_zh _) (cell_not_zh _) (cell_not_zh _)
          (cell_not_zh _) (cell_not_zh _) (cell_not_zh _)
      exact key ▸ ReachZh.xors ih ReachZh.top
  | ands _ _ iha ihb => exact ReachZh.ands iha ihb
  | ors _ _ iha ihb =>
      rename_i a b _ _
      have key : map2 zxor (map2 zand a a) (map2 zxor b (map2 zand a b))
          = map2 zor a b :=
        tbl_eq_of_cells (cell_or_zh _ _) (cell_or_zh _ _) (cell_or_zh _ _)
          (cell_or_zh _ _) (cell_or_zh _ _) (cell_or_zh _ _)
          (cell_or_zh _ _) (cell_or_zh _ _) (cell_or_zh _ _)
      exact key ▸ ReachZh.xors (ReachZh.ands iha iha)
        (ReachZh.xors ihb (ReachZh.ands iha ihb))

/-- ...and conversely (⊕ by its surviving canonical definition). -/
theorem canon_subsumes_zh {t : Tbl} (h : ReachZh t) : ReachC t := by
  induction h with
  | fst => exact .fst
  | snd => exact .snd
  | top => exact .top
  | bot => exact .bot
  | ands _ _ iha ihb => exact ReachC.ands iha ihb
  | xors _ _ iha ihb =>
      rename_i a b _ _
      have key : map2 zor (map2 zand a (map1 znot b))
          (map2 zand (map1 znot a) b) = map2 zxor a b :=
        tbl_eq_of_cells (cell_xor_canon _ _) (cell_xor_canon _ _)
          (cell_xor_canon _ _) (cell_xor_canon _ _) (cell_xor_canon _ _)
          (cell_xor_canon _ _) (cell_xor_canon _ _) (cell_xor_canon _ _)
          (cell_xor_canon _ _)
      exact key ▸ ReachC.ors (ReachC.ands iha (ReachC.nots ihb))
        (ReachC.ands (ReachC.nots iha) ihb)

/-- **Kernel clone equality** for the Zhegalkin pair. -/
theorem zhegalkin_clone_eq : ∀ t, ReachZh t ↔ ReachC t :=
  fun _ => ⟨canon_subsumes_zh, zh_subsumes_canon⟩

/-- The trio closed: ↛ alone, the pair {∧,⊕}, and the canonical basis
{¬,∧,∨} generate one and the same clone. -/
theorem nimp_eq_zhegalkin : ∀ t, Reach znimp t ↔ ReachZh t :=
  fun t => (nimp_clone_eq t).trans (zhegalkin_clone_eq t).symm

-- ============================================================
-- §4.  Lone conjunction: never negation (the 7-table cage)
-- ============================================================

def andCage : List Tbl := [
  ⟨F, F, F, F, F, F, F, F, F⟩,
  ⟨T, F, F, F, F, F, F, F, F⟩,
  ⟨T, F, F, T, F, F, T, F, F⟩,
  ⟨T, F, Z, T, F, Z, T, F, Z⟩,
  ⟨T, T, T, F, F, F, F, F, F⟩,
  ⟨T, T, T, F, F, F, Z, Z, Z⟩,
  ⟨T, T, T, T, T, T, T, T, T⟩
]

theorem andCage_closed : closedUnder zand andCage = true := by decide

theorem reach_and_in_cage {t : Tbl} (h : Reach zand t) :
    memb t andCage = true := by
  induction h with
  | fst => decide
  | snd => decide
  | top => decide
  | bot => decide
  | app _ _ iha ihb => exact closed_at andCage_closed _ iha _ ihb

/-- Lone ∧ can never make negation (the monotonicity ban, kernel form). -/
theorem and_cannot_not : ¬ Reach zand notTbl := by
  intro h
  exact absurd (reach_and_in_cage h) (by decide)

-- CHECKS: no sorry, no admit.

-- Axiom audit — MEASURED (VR discipline): the empty list, module-wide.
#print axioms cage_closed_nand
#print axioms cage_closed_nor
#print axioms nand_cannot_and
#print axioms nand_cannot_or
#print axioms nor_cannot_and
#print axioms nor_cannot_or
#print axioms nand_reaches_not
#print axioms nor_reaches_not
#print axioms nimp_reaches_not
#print axioms nimp_reaches_and
#print axioms nimp_reaches_or
#print axioms nimp_clone_eq
#print axioms zhegalkin_clone_eq
#print axioms nimp_eq_zhegalkin
#print axioms and_cannot_not
