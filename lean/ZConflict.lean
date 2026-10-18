import ZMin
import ZLP

/-!
# ZConflict — the rules the stand's conflict search and system refutation stand on. Zero axioms.

2026-10-18 (the duel with Z3 / cvc5 / dReal; the curator's "Да, делай все четыре теоремы"). Four steps the stand
(`ztl-stand`, `ustand/stand.py`, `ustand/lp.py`, `ustand/components.py`) took that day, each resting on a claim
that was only code. Here each claim is a theorem:

  1. MONOTONICITY (`minimal_conflicts`): a requirement set held by one design stays held when requirements are
     dropped (`earned_sub`); a set every design fails stays failed when requirements are added (`refuted_sup`);
     so a set judged EARNED decides all its subsets, a REFUTED one all its supersets, with no run. The COMPLEMENT
     PROBE (`probe`): the whole set without `e` EARNED — no conflict avoids `e`.
  2. THE CORE of a refutation: an accepted no-mix tree whose failing leaves name only requirements of `C`
     refutes every set holding `C` (`no_mix_core`); a Farkas certificate on the rows of `C` refutes every set
     holding them (`infeasible_core`); a catalog every design of which fails a member of `C` — `refuted_sup`.
  3. THE FLOAT SKIP (zmin's search): a requirement MET at one point of a piece cannot be failed over the whole
     piece (`skip_sound`), and a reading's lower end is at most any value it encloses (`skip_reading`) — so a
     skipped exact reading never loses a certificate.
  4. SYSTEMS: a state is REAL when every component's output is its law at its real input with its own parameters
     inside its own box (`run`). EARNED through enclosures is sound (`enclosure_earned`); a failing point LIFTED to
     a real state refutes the system (`lift_sound`).

PREMISES, said rather than hidden: that the kernel's readings decide the leaves (`ZMin.LeafOK`, as in `ZMin`);
for (3) that the float value stands for the value at a real point of the piece (a margin of `1e-9`, relative, in
the stand — a skip is search only, so a wrong one costs time, never soundness); for (4) that the checker solves
each component's outputs exactly at the lifted point (the stand refuses an irrational output).

VR discipline: `#print axioms` at the end — the empty list, every line. No `simp`, `omega`, `decide`, classical.
-/

namespace ZConflict

open ZCertify

/-! ## 1. Monotonicity over requirement sets -/

section Mono

variable {D : Type}

/-- Some design meets every requirement of `S` (`sat d i`: design `d` meets requirement `i` over the box). -/
def Earned (sat : D → Nat → Prop) (S : Nat → Prop) : Prop :=
  ∃ d, ∀ i, S i → sat d i

/-- Every design fails a NAMED member of `S` (the stand's REFUTED: a concrete failing requirement per design). -/
def Refuted (sat : D → Nat → Prop) (S : Nat → Prop) : Prop :=
  ∀ d, ∃ i, S i ∧ ¬ sat d i

/-- A set held by one design: every subset is held by the same design. -/
theorem earned_sub (sat : D → Nat → Prop) {S T : Nat → Prop} (h : Earned sat S) (hts : ∀ i, T i → S i) :
    Earned sat T :=
  match h with
  | ⟨d, hd⟩ => ⟨d, fun i hi => hd i (hts i hi)⟩

/-- A set every design fails: every superset too (each design already fails a member). -/
theorem refuted_sup (sat : D → Nat → Prop) {S T : Nat → Prop} (h : Refuted sat S) (hst : ∀ i, S i → T i) :
    Refuted sat T :=
  fun d => match h d with
    | ⟨i, hi, hn⟩ => ⟨i, hst i hi, hn⟩

/-- The two verdicts exclude each other. -/
theorem not_both (sat : D → Nat → Prop) {S : Nat → Prop} (he : Earned sat S) : ¬ Refuted sat S :=
  fun hr => match he with
    | ⟨d, hd⟩ => match hr d with
      | ⟨i, hi, hn⟩ => hn (hd i hi)

/-- THE COMPLEMENT PROBE. The set `U` without `e` EARNED: no subset of `U` that avoids `e` is refuted — every
conflict inside `U` holds `e`. (Stated as the negation the search uses: constructive, no excluded middle.) -/
theorem probe (sat : D → Nat → Prop) (U : Nat → Prop) (e : Nat) (hE : Earned sat (fun j => U j ∧ j ≠ e))
    (S : Nat → Prop) (hsub : ∀ i, S i → U i ∧ i ≠ e) : ¬ Refuted sat S :=
  not_both sat (earned_sub sat hE hsub)

/-- A catalog's core: every design fails a member of `C` — every set holding `C` is refuted (the same failures). -/
theorem design_core (sat : D → Nat → Prop) {C S : Nat → Prop} (hC : Refuted sat C) (hcs : ∀ i, C i → S i) :
    Refuted sat S :=
  refuted_sup sat hC hcs

end Mono

/-! ## 2. The core of a no-mix proof -/

section Core

variable {α β δ : Type}

/-- Robust on the requirements of `S` only: every requirement of `S`, at every point of its data box. -/
def RobustOn (P : ZMin.Problem α β δ) (S : Nat → Prop) (x : Point α) : Prop :=
  ∀ i d, S i → P.inData i d → P.meets i x d

/-- Every leaf FAILS, and names a requirement of `C`. -/
def LeavesIn (C : Nat → Prop) : Tree α (ZMin.Leaf δ) → Prop
  | .leaf .cost          => False
  | .leaf (.fails i _)   => C i
  | .split _ _ lo hi     => LeavesIn C lo ∧ LeavesIn C hi

/-- THE ZMIN CORE. An accepted tree whose leaves fail requirements of `C` only: no mix of the box is robust on any
set `S` holding `C` — the same split, the same failing points. -/
theorem no_mix_core (O : ZCertify.Ord α) (V : ZCertify.Ord β) (P : ZMin.Problem α β δ) (L : β)
    (C : Nat → Prop) :
    ∀ (t : Tree α (ZMin.Leaf δ)) (B : Box α), LeavesIn C t → Accepts (ZMin.LeafOK O V P L) B t →
      ∀ (S : Nat → Prop), (∀ i, C i → S i) → ∀ x, InBox O B x → ¬ RobustOn P S x := by
  intro t
  induction t with
  | leaf l =>
      intro B hin hacc S hcs x hx hr
      cases l with
      | cost => exact hin
      | fails i d => exact hacc.2 x hx (hr i d (hcs i hin) hacc.1)
  | split i t lo hi ihlo ihhi =>
      intro B hin hacc S hcs x hx
      cases cut_cover O i t hx with
      | inl h1 => exact ihlo _ hin.1 hacc.1 S hcs x h1
      | inr h2 => exact ihhi _ hin.2 hacc.2 S hcs x h2

/-- With `C` everything, the core theorem is `ZMin.no_mix` for the whole set. -/
theorem robust_on_all (P : ZMin.Problem α β δ) (x : Point α) (h : ZMin.Robust P x) :
    RobustOn P (fun _ => True) x :=
  fun i d _ hd => h i d hd

end Core

/-- THE FARKAS CORE. A certificate on the rows of `C` (its multipliers, the remainders at the mix in `lC`) with a
box-maximum below zero: the mix is infeasible on any list of rows `lS` holding those of `C` — rows outside `C` are
simply not used. -/
theorem infeasible_core {α : Type} (R : ZLP.ORing α) (M : α) (lC lS : List (α × α))
    (max_sound : R.le (ZLP.wsum R lC) M) (neg : ¬ R.le R.zero M)
    (hsub : ∀ yh, List.Mem yh lC → List.Mem yh lS) :
    ¬ (∀ yh, List.Mem yh lS → R.le R.zero yh.1 ∧ R.le R.zero yh.2) :=
  fun feas => ZLP.infeasible_sound R M lC max_sound neg (fun yh h => feas yh (hsub yh h))

/-! ## 3. The float skip -/

section Skip

variable {α β δ : Type}

/-- A requirement MET at one point of the piece cannot be failed over the whole piece: the FAILS leaf's condition
is false there, so skipping its exact reading loses no certificate. -/
theorem skip_sound (O : ZCertify.Ord α) (P : ZMin.Problem α β δ) {B : Box α} {i : Nat} {d : δ}
    (x0 : Point α) (hx0 : InBox O B x0) (hmet : P.meets i x0 d) :
    ¬ (∀ x, InBox O B x → ¬ P.meets i x d) :=
  fun hno => hno x0 hx0 hmet

/-- The reading's side of it: a lower end `lo` of a value over the piece is at most the value at any point of it;
with that value at most the bound `b`, `lo ≤ b` — the reading cannot put the piece past `b`. -/
theorem skip_reading (O : ZCertify.Ord α) (V : ZCertify.Ord β) (f : Point α → β) {B : Box α} (lo b : β)
    (hlo : ∀ x, InBox O B x → V.le lo (f x)) (x0 : Point α) (hx0 : InBox O B x0) (hmet : V.le (f x0) b) :
    V.le lo b :=
  V.trans (hlo x0 hx0) hmet

end Skip

/-! ## 4. Systems of components: enclosures and lifting -/

section Systems

variable {G Θ X Y : Type}

/-- A system of `n` components in the connections' order. Component `k` reads its input from the system's givens
and the outputs before it (`feed`), and puts out its law at that input and its own parameters (`law`), which lie
in its own box (`adm`). -/
structure Sys (G Θ X Y : Type) where
  feed : Nat → G → (Nat → Y) → X
  law  : Nat → X → Θ → Y
  adm  : Nat → Θ → Prop

/-- The REAL outputs, component by component (the stand's lift walks exactly this order). -/
def run (s : Sys G Θ X Y) (g : G) (θ : Nat → Θ) (y0 : Nat → Y) : Nat → (Nat → Y)
  | 0     => y0
  | k + 1 => fun j => match Nat.decEq j k with
      | isTrue _  => s.law k (s.feed k g (run s g θ y0 k)) (θ k)
      | isFalse _ => run s g θ y0 k j

/-- A real state: givens in their box, every component's parameters in its own box, its outputs the run. -/
def Real (s : Sys G Θ X Y) (inG : G → Prop) (n : Nat) (y0 : Nat → Y) (g : G) (ys : Nat → Y) : Prop :=
  inG g ∧ ∃ θ : Nat → Θ, (∀ k, k < n → s.adm k (θ k)) ∧ ys = run s g θ y0 n

/-- EARNED THROUGH ENCLOSURES. Every real state's outputs lie in the proved ranges (`encl`), and the requirement
holds at every point of the givens' box and those ranges: it holds at every real state. -/
theorem enclosure_earned (s : Sys G Θ X Y) (inG : G → Prop) (n : Nat) (y0 : Nat → Y)
    (inRanges : (Nat → Y) → Prop) (R : G → (Nat → Y) → Prop)
    (encl : ∀ g ys, Real s inG n y0 g ys → inRanges ys)
    (holds : ∀ g ys, inG g → inRanges ys → R g ys) :
    ∀ g ys, Real s inG n y0 g ys → R g ys :=
  fun g ys hr => holds g ys hr.1 (encl g ys hr)

/-- REFUTED BY LIFTING. Givens in their box, each component's parameters in its own box, the outputs solved along
the run: a requirement failing there fails at a REAL state — the system is refuted (no enclosure involved). -/
theorem lift_sound (s : Sys G Θ X Y) (inG : G → Prop) (n : Nat) (y0 : Nat → Y) (R : G → (Nat → Y) → Prop)
    (g : G) (θ : Nat → Θ) (hg : inG g) (hθ : ∀ k, k < n → s.adm k (θ k))
    (hfail : ¬ R g (run s g θ y0 n)) :
    ∃ g' ys, Real s inG n y0 g' ys ∧ ¬ R g' ys :=
  ⟨g, run s g θ y0 n, ⟨hg, θ, hθ, rfl⟩, hfail⟩

/-- The two meet: a requirement EARNED through enclosures cannot be refuted by a lifted point. -/
theorem lift_vs_enclosure (s : Sys G Θ X Y) (inG : G → Prop) (n : Nat) (y0 : Nat → Y)
    (inRanges : (Nat → Y) → Prop) (R : G → (Nat → Y) → Prop)
    (encl : ∀ g ys, Real s inG n y0 g ys → inRanges ys)
    (holds : ∀ g ys, inG g → inRanges ys → R g ys) :
    ¬ ∃ g ys, Real s inG n y0 g ys ∧ ¬ R g ys :=
  fun ⟨g, ys, hr, hn⟩ => hn (enclosure_earned s inG n y0 inRanges R encl holds g ys hr)

end Systems

end ZConflict

#print axioms ZConflict.earned_sub
#print axioms ZConflict.refuted_sup
#print axioms ZConflict.not_both
#print axioms ZConflict.probe
#print axioms ZConflict.design_core
#print axioms ZConflict.no_mix_core
#print axioms ZConflict.robust_on_all
#print axioms ZConflict.infeasible_core
#print axioms ZConflict.skip_sound
#print axioms ZConflict.skip_reading
#print axioms ZConflict.enclosure_earned
#print axioms ZConflict.lift_sound
#print axioms ZConflict.lift_vs_enclosure
