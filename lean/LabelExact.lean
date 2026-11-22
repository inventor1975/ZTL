import Linear

/-!
# The receipt names nothing irrelevant — on a linear claim. Zero axioms.

`Linear.linear_no_loss` says the judge loses no truth when every dirty
ground is mentioned once. This file adds the other half: on such a claim the
receipt also names nothing that could not matter.

    Linear.linear_no_loss   no truth is lost
    label_exact_linear      labF v φ a = true  →  pivotal v φ a
    drivable                a pending linear claim can be driven either way
    clash_names_an_idle_atom  and without linearity the theorem is false

Together: **on a linear claim the judge is exact in both directions.** What
remains imperfect there is the over-grant, and that comes from the collapse
`¬Z = F` rather than from multiplicity (`¬¬p` has one occurrence and still
grants).

WHY THE STATEMENT CARRIES A COMPLETION. Exactness cannot be said one atom at a
time. `p ⊕ q` is linear, the label names both atoms correctly, and yet NEITHER
moves the answer alone — `phXor Z .n = phXor T .n = phXor F Z = .n`. So `pivotal` asks
the joint question instead: is there a definite reading of the OTHER dirty
grounds under which answering this one yes and answering it no give different
verdicts? That is the human meaning of "the answer is waiting on you", and it is
what the bench measured.

THE SIBLING IS DRIVEN, NOT LEFT ALONE. Where both branches are still pending,
holding the sibling at `Z` would hide the pivot: `phAnd x Z` is injective in
nothing. So the proof first drives the sibling to a decided value (`drivable`,
below — itself a measured lemma: every one of 48,759 pending linear cells was
reachable to both `T` and `F`), then merges the two branch valuations. Linearity
is exactly what makes the merge safe — the atom under test cannot also live in
the branch being driven, so driving it cannot undo the pivot.

THE HYPOTHESIS IS LOAD-BEARING, and `clash_names_an_idle_atom` shows it: `p ∧ ¬p`
puts the receipt's own rule in the position of naming an atom that no reading can
move.

MEASURED FIRST: 128,372 linear cells (exhaustive depth ≤ 2 over three atoms plus
random depth ≤ 6 over four), zero inexact. Every one of the 13-18% inexact cells
carries an atom occurring twice.
-/

namespace V

/-- Agreement on the atoms a formula mentions is enough — the general form of
`eval_indep`, which fixed one atom at a time. -/
theorem evalK_congr (v w : Nat → V) :
    ∀ φ : Fm, (∀ n, occurs n φ = true → v n = w n) → foC v φ = foC w φ := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      exact congrArg phAtom (h n (by show decide (n = n) = true; exact decide_eq_true rfl))
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih =>
      intro h
      show phNot (foC v φ) = phNot (foC w φ)
      rw [ih (fun n hn => h n hn)]
  | conj φ ψ ihφ ihψ =>
      intro h
      show phAnd (foC v φ) (foC v ψ) = phAnd (foC w φ) (foC w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | disj φ ψ ihφ ihψ =>
      intro h
      show phOr (foC v φ) (foC v ψ) = phOr (foC w φ) (foC w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | imp φ ψ ihφ ihψ =>
      intro h
      show phImp (foC v φ) (foC v ψ) = phImp (foC w φ) (foC w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | xor φ ψ ihφ ihψ =>
      intro h
      show phXor (foC v φ) (foC v ψ) = phXor (foC w φ) (foC w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | xnor φ ψ ihφ ihψ =>
      intro h
      show phXnor (foC v φ) (foC v ψ) = phXnor (foC w φ) (foC w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]


/-! ## Drivable: a pending linear claim can be pushed either way

The piece the induction turns on, and it was measured before it was attempted:
48,759 pending linear cells, every one reachable to both `T` and `F`.

`fills v w φ` says the completion `w` differs from `v` only where `v` carried a
mark AND only inside `φ` — which is what keeps a sibling's value fixed while the
other branch is driven. -/

def fills (v w : Nat → V) (φ : Fm) : Prop :=
  (∀ n, v n ≠ Z → w n = v n) ∧ (∀ n, occurs n φ = false → w n = v n)

/-- Marks do not straddle: every marked atom occurs at most once. -/
def linMarks (v : Nat → V) (φ : Fm) : Prop :=
  ∀ n, v n = Z → occCount n φ ≤ 1

theorem fills_refl (v : Nat → V) (φ : Fm) : fills v v φ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- A completion of one branch leaves the other branch's value alone — the
composition step, and where `linMarks` earns its keep. -/
theorem occCount_pos_of_occurs (a : Nat) (φ : Fm) (h : occurs a φ = true) :
    occCount a φ ≠ 0 := by
  intro h0
  rw [occCount_zero_iff a φ h0] at h
  exact Bool.noConfusion h

/-- A completion of one branch leaves the other branch's value alone — the
composition step, and where `linMarks` earns its keep: a marked atom cannot sit
in both branches, so filling one cannot disturb the other. -/
theorem sibling_fixed (v w : Nat → V) (φ ψ : Fm)
    (hf : fills v w ψ) (hlin : ∀ n, v n = Z → occCount n φ + occCount n ψ ≤ 1) :
    foC w φ = foC v φ := by
  apply evalK_congr
  intro n hn
  have key : v n = Z ∨ v n ≠ Z := by
    cases hd : decide (v n = Z) with
    | true => exact Or.inl (of_decide_eq_true hd)
    | false => exact Or.inr (of_decide_eq_false hd)
  cases key with
  | inr h => exact hf.1 n h
  | inl hz =>
      have hsum := hlin n hz
      have h1 : 1 ≤ occCount n φ := Nat.pos_of_ne_zero (occCount_pos_of_occurs n φ hn)
      have h2 : occCount n ψ + 1 ≤ occCount n φ + occCount n ψ := by
        rw [Nat.add_comm (occCount n ψ) 1]
        exact Nat.add_le_add_right h1 (occCount n ψ)
      have h4 : occCount n ψ = 0 :=
        Nat.le_zero.mp (Nat.le_of_succ_le_succ (Nat.le_trans h2 hsum))
      exact hf.2 n (occCount_zero_iff n ψ h4)

#print axioms fills_refl


/-! ## Merging two completions

`Z ∧ Z` can be driven to `T` only by driving BOTH branches, so the two
completions have to be combined. Under `linMarks` the combination is safe: a
marked atom cannot sit in both branches, and an unmarked one is left alone by
both completions anyway. -/

def merge (φ : Fm) (wφ wψ : Nat → V) : Nat → V :=
  fun n => if occurs n φ = true then wφ n else wψ n

theorem merge_left (φ : Fm) (wφ wψ : Nat → V) :
    ∀ n, occurs n φ = true → merge φ wφ wψ n = wφ n := by
  intro n h
  show (if occurs n φ = true then wφ n else wψ n) = wφ n
  rw [if_pos h]

theorem merge_right (v : Nat → V) (φ ψ : Fm) (wφ wψ : Nat → V)
    (hfφ : fills v wφ φ) (hfψ : fills v wψ ψ)
    (hlin : ∀ n, v n = Z → occCount n φ + occCount n ψ ≤ 1) :
    ∀ n, occurs n ψ = true → merge φ wφ wψ n = wψ n := by
  intro n h
  show (if occurs n φ = true then wφ n else wψ n) = wψ n
  cases hp : occurs n φ with
  | false => rw [if_neg (by intro k; exact Bool.noConfusion k)]
  | true =>
      rw [if_pos rfl]
      -- n occurs in BOTH branches, so it cannot be marked
      have key : v n = Z ∨ v n ≠ Z := by
        cases hd : decide (v n = Z) with
        | true => exact Or.inl (of_decide_eq_true hd)
        | false => exact Or.inr (of_decide_eq_false hd)
      cases key with
      | inr hnz => rw [hfφ.1 n hnz, hfψ.1 n hnz]
      | inl hz =>
          have h1 : 1 ≤ occCount n φ := Nat.pos_of_ne_zero (occCount_pos_of_occurs n φ hp)
          have h2 : 1 ≤ occCount n ψ := Nat.pos_of_ne_zero (occCount_pos_of_occurs n ψ h)
          have h3 : 1 + 1 ≤ occCount n φ + occCount n ψ := Nat.add_le_add h1 h2
          exact absurd (Nat.le_trans h3 (hlin n hz)) (by decide)

theorem merge_fills (v : Nat → V) (op : Fm → Fm → Fm) (φ ψ : Fm) (wφ wψ : Nat → V)
    (hocc : ∀ n, occurs n (op φ ψ) = (occurs n φ || occurs n ψ))
    (hfφ : fills v wφ φ) (hfψ : fills v wψ ψ) :
    fills v (merge φ wφ wψ) (op φ ψ) := by
  constructor
  · intro n hnz
    show (if occurs n φ = true then wφ n else wψ n) = v n
    cases hp : occurs n φ with
    | true => rw [if_pos rfl]; exact hfφ.1 n hnz
    | false => rw [if_neg (by intro k; exact Bool.noConfusion k)]; exact hfψ.1 n hnz
  · intro n hn
    have hb := orF (by rw [← hocc n]; exact hn)
    show (if occurs n φ = true then wφ n else wψ n) = v n
    rw [if_neg (by rw [hb.1]; intro k; exact Bool.noConfusion k)]
    exact hfψ.2 n hb.2

#print axioms merge_left
#print axioms merge_right
#print axioms merge_fills



/-- A completion of one branch is a completion of the whole. -/
theorem fills_left (v w : Nat → V) (op : Fm → Fm → Fm) (φ ψ : Fm)
    (hocc : ∀ n, occurs n (op φ ψ) = (occurs n φ || occurs n ψ))
    (hf : fills v w φ) : fills v w (op φ ψ) :=
  ⟨hf.1, fun n hn => hf.2 n (orF (by rw [← hocc n]; exact hn)).1⟩

theorem fills_right (v w : Nat → V) (op : Fm → Fm → Fm) (φ ψ : Fm)
    (hocc : ∀ n, occurs n (op φ ψ) = (occurs n φ || occurs n ψ))
    (hf : fills v w ψ) : fills v w (op φ ψ) :=
  ⟨hf.1, fun n hn => hf.2 n (orF (by rw [← hocc n]; exact hn)).2⟩

/-! ## Drivable — the measured lemma, proved

48,759 pending linear cells were checked before this was attempted; every one
reachable to both `T` and `F`. -/

theorem drivable (v : Nat → V) :
    ∀ φ : Fm, linMarks v φ → foC v φ = .n →
      (∃ w, fills v w φ ∧ foC w φ = .t) ∧ (∃ w, fills v w φ ∧ foC w φ = .f) := by
  intro φ
  induction φ with
  | atom n =>
      intro _ hz
      have hvn : v n = Z := by
        have h0 : phAtom (v n) = .n := hz
        revert h0; cases v n <;> intro h0 <;> first | rfl | exact absurd h0 (by decide)
      constructor
      · refine ⟨setA n T v, ⟨?_, ?_⟩, ?_⟩
        · intro m hm
          exact setA_other T v (by intro he; rw [he, hvn] at hm; exact hm rfl)
        · intro m hm
          exact setA_other T v (Ne.symm (of_decide_eq_false hm))
        · show phAtom (setA n T v n) = .t
          rw [setA_self n T v]; rfl
      · refine ⟨setA n F v, ⟨?_, ?_⟩, ?_⟩
        · intro m hm
          exact setA_other F v (by intro he; rw [he, hvn] at hm; exact hm rfl)
        · intro m hm
          exact setA_other F v (Ne.symm (of_decide_eq_false hm))
        · show phAtom (setA n F v n) = .f
          rw [setA_self n F v]; rfl
  | top =>
      intro _ hz
      have h2 : (Ph.t) = Ph.n := hz
      exact absurd h2 (by decide)
  | bot =>
      intro _ hz
      have h2 : (Ph.f) = Ph.n := hz
      exact absurd h2 (by decide)
  | neg φ ih =>
      intro hlin hz
      have hφ : foC v φ = .n := by
        have h : phNot (foC v φ) = .n := hz
        revert h; cases foC v φ <;> intro h <;> first
          | rfl | exact absurd h (by decide)
      have both := ih hlin hφ
      constructor
      · obtain ⟨w, hf, hv⟩ := both.2
        exact ⟨w, hf, by show phNot (foC w φ) = .t; rw [hv]; rfl⟩
      · obtain ⟨w, hf, hv⟩ := both.1
        exact ⟨w, hf, by show phNot (foC w φ) = .f; rw [hv]; rfl⟩
  | conj φ ψ ihφ ihψ =>
      intro hlin hz
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.conj φ ψ) = (occurs n φ || occurs n ψ) :=
        fun _ => rfl
      have hv : phAnd (foC v φ) (foC v ψ) = .n := hz
      cases hva : foC v φ <;> cases hvb : foC v ψ <;>
        rw [hva, hvb] at hv <;> first
        | exact absurd hv (by decide)
        | skip
      -- (T, Z)
      · obtain ⟨wT, hfT, hTv⟩ := (ihψ hlψ hvb).1
        obtain ⟨wF, hfF, hFv⟩ := (ihψ hlψ hvb).2
        refine ⟨⟨wT, fills_right v wT Fm.conj φ ψ hocc hfT, ?_⟩,
                ⟨wF, fills_right v wF Fm.conj φ ψ hocc hfF, ?_⟩⟩
        · show phAnd (foC wT φ) (foC wT ψ) = .t
          rw [sibling_fixed v wT φ ψ hfT hlin, hva, hTv]; rfl
        · show phAnd (foC wF φ) (foC wF ψ) = .f
          rw [sibling_fixed v wF φ ψ hfF hlin, hva, hFv]; rfl
      -- (Z, T)
      · obtain ⟨wT, hfT, hTv⟩ := (ihφ hlφ hva).1
        obtain ⟨wF, hfF, hFv⟩ := (ihφ hlφ hva).2
        have hsym : ∀ n, v n = Z → occCount n ψ + occCount n φ ≤ 1 := by
          intro n hn; rw [Nat.add_comm]; exact hlin n hn
        refine ⟨⟨wT, fills_left v wT Fm.conj φ ψ hocc hfT, ?_⟩,
                ⟨wF, fills_left v wF Fm.conj φ ψ hocc hfF, ?_⟩⟩
        · show phAnd (foC wT φ) (foC wT ψ) = .t
          rw [sibling_fixed v wT ψ φ hfT hsym, hvb, hTv]; rfl
        · show phAnd (foC wF φ) (foC wF ψ) = .f
          rw [sibling_fixed v wF ψ φ hfF hsym, hvb, hFv]; rfl
      -- (Z, Z)
      · obtain ⟨wa, hfa, hav⟩ := (ihφ hlφ hva).1
        obtain ⟨wb, hfb, hbv⟩ := (ihψ hlψ hvb).1
        obtain ⟨wf, hff, hfv⟩ := (ihφ hlφ hva).2
        have hsym : ∀ n, v n = Z → occCount n ψ + occCount n φ ≤ 1 := by
          intro n hn; rw [Nat.add_comm]; exact hlin n hn
        constructor
        · refine ⟨merge φ wa wb, merge_fills v Fm.conj φ ψ wa wb hocc hfa hfb, ?_⟩
          show phAnd (foC (merge φ wa wb) φ) (foC (merge φ wa wb) ψ) = .t
          rw [evalK_congr (merge φ wa wb) wa φ (merge_left φ wa wb),
              evalK_congr (merge φ wa wb) wb ψ (merge_right v φ ψ wa wb hfa hfb hlin),
              hav, hbv]; rfl
        · refine ⟨wf, fills_left v wf Fm.conj φ ψ hocc hff, ?_⟩
          show phAnd (foC wf φ) (foC wf ψ) = .f
          rw [sibling_fixed v wf ψ φ hff hsym, hvb, hfv]; rfl
  | disj φ ψ ihφ ihψ =>
      intro hlin hz
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.disj φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hsym : ∀ n, v n = Z → occCount n ψ + occCount n φ ≤ 1 := by
        intro n hn; rw [Nat.add_comm]; exact hlin n hn
      have hv : phOr (foC v φ) (foC v ψ) = .n := hz
      cases hva : foC v φ <;> cases hvb : foC v ψ <;>
        rw [hva, hvb] at hv <;> first
        | exact absurd hv (by decide)
        | skip
      · obtain ⟨w1, hf1, hq1⟩ := (ihψ hlψ hvb).1
        obtain ⟨w2, hf2, hq2⟩ := (ihψ hlψ hvb).2
        refine ⟨⟨w1, fills_right v w1 Fm.disj φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_right v w2 Fm.disj φ ψ hocc hf2, ?_⟩⟩
        · show phOr (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 φ ψ hf1 hlin, hva, hq1]; rfl
        · show phOr (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 φ ψ hf2 hlin, hva, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihφ hlφ hva).1
        obtain ⟨w2, hf2, hq2⟩ := (ihφ hlφ hva).2
        refine ⟨⟨w1, fills_left v w1 Fm.disj φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_left v w2 Fm.disj φ ψ hocc hf2, ?_⟩⟩
        · show phOr (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 ψ φ hf1 hsym, hvb, hq1]; rfl
        · show phOr (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 ψ φ hf2 hsym, hvb, hq2]; rfl
      · obtain ⟨ws, hfs, hqs⟩ := (ihφ hlφ hva).1
        obtain ⟨wa, hfa, hav⟩ := (ihφ hlφ hva).2
        obtain ⟨wb, hfb, hbv⟩ := (ihψ hlψ hvb).2
        constructor
        · refine ⟨ws, fills_left v ws Fm.disj φ ψ hocc hfs, ?_⟩
          show phOr (foC ws φ) (foC ws ψ) = .t
          rw [sibling_fixed v ws ψ φ hfs hsym, hvb, hqs]; rfl
        · refine ⟨merge φ wa wb, merge_fills v Fm.disj φ ψ wa wb hocc hfa hfb, ?_⟩
          show phOr (foC (merge φ wa wb) φ) (foC (merge φ wa wb) ψ) = .f
          rw [evalK_congr (merge φ wa wb) wa φ (merge_left φ wa wb),
              evalK_congr (merge φ wa wb) wb ψ (merge_right v φ ψ wa wb hfa hfb hlin),
              hav, hbv]; rfl
  | imp φ ψ ihφ ihψ =>
      intro hlin hz
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.imp φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hsym : ∀ n, v n = Z → occCount n ψ + occCount n φ ≤ 1 := by
        intro n hn; rw [Nat.add_comm]; exact hlin n hn
      have hv : phImp (foC v φ) (foC v ψ) = .n := hz
      cases hva : foC v φ <;> cases hvb : foC v ψ <;>
        rw [hva, hvb] at hv <;> first
        | exact absurd hv (by decide)
        | skip
      · obtain ⟨w1, hf1, hq1⟩ := (ihψ hlψ hvb).1
        obtain ⟨w2, hf2, hq2⟩ := (ihψ hlψ hvb).2
        refine ⟨⟨w1, fills_right v w1 Fm.imp φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_right v w2 Fm.imp φ ψ hocc hf2, ?_⟩⟩
        · show phImp (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 φ ψ hf1 hlin, hva, hq1]; rfl
        · show phImp (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 φ ψ hf2 hlin, hva, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihφ hlφ hva).2
        obtain ⟨w2, hf2, hq2⟩ := (ihφ hlφ hva).1
        refine ⟨⟨w1, fills_left v w1 Fm.imp φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_left v w2 Fm.imp φ ψ hocc hf2, ?_⟩⟩
        · show phImp (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 ψ φ hf1 hsym, hvb, hq1]; rfl
        · show phImp (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 ψ φ hf2 hsym, hvb, hq2]; rfl
      · obtain ⟨ws, hfs, hqs⟩ := (ihφ hlφ hva).2
        obtain ⟨wa, hfa, hav⟩ := (ihφ hlφ hva).1
        obtain ⟨wb, hfb, hbv⟩ := (ihψ hlψ hvb).2
        constructor
        · refine ⟨ws, fills_left v ws Fm.imp φ ψ hocc hfs, ?_⟩
          show phImp (foC ws φ) (foC ws ψ) = .t
          rw [sibling_fixed v ws ψ φ hfs hsym, hvb, hqs]; rfl
        · refine ⟨merge φ wa wb, merge_fills v Fm.imp φ ψ wa wb hocc hfa hfb, ?_⟩
          show phImp (foC (merge φ wa wb) φ) (foC (merge φ wa wb) ψ) = .f
          rw [evalK_congr (merge φ wa wb) wa φ (merge_left φ wa wb),
              evalK_congr (merge φ wa wb) wb ψ (merge_right v φ ψ wa wb hfa hfb hlin),
              hav, hbv]; rfl
  | xor φ ψ ihφ ihψ =>
      intro hlin hz
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.xor φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hsym : ∀ n, v n = Z → occCount n ψ + occCount n φ ≤ 1 := by
        intro n hn; rw [Nat.add_comm]; exact hlin n hn
      have hv : phXor (foC v φ) (foC v ψ) = .n := hz
      cases hva : foC v φ <;> cases hvb : foC v ψ <;>
        rw [hva, hvb] at hv <;> first
        | exact absurd hv (by decide)
        | skip
      · obtain ⟨w1, hf1, hq1⟩ := (ihψ hlψ hvb).2
        obtain ⟨w2, hf2, hq2⟩ := (ihψ hlψ hvb).1
        refine ⟨⟨w1, fills_right v w1 Fm.xor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_right v w2 Fm.xor φ ψ hocc hf2, ?_⟩⟩
        · show phXor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 φ ψ hf1 hlin, hva, hq1]; rfl
        · show phXor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 φ ψ hf2 hlin, hva, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihψ hlψ hvb).1
        obtain ⟨w2, hf2, hq2⟩ := (ihψ hlψ hvb).2
        refine ⟨⟨w1, fills_right v w1 Fm.xor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_right v w2 Fm.xor φ ψ hocc hf2, ?_⟩⟩
        · show phXor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 φ ψ hf1 hlin, hva, hq1]; rfl
        · show phXor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 φ ψ hf2 hlin, hva, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihφ hlφ hva).2
        obtain ⟨w2, hf2, hq2⟩ := (ihφ hlφ hva).1
        refine ⟨⟨w1, fills_left v w1 Fm.xor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_left v w2 Fm.xor φ ψ hocc hf2, ?_⟩⟩
        · show phXor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 ψ φ hf1 hsym, hvb, hq1]; rfl
        · show phXor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 ψ φ hf2 hsym, hvb, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihφ hlφ hva).1
        obtain ⟨w2, hf2, hq2⟩ := (ihφ hlφ hva).2
        refine ⟨⟨w1, fills_left v w1 Fm.xor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_left v w2 Fm.xor φ ψ hocc hf2, ?_⟩⟩
        · show phXor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 ψ φ hf1 hsym, hvb, hq1]; rfl
        · show phXor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 ψ φ hf2 hsym, hvb, hq2]; rfl
      · obtain ⟨wa1, hfa1, ha1⟩ := (ihφ hlφ hva).1
        obtain ⟨wb1, hfb1, hb1⟩ := (ihψ hlψ hvb).2
        obtain ⟨wa2, hfa2, ha2⟩ := (ihφ hlφ hva).2
        obtain ⟨wb2, hfb2, hb2⟩ := (ihψ hlψ hvb).2
        constructor
        · refine ⟨merge φ wa1 wb1, merge_fills v Fm.xor φ ψ wa1 wb1 hocc hfa1 hfb1, ?_⟩
          show phXor (foC (merge φ wa1 wb1) φ) (foC (merge φ wa1 wb1) ψ) = .t
          rw [evalK_congr (merge φ wa1 wb1) wa1 φ (merge_left φ wa1 wb1),
              evalK_congr (merge φ wa1 wb1) wb1 ψ (merge_right v φ ψ wa1 wb1 hfa1 hfb1 hlin),
              ha1, hb1]; rfl
        · refine ⟨merge φ wa2 wb2, merge_fills v Fm.xor φ ψ wa2 wb2 hocc hfa2 hfb2, ?_⟩
          show phXor (foC (merge φ wa2 wb2) φ) (foC (merge φ wa2 wb2) ψ) = .f
          rw [evalK_congr (merge φ wa2 wb2) wa2 φ (merge_left φ wa2 wb2),
              evalK_congr (merge φ wa2 wb2) wb2 ψ (merge_right v φ ψ wa2 wb2 hfa2 hfb2 hlin),
              ha2, hb2]; rfl
  | xnor φ ψ ihφ ihψ =>
      intro hlin hz
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.xnor φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hsym : ∀ n, v n = Z → occCount n ψ + occCount n φ ≤ 1 := by
        intro n hn; rw [Nat.add_comm]; exact hlin n hn
      have hv : phXnor (foC v φ) (foC v ψ) = .n := hz
      cases hva : foC v φ <;> cases hvb : foC v ψ <;>
        rw [hva, hvb] at hv <;> first
        | exact absurd hv (by decide)
        | skip
      · obtain ⟨w1, hf1, hq1⟩ := (ihψ hlψ hvb).1
        obtain ⟨w2, hf2, hq2⟩ := (ihψ hlψ hvb).2
        refine ⟨⟨w1, fills_right v w1 Fm.xnor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_right v w2 Fm.xnor φ ψ hocc hf2, ?_⟩⟩
        · show phXnor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 φ ψ hf1 hlin, hva, hq1]; rfl
        · show phXnor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 φ ψ hf2 hlin, hva, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihψ hlψ hvb).2
        obtain ⟨w2, hf2, hq2⟩ := (ihψ hlψ hvb).1
        refine ⟨⟨w1, fills_right v w1 Fm.xnor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_right v w2 Fm.xnor φ ψ hocc hf2, ?_⟩⟩
        · show phXnor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 φ ψ hf1 hlin, hva, hq1]; rfl
        · show phXnor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 φ ψ hf2 hlin, hva, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihφ hlφ hva).1
        obtain ⟨w2, hf2, hq2⟩ := (ihφ hlφ hva).2
        refine ⟨⟨w1, fills_left v w1 Fm.xnor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_left v w2 Fm.xnor φ ψ hocc hf2, ?_⟩⟩
        · show phXnor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 ψ φ hf1 hsym, hvb, hq1]; rfl
        · show phXnor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 ψ φ hf2 hsym, hvb, hq2]; rfl
      · obtain ⟨w1, hf1, hq1⟩ := (ihφ hlφ hva).2
        obtain ⟨w2, hf2, hq2⟩ := (ihφ hlφ hva).1
        refine ⟨⟨w1, fills_left v w1 Fm.xnor φ ψ hocc hf1, ?_⟩,
                ⟨w2, fills_left v w2 Fm.xnor φ ψ hocc hf2, ?_⟩⟩
        · show phXnor (foC w1 φ) (foC w1 ψ) = .t
          rw [sibling_fixed v w1 ψ φ hf1 hsym, hvb, hq1]; rfl
        · show phXnor (foC w2 φ) (foC w2 ψ) = .f
          rw [sibling_fixed v w2 ψ φ hf2 hsym, hvb, hq2]; rfl
      · obtain ⟨wa1, hfa1, ha1⟩ := (ihφ hlφ hva).1
        obtain ⟨wb1, hfb1, hb1⟩ := (ihψ hlψ hvb).1
        obtain ⟨wa2, hfa2, ha2⟩ := (ihφ hlφ hva).1
        obtain ⟨wb2, hfb2, hb2⟩ := (ihψ hlψ hvb).2
        constructor
        · refine ⟨merge φ wa1 wb1, merge_fills v Fm.xnor φ ψ wa1 wb1 hocc hfa1 hfb1, ?_⟩
          show phXnor (foC (merge φ wa1 wb1) φ) (foC (merge φ wa1 wb1) ψ) = .t
          rw [evalK_congr (merge φ wa1 wb1) wa1 φ (merge_left φ wa1 wb1),
              evalK_congr (merge φ wa1 wb1) wb1 ψ (merge_right v φ ψ wa1 wb1 hfa1 hfb1 hlin),
              ha1, hb1]; rfl
        · refine ⟨merge φ wa2 wb2, merge_fills v Fm.xnor φ ψ wa2 wb2 hocc hfa2 hfb2, ?_⟩
          show phXnor (foC (merge φ wa2 wb2) φ) (foC (merge φ wa2 wb2) ψ) = .f
          rw [evalK_congr (merge φ wa2 wb2) wa2 φ (merge_left φ wa2 wb2),
              evalK_congr (merge φ wa2 wb2) wb2 ψ (merge_right v φ ψ wa2 wb2 hfa2 hfb2 hlin),
              ha2, hb2]; rfl

#print axioms evalK_congr


/-! ## Pivotal — what it means for a named atom to have been worth naming

The receipt names an atom because the answer is waiting on it. The honest test
of that claim is not "flip it and watch the value move" — with the sibling still
dirty, almost anything moves. The test is **joint**: fix every other
dirty atom to a definite reading, and see whether this atom still decides
the outcome. That is what the bench measured, and it is what is proved below. -/

def pivotal (v : Nat → V) (φ : Fm) (a : Nat) : Prop :=
  ∃ w1 w2 : Nat → V, fills v w1 φ ∧ fills v w2 φ ∧
    w1 a = T ∧ w2 a = F ∧
    (∀ n, n ≠ a → w1 n = w2 n) ∧ foC w1 φ ≠ foC w2 φ

/-- An atom that decides the answer is an atom the claim actually reads. -/
theorem pivotal_occurs (v : Nat → V) (φ : Fm) (a : Nat) (h : pivotal v φ a) :
    occurs a φ = true := by
  obtain ⟨w1, w2, _, _, _, _, hd, hne⟩ := h
  cases ho : occurs a φ with
  | true => rfl
  | false =>
      exact absurd (evalK_congr w1 w2 φ (fun n hn => hd n (fun he => by
        rw [he, ho] at hn; exact Bool.noConfusion hn))) hne

/-- Lift a pivot out of the LEFT branch: hold the sibling at a decided reading
`c` on which the connective is injective in its first argument. -/
theorem lift_left (v : Nat → V) (op : Fm → Fm → Fm) (f : Ph → Ph → Ph)
    (φ ψ : Fm) (a : Nat) (c : Ph)
    (hev : ∀ w : Nat → V, foC w (op φ ψ) = f (foC w φ) (foC w ψ))
    (hocc : ∀ n, occurs n (op φ ψ) = (occurs n φ || occurs n ψ))
    (hlin : ∀ n, v n = Z → occCount n φ + occCount n ψ ≤ 1)
    (u : Nat → V) (hfu : fills v u ψ) (hcu : foC u ψ = c)
    (hinj : ∀ x y : Ph, f x c = f y c → x = y)
    (hp : pivotal v φ a) : pivotal v (op φ ψ) a := by
  obtain ⟨w1, w2, hf1, hf2, ha1, ha2, hd, hne⟩ := hp
  have hoc : occurs a φ = true := pivotal_occurs v φ a ⟨w1, w2, hf1, hf2, ha1, ha2, hd, hne⟩
  refine ⟨merge φ w1 u, merge φ w2 u,
          merge_fills v op φ ψ w1 u hocc hf1 hfu,
          merge_fills v op φ ψ w2 u hocc hf2 hfu,
          by rw [merge_left φ w1 u a hoc]; exact ha1,
          by rw [merge_left φ w2 u a hoc]; exact ha2, ?_, ?_⟩
  · intro n hn
    show (if occurs n φ = true then w1 n else u n)
       = (if occurs n φ = true then w2 n else u n)
    cases hq : occurs n φ with
    | true => exact hd n hn
    | false => rfl
  · rw [hev, hev,
        evalK_congr (merge φ w1 u) w1 φ (merge_left φ w1 u),
        evalK_congr (merge φ w2 u) w2 φ (merge_left φ w2 u),
        evalK_congr (merge φ w1 u) u ψ (merge_right v φ ψ w1 u hf1 hfu hlin),
        evalK_congr (merge φ w2 u) u ψ (merge_right v φ ψ w2 u hf2 hfu hlin), hcu]
    intro h; exact hne (hinj _ _ h)

/-- Lift a pivot out of the RIGHT branch. -/
theorem lift_right (v : Nat → V) (op : Fm → Fm → Fm) (f : Ph → Ph → Ph)
    (φ ψ : Fm) (a : Nat) (c : Ph)
    (hev : ∀ w : Nat → V, foC w (op φ ψ) = f (foC w φ) (foC w ψ))
    (hocc : ∀ n, occurs n (op φ ψ) = (occurs n φ || occurs n ψ))
    (hlin : ∀ n, v n = Z → occCount n φ + occCount n ψ ≤ 1)
    (u : Nat → V) (hfu : fills v u φ) (hcu : foC u φ = c)
    (hinj : ∀ x y : Ph, f c x = f c y → x = y)
    (hp : pivotal v ψ a) : pivotal v (op φ ψ) a := by
  obtain ⟨w1, w2, hf1, hf2, ha1, ha2, hd, hne⟩ := hp
  have hoc : occurs a ψ = true := pivotal_occurs v ψ a ⟨w1, w2, hf1, hf2, ha1, ha2, hd, hne⟩
  refine ⟨merge φ u w1, merge φ u w2,
          merge_fills v op φ ψ u w1 hocc hfu hf1,
          merge_fills v op φ ψ u w2 hocc hfu hf2,
          by rw [merge_right v φ ψ u w1 hfu hf1 hlin a hoc]; exact ha1,
          by rw [merge_right v φ ψ u w2 hfu hf2 hlin a hoc]; exact ha2, ?_, ?_⟩
  · intro n hn
    show (if occurs n φ = true then u n else w1 n)
       = (if occurs n φ = true then u n else w2 n)
    cases hq : occurs n φ with
    | true => rfl
    | false => exact hd n hn
  · rw [hev, hev,
        evalK_congr (merge φ u w1) u φ (merge_left φ u w1),
        evalK_congr (merge φ u w2) u φ (merge_left φ u w2),
        evalK_congr (merge φ u w1) w1 ψ (merge_right v φ ψ u w1 hfu hf1 hlin),
        evalK_congr (merge φ u w2) w2 ψ (merge_right v φ ψ u w2 hfu hf2 hlin), hcu]
    intro h; exact hne (hinj _ _ h)

#print axioms lift_left
#print axioms lift_right

/-! ## The receipt names nothing idle — on a linear claim

Completeness (`receipt_complete`, `Receipt.lean`) says the label is never too
small. This says that on a claim where no dirty atom is read twice, it is
never too large either: **every atom on the receipt decides the answer** under
some definite reading of the others. 128 372 linear cells were measured first;
not one was inexact. The 13-18% inexactness of the general case lives entirely
where a dirty atom occurs more than once — `p ∧ ¬p` names `p` and `p`
cannot move it — which is the same occurrence-independence that costs the
tautologies. -/

theorem knot_inj : ∀ x y : Ph, phNot x = phNot y → x = y := by
  intro x y h; cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

/-- The label of an atom is raised exactly when that atom is the dirty one. -/
theorem atomL_true (x : V) (n m : Nat) (h : atomL x n m = true) : x = Z ∧ n = m := by
  cases x with
  | T => exact Bool.noConfusion h
  | F => exact Bool.noConfusion h
  | Z => exact ⟨rfl, of_decide_eq_true h⟩

theorem label_exact_linear (v : Nat → V) (a : Nat) :
    ∀ φ : Fm, linMarks v φ → labF v φ a = true → pivotal v φ a := by
  intro φ
  induction φ with
  | atom n =>
      intro _ hl
      obtain ⟨hz, hnm⟩ := atomL_true (v n) n a hl
      have hva : v a = Z := by rw [← hnm]; exact hz
      have hf : ∀ x : V, fills v (setA a x v) (Fm.atom n) := by
        intro x
        refine ⟨?_, ?_⟩
        · intro m hm
          exact setA_other x v (fun he => hm (by rw [he]; exact hva))
        · intro m hm
          have hnk : ¬ (n = m) := of_decide_eq_false hm
          exact setA_other x v (fun he => hnk (hnm.trans he.symm))
      refine ⟨setA a T v, setA a F v, hf T, hf F,
              setA_self a T v, setA_self a F v, ?_, ?_⟩
      · intro m hm; rw [setA_other T v hm, setA_other F v hm]
      · intro h
        have h1 : phAtom (setA a T v n) = phAtom (setA a F v n) := h
        rw [hnm, setA_self, setA_self] at h1
        exact absurd h1 (by decide)
  | top => intro _ hl; have h2 : (false : Bool) = true := hl; exact Bool.noConfusion h2
  | bot => intro _ hl; have h2 : (false : Bool) = true := hl; exact Bool.noConfusion h2
  | neg φ ih =>
      intro hlin hl
      obtain ⟨w1, w2, hf1, hf2, ha1, ha2, hd, hne⟩ := ih hlin hl
      exact ⟨w1, w2, hf1, hf2, ha1, ha2, hd, fun h => hne (knot_inj _ _ h)⟩
  | conj φ ψ ihφ ihψ =>
      intro hlin hl
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.conj φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hev : ∀ w : Nat → V, foC w (Fm.conj φ ψ) = phAnd (foC w φ) (foC w ψ) :=
        fun _ => rfl
      cases hva : foC v φ <;> cases hvb : foC v ψ
      · exfalso
        have hdec : labF v (Fm.conj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.conj φ ψ)
            (by show decidedB (phAnd (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.conj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.conj φ ψ)
            (by show decidedB (phAnd (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hla : labF v φ a = false :=
          label_empty_of_decided v a φ (by rw [hva]; rfl)
        cases hlb : labF v ψ a with
        | false =>
            exfalso
            have h2 : conjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_right v Fm.conj phAnd φ ψ a _ hev hocc hlin v (fills_refl v φ) hva
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
      · exfalso
        have hdec : labF v (Fm.conj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.conj φ ψ)
            (by show decidedB (phAnd (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.conj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.conj φ ψ)
            (by show decidedB (phAnd (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.conj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.conj φ ψ)
            (by show decidedB (phAnd (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hlb : labF v ψ a = false :=
          label_empty_of_decided v a ψ (by rw [hvb]; rfl)
        cases hla : labF v φ a with
        | false =>
            exfalso
            have h2 : conjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_left v Fm.conj phAnd φ ψ a _ hev hocc hlin v (fills_refl v ψ) hvb
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
      · exfalso
        have hdec : labF v (Fm.conj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.conj φ ψ)
            (by show decidedB (phAnd (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · cases hla : labF v φ a with
        | true =>
            obtain ⟨u, hfu, hcu⟩ := (drivable v ψ hlψ hvb).1
            exact lift_left v Fm.conj phAnd φ ψ a .t hev hocc hlin u hfu hcu
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
        | false =>
            cases hlb : labF v ψ a with
            | false =>
            exfalso
            have h2 : conjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
            | true =>
                obtain ⟨u, hfu, hcu⟩ := (drivable v φ hlφ hva).1
                exact lift_right v Fm.conj phAnd φ ψ a .t hev hocc hlin u hfu hcu
                  (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
  | disj φ ψ ihφ ihψ =>
      intro hlin hl
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.disj φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hev : ∀ w : Nat → V, foC w (Fm.disj φ ψ) = phOr (foC w φ) (foC w ψ) :=
        fun _ => rfl
      cases hva : foC v φ <;> cases hvb : foC v ψ
      · exfalso
        have hdec : labF v (Fm.disj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.disj φ ψ)
            (by show decidedB (phOr (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.disj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.disj φ ψ)
            (by show decidedB (phOr (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.disj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.disj φ ψ)
            (by show decidedB (phOr (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.disj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.disj φ ψ)
            (by show decidedB (phOr (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.disj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.disj φ ψ)
            (by show decidedB (phOr (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hla : labF v φ a = false :=
          label_empty_of_decided v a φ (by rw [hva]; rfl)
        cases hlb : labF v ψ a with
        | false =>
            exfalso
            have h2 : disjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_right v Fm.disj phOr φ ψ a _ hev hocc hlin v (fills_refl v φ) hva
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
      · exfalso
        have hdec : labF v (Fm.disj φ ψ) a = false :=
          label_empty_of_decided v a (Fm.disj φ ψ)
            (by show decidedB (phOr (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hlb : labF v ψ a = false :=
          label_empty_of_decided v a ψ (by rw [hvb]; rfl)
        cases hla : labF v φ a with
        | false =>
            exfalso
            have h2 : disjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_left v Fm.disj phOr φ ψ a _ hev hocc hlin v (fills_refl v ψ) hvb
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
      · cases hla : labF v φ a with
        | true =>
            obtain ⟨u, hfu, hcu⟩ := (drivable v ψ hlψ hvb).2
            exact lift_left v Fm.disj phOr φ ψ a .f hev hocc hlin u hfu hcu
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
        | false =>
            cases hlb : labF v ψ a with
            | false =>
            exfalso
            have h2 : disjL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
            | true =>
                obtain ⟨u, hfu, hcu⟩ := (drivable v φ hlφ hva).2
                exact lift_right v Fm.disj phOr φ ψ a .f hev hocc hlin u hfu hcu
                  (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
  | imp φ ψ ihφ ihψ =>
      intro hlin hl
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.imp φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hev : ∀ w : Nat → V, foC w (Fm.imp φ ψ) = phImp (foC w φ) (foC w ψ) :=
        fun _ => rfl
      cases hva : foC v φ <;> cases hvb : foC v ψ
      · exfalso
        have hdec : labF v (Fm.imp φ ψ) a = false :=
          label_empty_of_decided v a (Fm.imp φ ψ)
            (by show decidedB (phImp (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.imp φ ψ) a = false :=
          label_empty_of_decided v a (Fm.imp φ ψ)
            (by show decidedB (phImp (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hla : labF v φ a = false :=
          label_empty_of_decided v a φ (by rw [hva]; rfl)
        cases hlb : labF v ψ a with
        | false =>
            exfalso
            have h2 : impL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_right v Fm.imp phImp φ ψ a _ hev hocc hlin v (fills_refl v φ) hva
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
      · exfalso
        have hdec : labF v (Fm.imp φ ψ) a = false :=
          label_empty_of_decided v a (Fm.imp φ ψ)
            (by show decidedB (phImp (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.imp φ ψ) a = false :=
          label_empty_of_decided v a (Fm.imp φ ψ)
            (by show decidedB (phImp (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.imp φ ψ) a = false :=
          label_empty_of_decided v a (Fm.imp φ ψ)
            (by show decidedB (phImp (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.imp φ ψ) a = false :=
          label_empty_of_decided v a (Fm.imp φ ψ)
            (by show decidedB (phImp (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hlb : labF v ψ a = false :=
          label_empty_of_decided v a ψ (by rw [hvb]; rfl)
        cases hla : labF v φ a with
        | false =>
            exfalso
            have h2 : impL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_left v Fm.imp phImp φ ψ a _ hev hocc hlin v (fills_refl v ψ) hvb
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
      · cases hla : labF v φ a with
        | true =>
            obtain ⟨u, hfu, hcu⟩ := (drivable v ψ hlψ hvb).2
            exact lift_left v Fm.imp phImp φ ψ a .f hev hocc hlin u hfu hcu
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
        | false =>
            cases hlb : labF v ψ a with
            | false =>
            exfalso
            have h2 : impL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
            | true =>
                obtain ⟨u, hfu, hcu⟩ := (drivable v φ hlφ hva).1
                exact lift_right v Fm.imp phImp φ ψ a .t hev hocc hlin u hfu hcu
                  (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
  | xor φ ψ ihφ ihψ =>
      intro hlin hl
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.xor φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hev : ∀ w : Nat → V, foC w (Fm.xor φ ψ) = phXor (foC w φ) (foC w ψ) :=
        fun _ => rfl
      cases hva : foC v φ <;> cases hvb : foC v ψ
      · exfalso
        have hdec : labF v (Fm.xor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xor φ ψ)
            (by show decidedB (phXor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.xor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xor φ ψ)
            (by show decidedB (phXor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hla : labF v φ a = false :=
          label_empty_of_decided v a φ (by rw [hva]; rfl)
        cases hlb : labF v ψ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_right v Fm.xor phXor φ ψ a _ hev hocc hlin v (fills_refl v φ) hva
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
      · exfalso
        have hdec : labF v (Fm.xor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xor φ ψ)
            (by show decidedB (phXor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.xor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xor φ ψ)
            (by show decidedB (phXor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hla : labF v φ a = false :=
          label_empty_of_decided v a φ (by rw [hva]; rfl)
        cases hlb : labF v ψ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_right v Fm.xor phXor φ ψ a _ hev hocc hlin v (fills_refl v φ) hva
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
      · have hlb : labF v ψ a = false :=
          label_empty_of_decided v a ψ (by rw [hvb]; rfl)
        cases hla : labF v φ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_left v Fm.xor phXor φ ψ a _ hev hocc hlin v (fills_refl v ψ) hvb
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
      · have hlb : labF v ψ a = false :=
          label_empty_of_decided v a ψ (by rw [hvb]; rfl)
        cases hla : labF v φ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_left v Fm.xor phXor φ ψ a _ hev hocc hlin v (fills_refl v ψ) hvb
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
      · cases hla : labF v φ a with
        | true =>
            obtain ⟨u, hfu, hcu⟩ := (drivable v ψ hlψ hvb).1
            exact lift_left v Fm.xor phXor φ ψ a .t hev hocc hlin u hfu hcu
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
        | false =>
            cases hlb : labF v ψ a with
            | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
            | true =>
                obtain ⟨u, hfu, hcu⟩ := (drivable v φ hlφ hva).1
                exact lift_right v Fm.xor phXor φ ψ a .t hev hocc hlin u hfu hcu
                  (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
  | xnor φ ψ ihφ ihψ =>
      intro hlin hl
      have hlφ : linMarks v φ := fun n hn =>
        Nat.le_trans (Nat.le_add_right _ _) (hlin n hn)
      have hlψ : linMarks v ψ := fun n hn =>
        Nat.le_trans (Nat.le_add_left _ _) (hlin n hn)
      have hocc : ∀ n, occurs n (Fm.xnor φ ψ) = (occurs n φ || occurs n ψ) := fun _ => rfl
      have hev : ∀ w : Nat → V, foC w (Fm.xnor φ ψ) = phXnor (foC w φ) (foC w ψ) :=
        fun _ => rfl
      cases hva : foC v φ <;> cases hvb : foC v ψ
      · exfalso
        have hdec : labF v (Fm.xnor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xnor φ ψ)
            (by show decidedB (phXnor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.xnor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xnor φ ψ)
            (by show decidedB (phXnor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hla : labF v φ a = false :=
          label_empty_of_decided v a φ (by rw [hva]; rfl)
        cases hlb : labF v ψ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_right v Fm.xnor phXnor φ ψ a _ hev hocc hlin v (fills_refl v φ) hva
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
      · exfalso
        have hdec : labF v (Fm.xnor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xnor φ ψ)
            (by show decidedB (phXnor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · exfalso
        have hdec : labF v (Fm.xnor φ ψ) a = false :=
          label_empty_of_decided v a (Fm.xnor φ ψ)
            (by show decidedB (phXnor (foC v φ) (foC v ψ)) = true; rw [hva, hvb]; rfl)
        rw [hdec] at hl; exact Bool.noConfusion hl
      · have hla : labF v φ a = false :=
          label_empty_of_decided v a φ (by rw [hva]; rfl)
        cases hlb : labF v ψ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_right v Fm.xnor phXnor φ ψ a _ hev hocc hlin v (fills_refl v φ) hva
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)
      · have hlb : labF v ψ a = false :=
          label_empty_of_decided v a ψ (by rw [hvb]; rfl)
        cases hla : labF v φ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_left v Fm.xnor phXnor φ ψ a _ hev hocc hlin v (fills_refl v ψ) hvb
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
      · have hlb : labF v ψ a = false :=
          label_empty_of_decided v a ψ (by rw [hvb]; rfl)
        cases hla : labF v φ a with
        | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
        | true =>
            exact lift_left v Fm.xnor phXnor φ ψ a _ hev hocc hlin v (fills_refl v ψ) hvb
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
      · cases hla : labF v φ a with
        | true =>
            obtain ⟨u, hfu, hcu⟩ := (drivable v ψ hlψ hvb).1
            exact lift_left v Fm.xnor phXnor φ ψ a .t hev hocc hlin u hfu hcu
              (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihφ hlφ hla)
        | false =>
            cases hlb : labF v ψ a with
            | false =>
            exfalso
            have h2 : xorL (foC v φ) (foC v ψ) (labF v φ a) (labF v ψ a) = true := hl
            rw [hva, hvb, hla, hlb] at h2
            exact absurd h2 (by decide)
            | true =>
                obtain ⟨u, hfu, hcu⟩ := (drivable v φ hlφ hva).1
                exact lift_right v Fm.xnor phXnor φ ψ a .t hev hocc hlin u hfu hcu
                  (by intro p q hpq; cases p <;> cases q <;> first | rfl | exact absurd hpq (by decide)) (ihψ hlψ hlb)

#print axioms knot_inj
#print axioms label_exact_linear

/-! ## The hypothesis is not decoration

`p ∧ ¬p` reads one dirty atom twice. The receipt names `p` — correctly, by
its own rule, since neither branch is settled — but no reading of `p` moves the
answer: yes gives `F`, no gives `F`. This is the whole of the measured 13-18%
inexactness, and it is the same occurrence-independence that costs `p → p`. -/

theorem clash_names_an_idle_atom :
    labF (fun _ => Z) (Fm.conj (Fm.atom 0) (Fm.neg (Fm.atom 0))) 0 = true
  ∧ ¬ linMarks (fun _ => Z) (Fm.conj (Fm.atom 0) (Fm.neg (Fm.atom 0)))
  ∧ ¬ pivotal (fun _ => Z) (Fm.conj (Fm.atom 0) (Fm.neg (Fm.atom 0))) 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hlin
    have h := hlin 0 rfl
    exact absurd h (by decide)
  · intro h
    obtain ⟨w1, w2, _, _, ha1, ha2, _, hne⟩ := h
    apply hne
    show phAnd (phAtom (w1 0)) (phNot (phAtom (w1 0))) = phAnd (phAtom (w2 0)) (phNot (phAtom (w2 0)))
    rw [ha1, ha2]
    decide

#print axioms clash_names_an_idle_atom

end V

#print axioms V.drivable