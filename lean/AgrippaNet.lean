import Agrippa

/-!
# AgrippaNet — the count with "and", "or", "not": knowledge is a value FORCED by acts. Zero axioms.

2026-10-25 (the curator: "weak point 1 first"). `Agrippa.lean` proves the count for chains: every statement rests on
ONE reason. Real justification rests on several at once — "x because a AND b", "x because a OR b". Here a statement
rests on an EXPRESSION over other statements (references joined by and / or / not); acts and posits are as in
`Agrippa.lean`'s base section (an act's value is computed from its content, a posit's is set by the base).

  `knows_of_good`    SUFFICIENCY. A statement whose reasons bottom out, in finitely many steps through and/or/not, in
                     acts alone (`GoodH`) has a reading, and every reading under EVERY base gives it the same value.
  `act_or_dogma`     THE HONEST COUNTEREXAMPLE to "a dogma anywhere in the reasons spoils knowledge": x := (act true)
                     ∨ (dogma) has one value under every reading and every base. An act can OVERRIDE a dogma. So the
                     thesis reads: knowledge is a value FORCED by acts — not "no dogma among the reasons".
  `dogma_net_two`, `liar_net_zero`  the controls, in the richer language: the dogma reads twice, the liar never.
  `knows_unless_loop_or_posit`  NECESSITY, constructively: on a closed finite base, a statement whose reasons contain
                     no posit and no loop IS knowledge. So whatever is not knowledge rests on a loop (a horn of
                     Agrippa: circle, dogma, liar) or on a posit (a Thing). Decided by a bounded check (`goodB`) and
                     the pigeonhole of `Agrippa.pigeon` — no excluded middle.

The connectives are given — the medium, not derived from the act.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace AgrippaNet

/-- An expression over statements: a reference to statement n, or not/and/or of expressions. -/
inductive Ex where
  | ref : Nat → Ex
  | neg : Ex → Ex
  | and : Ex → Ex → Ex
  | or  : Ex → Ex → Ex

/-- What a statement rests on: an act (the claim m = n, its value computed), a posit (the base sets it), or an
expression over other statements. -/
inductive Sup where
  | act : Nat → Nat → Sup
  | posit : Nat → Sup
  | expr : Ex → Sup

abbrev Net := Nat → Sup

def evalEx (v : Nat → Bool) : Ex → Bool
  | .ref n => v n
  | .neg e => !(evalEx v e)
  | .and e f => evalEx v e && evalEx v f
  | .or e f => evalEx v e || evalEx v f

/-- n occurs in the expression. -/
inductive Refs : Ex → Nat → Prop where
  | ref (n : Nat) : Refs (.ref n) n
  | neg {e n} : Refs e n → Refs (.neg e) n
  | andL {e f n} : Refs e n → Refs (.and e f) n
  | andR {e f n} : Refs f n → Refs (.and e f) n
  | orL {e f n} : Refs e n → Refs (.or e f) n
  | orR {e f n} : Refs f n → Refs (.or e f) n

/-- Two valuations agreeing on every statement an expression mentions give it the same value. -/
theorem evalEx_congr (v w : Nat → Bool) : ∀ e, (∀ n, Refs e n → v n = w n) → evalEx v e = evalEx w e
  | .ref n, h => h n (.ref n)
  | .neg e, h => by
      show (!(evalEx v e)) = !(evalEx w e)
      rw [evalEx_congr v w e (fun n hn => h n (.neg hn))]
  | .and e f, h => by
      show (evalEx v e && evalEx v f) = (evalEx w e && evalEx w f)
      rw [evalEx_congr v w e (fun n hn => h n (.andL hn)), evalEx_congr v w f (fun n hn => h n (.andR hn))]
  | .or e f, h => by
      show (evalEx v e || evalEx v f) = (evalEx w e || evalEx w f)
      rw [evalEx_congr v w e (fun n hn => h n (.orL hn)), evalEx_congr v w f (fun n hn => h n (.orR hn))]

/-- What a statement's support demands under base β and valuation v. -/
def val (N : Net) (β : Nat → Bool) (v : Nat → Bool) (y : Nat) : Bool :=
  match N y with
  | .act m n => Nat.beq m n
  | .posit i => β i
  | .expr e => evalEx v e

/-- The statements x's value rests on: x, and whatever a member's expression mentions. -/
inductive Cone (N : Net) (x : Nat) : Nat → Prop where
  | self : Cone N x x
  | step {y e z} : Cone N x y → N y = .expr e → Refs e z → Cone N x z

/-- v reads x under base β: every support in x's cone holds. -/
def Reading (N : Net) (β : Nat → Bool) (x : Nat) (v : Nat → Bool) : Prop :=
  ∀ y, Cone N x y → v y = val N β v y

/-- Resting on acts alone, through at most h steps of and/or/not. -/
inductive GoodH (N : Net) : Nat → Nat → Prop where
  | act {h y m n} : N y = .act m n → GoodH N h y
  | expr {h y e} : N y = .expr e → (∀ z, Refs e z → GoodH N h z) → GoodH N (h + 1) y

theorem goodH_mono (N : Net) : ∀ {h y}, GoodH N h y → GoodH N (h + 1) y := by
  intro h y g
  induction g with
  | act ha => exact .act ha
  | expr he _ ih => exact .expr he (fun z hz => ih z hz)

theorem goodH_le (N : Net) {h y : Nat} (g : GoodH N h y) : ∀ d, GoodH N (h + d) y
  | 0 => g
  | d + 1 => goodH_mono N (goodH_le N g d)

/-- Every statement in a good statement's cone is good, at the same bound. -/
theorem cone_good (N : Net) {h x : Nat} (gx : GoodH N h x) : ∀ {y}, Cone N x y → GoodH N h y := by
  intro y c
  induction c with
  | self => exact gx
  | step _ hy hz ih =>
      cases ih with
      | act ha => rw [ha] at hy; exact Sup.noConfusion hy
      | expr he hall =>
          rw [he] at hy
          cases hy
          exact goodH_mono N (hall _ hz)

/-- Uniqueness, and the base does not matter: two readings, under ANY two bases, agree on a good statement. -/
theorem good_unique (N : Net) {β β' : Nat → Bool} {v w : Nat → Bool} {x : Nat}
    (hv : Reading N β x v) (hw : Reading N β' x w) :
    ∀ {h y}, GoodH N h y → Cone N x y → v y = w y := by
  intro h y g
  induction g with
  | @act h y m n ha =>
      intro c
      have ev := hv y c
      have ew := hw y c
      unfold val at ev ew
      rw [ha] at ev ew
      rw [ev, ew]
  | @expr h y e he _ ih =>
      intro c
      have ev := hv y c
      have ew := hw y c
      unfold val at ev ew
      rw [he] at ev ew
      rw [ev, ew]
      exact evalEx_congr v w e (fun z hz => ih z hz (Cone.step c he hz))

/-- The evaluator with fuel: acts and posits at once, an expression from the previous fuel. -/
def ev (N : Net) (β : Nat → Bool) : Nat → Nat → Bool
  | 0, y => match N y with
    | .act m n => Nat.beq m n
    | .posit i => β i
    | .expr _ => false
  | k + 1, y => match N y with
    | .act m n => Nat.beq m n
    | .posit i => β i
    | .expr e => evalEx (ev N β k) e

theorem ev_act (N : Net) (β : Nat → Bool) {y m n : Nat} (ha : N y = .act m n) : ∀ k, ev N β k y = Nat.beq m n
  | 0 => by unfold ev; rw [ha]
  | k + 1 => by unfold ev; rw [ha]

theorem ev_expr (N : Net) (β : Nat → Bool) {y : Nat} {e : Ex} (he : N y = .expr e) (k : Nat) :
    ev N β (k + 1) y = evalEx (ev N β k) e := by
  show (match N y with
    | .act m n => Nat.beq m n
    | .posit i => β i
    | .expr e => evalEx (ev N β k) e) = _
  rw [he]

/-- Past its bound, a good statement's evaluation is stable. -/
theorem ev_stable (N : Net) (β : Nat → Bool) : ∀ {h y}, GoodH N h y → ∀ d, ev N β (h + d) y = ev N β h y := by
  intro h y g
  induction g with
  | @act h y m n ha => intro d; rw [ev_act N β ha, ev_act N β ha]
  | @expr h y e he _ ih =>
      intro d
      have e1 : h + 1 + d = (h + d) + 1 := by
        rw [Nat.add_assoc, Nat.add_comm 1 d, ← Nat.add_assoc]
      rw [e1, ev_expr N β he, ev_expr N β he]
      exact evalEx_congr _ _ e (fun z hz => ih z hz d)

/-- SUFFICIENCY. A statement resting on acts alone has a reading, and every reading under every base gives it the
same value: knowledge, independent of the base. -/
theorem knows_of_good (N : Net) {h x : Nat} (gx : GoodH N h x) :
    (∀ β, ∃ v, Reading N β x v) ∧
    ∀ β β' v w, Reading N β x v → Reading N β' x w → v x = w x := by
  refine ⟨fun β => ⟨ev N β (h + 1), ?_⟩, fun β β' v w hv hw => good_unique N hv hw gx .self⟩
  intro y c
  have gy := cone_good N gx c
  cases gy with
  | act ha => unfold val; rw [ha, ev_act N β ha]
  | @expr h' _ e he hall =>
      unfold val
      rw [he, ev_expr N β he]
      exact evalEx_congr _ _ e (fun z hz => (ev_stable N β (hall z hz) 1).trans (ev_stable N β (hall z hz) 2).symm)


/-! ## Necessity: no loop and no posit among the reasons ⇒ knowledge -/

/-- y rests directly on z. -/
def Dep (N : Net) (y z : Nat) : Prop := ∃ e, N y = .expr e ∧ Refs e z

/-- A loop among x's reasons: some y in x's cone returns to itself in L + 1 ≥ 1 steps. -/
def Loop (N : Net) (x : Nat) : Prop :=
  ∃ y, Cone N x y ∧ ∃ (q : Nat → Nat) (L : Nat), q 0 = y ∧ q (L + 1) = y ∧ ∀ i, i ≤ L → Dep N (q i) (q (i + 1))

/-- A closed base of n statements: what the first n mention is among them. -/
def ClosedN (N : Net) (n : Nat) : Prop := ∀ y e z, y < n → N y = .expr e → Refs e z → z < n

/-- Every statement an expression's check needs is true. -/
def allB (f : Nat → Bool) : Ex → Bool
  | .ref n => f n
  | .neg e => allB f e
  | .and e g => allB f e && allB f g
  | .or e g => allB f e && allB f g

theorem allB_true (f : Nat → Bool) : ∀ e, allB f e = true → ∀ z, Refs e z → f z = true
  | .ref n, h, _, .ref _ => h
  | .neg e, h, z, .neg hz => allB_true f e h z hz
  | .and e g, h, z, .andL hz => by
      cases he : allB f e with
      | false => have h' : (allB f e && allB f g) = true := h; rw [he] at h'; exact Bool.noConfusion h'
      | true => exact allB_true f e he z hz
  | .and e g, h, z, .andR hz => by
      cases hg : allB f g with
      | false =>
          have h' : (allB f e && allB f g) = true := h
          rw [hg] at h'
          cases he : allB f e <;> (rw [he] at h'; exact Bool.noConfusion h')
      | true => exact allB_true f g hg z hz
  | .or e g, h, z, .orL hz => by
      cases he : allB f e with
      | false => have h' : (allB f e && allB f g) = true := h; rw [he] at h'; exact Bool.noConfusion h'
      | true => exact allB_true f e he z hz
  | .or e g, h, z, .orR hz => by
      cases hg : allB f g with
      | false =>
          have h' : (allB f e && allB f g) = true := h
          rw [hg] at h'
          cases he : allB f e <;> (rw [he] at h'; exact Bool.noConfusion h')
      | true => exact allB_true f g hg z hz

theorem allB_false (f : Nat → Bool) : ∀ e, allB f e = false → ∃ z, Refs e z ∧ f z = false
  | .ref n, h => ⟨n, .ref n, h⟩
  | .neg e, h => let ⟨z, hz, hf⟩ := allB_false f e h; ⟨z, .neg hz, hf⟩
  | .and e g, h => by
      cases he : allB f e with
      | false => let ⟨z, hz, hf⟩ := allB_false f e he; exact ⟨z, .andL hz, hf⟩
      | true =>
          have h' : (allB f e && allB f g) = false := h
          rw [he] at h'
          let ⟨z, hz, hf⟩ := allB_false f g h'; exact ⟨z, .andR hz, hf⟩
  | .or e g, h => by
      cases he : allB f e with
      | false => let ⟨z, hz, hf⟩ := allB_false f e he; exact ⟨z, .orL hz, hf⟩
      | true =>
          have h' : (allB f e && allB f g) = false := h
          rw [he] at h'
          let ⟨z, hz, hf⟩ := allB_false f g h'; exact ⟨z, .orR hz, hf⟩

theorem refs_nonempty : ∀ e, ∃ z, Refs e z
  | .ref n => ⟨n, .ref n⟩
  | .neg e => let ⟨z, hz⟩ := refs_nonempty e; ⟨z, .neg hz⟩
  | .and e _ => let ⟨z, hz⟩ := refs_nonempty e; ⟨z, .andL hz⟩
  | .or e _ => let ⟨z, hz⟩ := refs_nonempty e; ⟨z, .orL hz⟩

/-- The bounded check: does y rest on acts alone within k steps? Decided, not assumed. -/
def goodB (N : Net) : Nat → Nat → Bool
  | 0, y => match N y with
    | .act _ _ => true
    | .posit _ => false
    | .expr _ => false
  | k + 1, y => match N y with
    | .act _ _ => true
    | .posit _ => false
    | .expr e => allB (goodB N k) e

theorem goodB_sound (N : Net) : ∀ k y, goodB N k y = true → GoodH N k y
  | 0, y, h => by
      unfold goodB at h
      cases hy : N y with
      | act m n => exact .act hy
      | posit i => rw [hy] at h; exact Bool.noConfusion h
      | expr e => rw [hy] at h; exact Bool.noConfusion h
  | k + 1, y, h => by
      unfold goodB at h
      cases hy : N y with
      | act m n => exact .act hy
      | posit i => rw [hy] at h; exact Bool.noConfusion h
      | expr e =>
          rw [hy] at h
          exact .expr hy (fun z hz => goodB_sound N k z (allB_true _ e h z hz))

/-- A failed check walks: from a statement that fails within k steps, and has no posit below it, a path of k + 1
dependency steps, every node in x's cone. -/
theorem fail_path (N : Net) (x : Nat) (np : ∀ y, Cone N x y → ∀ i, N y ≠ .posit i) :
    ∀ k y, goodB N k y = false → Cone N x y →
      ∃ p : Nat → Nat, p 0 = y ∧ (∀ i, i ≤ k → Dep N (p i) (p (i + 1))) ∧ (∀ i, i ≤ k + 1 → Cone N x (p i))
  | 0, y, h, c => by
      unfold goodB at h
      cases hy : N y with
      | act m n => rw [hy] at h; exact Bool.noConfusion h
      | posit i => exact absurd hy (np y c i)
      | expr e =>
          obtain ⟨z, hz⟩ := refs_nonempty e
          refine ⟨fun i => match i with | 0 => y | _ + 1 => z, rfl, ?_, ?_⟩
          · intro i hi
            cases i with
            | zero => exact ⟨e, hy, hz⟩
            | succ i => exact absurd hi (Nat.not_succ_le_zero i)
          · intro i _
            cases i with
            | zero => exact c
            | succ i => exact Cone.step c hy hz
  | k + 1, y, h, c => by
      unfold goodB at h
      cases hy : N y with
      | act m n => rw [hy] at h; exact Bool.noConfusion h
      | posit i => exact absurd hy (np y c i)
      | expr e =>
          rw [hy] at h
          obtain ⟨z, hz, hf⟩ := allB_false _ e h
          obtain ⟨q, q0, qdep, qcone⟩ := fail_path N x np k z hf (Cone.step c hy hz)
          refine ⟨fun i => match i with | 0 => y | j + 1 => q j, rfl, ?_, ?_⟩
          · intro i hi
            cases i with
            | zero => show Dep N y (q 0); rw [q0]; exact ⟨e, hy, hz⟩
            | succ j => exact qdep j (Nat.le_of_succ_le_succ hi)
          · intro i hi
            cases i with
            | zero => exact c
            | succ j => exact qcone j (Nat.le_of_succ_le_succ hi)

theorem cone_lt (N : Net) {n x : Nat} (hc : ClosedN N n) (hx : x < n) : ∀ {y}, Cone N x y → y < n := by
  intro y c
  induction c with
  | self => exact hx
  | step _ hy hz ih => exact hc _ _ _ ih hy hz

/-- NECESSITY. On a closed base of n statements: no posit and no loop among x's reasons ⇒ x is knowledge (rests on
acts alone, within n steps; `knows_of_good` then gives existence, uniqueness and independence from the base). -/
theorem good_unless_loop_or_posit (N : Net) (n x : Nat) (hc : ClosedN N n) (hx : x < n)
    (np : ∀ y, Cone N x y → ∀ i, N y ≠ .posit i) (nl : ¬ Loop N x) : GoodH N n x := by
  cases hg : goodB N n x with
  | true => exact goodB_sound N n x hg
  | false =>
      exfalso
      obtain ⟨p, p0, pdep, pcone⟩ := fail_path N x np n x hg .self
      obtain ⟨a, b, hab, hbn, heq⟩ :=
        Agrippa.pigeon n p (fun k hk => cone_lt N hc hx (pcone k (Nat.le_succ_of_le hk)))
      obtain ⟨d, hd0⟩ := Agrippa.le_split hab
      have hd : a + 1 + d = b := hd0
      apply nl
      refine ⟨p a, pcone a (Nat.le_succ_of_le (Nat.le_trans (Nat.le_of_lt hab) hbn)),
        fun i => p (a + i), d, rfl, ?_, ?_⟩
      · show p (a + (d + 1)) = p a
        have e1 : a + (d + 1) = b := by rw [← hd, Nat.add_assoc, Nat.add_comm 1 d]
        rw [e1]; exact heq.symm
      · intro i hi
        have hle : a + i ≤ n := by
          have h1 : a + i ≤ a + d := Nat.add_le_add_left hi a
          have h2 : a + d < a + 1 + d := by
            rw [Nat.add_assoc, Nat.add_comm 1 d, ← Nat.add_assoc]; exact Nat.lt_succ_self _
          rw [hd] at h2
          exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt h1 h2)) hbn
        exact pdep (a + i) hle

/-- The thesis in one line: on a closed finite base, a statement with no posit and no loop among its reasons has a
reading under every base, and one value under every reading and every base. Whatever is NOT knowledge rests on a
loop (a horn) or on a posit (a Thing). -/
theorem knows_unless_loop_or_posit (N : Net) (n x : Nat) (hc : ClosedN N n) (hx : x < n)
    (np : ∀ y, Cone N x y → ∀ i, N y ≠ .posit i) (nl : ¬ Loop N x) :
    (∀ β, ∃ v, Reading N β x v) ∧ ∀ β β' v w, Reading N β x v → Reading N β' x w → v x = w x :=
  knows_of_good N (good_unless_loop_or_posit N n x hc hx np nl)

/-! ## The counterexample and the controls -/

/-- x := a ∨ d, a the act "0 = 0", d the dogma "d because d". -/
def actOrDogma : Net := fun n =>
  if n = 0 then .expr (.or (.ref 1) (.ref 2)) else if n = 1 then .act 0 0 else .expr (.ref 2)

theorem cone_aod {y : Nat} (c : Cone actOrDogma 0 y) : y = 0 ∨ y = 1 ∨ y = 2 := by
  induction c with
  | self => exact .inl rfl
  | @step y e z _ hy hz ih =>
      cases ih with
      | inl h0 =>
          subst h0
          have hy' : Sup.expr (.or (.ref 1) (.ref 2)) = Sup.expr e := hy
          cases hy'
          cases hz with
          | orL h => cases h; exact .inr (.inl rfl)
          | orR h => cases h; exact .inr (.inr rfl)
      | inr h12 =>
          cases h12 with
          | inl h1 =>
              subst h1
              have hy' : Sup.act 0 0 = Sup.expr e := hy
              exact Sup.noConfusion hy'
          | inr h2 =>
              subst h2
              have hy' : Sup.expr (.ref 2) = Sup.expr e := hy
              cases hy'
              cases hz
              exact .inr (.inr rfl)

/-- THE ACT OVERRIDES THE DOGMA. A dogma sits among x's reasons, and x still has a reading under every base and one
value under every reading and every base. -/
theorem act_or_dogma :
    (∀ β, ∃ v, Reading actOrDogma β 0 v) ∧
    ∀ β β' v w, Reading actOrDogma β 0 v → Reading actOrDogma β' 0 w → v 0 = w 0 := by
  have v1 : ∀ β v, Reading actOrDogma β 0 v → v 1 = true := by
    intro β v hv
    have e := hv 1 (Cone.step Cone.self rfl (Refs.orL (Refs.ref 1)))
    exact e
  have v0 : ∀ β v, Reading actOrDogma β 0 v → v 0 = true := by
    intro β v hv
    have e : v 0 = (v 1 || v 2) := hv 0 Cone.self
    rw [e, v1 β v hv]; rfl
  refine ⟨fun β => ⟨fun _ => true, ?_⟩, fun β β' v w hv hw => by rw [v0 β v hv, v0 β' w hw]⟩
  intro y c
  cases cone_aod c with
  | inl h => subst h; rfl
  | inr h =>
      cases h with
      | inl h => subst h; rfl
      | inr h => subst h; rfl


/-- x := b ∨ d with b the FALSE act "0 = 1": the dogma decides, and x reads twice. Only a true act overrides. -/
def falseActOrDogma : Net := fun n =>
  if n = 0 then .expr (.or (.ref 1) (.ref 2)) else if n = 1 then .act 0 1 else .expr (.ref 2)

theorem cone_faod {y : Nat} (c : Cone falseActOrDogma 0 y) : y = 0 ∨ y = 1 ∨ y = 2 := by
  induction c with
  | self => exact .inl rfl
  | @step y e z _ hy hz ih =>
      cases ih with
      | inl h0 =>
          subst h0
          have hy' : Sup.expr (.or (.ref 1) (.ref 2)) = Sup.expr e := hy
          cases hy'
          cases hz with
          | orL h => cases h; exact .inr (.inl rfl)
          | orR h => cases h; exact .inr (.inr rfl)
      | inr h12 =>
          cases h12 with
          | inl h1 =>
              subst h1
              have hy' : Sup.act 0 1 = Sup.expr e := hy
              exact Sup.noConfusion hy'
          | inr h2 =>
              subst h2
              have hy' : Sup.expr (.ref 2) = Sup.expr e := hy
              cases hy'
              cases hz
              exact .inr (.inr rfl)

theorem false_act_or_dogma_two : ∃ v w, Reading falseActOrDogma (fun _ => false) 0 v ∧
    Reading falseActOrDogma (fun _ => false) 0 w ∧ v 0 ≠ w 0 := by
  refine ⟨fun n => if n = 1 then false else true, fun _ => false, ?_, ?_, Bool.noConfusion⟩
  · intro y c
    cases cone_faod c with
    | inl h => subst h; rfl
    | inr h => cases h with
      | inl h => subst h; rfl
      | inr h => subst h; rfl
  · intro y c
    cases cone_faod c with
    | inl h => subst h; rfl
    | inr h => cases h with
      | inl h => subst h; rfl
      | inr h => subst h; rfl

/-- The dogma alone: d := d, two readings that disagree. -/
def dogmaNet : Net := fun _ => .expr (.ref 0)

theorem cone_dogma {y : Nat} (c : Cone dogmaNet 0 y) : y = 0 := by
  induction c with
  | self => rfl
  | @step y e z _ hy hz ih =>
      subst ih
      have hy' : Sup.expr (.ref 0) = Sup.expr e := hy
      cases hy'
      cases hz
      rfl

theorem dogma_net_two : ∃ v w, Reading dogmaNet (fun _ => false) 0 v ∧ Reading dogmaNet (fun _ => false) 0 w ∧
    v 0 ≠ w 0 := by
  refine ⟨fun _ => true, fun _ => false, ?_, ?_, Bool.noConfusion⟩
  · intro y c; rw [cone_dogma c]; rfl
  · intro y c; rw [cone_dogma c]; rfl

/-- The liar: l := ¬l, no reading under any base. -/
def liarNet : Net := fun _ => .expr (.neg (.ref 0))

theorem liar_net_zero (β : Nat → Bool) : ¬ ∃ v, Reading liarNet β 0 v := by
  intro ⟨v, hv⟩
  have e : v 0 = !(v 0) := hv 0 Cone.self
  cases h : v 0 with
  | false => rw [h] at e; exact Bool.noConfusion e
  | true => rw [h] at e; exact Bool.noConfusion e

end AgrippaNet

#print axioms AgrippaNet.evalEx_congr
#print axioms AgrippaNet.goodH_mono
#print axioms AgrippaNet.cone_good
#print axioms AgrippaNet.good_unique
#print axioms AgrippaNet.ev_stable
#print axioms AgrippaNet.knows_of_good
#print axioms AgrippaNet.allB_true
#print axioms AgrippaNet.allB_false
#print axioms AgrippaNet.goodB_sound
#print axioms AgrippaNet.fail_path
#print axioms AgrippaNet.cone_lt
#print axioms AgrippaNet.good_unless_loop_or_posit
#print axioms AgrippaNet.knows_unless_loop_or_posit
#print axioms AgrippaNet.act_or_dogma
#print axioms AgrippaNet.false_act_or_dogma_two
#print axioms AgrippaNet.dogma_net_two
#print axioms AgrippaNet.liar_net_zero
