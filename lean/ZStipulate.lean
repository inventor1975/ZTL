import ZGround

/-!
# ZStipulate — the passport's stipulation theorem (`zpassport.stipulation_theorem`), proved. Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема». Until today `zpassport.py` stated it as
MEASURED on its zoos: an UNDERDETERMINED (or INTRINSIC) component, once a classical model of it is stipulated, is
grounded at that model, and nothing already grounded is disturbed.

SETTING (`ZGround`): a system `d` of definitions, the stable jump `jumpS`, its least fixed point `lfp d`. A
STIPULATION `σ : List (Option Bool)` replaces the definition of name i by the constant `σ i` where `σ i = some b`
(`stip d σ`: `top` for true, `bot` for false) and keeps it elsewhere.

A MODEL for the stipulation is a phase list `M` above `lfp d` that holds the stipulated values and in which every
stipulated name's OWN definition evaluates to its stipulated value: `evalS M (d i) = ph b`. This is the passport's
"classical model of the component given its grounded environment": `M` = the least fixed point with the component
overwritten by the model (the component's names are `n` there, so `M` lies above it), and the component's
definitions read only the component and its grounded environment, all determined in `M`.

PROVED HERE (`stipulation`):
  (a) NOTHING GROUNDED IS DISTURBED: `lfp d ≤ lfp (stip d σ)` — every name determined before keeps its value;
  (b) THE COMPONENT IS GROUNDED AT THE MODEL: every stipulated name has its stipulated value in `lfp (stip d σ)`.
The proof: by induction the k-th iterate of `d` lies below the k-th iterate of `stip d σ` — a kept definition by the
monotonicity of the step (`evalS_mono`), a stipulated one because every iterate of `d` lies below `lfp d ≤ M`, where
its definition gives exactly the stipulated value.

The PARADOX half of the Python theorem ("every stipulation contradicts a definition") is the definition of "no
classical model" and needs no proof.
-/

namespace V

/-- A Boolean as a determined phase. -/
def ph : Bool → Ph
  | true => .t
  | false => .f

/-- The i-th definition (off the end: `top`, never read — `getP` gives `n` there). -/
def getF : Sys → Nat → Fm
  | [], _ => .top
  | φ :: _, 0 => φ
  | _ :: d, n + 1 => getF d n

def getO : List (Option Bool) → Nat → Option Bool
  | [], _ => none
  | x :: _, 0 => x
  | _ :: σ, n + 1 => getO σ n

def constF : Bool → Fm
  | true => .top
  | false => .bot

/-- The stipulated system. -/
def stip : Sys → List (Option Bool) → Sys
  | [], _ => []
  | φ :: d, [] => φ :: stip d []
  | φ :: d, none :: σ => φ :: stip d σ
  | _ :: d, some b :: σ => constF b :: stip d σ

theorem stip_length : ∀ (d : Sys) (σ : List (Option Bool)), (stip d σ).length = d.length
  | [], _ => rfl
  | _ :: d, [] => congrArg Nat.succ (stip_length d [])
  | _ :: d, none :: σ => congrArg Nat.succ (stip_length d σ)
  | _ :: d, some _ :: σ => congrArg Nat.succ (stip_length d σ)

theorem getF_stip_none : ∀ (d : Sys) (σ : List (Option Bool)) (i : Nat), getO σ i = none →
    getF (stip d σ) i = getF d i
  | [], _, _, _ => rfl
  | _ :: d, [], 0, _ => rfl
  | _ :: d, [], i + 1, h => getF_stip_none d [] i h
  | _ :: d, none :: σ, 0, _ => rfl
  | _ :: d, none :: σ, i + 1, h => getF_stip_none d σ i h
  | _ :: d, some _ :: σ, 0, h => by cases h
  | _ :: d, some _ :: σ, i + 1, h => getF_stip_none d σ i h

theorem getF_stip_some : ∀ (d : Sys) (σ : List (Option Bool)) (i : Nat) (b : Bool), getO σ i = some b →
    i < d.length → getF (stip d σ) i = constF b
  | [], _, _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: d, [], 0, _, h, _ => by cases h
  | _ :: d, [], i + 1, b, h, hl => getF_stip_some d [] i b h (Nat.lt_of_succ_lt_succ hl)
  | _ :: d, none :: σ, 0, _, h, _ => by cases h
  | _ :: d, none :: σ, i + 1, b, h, hl => getF_stip_some d σ i b h (Nat.lt_of_succ_lt_succ hl)
  | _ :: d, some c :: σ, 0, b, h, _ => by
      have : c = b := Option.some.inj h
      rw [this]; rfl
  | _ :: d, some _ :: σ, i + 1, b, h, hl => getF_stip_some d σ i b h (Nat.lt_of_succ_lt_succ hl)

/-- The jump read at one coordinate. -/
theorem getP_jumpS : ∀ (d : Sys) (v : PVal) (i : Nat), i < d.length → getP (jumpS d v) i = evalS v (getF d i)
  | [], _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: d, v, i + 1, hl => getP_jumpS d v i (Nat.lt_of_succ_lt_succ hl)

theorem getP_ge : ∀ (v : PVal) (i : Nat), v.length ≤ i → getP v i = .n
  | [], _, _ => rfl
  | _ :: _, 0, hl => absurd hl (Nat.not_succ_le_zero _)
  | _ :: v, i + 1, hl => getP_ge v i (Nat.le_of_succ_le_succ hl)

/-- Coordinatewise order gives the order (same length). -/
theorem pvLeq_of_getP : ∀ (v w : PVal), v.length = w.length →
    (∀ i, phLeq (getP v i) (getP w i) = true) → pvLeq v w = true
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl
  | a :: v, b :: w, hl, h => by
      show (phLeq a b && pvLeq v w) = true
      have h0 : phLeq a b = true := h 0
      rw [h0, pvLeq_of_getP v w (Nat.succ.inj hl) (fun i => h (i + 1))]; rfl

theorem phLeq_trans : ∀ a b c : Ph, phLeq a b = true → phLeq b c = true → phLeq a c = true := by decide

theorem pvLeq_trans : ∀ (u v w : PVal), pvLeq u v = true → pvLeq v w = true → pvLeq u w = true
  | [], [], [], _, _ => rfl
  | a :: u, b :: v, c :: w, h1, h2 => by
      have p1 := (andEqTrue _ _).mp h1
      have p2 := (andEqTrue _ _).mp h2
      exact (andEqTrue _ _).mpr ⟨phLeq_trans a b c p1.1 p2.1, pvLeq_trans u v w p1.2 p2.2⟩
  | [], [], _ :: _, _, h2 => nomatch h2
  | [], _ :: _, _, h1, _ => nomatch h1
  | _ :: _, [], _, h1, _ => nomatch h1
  | _ :: _, _ :: _, [], _, h2 => nomatch h2

theorem allB_const : ∀ (cs : List (List Bool)) (p : List Bool → Bool), (∀ c, p c = true) → allB cs p = true
  | [], _, _ => rfl
  | c :: cs, p, h => and_mk _ _ (h c) (allB_const cs p h)

theorem evalS_const (v : PVal) : ∀ b : Bool, evalS v (constF b) = ph b
  | true => by
      show (if allB (comps (pad v (maxAtom .top + 1))) (fun c => clEval (bget c) .top) = true then Ph.t
        else if allB (comps (pad v (maxAtom .top + 1))) (fun c => !clEval (bget c) .top) = true then Ph.f
        else Ph.n) = Ph.t
      rw [allB_const (comps (pad v (maxAtom .top + 1))) (fun c => clEval (bget c) Fm.top) (fun _ => rfl)]; rfl
  | false => by
      show (if allB (comps (pad v (maxAtom .bot + 1))) (fun c => clEval (bget c) .bot) = true then Ph.t
        else if allB (comps (pad v (maxAtom .bot + 1))) (fun c => !clEval (bget c) .bot) = true then Ph.f
        else Ph.n) = Ph.f
      have hf : allB (comps (pad v (maxAtom .bot + 1))) (fun c => clEval (bget c) .bot) = false := by
        cases h : allB (comps (pad v (maxAtom .bot + 1))) (fun c => clEval (bget c) .bot)
        · rfl
        · exact Bool.noConfusion (allB_first _ _ h)
      rw [hf, allB_const (comps (pad v (maxAtom .bot + 1))) (fun c => !clEval (bget c) Fm.bot) (fun _ => rfl)]; rfl

/-- Every iterate lies below the least fixed point. -/
theorem iter_le_lfp (d : Sys) : ∀ k, pvLeq (iter d k) (lfp d) = true := by
  intro k
  induction k with
  | zero => exact bot_leq (iter_length d (d.length + 1))
  | succ k ih =>
      have h := jumpS_mono d ih
      rw [kt_fixed] at h
      exact h

/-- **THE STIPULATION THEOREM.** -/
theorem stipulation (d : Sys) (σ : List (Option Bool)) (M : PVal)
    (hle : pvLeq (lfp d) M = true)
    (hmodel : ∀ i b, getO σ i = some b → i < d.length → evalS M (getF d i) = ph b) :
    pvLeq (lfp d) (lfp (stip d σ)) = true ∧
    ∀ i b, getO σ i = some b → i < d.length → getP (lfp (stip d σ)) i = ph b := by
  have hlen : (stip d σ).length = d.length := stip_length d σ
  -- (a) iterate by iterate
  have step : ∀ k, pvLeq (iter d k) (iter (stip d σ) k) = true := by
    intro k
    induction k with
    | zero =>
        show pvLeq (bot d.length) (bot (stip d σ).length) = true
        rw [hlen]; exact pvLeq_refl _
    | succ k ih =>
        show pvLeq (jumpS d (iter d k)) (jumpS (stip d σ) (iter (stip d σ) k)) = true
        apply pvLeq_of_getP
        · rw [jumpS_length, jumpS_length, hlen]
        · intro i
          cases Nat.lt_or_ge i d.length with
          | inr hge =>
              rw [getP_ge _ i (by rw [jumpS_length]; exact hge),
                  getP_ge _ i (by rw [jumpS_length, hlen]; exact hge)]
              rfl
          | inl hlt =>
              rw [getP_jumpS d _ i hlt, getP_jumpS (stip d σ) _ i (by rw [hlen]; exact hlt)]
              cases hs : getO σ i with
              | none =>
                  rw [getF_stip_none d σ i hs]
                  exact evalS_mono ih (getF d i)
              | some b =>
                  rw [getF_stip_some d σ i b hs hlt, evalS_const, ← hmodel i b hs hlt]
                  have hM : pvLeq (iter d k) M = true := pvLeq_trans _ _ _ (iter_le_lfp d k) hle
                  exact evalS_mono hM (getF d i)
  refine ⟨?_, ?_⟩
  · have h := step (d.length + 1)
    have e : lfp (stip d σ) = iter (stip d σ) ((stip d σ).length + 1) := rfl
    rw [e, hlen]; exact h
  · intro i b hs hlt
    have hfix := kt_fixed (stip d σ)
    rw [← hfix, getP_jumpS (stip d σ) _ i (by rw [hlen]; exact hlt), getF_stip_some d σ i b hs hlt, evalS_const]

/-- The truth-teller τ ≡ τ (two models): stipulating τ = T grounds it at T. -/
example : lfp (stip [.atom 0] [some true]) = [.t] := rfl
/-- The even cycle E1 ≡ ¬E2, E2 ≡ ¬E1 with a downstream g ≡ E1 ∨ E2: stipulate E1 = T. -/
example : lfp (stip [.neg (.atom 1), .neg (.atom 0), .disj (.atom 0) (.atom 1)] [some true]) = [.t, .f, .t] := rfl

end V

#print axioms V.stip_length
#print axioms V.getF_stip_none
#print axioms V.getF_stip_some
#print axioms V.getP_jumpS
#print axioms V.getP_ge
#print axioms V.pvLeq_of_getP
#print axioms V.phLeq_trans
#print axioms V.pvLeq_trans
#print axioms V.allB_const
#print axioms V.evalS_const
#print axioms V.iter_le_lfp
#print axioms V.stipulation
