import ZGround
import ZAlgebra
import ZBackward

/-!
# ZInputSubst — substituting INPUTS never revokes grounding (`zfl.cyclic_stable`). Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема». `zfl.cyclic_stable` (2026-11-24) reads a
claim over a SELF-REFERENTIAL system in which a dirty input occurs more than once: first with every occurrence made its
own input (per occurrence) — EARNED / REFUTED there is final; otherwise over every completion of the repeated inputs
(each fixed to one value) — EARNED IF STABLE / REFUTED IF STABLE. Its first return was justified by measurement only.

PROVED HERE (`lfp_subst_mono`): for a system `d` (own names 0 … n-1) and a substitution τ that keeps every own name and
sends every INPUT (an atom ≥ n) to a formula over inputs only, every name grounded in `lfp d` keeps its value in
`lfp (d.map (substF τ))`. Two instances are what `cyclic_stable` needs:
  * IDENTIFICATION: the per-occurrence system, its fresh inputs sent back to the one input they copy — so what the
    per-occurrence reading grounds, the identified reading grounds the same way;
  * COMPLETION: an input sent to the constant `top` or `bot` — so it also holds in every completion.
Hence the per-occurrence verdict, when it settles, is the verdict under every identification and every completion:
returning it first is sound. (The step to the judge's label is the judge's rule, not re-proved here.)

THE KEY LEMMA (`evalS_subst_mono`): one stable step. A classical completion of the substituted formula induces one of
the original (atom i ↦ the value of τ i), which agrees with the own names because τ keeps them.
-/

namespace V
open ZBackward (mem_map_inv mem_append_inv)

/-! ## Classical evaluation: substitution and congruence -/

theorem clEval_subst (g : Nat → Bool) (τ : Nat → Fm) : ∀ φ : Fm,
    clEval g (substF τ φ) = clEval (fun n => clEval g (τ n)) φ
  | .atom _ => rfl
  | .top => rfl
  | .bot => rfl
  | .neg φ => congrArg (fun x => !x) (clEval_subst g τ φ)
  | .conj φ ψ => by
      show (clEval g (substF τ φ) && clEval g (substF τ ψ)) = _
      rw [clEval_subst g τ φ, clEval_subst g τ ψ]; rfl
  | .disj φ ψ => by
      show (clEval g (substF τ φ) || clEval g (substF τ ψ)) = _
      rw [clEval_subst g τ φ, clEval_subst g τ ψ]; rfl
  | .imp φ ψ => by
      show (!clEval g (substF τ φ) || clEval g (substF τ ψ)) = _
      rw [clEval_subst g τ φ, clEval_subst g τ ψ]; rfl
  | .xor φ ψ => by
      show (clEval g (substF τ φ) != clEval g (substF τ ψ)) = _
      rw [clEval_subst g τ φ, clEval_subst g τ ψ]; rfl
  | .xnor φ ψ => by
      show (clEval g (substF τ φ) == clEval g (substF τ ψ)) = _
      rw [clEval_subst g τ φ, clEval_subst g τ ψ]; rfl

-- core's Nat.le_max_left/right, Nat.add_sub_add_right, Nat.add_sub_cancel' carry `propext`: in-house versions
theorem le_max_l (a b : Nat) : a ≤ Nat.max a b := by
  show a ≤ (if a ≤ b then b else a)
  cases Nat.lt_or_ge b a with
  | inl h => rw [if_neg (Nat.not_le_of_gt h)]; exact Nat.le_refl a
  | inr h =>
      cases Nat.lt_or_ge a b with
      | inl h' => rw [if_pos (Nat.le_of_lt h')]; exact Nat.le_of_lt h'
      | inr h' => rw [if_pos h]; exact h
theorem le_max_r (a b : Nat) : b ≤ Nat.max a b := by
  show b ≤ (if a ≤ b then b else a)
  cases Nat.lt_or_ge b a with
  | inl h => rw [if_neg (Nat.not_le_of_gt h)]; exact Nat.le_of_lt h
  | inr h =>
      cases Nat.lt_or_ge a b with
      | inl h' => rw [if_pos (Nat.le_of_lt h')]; exact Nat.le_refl b
      | inr h' => rw [if_pos h]; exact Nat.le_refl b
theorem add_sub_of_le' : ∀ (n m : Nat), n ≤ m → n + (m - n) = m
  | 0, m, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | n + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, m + 1, h => by
      rw [Nat.succ_sub_succ, Nat.succ_add, add_sub_of_le' n m (Nat.le_of_succ_le_succ h)]

/-- Two valuations that agree on the atoms up to `maxAtom φ` agree on φ. -/
theorem clEval_congr (g h : Nat → Bool) : ∀ φ : Fm, (∀ n, n ≤ maxAtom φ → g n = h n) → clEval g φ = clEval h φ
  | .atom n, e => e n (Nat.le_refl n)
  | .top, _ => rfl
  | .bot, _ => rfl
  | .neg φ, e => congrArg (fun x => !x) (clEval_congr g h φ e)
  | .conj φ ψ, e => by
      show (clEval g φ && clEval g ψ) = (clEval h φ && clEval h ψ)
      rw [clEval_congr g h φ (fun n hn => e n (Nat.le_trans hn (le_max_l _ _))),
          clEval_congr g h ψ (fun n hn => e n (Nat.le_trans hn (le_max_r _ _)))]
  | .disj φ ψ, e => by
      show (clEval g φ || clEval g ψ) = (clEval h φ || clEval h ψ)
      rw [clEval_congr g h φ (fun n hn => e n (Nat.le_trans hn (le_max_l _ _))),
          clEval_congr g h ψ (fun n hn => e n (Nat.le_trans hn (le_max_r _ _)))]
  | .imp φ ψ, e => by
      show (!clEval g φ || clEval g ψ) = (!clEval h φ || clEval h ψ)
      rw [clEval_congr g h φ (fun n hn => e n (Nat.le_trans hn (le_max_l _ _))),
          clEval_congr g h ψ (fun n hn => e n (Nat.le_trans hn (le_max_r _ _)))]
  | .xor φ ψ, e => by
      show (clEval g φ != clEval g ψ) = (clEval h φ != clEval h ψ)
      rw [clEval_congr g h φ (fun n hn => e n (Nat.le_trans hn (le_max_l _ _))),
          clEval_congr g h ψ (fun n hn => e n (Nat.le_trans hn (le_max_r _ _)))]
  | .xnor φ ψ, e => by
      show (clEval g φ == clEval g ψ) = (clEval h φ == clEval h ψ)
      rw [clEval_congr g h φ (fun n hn => e n (Nat.le_trans hn (le_max_l _ _))),
          clEval_congr g h ψ (fun n hn => e n (Nat.le_trans hn (le_max_r _ _)))]

/-! ## Completions, read position by position -/

/-- A classical value is allowed by a phase. -/
def okAt : Ph → Bool → Bool
  | .t, b => b
  | .f, b => !b
  | .n, _ => true

/-- c is a completion of w: same length, every determined position kept. -/
def consOk : PVal → List Bool → Bool
  | [], [] => true
  | p :: w, b :: c => okAt p b && consOk w c
  | [], _ :: _ => false
  | _ :: _, [] => false

theorem mem_comps : ∀ (w : PVal) (c : List Bool), c ∈ comps w → consOk w c = true
  | [], c, h => by cases h with
    | head => rfl
    | tail _ t => nomatch t
  | .n :: w, c, h => by
      cases mem_append_inv h with
      | inl h1 => obtain ⟨u, hu, rfl⟩ := mem_map_inv _ h1; exact and_mk _ _ rfl (mem_comps w u hu)
      | inr h1 => obtain ⟨u, hu, rfl⟩ := mem_map_inv _ h1; exact and_mk _ _ rfl (mem_comps w u hu)
  | .t :: w, c, h => by
      obtain ⟨u, hu, rfl⟩ := mem_map_inv _ h; exact and_mk _ _ rfl (mem_comps w u hu)
  | .f :: w, c, h => by
      obtain ⟨u, hu, rfl⟩ := mem_map_inv _ h; exact and_mk _ _ rfl (mem_comps w u hu)

theorem comps_of_cons : ∀ (w : PVal) (c : List Bool), consOk w c = true → c ∈ comps w
  | [], [], _ => List.Mem.head _
  | p :: w, b :: c, h => by
      have h2 := and_true_iff2 _ _ h
      have ih := comps_of_cons w c h2.2
      cases p <;> cases b
      · exact Bool.noConfusion h2.1
      · exact ZBackward.mem_map_of _ ih
      · exact ZBackward.mem_map_of _ ih
      · exact Bool.noConfusion h2.1
      · exact ZBackward.mem_append_r _ (ZBackward.mem_map_of _ ih)
      · exact ZBackward.mem_append_l _ (ZBackward.mem_map_of _ ih)
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem allB_mem : ∀ (cs : List (List Bool)) (p : List Bool → Bool) (c : List Bool),
    allB cs p = true → c ∈ cs → p c = true
  | _ :: cs, p, c, h, hm => by
      have h2 := and_true_iff2 _ _ h
      cases hm with
      | head => exact h2.1
      | tail _ t => exact allB_mem cs p c h2.2 t

theorem allB_of : ∀ (cs : List (List Bool)) (p : List Bool → Bool), (∀ c, c ∈ cs → p c = true) → allB cs p = true
  | [], _, _ => rfl
  | c :: cs, p, h => and_mk _ _ (h c (List.Mem.head _)) (allB_of cs p (fun d hd => h d (List.Mem.tail _ hd)))

/-- consOk, position by position. -/
theorem consOk_pos : ∀ (w : PVal) (c : List Bool), consOk w c = true →
    w.length = c.length ∧ ∀ i, i < w.length → okAt (getP w i) (bget c i) = true
  | [], [], _ => ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | p :: w, b :: c, h => by
      have h2 := and_true_iff2 _ _ h
      obtain ⟨hl, hp⟩ := consOk_pos w c h2.2
      refine ⟨congrArg Nat.succ hl, fun i hi => ?_⟩
      cases i with
      | zero => exact h2.1
      | succ i => exact hp i (Nat.lt_of_succ_lt_succ hi)
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem consOk_of_pos : ∀ (w : PVal) (c : List Bool), w.length = c.length →
    (∀ i, i < w.length → okAt (getP w i) (bget c i) = true) → consOk w c = true
  | [], [], _, _ => rfl
  | p :: w, b :: c, hl, hp => and_mk _ _ (hp 0 (Nat.succ_pos _))
      (consOk_of_pos w c (Nat.succ.inj hl) (fun i hi => hp (i + 1) (Nat.succ_lt_succ hi)))
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl

/-! ## A tabulated valuation -/

def tab (f : Nat → Bool) (i : Nat) : Nat → List Bool
  | 0 => []
  | k + 1 => f i :: tab f (i + 1) k

theorem tab_length (f : Nat → Bool) : ∀ (i k : Nat), (tab f i k).length = k
  | _, 0 => rfl
  | i, k + 1 => congrArg Nat.succ (tab_length f (i + 1) k)

theorem bget_tab (f : Nat → Bool) : ∀ (i k n : Nat), n < k → bget (tab f i k) n = f (i + n)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | i, k + 1, 0, _ => by show f i = f (i + 0); rw [Nat.add_zero]
  | i, k + 1, n + 1, h => by
      show bget (tab f (i + 1) k) n = f (i + (n + 1))
      rw [bget_tab f (i + 1) k n (Nat.lt_of_succ_lt_succ h), Nat.add_assoc, Nat.add_comm 1 n]

/-! ## pad, position by position -/

theorem getP_append_l : ∀ (v r : PVal) (i : Nat), i < v.length → getP (v ++ r) i = getP v i
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: v, r, i + 1, h => getP_append_l v r i (Nat.lt_of_succ_lt_succ h)

theorem getP_replicate : ∀ (m i : Nat), getP (List.replicate m Ph.n) i = .n
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | m + 1, i + 1 => getP_replicate m i

theorem getP_append_r : ∀ (v r : PVal) (i : Nat), v.length ≤ i → getP (v ++ r) i = getP r (i - v.length)
  | [], _, i, _ => by show _ = getP _ (i - 0); rw [Nat.sub_zero]; rfl
  | _ :: _, _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: v, r, i + 1, h => by
      show getP (v ++ r) i = getP r (i + 1 - (v.length + 1))
      rw [Nat.succ_sub_succ]; exact getP_append_r v r i (Nat.le_of_succ_le_succ h)

theorem getP_pad_own (v : PVal) (k i : Nat) (h : i < v.length) : getP (pad v k) i = getP v i :=
  getP_append_l v _ i h

theorem getP_pad_input (v : PVal) (k i : Nat) (h : v.length ≤ i) : getP (pad v k) i = .n := by
  show getP (v ++ List.replicate (k - v.length) Ph.n) i = .n
  rw [getP_append_r v _ i h, getP_replicate]

theorem length_append' : ∀ (v r : PVal), (v ++ r).length = v.length + r.length
  | [], r => (Nat.zero_add _).symm
  | _ :: v, r => by
      show (v ++ r).length + 1 = (v.length + 1) + r.length
      rw [length_append' v r, Nat.add_right_comm]

theorem length_replicate' : ∀ (m : Nat), (List.replicate m Ph.n).length = m
  | 0 => rfl
  | m + 1 => congrArg Nat.succ (length_replicate' m)

theorem pad_length_ge (v : PVal) (k : Nat) : k ≤ (pad v k).length := by
  show k ≤ (v ++ List.replicate (k - v.length) Ph.n).length
  rw [length_append', length_replicate']
  cases Nat.lt_or_ge k v.length with
  | inl h => exact Nat.le_trans (Nat.le_of_lt h) (Nat.le_add_right _ _)
  | inr h => rw [add_sub_of_le' _ _ h]; exact Nat.le_refl k

theorem pad_length_own (v : PVal) (k : Nat) : v.length ≤ (pad v k).length := by
  show v.length ≤ (v ++ List.replicate (k - v.length) Ph.n).length
  rw [length_append']; exact Nat.le_add_right _ _

/-! ## The key lemma: one stable step -/

theorem consts_ok (g : Bool → Bool) (v : PVal) (φ : Fm) (τ : Nat → Fm)
    (hk : ∀ i, i < v.length → τ i = .atom i)
    (h : allB (comps (pad v (maxAtom φ + 1))) (fun c => g (clEval (bget c) φ)) = true) :
    allB (comps (pad v (maxAtom (substF τ φ) + 1))) (fun c => g (clEval (bget c) (substF τ φ))) = true := by
  apply allB_of
  intro c' hc'
  obtain ⟨hl', hp'⟩ := consOk_pos _ _ (mem_comps _ _ hc')
  -- the induced completion of the original: atom i ↦ the value of τ i
  let L := (pad v (maxAtom φ + 1)).length
  let f : Nat → Bool := fun i => clEval (bget c') (τ i)
  let c := tab f 0 L
  have hc : c ∈ comps (pad v (maxAtom φ + 1)) := by
    apply comps_of_cons
    apply consOk_of_pos _ _ (tab_length f 0 L).symm
    intro i hi
    rw [bget_tab f 0 L i hi, Nat.zero_add]
    cases Nat.lt_or_ge i v.length with
    | inl hown =>
        rw [getP_pad_own v _ i hown]
        show okAt (getP v i) (clEval (bget c') (τ i)) = true
        rw [hk i hown]
        have hi' : i < (pad v (maxAtom (substF τ φ) + 1)).length :=
          Nat.lt_of_lt_of_le hown (pad_length_own v _)
        have := hp' i hi'
        rw [getP_pad_own v _ i hown] at this
        exact this
    | inr hinp => rw [getP_pad_input v _ i hinp]; rfl
  have hφ := allB_mem _ _ c h hc
  show g (clEval (bget c') (substF τ φ)) = true
  rw [clEval_subst]
  have e : clEval (fun n => clEval (bget c') (τ n)) φ = clEval (bget c) φ := by
    apply clEval_congr
    intro n hn
    have hnL : n < L := Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hn) (pad_length_ge v _)
    show f n = bget (tab f 0 L) n
    rw [bget_tab f 0 L n hnL, Nat.zero_add]
  rw [e]; exact hφ

/-- **ONE STEP.** Substituting inputs (τ keeps the own names) never revokes what the stable step determines. -/
theorem evalS_subst_mono (v : PVal) (φ : Fm) (τ : Nat → Fm) (hk : ∀ i, i < v.length → τ i = .atom i) :
    phLeq (evalS v φ) (evalS v (substF τ φ)) = true := by
  unfold evalS
  by_cases hT : allB (comps (pad v (maxAtom φ + 1))) (fun c => clEval (bget c) φ) = true
  · have hT' := consts_ok (fun b => b) v φ τ hk hT
    rw [if_pos hT, if_pos hT']; rfl
  · rw [if_neg hT]
    by_cases hF : allB (comps (pad v (maxAtom φ + 1))) (fun c => !clEval (bget c) φ) = true
    · have hF' := consts_ok (fun b => !b) v φ τ hk hF
      have hT' : ¬ allB (comps (pad v (maxAtom (substF τ φ) + 1))) (fun c => clEval (bget c) (substF τ φ)) = true :=
        fun h => not_both _ (allB_first _ _ h) (allB_first _ _ hF')
      rw [if_pos hF, if_neg hT', if_pos hF']; rfl
    · rw [if_neg hF]; exact leqN _

def getF' : Sys → Nat → Fm
  | [], _ => .top
  | φ :: _, 0 => φ
  | _ :: d, n + 1 => getF' d n

theorem getP_jumpS' : ∀ (d : Sys) (v : PVal) (i : Nat), i < d.length → getP (jumpS d v) i = evalS v (getF' d i)
  | [], _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: d, v, i + 1, hl => getP_jumpS' d v i (Nat.lt_of_succ_lt_succ hl)

theorem getF'_map (f : Fm → Fm) : ∀ (d : Sys) (i : Nat), i < d.length → getF' (d.map f) i = f (getF' d i)
  | [], _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: d, i + 1, hl => getF'_map f d i (Nat.lt_of_succ_lt_succ hl)

theorem length_map' (f : Fm → Fm) : ∀ d : Sys, (d.map f).length = d.length
  | [] => rfl
  | _ :: d => congrArg Nat.succ (length_map' f d)

theorem getP_ge' : ∀ (v : PVal) (i : Nat), v.length ≤ i → getP v i = .n
  | [], _, _ => rfl
  | _ :: _, 0, hl => absurd hl (Nat.not_succ_le_zero _)
  | _ :: v, i + 1, hl => getP_ge' v i (Nat.le_of_succ_le_succ hl)

theorem pvLeq_of_getP' : ∀ (v w : PVal), v.length = w.length →
    (∀ i, phLeq (getP v i) (getP w i) = true) → pvLeq v w = true
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl
  | a :: v, b :: w, hl, h => by
      show (phLeq a b && pvLeq v w) = true
      have h0 : phLeq a b = true := h 0
      rw [h0, pvLeq_of_getP' v w (Nat.succ.inj hl) (fun i => h (i + 1))]; rfl

theorem phLeq_trans' : ∀ a b c : Ph, phLeq a b = true → phLeq b c = true → phLeq a c = true := by decide

/-- **THE THEOREM.** Substituting the inputs of a system (own names kept) never revokes a grounding. -/
theorem lfp_subst_mono (d : Sys) (τ : Nat → Fm) (hk : ∀ i, i < d.length → τ i = .atom i) :
    pvLeq (lfp d) (lfp (d.map (substF τ))) = true := by
  have hlen : (d.map (substF τ)).length = d.length := length_map' _ d
  have step : ∀ k, pvLeq (iter d k) (iter (d.map (substF τ)) k) = true := by
    intro k
    induction k with
    | zero =>
        show pvLeq (bot d.length) (bot (d.map (substF τ)).length) = true
        rw [hlen]; exact pvLeq_refl _
    | succ k ih =>
        show pvLeq (jumpS d (iter d k)) (jumpS (d.map (substF τ)) (iter (d.map (substF τ)) k)) = true
        apply pvLeq_of_getP'
        · rw [jumpS_length, jumpS_length, hlen]
        · intro i
          cases Nat.lt_or_ge i d.length with
          | inr hge =>
              rw [getP_ge' _ i (by rw [jumpS_length]; exact hge),
                  getP_ge' _ i (by rw [jumpS_length, hlen]; exact hge)]
              rfl
          | inl hlt =>
              rw [getP_jumpS' d _ i hlt, getP_jumpS' _ _ i (by rw [hlen]; exact hlt), getF'_map _ d i hlt]
              have hk' : ∀ j, j < (iter d k).length → τ j = .atom j := fun j hj =>
                hk j (by rw [iter_length] at hj; exact hj)
              exact phLeq_trans' _ _ _ (evalS_subst_mono (iter d k) (getF' d i) τ hk')
                (evalS_mono ih (substF τ (getF' d i)))
  have h := step (d.length + 1)
  have e : lfp (d.map (substF τ)) = iter (d.map (substF τ)) ((d.map (substF τ)).length + 1) := rfl
  rw [e, hlen]; exact h

/-- IDENTIFICATION: `A ≡ (x₁ ∨ ¬x₂) ∨ A`, two occurrences of one input made two inputs 1, 2, is not grounded; sent
back to one input (2 ↦ 1) it is T. The theorem says the converse direction can never happen. -/
example : lfp [.disj (.disj (.atom 1) (.neg (.atom 2))) (.atom 0)] = [.n] := rfl
example : lfp ([.disj (.disj (.atom 1) (.neg (.atom 2))) (.atom 0)].map
    (substF (fun n => if n = 2 then .atom 1 else .atom n))) = [.t] := rfl

end V

#print axioms V.le_max_l
#print axioms V.le_max_r
#print axioms V.add_sub_of_le'
#print axioms V.clEval_subst
#print axioms V.clEval_congr
#print axioms V.mem_comps
#print axioms V.comps_of_cons
#print axioms V.allB_mem
#print axioms V.allB_of
#print axioms V.consOk_pos
#print axioms V.consOk_of_pos
#print axioms V.tab_length
#print axioms V.bget_tab
#print axioms V.getP_pad_own
#print axioms V.getP_pad_input
#print axioms V.pad_length_ge
#print axioms V.consts_ok
#print axioms V.evalS_subst_mono
#print axioms V.lfp_subst_mono
