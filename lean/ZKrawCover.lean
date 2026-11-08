import ZKrawSys
/-!
# ZKrawCover — a system with a WIDE parameter box: a tree of cuts in the parameters, each leaf with its own
Krawczyk certificate (centre, cube, `Y`, `Z`). Zero axioms.

For every real parameter vector in the inner box, the system has a solution in the bounding cube, and the solution
is unique in the cube of its leaf (`kt_root`). A real parameter is placed in a leaf by cotransitivity, as in
`ZRootPar.tree_root`, not by a decision.
-/

namespace ZKrawCover
open VR VR.Numbers VR.CSR ZNumBin ZField ZIv ZDivIv ZXE ZRealCF ZExp ZRealExp ZRootExp ZRootDiv ZRootPVR ZRootPar
  ZBanach ZKraw ZKrawSys

inductive KT where
  | leaf : List D → D → D → List (List D) → List (List D) → KT
  | cut : Nat → D → D → KT → KT → KT

/-- The leaf cube inside the bounding cube. -/
def cubeIn (d : Nat) (ys : List D) (r : D) (ys0 : List D) (r0 : D) : Bool :=
  allB d (fun i => dle (lo ys0 r0 i) (lo ys r i) && dle (hi ys r i) (hi ys0 r0 i))

/-- **THE COVER CERTIFICATE.** -/
def chkKT (d : Nat) (Fs : Nat → XE) (ys0 : List D) (r0 : D) (R E L μ : Nat) : PS → KT → Bool
  | ps, .leaf ys r rh Y Z => chkK d ys r rh R E L ps (Gsys d (mat Y) Fs) && chkZ d (mat Y) (mat Z) && cubeIn d ys r ys0 r0
  | ps, .cut i c w l rt => optB (lookI i ps) (fun I =>
      dle (dadd (dadd (dadd c (dneg w)) (mg μ)) (mg μ)) (dadd (dadd c w) (dneg (mg μ))) &&
      chkKT d Fs ys0 r0 R E L μ (setI i (I.1, dadd c w) ps) l && chkKT d Fs ys0 r0 R E L μ (setI i (dadd c (dneg w), I.2) ps) rt)

theorem peOf_setI (ps : PS) (i : Nat) (I : Iv) (p : Vec) (j : Nat) : peOf (setI i I ps) p j = peOf ps p j := by
  show cond (isP j (setI i I ps)) (p j) rzero = cond (isP j ps) (p j) rzero
  rw [isP_setI]

theorem evR_setI {d : Nat} (ps : PS) (i : Nat) (I : Iv) (p u : Vec) (G : XE) :
    evR (envK d (peOf (setI i I ps) p) u) G = evR (envK d (peOf ps p) u) G :=
  evR_congr (fun j => by
    show cond (Nat.blt j d) (u j) (peOf (setI i I ps) p j) = cond (Nat.blt j d) (u j) (peOf ps p j)
    rw [peOf_setI]) G

theorem cube_mono {d : Nat} {ys ys0 : List D} {r r0 : D} (h : cubeIn d ys r ys0 r0 = true) {x : Vec}
    (hx : InC d ys r x) : InC d ys0 r0 x :=
  inC_of (fun i hi => by
    obtain ⟨h1, h2⟩ := and2 (allB_sound h i hi)
    obtain ⟨x1, x2⟩ := inC_get hx hi
    exact ⟨rCF.le_trans (dle_sound rOH h1) x1, rCF.le_trans x2 (dle_sound rOH h2)⟩)

/-- The conclusion for one parameter vector: a solution in the bounding cube, unique in some cube around it. -/
def Sol (d : Nat) (Fs : Nat → XE) (ys0 : List D) (r0 : D) (ps : PS) (p : Vec) : Prop :=
  ∃ x : Vec, InC d ys0 r0 x ∧ (∀ i, i < d → rEq (evR (envK d (peOf ps p) x) (Fs i)) rzero) ∧
    ∃ ys r, InC d ys r x ∧ ∀ u, InC d ys r u → (∀ i, i < d → rEq (evR (envK d (peOf ps p) u) (Fs i)) rzero) →
      ∀ i, i < d → rEq (u i) (x i)

theorem sol_setI {d : Nat} {Fs : Nat → XE} {ys0 : List D} {r0 : D} {ps : PS} {i : Nat} {I : Iv} {p : Vec}
    (h : Sol d Fs ys0 r0 (setI i I ps) p) : Sol d Fs ys0 r0 ps p := by
  obtain ⟨x, hx, hF, ys, r, hxr, hu⟩ := h
  refine ⟨x, hx, fun k hk => ?_, ys, r, hxr, fun u hu' hFu => hu u hu' (fun k hk => ?_)⟩
  · rw [← evR_setI ps i I p x (Fs k)]; exact hF k hk
  · rw [evR_setI ps i I p u (Fs k)]; exact hFu k hk

/-- **ON A COVERED PARAMETER BOX, FOR EVERY REAL PARAMETER VECTOR IN THE INNER BOX, THE SYSTEM HAS ITS SOLUTION —
unique in the cube of its leaf.** -/
theorem kt_root (d : Nat) (Fs : Nat → XE) (ys0 : List D) (r0 : D) (R E L μ : Nat) :
    ∀ (t : KT) (ps : PS), chkKT d Fs ys0 r0 R E L μ ps t = true →
    ∀ (p : Vec), InnerIn μ p ps → Sol d Fs ys0 r0 ps p
  | .leaf ys r rh Y Z, ps, h, p, hin => by
      obtain ⟨h12, hc⟩ := and2 h
      obtain ⟨hk, hz⟩ := and2 h12
      obtain ⟨x, hx, hF, hu⟩ := sys_root hk hz p hin
      exact ⟨x, cube_mono hc hx, hF, ys, r, hx, hu⟩
  | .cut i c w l rt, ps, h, p, hin => by
      obtain ⟨I, hI, hc⟩ := optB_some h
      obtain ⟨h12, hr⟩ := and2 hc
      obtain ⟨hgap, hl⟩ := and2 h12
      obtain ⟨b1, b2⟩ := lookI_inner hin hI
      have gap := dle_sound rOH hgap
      have e1 := dv_add rOH (dadd (dadd c (dneg w)) (mg μ)) (mg μ)
      have e2 := ZRootPVR.dv_hp μ
      have pos : rlt rzero (radd (dv rOH (dadd (dadd c w) (dneg (mg μ)))) (rneg (dv rOH (dadd (dadd c (dneg w)) (mg μ))))) := by
        have g' : rCF.le (rCF.add (dv rOH (dadd (dadd c (dneg w)) (mg μ))) (hp rOH μ))
            (dv rOH (dadd (dadd c w) (dneg (mg μ)))) :=
          rCF.le_respects (rCF.trans e1 (rCF.add_congr (rCF.refl _) e2)) (rCF.refl _) gap
        exact rCF.pos_mono (ZNone.pos_hp rCF μ) (gap_le rCF g')
      cases rcotrans pos (p i) with
      | inl hle =>
          exact sol_setI (kt_root d Fs ys0 r0 R E L μ l _ hl p (innerIn_setI (I := (I.1, dadd c w)) b1 hle hin))
      | inr hge =>
          exact sol_setI (kt_root d Fs ys0 r0 R E L μ rt _ hr p (innerIn_setI (I := (dadd c (dneg w), I.2)) hge b2 hin))

end ZKrawCover

#print axioms ZKrawCover.kt_root
