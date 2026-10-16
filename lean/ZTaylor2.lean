import ZSlopeSqrt

/-!
# ZTaylor2 — the kernel's second Taylor coefficient bounds the SYMMETRIC second difference. Zero axioms.

The Taylor leaf of order 2 (`zintegral.py`, the midpoint rule) encloses `∫ f` over `[m − h, m + h]` by
`2h·f(m) + [C2]·2h³/3`, where `C2` is the kernel's reading of `f''/2` over the piece (`zcertify.taylor_coeffs`,
recurrences along the graph). Classically that is Taylor's theorem with the Lagrange remainder. Here, without the
mean value theorem and without a derivative AT a point: the symmetric second difference

    f(m + s) + f(m − s) − 2·f(m)   lies in   2s²·[C2]                                   (`sd_sound`)

because it splits along the graph exactly as the kernel's recurrences do. For a product,

    u₊v₊ + u₋v₋ − 2u₀v₀ = v₀·(u₊ + u₋ − 2u₀) + u₀·(v₊ + v₋ − 2v₀) + (u₊ − u₀)(v₊ − v₀) + (u₀ − u₋)(v₀ − v₋)

— the kernel's `c2(uv) = U0·V2 + U1·V1 + U2·V0`, the two slope products being `ZSlopeSqrt.slope_sound`'s (first
order, already proved). No odd term is needed: it cancels between `m + s` and `m − s`.

Stage 1 (this file): the grammar `const var + − ×`. `exp`, `/`, `sqrt`, `ln` need their own second-order steps.
-/

namespace ZTaylor2

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt

/-- The kernel's reading of the second Taylor coefficient `f''/2` over a box, as relations its computed intervals
satisfy (`zcertify.taylor_coeffs`, order 2): constants and quantities `0`; sums termwise; a product by the
convolution `U0·V2 + U1·V1 + U2·V0`, each product at its corners. -/
inductive T2Read (B : Box QExpr) (i : Nat) : G → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l qzero → qle qzero h → T2Read B i (.const c) l h
  | var {j : Nat} {l h : QExpr} : qle l qzero → qle qzero h → T2Read B i (.var j) l h
  | add {u v : G} {l1 h1 l2 h2 l h : QExpr} : T2Read B i u l1 h1 → T2Read B i v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → T2Read B i (.add u v) l h
  | sub {u v : G} {l1 h1 l2 h2 l h : QExpr} : T2Read B i u l1 h1 → T2Read B i v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → T2Read B i (.sub u v) l h
  | mul {u v : G} {lu hu lv hv du1 du2 dv1 dv2 a1 a2 b1 b2 p1 P1 p2 P2 p3 P3 l h : QExpr} :
      VRead B u lu hu → VRead B v lv hv → DRead B i u du1 du2 → DRead B i v dv1 dv2 →
      T2Read B i u a1 a2 → T2Read B i v b1 b2 →
      Corners p1 P1 lu hu b1 b2 → Corners p2 P2 du1 du2 dv1 dv2 → Corners p3 P3 a1 a2 lv hv →
      qle l (qadd (qadd p1 p2) p3) → qle (qadd (qadd P1 P2) P3) h → T2Read B i (.mul u v) l h

/-- The symmetric second difference at index `n`. -/
def sd (n : Nat) (p0 pp pm : Point QExpr) (e : G) : QExpr :=
  qsub (qadd (evalN n pp e) (evalN n pm e)) (qadd (evalN n p0 e) (evalN n p0 e))

/-- `2s²`. -/
def two_sq (s : QExpr) : QExpr := qmul (qadd qone qone) (qmul s s)

theorem two_sq_nonneg (s : QExpr) : qle qzero (two_sq s) :=
  qmul_nonneg (by have := qone_pos; have := qle_of_qlt qone_pos; rat_linarith) (qmul_self_nonneg s)

/-- A bound `c ≤ 0 ≤ C` gives `c·d ≤ 0 ≤ C·d` for `d ≥ 0`. -/
theorem zero_between {c C d : QExpr} (hc : qle c qzero) (hC : qle qzero C) (hd : qle qzero d) :
    qle (qmul c d) qzero ∧ qle qzero (qmul C d) := by
  have f := qmul_nonneg (a := qneg c) (b := d) (by rat_linarith) hd
  have e : qEq (qmul (qneg c) d) (qneg (qmul c d)) := by rat_ring
  exact ⟨by rat_linarith, qmul_nonneg hC hd⟩

/-- THE SYMMETRIC SECOND DIFFERENCE IS BOUNDED BY THE KERNEL'S SECOND COEFFICIENT. Three points of the box, differing
only in quantity `i`: `m`, `m + s`, `m − s` (`s ≥ 0`). Then `f(m + s) + f(m − s) − 2f(m)` is eventually in
`2s²·[l, h]`, to every precision. -/
theorem sd_sound {B : Box QExpr} {i : Nat} {p0 pp pm : Point QExpr}
    (h0 : InBox qOrd B p0) (hp : InBox qOrd B pp) (hm : InBox qOrd B pm)
    (fp : ∀ j, j ≠ i → pp j = p0 j) (fm : ∀ j, j ≠ i → p0 j = pm j)
    (hs : qle qzero (qsub (pp i) (p0 i))) (hsym : qEq (qsub (p0 i) (pm i)) (qsub (pp i) (p0 i))) :
    ∀ {e : G} {l h : QExpr}, T2Read B i e l h →
      Ev (fun n => sd n p0 pp pm e) (qmul l (two_sq (qsub (pp i) (p0 i)))) (qmul h (two_sq (qsub (pp i) (p0 i)))) := by
  have hd := two_sq_nonneg (qsub (pp i) (p0 i))
  have hs' : qle qzero (qsub (p0 i) (pm i)) := qle_respects (qEq_refl _) (qEq_symm hsym) hs
  intro e l h r
  induction r with
  | @const c l h hl hh =>
      obtain ⟨z1, z2⟩ := zero_between hl hh hd
      have e0 : qEq (qsub (qadd c c) (qadd c c)) qzero := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub (qadd c c) (qadd c c)); rat_linarith,
                                       by show qle (qsub (qadd c c) (qadd c c)) _; rat_linarith⟩)
  | @var j l h hl hh =>
      obtain ⟨z1, z2⟩ := zero_between hl hh hd
      have e0 : qEq (qsub (qadd (pp j) (pm j)) (qadd (p0 j) (p0 j))) qzero := by
        cases Nat.decEq j i with
        | isTrue hj => subst hj; unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
        | isFalse hj => rw [fp j hj, ← fm j hj]; unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub (qadd (pp j) (pm j)) (qadd (p0 j) (p0 j))); rat_linarith,
                                       by show qle (qsub (qadd (pp j) (pm j)) (qadd (p0 j) (p0 j))) _; rat_linarith⟩)
  | @add u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd l1 l2) (two_sq (qsub (pp i) (p0 i))))
          (qadd (qmul l1 (two_sq (qsub (pp i) (p0 i)))) (qmul l2 (two_sq (qsub (pp i) (p0 i))))) := by rat_ring
      have r2 : qEq (qmul (qadd h1 h2) (two_sq (qsub (pp i) (p0 i))))
          (qadd (qmul h1 (two_sq (qsub (pp i) (p0 i)))) (qmul h2 (two_sq (qsub (pp i) (p0 i))))) := by rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_add ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qadd (qadd (evalN n pp u) (evalN n pp v)) (qadd (evalN n pm u) (evalN n pm v)))
        (qadd (qadd (evalN n p0 u) (evalN n p0 v)) (qadd (evalN n p0 u) (evalN n p0 v))))
      unfold sd qsub; rat_ring
  | @sub u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qsub l1 h2) (two_sq (qsub (pp i) (p0 i))))
          (qsub (qmul l1 (two_sq (qsub (pp i) (p0 i)))) (qmul h2 (two_sq (qsub (pp i) (p0 i))))) := by unfold qsub; rat_ring
      have r2 : qEq (qmul (qsub h1 l2) (two_sq (qsub (pp i) (p0 i))))
          (qsub (qmul h1 (two_sq (qsub (pp i) (p0 i)))) (qmul l2 (two_sq (qsub (pp i) (p0 i))))) := by unfold qsub; rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_sub ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qadd (qsub (evalN n pp u) (evalN n pp v)) (qsub (evalN n pm u) (evalN n pm v)))
        (qadd (qsub (evalN n p0 u) (evalN n p0 v)) (qsub (evalN n p0 u) (evalN n p0 v))))
      unfold sd qsub; rat_ring
  | @mul u v lu hu lv hv du1 du2 dv1 dv2 a1 a2 b1 b2 p1 P1 p2 P2 p3 P3 l h ru rv du dv _ _ c1 c2 c3 hl hh ih1 ih2 =>
      -- the four terms of the split
      have T1 := Ev_mul ih1 (value_sound h0 rv) (corners_scale_left c3 hd)
      have T2 := Ev_mul (value_sound h0 ru) ih2 (corners_scale c1 hd)
      have Su := slope_sound h0 hp (fun j hj => fp j hj) hs du
      have Sv := slope_sound h0 hp (fun j hj => fp j hj) hs dv
      have T3 := Ev_mul Su Sv (corners_scale (corners_scale_left c2 hs) hs)
      have Su' := slope_sound hm h0 (fun j hj => fm j hj) hs' du
      have Sv' := slope_sound hm h0 (fun j hj => fm j hj) hs' dv
      have T4 := Ev_mul Su' Sv' (corners_scale (corners_scale_left c2 hs') hs')
      have S := Ev_add (Ev_add T1 T2) (Ev_add T3 T4)
      -- s' = s: the minus side's slope products are the plus side's
      have q1 : qEq (qmul (qmul p2 (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul p2 (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have q2 : qEq (qmul (qmul P2 (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul P2 (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd (qadd p1 p2) p3) (two_sq (qsub (pp i) (p0 i))))
          (qadd (qadd (qmul p3 (two_sq (qsub (pp i) (p0 i)))) (qmul p1 (two_sq (qsub (pp i) (p0 i)))))
            (qadd (qmul (qmul p2 (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i)))
              (qmul (qmul p2 (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))))) := by unfold two_sq; rat_ring
      have r2 : qEq (qmul (qadd (qadd P1 P2) P3) (two_sq (qsub (pp i) (p0 i))))
          (qadd (qadd (qmul P3 (two_sq (qsub (pp i) (p0 i)))) (qmul P1 (two_sq (qsub (pp i) (p0 i)))))
            (qadd (qmul (qmul P2 (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i)))
              (qmul (qmul P2 (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))))) := by unfold two_sq; rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) S) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qadd (qmul (evalN n pp u) (evalN n pp v)) (qmul (evalN n pm u) (evalN n pm v)))
        (qadd (qmul (evalN n p0 u) (evalN n p0 v)) (qmul (evalN n p0 u) (evalN n p0 v))))
      unfold sd qsub; rat_ring

end ZTaylor2

#print axioms ZTaylor2.sd_sound
