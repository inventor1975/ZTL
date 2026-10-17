import ZExp2

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

The grammar `const var + − × exp / sqrt sin cos` (`exp`'s own second-order step: `ZExp2.Ev_exp2`; `sin`, `cos`:
`ZTrig.Ev_sin2`/`Ev_cos2`, chords on a grid; `/` and `sqrt` by the exact identities `w·v = u`, `s² = u − gap`). `ln` is NOT covered: the kernel's `l2 = (a2 − l1·a1/2)/a0` holds classically
at one point ξ, while this algebra produces a ratio `u(ζ)/u(ξ)` of two points — a same-point argument is missing.
-/

namespace ZTaylor2

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZExp2

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
  | exp {u : G} {lu hu El Eh du1 du2 a1 a2 g G r R' t T l h : QExpr} :
      VRead B u lu hu → (∃ z, ExpCert lu El z) → (∃ z, ExpCert hu z Eh) → DRead B i u du1 du2 → T2Read B i u a1 a2 →
      Corners g G du1 du2 El Eh → Corners r R' du1 du2 g G → Corners t T a1 a2 El Eh →
      qle (qadd l l) (qadd r (qadd t t)) → qle (qadd R' (qadd T T)) (qadd h h) → T2Read B i (.exp u) l h
  | div {u v : G} {lv hv lw hw r1 r2 dw1 dw2 dv1 dv2 a1 a2 b1 b2 p P q Q n1 n2 l h : QExpr} :
      VRead B v lv hv → RecipOK r1 r2 lv hv → VRead B (.div u v) lw hw →
      DRead B i (.div u v) dw1 dw2 → DRead B i v dv1 dv2 → T2Read B i u a1 a2 → T2Read B i v b1 b2 →
      Corners p P dw1 dw2 dv1 dv2 → Corners q Q lw hw b1 b2 →
      qle n1 (qsub (qsub a1 P) Q) → qle (qsub (qsub a2 p) q) n2 → Corners l h n1 n2 r1 r2 → T2Read B i (.div u v) l h
  | sqrt {u : G} {lu hu SL SH w1 w2 r1 r2 ds1 ds2 a1 a2 p P n1 n2 l h : QExpr} :
      VRead B u lu hu → qle qzero lu → qle qzero SL → qle (sq SL) lu → qle qzero SH → qle hu (sq SH) →
      qle w1 (qadd SL SL) → qle (qadd SH SH) w2 → RecipOK r1 r2 w1 w2 →
      DRead B i (.sqrt u) ds1 ds2 → T2Read B i u a1 a2 → Corners p P ds1 ds2 ds1 ds2 →
      qle n1 (qsub a1 P) → qle (qsub a2 p) n2 → Corners l h n1 n2 r1 r2 → T2Read B i (.sqrt u) l h
  | sin {u : G} {lu hu sl sh cl ch du1 du2 a1 a2 g G r R' t T l h : QExpr} :
      VRead B u lu hu → qle lu hu → ZTrig.SinHi lu hu sh → ZTrig.SinLo lu hu sl → ZTrig.CosHi lu hu ch →
      ZTrig.CosLo lu hu cl → DRead B i u du1 du2 → T2Read B i u a1 a2 →
      Corners g G du1 du2 (qneg sh) (qneg sl) → Corners r R' du1 du2 g G → Corners t T a1 a2 cl ch →
      qle (qadd l l) (qadd r (qadd t t)) → qle (qadd R' (qadd T T)) (qadd h h) → T2Read B i (.sin u) l h
  | cos {u : G} {lu hu cl ch sl sh du1 du2 a1 a2 g G r R' t T l h : QExpr} :
      VRead B u lu hu → qle lu hu → ZTrig.CosHi lu hu ch → ZTrig.CosLo lu hu cl → ZTrig.SinHi lu hu sh →
      ZTrig.SinLo lu hu sl → DRead B i u du1 du2 → T2Read B i u a1 a2 →
      Corners g G du1 du2 (qneg ch) (qneg cl) → Corners r R' du1 du2 g G → Corners t T a1 a2 (qneg sh) (qneg sl) →
      qle (qadd l l) (qadd r (qadd t t)) → qle (qadd R' (qadd T T)) (qadd h h) → T2Read B i (.cos u) l h

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

/-- `a + b ≤ n` gives `a ≤ n` and `b ≤ n` (no `omega`: it brings `propext`). -/
theorem le_l {a b n : Nat} (h : a + b ≤ n) : a ≤ n := Nat.le_trans (Nat.le_add_right a b) h
theorem le_r {a b n : Nat} (h : a + b ≤ n) : b ≤ n := Nat.le_trans (Nat.le_add_left b a) h

set_option maxRecDepth 200000 in
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
  | @exp u lu hu El Eh du1 du2 a1 a2 g G r R' t T l h ru cl ch du _ cg cr c3 hl hh ih =>
      -- 2·sd(e^u) = r2(u0, u₊) + r2(u0, u₋) + 2·e^{u0}·sd(u)
      have U0 := value_sound h0 ru
      have Up := value_sound hp ru
      have Um := value_sound hm ru
      have V0 := value_sound h0 (VRead.exp ru cl ch)
      have Rp := Ev_exp2 U0 Up cl ch
      have Rm := Ev_exp2 U0 Um cl ch
      have Sp := slope_sound h0 hp (fun j hj => fp j hj) hs du
      have Sm := slope_sound hm h0 (fun j hj => fm j hj) hs' du
      obtain ⟨⟨g11, g12, g21, g22⟩, ⟨G11, G12, G21, G22⟩⟩ := cg
      have cEl : Corners g G du1 du2 El El := ⟨⟨g11, g11, g21, g21⟩, ⟨G11, G11, G21, G21⟩⟩
      have cEh : Corners g G du1 du2 Eh Eh := ⟨⟨g12, g12, g22, g22⟩, ⟨G12, G12, G22, G22⟩⟩
      have kEl : Ev (fun _ => El) El El := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
      have kEh : Ev (fun _ => Eh) Eh Eh := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
      have PpL := Ev_mul Sp (Ev_mul Sp kEl (corners_scale_left cEl hs)) (corners_scale (corners_scale_left cr hs) hs)
      have PpH := Ev_mul Sp (Ev_mul Sp kEh (corners_scale_left cEh hs)) (corners_scale (corners_scale_left cr hs) hs)
      have PmL := Ev_mul Sm (Ev_mul Sm kEl (corners_scale_left cEl hs')) (corners_scale (corners_scale_left cr hs') hs')
      have PmH := Ev_mul Sm (Ev_mul Sm kEh (corners_scale_left cEh hs')) (corners_scale (corners_scale_left cr hs') hs')
      have T3 := Ev_mul ih V0 (corners_scale_left c3 hd)
      intro k
      obtain ⟨N1, h1⟩ := Rp (k + 2)
      obtain ⟨N2, h2⟩ := Rm (k + 2)
      obtain ⟨N3, h3⟩ := PpL (k + 2)
      obtain ⟨N4, h4⟩ := PpH (k + 2)
      obtain ⟨N5, h5⟩ := PmL (k + 2)
      obtain ⟨N6, h6⟩ := PmH (k + 2)
      obtain ⟨N7, h7⟩ := T3 (k + 2)
      refine ⟨N1 + (N2 + (N3 + (N4 + (N5 + (N6 + N7))))), fun n hn => ?_⟩
      have z1 := le_l hn
      have z2 := le_r hn
      have z3 := le_r z2
      have z4 := le_r z3
      have z5 := le_r z4
      have z6 := le_r z5
      obtain ⟨x1, y1⟩ := h1 n z1
      obtain ⟨x2, y2⟩ := h2 n (le_l z2)
      obtain ⟨x3, _⟩ := h3 n (le_l z3)
      obtain ⟨_, y4⟩ := h4 n (le_l z4)
      obtain ⟨x5, _⟩ := h5 n (le_l z5)
      obtain ⟨_, y6⟩ := h6 n (le_l z6)
      obtain ⟨x7, y7⟩ := h7 n (le_r z6)
      have X1 : qle (qsub (qmul (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qsub (evalN n pp u) (evalN n p0 u))) El) (qeps (k + 2)))
          (qmul two (qsub (qsub (eseq (evalN n pp u) n) (eseq (evalN n p0 u) n))
            (qmul (qsub (evalN n pp u) (evalN n p0 u)) (eseq (evalN n p0 u) n)))) := x1
      have Y1 : qle (qmul two (qsub (qsub (eseq (evalN n pp u) n) (eseq (evalN n p0 u) n))
            (qmul (qsub (evalN n pp u) (evalN n p0 u)) (eseq (evalN n p0 u) n))))
          (qadd (qmul (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qsub (evalN n pp u) (evalN n p0 u))) Eh) (qeps (k + 2))) := y1
      have X2 : qle (qsub (qmul (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qsub (evalN n pm u) (evalN n p0 u))) El) (qeps (k + 2)))
          (qmul two (qsub (qsub (eseq (evalN n pm u) n) (eseq (evalN n p0 u) n))
            (qmul (qsub (evalN n pm u) (evalN n p0 u)) (eseq (evalN n p0 u) n)))) := x2
      have Y2 : qle (qmul two (qsub (qsub (eseq (evalN n pm u) n) (eseq (evalN n p0 u) n))
            (qmul (qsub (evalN n pm u) (evalN n p0 u)) (eseq (evalN n p0 u) n))))
          (qadd (qmul (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qsub (evalN n pm u) (evalN n p0 u))) Eh) (qeps (k + 2))) := y2
      have X3 : qle (qsub (qmul (qmul r (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) (qeps (k + 2)))
          (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) El)) := x3
      have Y4 : qle (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) Eh))
          (qadd (qmul (qmul R' (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) (qeps (k + 2))) := y4
      have X5 : qle (qsub (qmul (qmul r (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i))) (qeps (k + 2)))
          (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qmul (qsub (evalN n p0 u) (evalN n pm u)) El)) := x5
      have Y6 : qle (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qmul (qsub (evalN n p0 u) (evalN n pm u)) Eh))
          (qadd (qmul (qmul R' (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i))) (qeps (k + 2))) := y6
      have X7 : qle (qsub (qmul t (two_sq (qsub (pp i) (p0 i)))) (qeps (k + 2)))
          (qmul (sd n p0 pp pm u) (eseq (evalN n p0 u) n)) := x7
      have Y7 : qle (qmul (sd n p0 pp pm u) (eseq (evalN n p0 u) n))
          (qadd (qmul T (two_sq (qsub (pp i) (p0 i)))) (qeps (k + 2))) := y7
      clear x1 y1 x2 y2 x3 y4 x5 y6 x7 y7 h1 h2 h3 h4 h5 h6 h7 Rp Rm PpL PpH PmL PmH T3 Sp Sm U0 Up Um V0
        cEl cEh kEl kEh g11 g12 g21 g22 G11 G12 G21 G22 cr c3 ih du ru cl ch
      have q1 : qEq (qmul (qmul r (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul r (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have q2 : qEq (qmul (qmul R' (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul R' (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have e2 := qeps_succ_add k
      have e3 := qeps_succ_add (k + 1)
      have ep := qeps_nonneg (k + 2)
      show qle _ (qsub (qadd (eseq (evalN n pp u) n) (eseq (evalN n pm u) n))
          (qadd (eseq (evalN n p0 u) n) (eseq (evalN n p0 u) n))) ∧
        qle (qsub (qadd (eseq (evalN n pp u) n) (eseq (evalN n pm u) n))
          (qadd (eseq (evalN n p0 u) n) (eseq (evalN n p0 u) n))) _
      unfold two two_sq sd qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | @sin u lu hu sl sh cl ch du1 du2 a1 a2 g G r R' t T l h ru hlh shi slo chi clo du _ cg cr c3 hl hh ih =>
      have U0 := value_sound h0 ru
      have Up := value_sound hp ru
      have Um := value_sound hm ru
      have V0 := ZTrig.Ev_cos U0 hlh chi clo
      have Rp := ZTrig.Ev_sin2 U0 Up hlh shi slo
      have Rm := ZTrig.Ev_sin2 U0 Um hlh shi slo
      have Sp := slope_sound h0 hp (fun j hj => fp j hj) hs du
      have Sm := slope_sound hm h0 (fun j hj => fm j hj) hs' du
      obtain ⟨⟨g11, g12, g21, g22⟩, ⟨G11, G12, G21, G22⟩⟩ := cg
      have cEl : Corners g G du1 du2 (qneg sh) (qneg sh) := ⟨⟨g11, g11, g21, g21⟩, ⟨G11, G11, G21, G21⟩⟩
      have cEh : Corners g G du1 du2 (qneg sl) (qneg sl) := ⟨⟨g12, g12, g22, g22⟩, ⟨G12, G12, G22, G22⟩⟩
      have kEl : Ev (fun _ => (qneg sh)) (qneg sh) (qneg sh) := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
      have kEh : Ev (fun _ => (qneg sl)) (qneg sl) (qneg sl) := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
      have PpL := Ev_mul Sp (Ev_mul Sp kEl (corners_scale_left cEl hs)) (corners_scale (corners_scale_left cr hs) hs)
      have PpH := Ev_mul Sp (Ev_mul Sp kEh (corners_scale_left cEh hs)) (corners_scale (corners_scale_left cr hs) hs)
      have PmL := Ev_mul Sm (Ev_mul Sm kEl (corners_scale_left cEl hs')) (corners_scale (corners_scale_left cr hs') hs')
      have PmH := Ev_mul Sm (Ev_mul Sm kEh (corners_scale_left cEh hs')) (corners_scale (corners_scale_left cr hs') hs')
      have T3 := Ev_mul ih V0 (corners_scale_left c3 hd)
      intro k
      obtain ⟨N1, h1⟩ := Rp (k + 2)
      obtain ⟨N2, h2⟩ := Rm (k + 2)
      obtain ⟨N3, h3⟩ := PpL (k + 2)
      obtain ⟨N4, h4⟩ := PpH (k + 2)
      obtain ⟨N5, h5⟩ := PmL (k + 2)
      obtain ⟨N6, h6⟩ := PmH (k + 2)
      obtain ⟨N7, h7⟩ := T3 (k + 2)
      refine ⟨N1 + (N2 + (N3 + (N4 + (N5 + (N6 + N7))))), fun n hn => ?_⟩
      have z1 := le_l hn
      have z2 := le_r hn
      have z3 := le_r z2
      have z4 := le_r z3
      have z5 := le_r z4
      have z6 := le_r z5
      obtain ⟨x1, y1⟩ := h1 n z1
      obtain ⟨x2, y2⟩ := h2 n (le_l z2)
      obtain ⟨x3, _⟩ := h3 n (le_l z3)
      obtain ⟨_, y4⟩ := h4 n (le_l z4)
      obtain ⟨x5, _⟩ := h5 n (le_l z5)
      obtain ⟨_, y6⟩ := h6 n (le_l z6)
      obtain ⟨x7, y7⟩ := h7 n (le_r z6)
      have X1 : qle (qsub (qmul (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qsub (evalN n pp u) (evalN n p0 u))) (qneg sh)) (qeps (k + 2)))
          (qadd (qsub (qsub (ZTrig.Sn (evalN n pp u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n)))
            (qsub (qsub (ZTrig.Sn (evalN n pp u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n)))) := x1
      have Y1 : qle (qadd (qsub (qsub (ZTrig.Sn (evalN n pp u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n)))
            (qsub (qsub (ZTrig.Sn (evalN n pp u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n))))
          (qadd (qmul (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qsub (evalN n pp u) (evalN n p0 u))) (qneg sl)) (qeps (k + 2))) := y1
      have X2 : qle (qsub (qmul (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qsub (evalN n pm u) (evalN n p0 u))) (qneg sh)) (qeps (k + 2)))
          (qadd (qsub (qsub (ZTrig.Sn (evalN n pm u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n)))
            (qsub (qsub (ZTrig.Sn (evalN n pm u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n)))) := x2
      have Y2 : qle (qadd (qsub (qsub (ZTrig.Sn (evalN n pm u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n)))
            (qsub (qsub (ZTrig.Sn (evalN n pm u) n) (ZTrig.Sn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (ZTrig.Cn (evalN n p0 u) n))))
          (qadd (qmul (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qsub (evalN n pm u) (evalN n p0 u))) (qneg sl)) (qeps (k + 2))) := y2
      have X3 : qle (qsub (qmul (qmul r (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) (qeps (k + 2)))
          (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg sh))) := x3
      have Y4 : qle (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg sl)))
          (qadd (qmul (qmul R' (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) (qeps (k + 2))) := y4
      have X5 : qle (qsub (qmul (qmul r (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i))) (qeps (k + 2)))
          (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qneg sh))) := x5
      have Y6 : qle (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qneg sl)))
          (qadd (qmul (qmul R' (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i))) (qeps (k + 2))) := y6
      have X7 : qle (qsub (qmul t (two_sq (qsub (pp i) (p0 i)))) (qeps (k + 2)))
          (qmul (sd n p0 pp pm u) (ZTrig.Cn (evalN n p0 u) n)) := x7
      have Y7 : qle (qmul (sd n p0 pp pm u) (ZTrig.Cn (evalN n p0 u) n))
          (qadd (qmul T (two_sq (qsub (pp i) (p0 i)))) (qeps (k + 2))) := y7
      clear x1 y1 x2 y2 x3 y4 x5 y6 x7 y7 h1 h2 h3 h4 h5 h6 h7 Rp Rm PpL PpH PmL PmH T3 Sp Sm U0 Up Um V0
        cEl cEh kEl kEh g11 g12 g21 g22 G11 G12 G21 G22 cr c3 ih du ru shi slo chi clo
      have q1 : qEq (qmul (qmul r (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul r (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have q2 : qEq (qmul (qmul R' (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul R' (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have e2 := qeps_succ_add k
      have e3 := qeps_succ_add (k + 1)
      have ep := qeps_nonneg (k + 2)
      show qle _ (qsub (qadd (ZTrig.Sn (evalN n pp u) n) (ZTrig.Sn (evalN n pm u) n))
          (qadd (ZTrig.Sn (evalN n p0 u) n) (ZTrig.Sn (evalN n p0 u) n))) ∧
        qle (qsub (qadd (ZTrig.Sn (evalN n pp u) n) (ZTrig.Sn (evalN n pm u) n))
          (qadd (ZTrig.Sn (evalN n p0 u) n) (ZTrig.Sn (evalN n p0 u) n))) _
      unfold two_sq sd qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | @cos u lu hu cl ch sl sh du1 du2 a1 a2 g G r R' t T l h ru hlh chi clo shi slo du _ cg cr c3 hl hh ih =>
      have U0 := value_sound h0 ru
      have Up := value_sound hp ru
      have Um := value_sound hm ru
      have V0 := ZTrig.Ev_negate (ZTrig.Ev_sin U0 hlh shi slo)
      have Rp := ZTrig.Ev_cos2 U0 Up hlh chi clo
      have Rm := ZTrig.Ev_cos2 U0 Um hlh chi clo
      have Sp := slope_sound h0 hp (fun j hj => fp j hj) hs du
      have Sm := slope_sound hm h0 (fun j hj => fm j hj) hs' du
      obtain ⟨⟨g11, g12, g21, g22⟩, ⟨G11, G12, G21, G22⟩⟩ := cg
      have cEl : Corners g G du1 du2 (qneg ch) (qneg ch) := ⟨⟨g11, g11, g21, g21⟩, ⟨G11, G11, G21, G21⟩⟩
      have cEh : Corners g G du1 du2 (qneg cl) (qneg cl) := ⟨⟨g12, g12, g22, g22⟩, ⟨G12, G12, G22, G22⟩⟩
      have kEl : Ev (fun _ => (qneg ch)) (qneg ch) (qneg ch) := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
      have kEh : Ev (fun _ => (qneg cl)) (qneg cl) (qneg cl) := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
      have PpL := Ev_mul Sp (Ev_mul Sp kEl (corners_scale_left cEl hs)) (corners_scale (corners_scale_left cr hs) hs)
      have PpH := Ev_mul Sp (Ev_mul Sp kEh (corners_scale_left cEh hs)) (corners_scale (corners_scale_left cr hs) hs)
      have PmL := Ev_mul Sm (Ev_mul Sm kEl (corners_scale_left cEl hs')) (corners_scale (corners_scale_left cr hs') hs')
      have PmH := Ev_mul Sm (Ev_mul Sm kEh (corners_scale_left cEh hs')) (corners_scale (corners_scale_left cr hs') hs')
      have T3 := Ev_mul ih V0 (corners_scale_left c3 hd)
      intro k
      obtain ⟨N1, h1⟩ := Rp (k + 2)
      obtain ⟨N2, h2⟩ := Rm (k + 2)
      obtain ⟨N3, h3⟩ := PpL (k + 2)
      obtain ⟨N4, h4⟩ := PpH (k + 2)
      obtain ⟨N5, h5⟩ := PmL (k + 2)
      obtain ⟨N6, h6⟩ := PmH (k + 2)
      obtain ⟨N7, h7⟩ := T3 (k + 2)
      refine ⟨N1 + (N2 + (N3 + (N4 + (N5 + (N6 + N7))))), fun n hn => ?_⟩
      have z1 := le_l hn
      have z2 := le_r hn
      have z3 := le_r z2
      have z4 := le_r z3
      have z5 := le_r z4
      have z6 := le_r z5
      obtain ⟨x1, y1⟩ := h1 n z1
      obtain ⟨x2, y2⟩ := h2 n (le_l z2)
      obtain ⟨x3, _⟩ := h3 n (le_l z3)
      obtain ⟨_, y4⟩ := h4 n (le_l z4)
      obtain ⟨x5, _⟩ := h5 n (le_l z5)
      obtain ⟨_, y6⟩ := h6 n (le_l z6)
      obtain ⟨x7, y7⟩ := h7 n (le_r z6)
      have X1 : qle (qsub (qmul (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qsub (evalN n pp u) (evalN n p0 u))) (qneg ch)) (qeps (k + 2)))
          (qadd (qsub (qsub (ZTrig.Cn (evalN n pp u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n))))
            (qsub (qsub (ZTrig.Cn (evalN n pp u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n))))) := x1
      have Y1 : qle (qadd (qsub (qsub (ZTrig.Cn (evalN n pp u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n))))
            (qsub (qsub (ZTrig.Cn (evalN n pp u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n)))))
          (qadd (qmul (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qsub (evalN n pp u) (evalN n p0 u))) (qneg cl)) (qeps (k + 2))) := y1
      have X2 : qle (qsub (qmul (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qsub (evalN n pm u) (evalN n p0 u))) (qneg ch)) (qeps (k + 2)))
          (qadd (qsub (qsub (ZTrig.Cn (evalN n pm u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n))))
            (qsub (qsub (ZTrig.Cn (evalN n pm u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n))))) := x2
      have Y2 : qle (qadd (qsub (qsub (ZTrig.Cn (evalN n pm u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n))))
            (qsub (qsub (ZTrig.Cn (evalN n pm u) n) (ZTrig.Cn (evalN n p0 u) n)) (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qneg (ZTrig.Sn (evalN n p0 u) n)))))
          (qadd (qmul (qmul (qsub (evalN n pm u) (evalN n p0 u)) (qsub (evalN n pm u) (evalN n p0 u))) (qneg cl)) (qeps (k + 2))) := y2
      have X3 : qle (qsub (qmul (qmul r (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) (qeps (k + 2)))
          (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg ch))) := x3
      have Y4 : qle (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qmul (qsub (evalN n pp u) (evalN n p0 u)) (qneg cl)))
          (qadd (qmul (qmul R' (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) (qeps (k + 2))) := y4
      have X5 : qle (qsub (qmul (qmul r (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i))) (qeps (k + 2)))
          (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qneg ch))) := x5
      have Y6 : qle (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qmul (qsub (evalN n p0 u) (evalN n pm u)) (qneg cl)))
          (qadd (qmul (qmul R' (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i))) (qeps (k + 2))) := y6
      have X7 : qle (qsub (qmul t (two_sq (qsub (pp i) (p0 i)))) (qeps (k + 2)))
          (qmul (sd n p0 pp pm u) (qneg (ZTrig.Sn (evalN n p0 u) n))) := x7
      have Y7 : qle (qmul (sd n p0 pp pm u) (qneg (ZTrig.Sn (evalN n p0 u) n)))
          (qadd (qmul T (two_sq (qsub (pp i) (p0 i)))) (qeps (k + 2))) := y7
      clear x1 y1 x2 y2 x3 y4 x5 y6 x7 y7 h1 h2 h3 h4 h5 h6 h7 Rp Rm PpL PpH PmL PmH T3 Sp Sm U0 Up Um V0
        cEl cEh kEl kEh g11 g12 g21 g22 G11 G12 G21 G22 cr c3 ih du ru shi slo chi clo
      have q1 : qEq (qmul (qmul r (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul r (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have q2 : qEq (qmul (qmul R' (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul R' (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have e2 := qeps_succ_add k
      have e3 := qeps_succ_add (k + 1)
      have ep := qeps_nonneg (k + 2)
      show qle _ (qsub (qadd (ZTrig.Cn (evalN n pp u) n) (ZTrig.Cn (evalN n pm u) n))
          (qadd (ZTrig.Cn (evalN n p0 u) n) (ZTrig.Cn (evalN n p0 u) n))) ∧
        qle (qsub (qadd (ZTrig.Cn (evalN n pp u) n) (ZTrig.Cn (evalN n pm u) n))
          (qadd (ZTrig.Cn (evalN n p0 u) n) (ZTrig.Cn (evalN n p0 u) n))) _
      unfold two_sq sd qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | @div u v lv hv lw hw r1 r2 dw1 dw2 dv1 dv2 a1 a2 b1 b2 p P q Q n1 n2 l h rv hR rw dw dv _ _ cp cq hn1 hn2 cl ih1 ih2 =>
      -- w·v = u at each point: sd(u) − w0·sd(v) − Δ₊wΔ₊v − Δ₋wΔ₋v = v0·sd(w)
      have T2 := Ev_mul (value_sound h0 rw) ih2 (corners_scale cq hd)
      have T3 := Ev_mul (slope_sound h0 hp (fun j hj => fp j hj) hs dw) (slope_sound h0 hp (fun j hj => fp j hj) hs dv)
        (corners_scale (corners_scale_left cp hs) hs)
      have T4 := Ev_mul (slope_sound hm h0 (fun j hj => fm j hj) hs' dw) (slope_sound hm h0 (fun j hj => fm j hj) hs' dv)
        (corners_scale (corners_scale_left cp hs') hs')
      have q1 : qEq (qmul (qmul p (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul p (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have q2 : qEq (qmul (qmul P (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul P (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have s1 := ZExp.scale hn1 hd
      have s2 := ZExp.scale hn2 hd
      have Num := Ev_widen (Ev_sub (Ev_sub ih1 T2) (Ev_add T3 T4))
        (l' := qmul n1 (two_sq (qsub (pp i) (p0 i)))) (h' := qmul n2 (two_sq (qsub (pp i) (p0 i))))
        (by unfold two_sq qsub at *; rat_linarith) (by unfold two_sq qsub at *; rat_linarith)
      have Rv := Ev_recip (value_sound h0 rv) hR
      have Qv := Ev_mul Num Rv (corners_scale_left cl hd)
      obtain ⟨J, hJ⟩ := recip_near hR 0
      obtain ⟨N0, hN0⟩ := value_sound h0 rv J
      obtain ⟨Np, hNp⟩ := value_sound hp rv J
      obtain ⟨Nm, hNm⟩ := value_sound hm rv J
      refine Ev_congr_ev (N0 + (Np + Nm)) (fun n hn => ?_) Qv
      obtain ⟨a0', b0'⟩ := hN0 n (le_l hn)
      obtain ⟨ap', bp'⟩ := hNp n (le_l (le_r hn))
      obtain ⟨am', bm'⟩ := hNm n (le_r (le_r hn))
      obtain ⟨z0, _, _⟩ := hJ _ a0' b0'
      obtain ⟨zp, _, _⟩ := hJ _ ap' bp'
      obtain ⟨zm, _, _⟩ := hJ _ am' bm'
      have c0 := qmul_inv'_cancel z0
      have cp' := qmul_inv'_cancel zp
      have cm' := qmul_inv'_cancel zm
      -- w_x·v_x = u_x
      have wv : ∀ (x y : QExpr), qEq (qmul y (qinv' y)) qone → qEq (qmul (qmul x (qinv' y)) y) x := fun x y c => by
        have e := qmul_respects (qEq_refl x) c
        have e2 : qEq (qmul (qmul x (qinv' y)) y) (qmul x (qmul y (qinv' y))) := by rat_ring
        exact qEq_trans e2 (qEq_trans e (qmul_one x))
      have f0 := wv (evalN n p0 u) (evalN n p0 v) c0
      have fp' := wv (evalN n pp u) (evalN n pp v) cp'
      have fm' := wv (evalN n pm u) (evalN n pm v) cm'
      -- the numerator is v0·sd(w)
      have hnum : qEq (qsub (qsub (sd n p0 pp pm u)
            (qmul (qmul (evalN n p0 u) (qinv' (evalN n p0 v))) (sd n p0 pp pm v)))
          (qadd (qmul (qsub (qmul (evalN n pp u) (qinv' (evalN n pp v))) (qmul (evalN n p0 u) (qinv' (evalN n p0 v))))
                  (qsub (evalN n pp v) (evalN n p0 v)))
                (qmul (qsub (qmul (evalN n p0 u) (qinv' (evalN n p0 v))) (qmul (evalN n pm u) (qinv' (evalN n pm v))))
                  (qsub (evalN n p0 v) (evalN n pm v)))))
          (qmul (sd n p0 pp pm (.div u v)) (evalN n p0 v)) := by
        show qEq _ (qmul (qsub (qadd (qmul (evalN n pp u) (qinv' (evalN n pp v))) (qmul (evalN n pm u) (qinv' (evalN n pm v))))
          (qadd (qmul (evalN n p0 u) (qinv' (evalN n p0 v))) (qmul (evalN n p0 u) (qinv' (evalN n p0 v))))) (evalN n p0 v))
        unfold sd qsub at *
        exact qle_antisymm (by rat_linarith) (by rat_linarith)
      have e1 := qmul_respects hnum (qEq_refl (qinv' (evalN n p0 v)))
      have e2 : qEq (qmul (qmul (sd n p0 pp pm (.div u v)) (evalN n p0 v)) (qinv' (evalN n p0 v)))
          (qmul (sd n p0 pp pm (.div u v)) (qmul (evalN n p0 v) (qinv' (evalN n p0 v)))) := by rat_ring
      have e3 := qmul_respects (qEq_refl (sd n p0 pp pm (.div u v))) c0
      exact qEq_trans e1 (qEq_trans e2 (qEq_trans e3 (qmul_one _)))
  | @sqrt u lu hu SL SH w1 w2 r1 r2 ds1 ds2 a1 a2 p P n1 n2 l h ru hlo hSL hSL2 hSH hSH2 hw1 hw2 hR ds _ cp hn1 hn2 cl ih =>
      -- s² = u − θ: sd(u) − sd(θ) − (Δ₊s)² − (Δ₋s)² = 2·s0·sd(s)
      have G0 := gap_ev (value_sound h0 ru) hlo hSH hSH2
      have Gp := gap_ev (value_sound hp ru) hlo hSH hSH2
      have Gm := gap_ev (value_sound hm ru) hlo hSH hSH2
      have Gs := Ev_sub (Ev_add Gp Gm) (Ev_add G0 G0)
      have Sp := slope_sound h0 hp (fun j hj => fp j hj) hs ds
      have Sm := slope_sound hm h0 (fun j hj => fm j hj) hs' ds
      have T3 := Ev_mul Sp Sp (corners_scale (corners_scale_left cp hs) hs)
      have T4 := Ev_mul Sm Sm (corners_scale (corners_scale_left cp hs') hs')
      have q1 : qEq (qmul (qmul p (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul p (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have q2 : qEq (qmul (qmul P (qsub (p0 i) (pm i))) (qsub (p0 i) (pm i)))
          (qmul (qmul P (qsub (pp i) (p0 i))) (qsub (pp i) (p0 i))) := qmul_respects (qmul_respects (qEq_refl _) hsym) hsym
      have s1 := ZExp.scale hn1 hd
      have s2 := ZExp.scale hn2 hd
      have z0 : qEq (qsub (qadd qzero qzero) (qadd qzero qzero)) qzero := by unfold qsub; rat_ring
      have Num := Ev_widen (Ev_sub (Ev_sub ih Gs) (Ev_add T3 T4))
        (l' := qmul n1 (two_sq (qsub (pp i) (p0 i)))) (h' := qmul n2 (two_sq (qsub (pp i) (p0 i))))
        (by unfold two_sq qsub at *; rat_linarith) (by unfold two_sq qsub at *; rat_linarith)
      have V0 := value_sound h0 (VRead.sqrt ru hlo hSL hSL2 hSH hSH2)
      have W := Ev_widen (Ev_add V0 V0) hw1 hw2
      have Rv := Ev_recip W hR
      have Qv := Ev_mul Num Rv (corners_scale_left cl hd)
      obtain ⟨J, hJ⟩ := recip_near hR 0
      obtain ⟨N0, hN0⟩ := W J
      refine Ev_congr_ev N0 (fun n hn => ?_) Qv
      obtain ⟨a0', b0'⟩ := hN0 n hn
      obtain ⟨z, _, _⟩ := hJ _ a0' b0'
      have c0 := qmul_inv'_cancel z
      have hnum : qEq (qsub (qsub (sd n p0 pp pm u)
            (qsub (qadd (qsub (evalN n pp u) (sq (rsqrt (evalN n pp u) n))) (qsub (evalN n pm u) (sq (rsqrt (evalN n pm u) n))))
              (qadd (qsub (evalN n p0 u) (sq (rsqrt (evalN n p0 u) n))) (qsub (evalN n p0 u) (sq (rsqrt (evalN n p0 u) n))))))
          (qadd (qmul (qsub (rsqrt (evalN n pp u) n) (rsqrt (evalN n p0 u) n)) (qsub (rsqrt (evalN n pp u) n) (rsqrt (evalN n p0 u) n)))
                (qmul (qsub (rsqrt (evalN n p0 u) n) (rsqrt (evalN n pm u) n)) (qsub (rsqrt (evalN n p0 u) n) (rsqrt (evalN n pm u) n)))))
          (qmul (sd n p0 pp pm (.sqrt u)) (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n))) := by
        show qEq _ (qmul (qsub (qadd (rsqrt (evalN n pp u) n) (rsqrt (evalN n pm u) n))
          (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n))) (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n)))
        unfold sd sq qsub; rat_ring
      have e1 := qmul_respects hnum (qEq_refl (qinv' (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n))))
      have e2 : qEq (qmul (qmul (sd n p0 pp pm (.sqrt u)) (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n)))
            (qinv' (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n))))
          (qmul (sd n p0 pp pm (.sqrt u)) (qmul (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n))
            (qinv' (qadd (rsqrt (evalN n p0 u) n) (rsqrt (evalN n p0 u) n))))) := by rat_ring
      have e3 := qmul_respects (qEq_refl (sd n p0 pp pm (.sqrt u))) c0
      exact qEq_trans e1 (qEq_trans e2 (qEq_trans e3 (qmul_one _)))

/-- Nonvacuity: `x·x` on `[0, 1]` reads its second coefficient `[1, 1]` — exactly `f''/2`: the convolution
`U0·V2 + U1·V1 + U2·V0 = [0,1]·0 + 1·1 + 0·[0,1]`. -/
example : T2Read (fun _ => (qzero, qone)) 0 (.mul (.var 0) (.var 0)) qone qone :=
  T2Read.mul (lu := qzero) (hu := qone) (lv := qzero) (hv := qone) (du1 := qone) (du2 := qone) (dv1 := qone)
    (dv2 := qone) (a1 := qzero) (a2 := qzero) (b1 := qzero) (b2 := qzero) (p1 := qzero) (P1 := qzero)
    (p2 := qone) (P2 := qone) (p3 := qzero) (P3 := qzero)
    (VRead.var (by decide) (by decide)) (VRead.var (by decide) (by decide))
    (DRead.self (by decide) (by decide)) (DRead.self (by decide) (by decide))
    (T2Read.var (by decide) (by decide)) (T2Read.var (by decide) (by decide))
    (by unfold Corners; decide) (by unfold Corners; decide) (by unfold Corners; decide) (by decide) (by decide)

end ZTaylor2

#print axioms ZTaylor2.sd_sound
