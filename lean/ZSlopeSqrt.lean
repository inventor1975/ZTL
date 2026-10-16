import ZSqrt

/-!
# ZSlopeSqrt — the kernel's certificate rule for `+ − × / exp ln sqrt`, on VR's operational reals. Zero axioms.

`ZSlopeDiv` with `√` added (`ZSqrt`: the root found on a grid, the value read as the kernel's rational fork
`[SL, SH]` with `SL² ≤ lo`, `hi ≤ SH²`, as `znum._rat_sqrt` builds it, `lo ≥ 0`). The kernel reads the derivative
of `√u` as `Du × [1/(2·√U)]` (`zcertify._graph_grad`): here `2·√U` is read in `[w1, w2] ⊇ [2·SL, 2·SH]`, its
reciprocal by `RecipOK` (clear of zero — the kernel refuses `√` at or near `0` there), and the slope is the exact
step `√b − √a = (b − a)·1/(√a + √b)` up to the grid's gap (`ZSqrt.Ev_sqrt_slope`) — no mean value theorem.
Everything else is `ZSlopeDiv`'s, re-proved over the larger grammar (the grammar is an inductive type, so it is
re-stated, not extended).
-/

namespace ZSlopeSqrt

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-! ## The grammar with `/` and `exp` -/

theorem Ev_congr_ev {x y : Nat → QExpr} {l h : QExpr} (N0 : Nat) (e : ∀ n, N0 ≤ n → qEq (x n) (y n))
    (hx : Ev x l h) : Ev y l h := fun k => by
  obtain ⟨N, hN⟩ := hx k
  refine ⟨N + N0, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n (Nat.le_trans (Nat.le_add_right N N0) hn)
  have := e n (Nat.le_trans (Nat.le_add_left N0 N) hn)
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- Corners scaled by `d ≥ 0` in the FIRST factor. -/
theorem corners_scale_left {m M a1 a2 b1 b2 d : QExpr} (hc : Corners m M a1 a2 b1 b2) (hd : qle qzero d) :
    Corners (qmul m d) (qmul M d) (qmul a1 d) (qmul a2 d) b1 b2 := by
  obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hc
  have r : ∀ x y : QExpr, qEq (qmul (qmul x y) d) (qmul (qmul x d) y) := fun x y => by rat_ring
  exact ⟨⟨qle_respects (qEq_refl _) (r _ _) (ZExp.scale l11 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l12 hd),
          qle_respects (qEq_refl _) (r _ _) (ZExp.scale l21 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l22 hd)⟩,
         ⟨qle_respects (r _ _) (qEq_refl _) (ZExp.scale h11 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h12 hd),
          qle_respects (r _ _) (qEq_refl _) (ZExp.scale h21 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h22 hd)⟩⟩

inductive G where
  | const : QExpr → G
  | var   : Nat → G
  | add   : G → G → G
  | sub   : G → G → G
  | mul   : G → G → G
  | div   : G → G → G
  | exp   : G → G
  | ln    : G → G
  | sqrt  : G → G

def evalN (n : Nat) (p : Point QExpr) : G → QExpr
  | .const c => c
  | .var i => p i
  | .add u v => qadd (evalN n p u) (evalN n p v)
  | .sub u v => qsub (evalN n p u) (evalN n p v)
  | .mul u v => qmul (evalN n p u) (evalN n p v)
  | .div u v => qmul (evalN n p u) (qinv' (evalN n p v))
  | .exp u => eseq (evalN n p u) n
  | .ln u => lnseq (evalN n p u) n
  | .sqrt u => rsqrt (evalN n p u) n

/-- The kernel's value reading: a quotient is `U × [1/V]`, `V` clear of zero (`RecipOK`). -/
inductive VRead (B : Box QExpr) : G → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l c → qle c h → VRead B (.const c) l h
  | var {i : Nat} {l h : QExpr} : qle l (B i).1 → qle (B i).2 h → VRead B (.var i) l h
  | add {u v : G} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → VRead B (.add u v) l h
  | sub {u v : G} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → VRead B (.sub u v) l h
  | mul {u v : G} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      Corners l h l1 h1 l2 h2 → VRead B (.mul u v) l h
  | div {u v : G} {lu hu lv hv li hi l h : QExpr} : VRead B u lu hu → VRead B v lv hv →
      RecipOK li hi lv hv → Corners l h lu hu li hi → VRead B (.div u v) l h
  | exp {u : G} {lu hu El Eh : QExpr} : VRead B u lu hu →
      (∃ z, ExpCert lu El z) → (∃ z, ExpCert hu z Eh) → VRead B (.exp u) El Eh
  | ln {u : G} {lu hu Ll Lh zl wl zh wh : QExpr} : VRead B u lu hu → qlt qzero lu →
      ExpCert Ll zl wl → qle wl lu → ExpCert Lh wh zh → qle hu wh → VRead B (.ln u) Ll Lh
  | sqrt {u : G} {lu hu SL SH : QExpr} : VRead B u lu hu → qle qzero lu →
      qle qzero SL → qle (sq SL) lu → qle qzero SH → qle hu (sq SH) → VRead B (.sqrt u) SL SH

theorem value_sound {B : Box QExpr} {p : Point QExpr} (hp : InBox qOrd B p) :
    ∀ {e : G} {l h : QExpr}, VRead B e l h → Ev (fun n => evalN n p e) l h := by
  intro e l h r
  induction r with
  | const h1 h2 => exact Ev_of_exact 0 (fun _ _ => ⟨h1, h2⟩)
  | var h1 h2 => exact Ev_of_exact 0 (fun _ _ => ⟨qle_trans h1 (hp _).1, qle_trans (hp _).2 h2⟩)
  | add _ _ hl hh ih1 ih2 => exact Ev_widen (Ev_add ih1 ih2) hl hh
  | sub _ _ hl hh ih1 ih2 => exact Ev_widen (Ev_sub ih1 ih2) hl hh
  | mul _ _ hc ih1 ih2 => exact Ev_mul ih1 ih2 hc
  | div _ _ hR hc ih1 ih2 => exact Ev_mul ih1 (Ev_recip ih2 hR) hc
  | exp _ cl ch ih => exact Ev_exp ih cl ch
  | ln _ hlo cl hwl ch hwh ih => exact Ev_ln ih hlo cl hwl ch hwh
  | sqrt _ _ hSL hSL2 hSH hSH2 ih => exact Ev_sqrt ih hSL hSL2 hSH hSH2

/-- The kernel's derivative reading: the quotient rule `(Du·V − U·Dv) / (V·V)`, each product at its corners,
`V·V` read as an independent product (which is what bounds `v(p)·v(p')`). -/
inductive DRead (B : Box QExpr) (i : Nat) : G → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l qzero → qle qzero h → DRead B i (.const c) l h
  | self {l h : QExpr} : qle l qone → qle qone h → DRead B i (.var i) l h
  | other {j : Nat} {l h : QExpr} : j ≠ i → qle l qzero → qle qzero h → DRead B i (.var j) l h
  | add {u v : G} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → DRead B i (.add u v) l h
  | sub {u v : G} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → DRead B i (.sub u v) l h
  | mul {u v : G} {lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h : QExpr} :
      VRead B u lu hu → VRead B v lv hv → DRead B i u du1 du2 → DRead B i v dv1 dv2 →
      Corners m1 M1 lu hu dv1 dv2 → Corners m2 M2 lv hv du1 du2 →
      qle l (qadd m1 m2) → qle (qadd M1 M2) h → DRead B i (.mul u v) l h
  | div {u v : G} {lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 n1 n2 w1 w2 r1 r2 l h : QExpr} :
      VRead B u lu hu → VRead B v lv hv → DRead B i u du1 du2 → DRead B i v dv1 dv2 →
      Corners m1 M1 du1 du2 lv hv → Corners m2 M2 lu hu dv1 dv2 →
      qle n1 (qsub m1 M2) → qle (qsub M1 m2) n2 →
      Corners w1 w2 lv hv lv hv → RecipOK r1 r2 w1 w2 → Corners l h n1 n2 r1 r2 → DRead B i (.div u v) l h
  | exp {u : G} {lu hu El Eh du1 du2 m M l h : QExpr} :
      VRead B u lu hu → (∃ z, ExpCert lu El z) → (∃ z, ExpCert hu z Eh) → DRead B i u du1 du2 →
      Corners m M El Eh du1 du2 → qle l m → qle M h → DRead B i (.exp u) l h
  | ln {u : G} {lu hu Li Hi du1 du2 m M l h : QExpr} :
      VRead B u lu hu → qlt qzero lu → RecipOK Li Hi lu hu → DRead B i u du1 du2 →
      Corners m M Li Hi du1 du2 → qle l m → qle M h → DRead B i (.ln u) l h
  | sqrt {u : G} {lu hu SL SH w1 w2 r1 r2 du1 du2 m M l h : QExpr} :
      VRead B u lu hu → qle qzero lu → qle qzero SL → qle (sq SL) lu → qle qzero SH → qle hu (sq SH) →
      qle w1 (qadd SL SL) → qle (qadd SH SH) w2 → RecipOK r1 r2 w1 w2 → DRead B i u du1 du2 →
      Corners m M du1 du2 r1 r2 → qle l m → qle M h → DRead B i (.sqrt u) l h

/-- The quotient's difference, exactly: `u'/v' − u/v = (Δu·v − u·Δv)·(1/v)(1/v')`, `v, v' ≠ 0`. -/
theorem quot_diff {u v u' v' : QExpr} (hv : ¬ qEq v qzero) (hv' : ¬ qEq v' qzero) :
    qEq (qsub (qmul u' (qinv' v')) (qmul u (qinv' v)))
      (qmul (qsub (qmul (qsub u' u) v) (qmul u (qsub v' v))) (qinv' (qmul v v'))) := by
  have c := qmul_inv'_cancel hv
  have c' := qmul_inv'_cancel hv'
  have m := qinv'_mul hv hv'
  have e1 : qEq (qmul (qsub (qmul (qsub u' u) v) (qmul u (qsub v' v))) (qmul (qinv' v) (qinv' v')))
      (qsub (qmul (qmul u' (qmul v (qinv' v))) (qinv' v')) (qmul (qmul u (qmul v' (qinv' v'))) (qinv' v))) := by
    unfold qsub; rat_ring
  have e2 := qmul_respects (qmul_respects (qEq_refl u') c) (qEq_refl (qinv' v'))
  have e3 := qmul_respects (qmul_respects (qEq_refl u) c') (qEq_refl (qinv' v))
  have e4 : qEq (qmul (qmul u' qone) (qinv' v')) (qmul u' (qinv' v')) := by rat_ring
  have e5 : qEq (qmul (qmul u qone) (qinv' v)) (qmul u (qinv' v)) := by rat_ring
  have e6 := qmul_respects (qEq_refl (qsub (qmul (qsub u' u) v) (qmul u (qsub v' v)))) m
  unfold qsub at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem slope_sound {B : Box QExpr} {i : Nat} {p p' : Point QExpr} (hp : InBox qOrd B p)
    (hp' : InBox qOrd B p') (hfix : ∀ j, j ≠ i → p' j = p j) (hd : qle qzero (qsub (p' i) (p i))) :
    ∀ {e : G} {l h : QExpr}, DRead B i e l h →
      Ev (fun n => qsub (evalN n p' e) (evalN n p e)) (qmul l (qsub (p' i) (p i))) (qmul h (qsub (p' i) (p i))) := by
  intro e l h r
  induction r with
  | @const c l h hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub c c) qzero := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub c c); rat_linarith, by show qle (qsub c c) _; rat_linarith⟩)
  | @self l h hl hh =>
      have f1 : qle qzero (qmul (qsub qone l) (qsub (p' i) (p i))) := qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e1 : qEq (qmul (qsub qone l) (qsub (p' i) (p i)))
          (qadd (qsub (p' i) (p i)) (qneg (qmul l (qsub (p' i) (p i))))) := by unfold qsub; rat_ring
      have f2 : qle qzero (qmul (qsub h qone) (qsub (p' i) (p i))) := qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e2 : qEq (qmul (qsub h qone) (qsub (p' i) (p i)))
          (qadd (qmul h (qsub (p' i) (p i))) (qneg (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub (p' i) (p i)); rat_linarith,
                                       by show qle (qsub (p' i) (p i)) _; rat_linarith⟩)
  | @other j l h hj hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub (p j) (p j)) qzero := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => by
        show qle _ (qsub (p' j) (p j)) ∧ qle (qsub (p' j) (p j)) _
        rw [hfix j hj]; exact ⟨by rat_linarith, by rat_linarith⟩)
  | @add u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd l1 l2) (qsub (p' i) (p i)))
          (qadd (qmul l1 (qsub (p' i) (p i))) (qmul l2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd h1 h2) (qsub (p' i) (p i)))
          (qadd (qmul h1 (qsub (p' i) (p i))) (qmul h2 (qsub (p' i) (p i)))) := by rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_add ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qadd (evalN n p' u) (evalN n p' v)) (qadd (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @sub u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qsub l1 h2) (qsub (p' i) (p i)))
          (qsub (qmul l1 (qsub (p' i) (p i))) (qmul h2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      have r2 : qEq (qmul (qsub h1 l2) (qsub (p' i) (p i)))
          (qsub (qmul h1 (qsub (p' i) (p i))) (qmul l2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_sub ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qsub (evalN n p' u) (evalN n p' v)) (qsub (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @mul u v lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h ru rv _ _ c1 c2 hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd m1 m2) (qsub (p' i) (p i)))
          (qadd (qmul m1 (qsub (p' i) (p i))) (qmul m2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd M1 M2) (qsub (p' i) (p i)))
          (qadd (qmul M1 (qsub (p' i) (p i))) (qmul M2 (qsub (p' i) (p i)))) := by rat_ring
      have A := Ev_mul (value_sound hp' ru) ih2 (corners_scale c1 hd)
      have Bv := Ev_mul (value_sound hp rv) ih1 (corners_scale c2 hd)
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_add A Bv)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qmul (evalN n p' u) (evalN n p' v)) (qmul (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @div u v lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 n1 n2 w1 w2 r1 r2 l h ru rv _ _ c1 c2 hn1 hn2 cw hR cq ih1 ih2 =>
      have d := qsub (p' i) (p i)
      -- numerator Δu·v − u·Δv in [n1·d, n2·d]
      have A := Ev_mul ih1 (value_sound hp rv) (corners_scale_left c1 hd)
      have Bu := Ev_mul (value_sound hp ru) ih2 (corners_scale c2 hd)
      have s1 := ZExp.scale hn1 hd
      have s2 := ZExp.scale hn2 hd
      have t1 : qEq (qmul (qsub m1 M2) (qsub (p' i) (p i)))
          (qsub (qmul m1 (qsub (p' i) (p i))) (qmul M2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      have t2 : qEq (qmul (qsub M1 m2) (qsub (p' i) (p i)))
          (qsub (qmul M1 (qsub (p' i) (p i))) (qmul m2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      have Num := Ev_widen (Ev_sub A Bu) (l' := qmul n1 (qsub (p' i) (p i))) (h' := qmul n2 (qsub (p' i) (p i)))
        (by rat_linarith) (by rat_linarith)
      -- the denominator's reciprocal 1/(v·v') in [r1, r2]
      have W := Ev_mul (value_sound hp rv) (value_sound hp' rv) cw
      have Wr := Ev_recip W hR
      have Q := Ev_mul Num Wr (corners_scale_left cq hd)
      -- eventually v, v' ≠ 0 (their product is near W, clear of zero): the exact identity
      obtain ⟨J, hJ⟩ := recip_near hR 0
      obtain ⟨N, hN⟩ := W J
      refine Ev_congr_ev N (fun n hn => ?_) Q
      obtain ⟨a, b⟩ := hN n hn
      obtain ⟨hz, _, _⟩ := hJ _ a b
      have hz' : ¬ qEq (qmul (evalN n p v) (evalN n p' v)) qzero := hz
      have nv : ¬ qEq (evalN n p v) qzero := fun e => hz' (by
        have := qmul_respects e (qEq_refl (evalN n p' v)); have z := qzero_mul (evalN n p' v)
        exact qle_antisymm (by rat_linarith) (by rat_linarith))
      have nv' : ¬ qEq (evalN n p' v) qzero := fun e => hz' (by
        have := qmul_respects (qEq_refl (evalN n p v)) e; have z := qmul_zero (evalN n p v)
        exact qle_antisymm (by rat_linarith) (by rat_linarith))
      exact qEq_symm (quot_diff (u := evalN n p u) (u' := evalN n p' u) nv nv')
  | @exp u lu hu El Eh du1 du2 m M l h ru cl ch _ hc hl hh ih =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      exact Ev_widen (Ev_exp_slope (value_sound hp ru) (value_sound hp' ru)
        (Ev_exp (value_sound hp ru) cl ch) (Ev_exp (value_sound hp' ru) cl ch) ih (corners_scale hc hd)) s1 s2
  | @ln u lu hu Li Hi du1 du2 m M l h ru hlo hR _ hc hl hh ih =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      exact Ev_widen (Ev_ln_slope (value_sound hp ru) (value_sound hp' ru) hlo hR ih (corners_scale hc hd)) s1 s2
  | @sqrt u lu hu SL SH w1 w2 r1 r2 du1 du2 m M l h ru hlo hSL hSL2 hSH hSH2 hw1 hw2 hR _ hc hl hh ih =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      exact Ev_widen (Ev_sqrt_slope (value_sound hp ru) (value_sound hp' ru) hlo hSL hSL2 hSH hSH2 hw1 hw2 hR ih
        (corners_scale_left hc hd)) s1 s2

/-! ## The value is an operational real wherever a value reading covers the point -/

/-- A value reading over a box makes the value at each of its points an operational real (the denominators are
clear of zero, the `exp` arguments bounded). -/
theorem evalN_cauchy {B : Box QExpr} {p : Point QExpr} (hp : InBox qOrd B p) :
    ∀ {e : G} {l h : QExpr}, VRead B e l h → Cauchy (fun n => evalN n p e) := by
  intro e l h r
  induction r with
  | const _ _ => exact fun k => ⟨0, fun _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩
  | var _ _ => exact fun k => ⟨0, fun _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩
  | add _ _ _ _ ih1 ih2 => exact (radd ⟨_, ih1⟩ ⟨_, ih2⟩).cauchy
  | sub _ _ _ _ ih1 ih2 => exact (radd ⟨_, ih1⟩ (rneg ⟨_, ih2⟩)).cauchy
  | mul _ _ _ ih1 ih2 => exact (rmul ⟨_, ih1⟩ ⟨_, ih2⟩).cauchy
  | div _ rv hR _ ih1 ih2 => exact (rmul ⟨_, ih1⟩ ⟨_, recip_cauchy ih2 (value_sound hp rv) hR⟩).cauchy
  | exp _ _ _ ih => exact rexpR_cauchy ⟨_, ih⟩
  | ln ru hlo _ _ _ _ ih => exact ln_cauchy ih (value_sound hp ru) hlo
  | sqrt ru hlo _ _ _ _ ih => exact sqrt_cauchy ih (value_sound hp ru) hlo

/-- The value at `p`, given a value reading over a box containing `p`. -/
def valR {B : Box QExpr} {p : Point QExpr} {e : G} {l h : QExpr} (hp : InBox qOrd B p) (r : VRead B e l h) : RExpr :=
  ⟨fun n => evalN n p e, evalN_cauchy hp r⟩

/-! ## Monotone, and the certificate rule -/

/-- `x ≤ y` for sequences, to every precision from some index on — `rle`'s own shape. -/
def SLe (x y : Nat → QExpr) : Prop := ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub (x n) (y n)) (qeps k)

theorem SLe_refl (x : Nat → QExpr) : SLe x x := fun k => ⟨0, fun n _ => by
  have := qeps_nonneg k; unfold qsub; have := qadd_neg (x n); rat_linarith⟩

theorem SLe_trans {x y z : Nat → QExpr} (h1 : SLe x y) (h2 : SLe y z) : SLe x z := fun k => by
  obtain ⟨N1, a⟩ := h1 (k + 1)
  obtain ⟨N2, b⟩ := h2 (k + 1)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have u := a n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  have v := b n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  have := qeps_succ_add k
  unfold qsub at *; rat_linarith

theorem mono_up {B : Box QExpr} {i : Nat} {e : G} {l h : QExpr} (r : DRead B i e l h) (hl : qle qzero l) :
    ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun n => evalN n (upd p i (endOf B true i)) e) := by
  intro p hp k
  have hp' := upd_end_inbox qOrd i true hp
  have hu : upd p i (endOf B true i) i = (B i).2 := upd_self p i _
  have hd : qle qzero (qsub (upd p i (endOf B true i) i) (p i)) := by
    have h2 : qle (p i) (B i).2 := (hp i).2
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨N, hN⟩ := slope_sound hp hp' (upd_other p i _) hd r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s0, _⟩ := hN n hn
  have s : qle (qsub (qmul l (qsub (upd p i (endOf B true i) i) (p i))) (qeps k))
      (qsub (evalN n (upd p i (endOf B true i)) e) (evalN n p e)) := s0
  have f := qmul_nonneg hl hd
  show qle (qsub (evalN n p e) (evalN n (upd p i (endOf B true i)) e)) (qeps k)
  unfold qsub at *
  rat_linarith

theorem mono_down {B : Box QExpr} {i : Nat} {e : G} {l h : QExpr} (r : DRead B i e l h) (hh : qle h qzero) :
    ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun n => evalN n (upd p i (endOf B false i)) e) := by
  intro p hp k
  have hp' := upd_end_inbox qOrd i false hp
  have hu : upd p i (endOf B false i) i = (B i).1 := upd_self p i _
  have hfix : ∀ j, j ≠ i → p j = upd p i (endOf B false i) j := fun j hj => (upd_other p i _ j hj).symm
  have hd : qle qzero (qsub (p i) (upd p i (endOf B false i) i)) := by
    have h1 : qle (B i).1 (p i) := (hp i).1
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨N, hN⟩ := slope_sound hp' hp hfix hd r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, s0⟩ := hN n hn
  have s : qle (qsub (evalN n p e) (evalN n (upd p i (endOf B false i)) e))
      (qadd (qmul h (qsub (p i) (upd p i (endOf B false i) i))) (qeps k)) := s0
  have f : qle qzero (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i))) := qmul_nonneg (by rat_linarith) hd
  have e1 : qEq (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i)))
      (qneg (qmul h (qsub (p i) (upd p i (endOf B false i) i)))) := by rat_ring
  show qle (qsub (evalN n p e) (evalN n (upd p i (endOf B false i)) e)) (qeps k)
  unfold qsub at *
  rat_linarith

def Uses : G → Nat → Prop
  | .const _, _ => False
  | .var i, j => j = i
  | .add u v, j => Uses u j ∨ Uses v j
  | .sub u v, j => Uses u j ∨ Uses v j
  | .mul u v, j => Uses u j ∨ Uses v j
  | .div u v, j => Uses u j ∨ Uses v j
  | .exp u, j => Uses u j
  | .ln u, j => Uses u j
  | .sqrt u, j => Uses u j

theorem evalN_dep (n : Nat) (p q : Point QExpr) : ∀ e : G, (∀ j, Uses e j → p j = q j) → evalN n p e = evalN n q e
  | .const _, _ => rfl
  | .var i, h => h i rfl
  | .add u v, h => by
      show qadd _ _ = qadd _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .sub u v, h => by
      show qsub _ _ = qsub _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .mul u v, h => by
      show qmul _ _ = qmul _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .div u v, h => by
      show qmul _ (qinv' _) = qmul _ (qinv' _)
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .exp u, h => by
      show eseq _ n = eseq _ n
      rw [evalN_dep n p q u h]
  | .ln u, h => by
      show lnseq _ n = lnseq _ n
      rw [evalN_dep n p q u h]
  | .sqrt u, h => by
      show rsqrt _ n = rsqrt _ n
      rw [evalN_dep n p q u h]

theorem corner_bound_S (e : G) (B : Box QExpr) (sg : Nat → Bool) :
    ∀ (ns : List Nat), (∀ i, List.Mem i ns → ∀ p, InBox qOrd B p →
        SLe (fun n => evalN n p e) (fun n => evalN n (upd p i (endOf B (sg i) i)) e)) →
      ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun n => evalN n (cornerOn B sg ns p) e) := by
  intro ns
  induction ns with
  | nil => intro _ p _; exact SLe_refl _
  | cons i ns ih =>
      intro hm p hp
      exact SLe_trans (hm i (List.Mem.head ns) p hp)
        (ih (fun j hj => hm j (List.Mem.tail i hj)) _ (upd_end_inbox qOrd i (sg i) hp))

def IvOK (e : G) (c : QExpr) (B : Box QExpr) : Prop := ∃ l h, VRead B e l h ∧ qle h c

def DerivOK (e : G) (B : Box QExpr) (i : Nat) : Bool → Prop
  | true => ∃ l h, DRead B i e l h ∧ qle qzero l
  | false => ∃ l h, DRead B i e l h ∧ qle h qzero

def LeafOK (e : G) (ns : List Nat) (c : QExpr) : Box QExpr → Leaf → Prop
  | B, .interval => IvOK e c B
  | B, .monotone sg => (∀ i, List.Mem i ns → DerivOK e B i (sg i)) ∧ IvOK e c (cornerBox B sg)

theorem iv_le {B : Box QExpr} {e : G} {c : QExpr} (h : IvOK e c B) :
    ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun _ => c) := by
  intro p hp k
  obtain ⟨l, h', r, hc⟩ := h
  obtain ⟨N, hN⟩ := value_sound hp r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, b⟩ := hN n hn
  show qle (qsub (evalN n p e) c) (qeps k)
  unfold qsub; rat_linarith

/-- THE CERTIFICATE RULE IS SOUND FOR `+ − × / exp`, premise-free, on VR's operational reals: an accepted
certificate shows that at every point of the box the value's approximants are eventually below `c` to every
precision; wherever a value reading covers the point (`valR`), that is `rle` of an operational real
(`certificate_sound_R`). -/
theorem certificate_sound (e : G) (ns : List Nat) (c : QExpr) (hns : ∀ j, Uses e j → List.Mem j ns) :
    ∀ (t : Tree QExpr Leaf) (B : Box QExpr), Accepts (LeafOK e ns c) B t →
      ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun _ => c) := by
  apply accepts_sound qOrd (LeafOK e ns c) (fun p => SLe (fun n => evalN n p e) (fun _ => c))
  intro B lf hok p hp
  cases lf with
  | interval => exact iv_le hok p hp
  | monotone sg =>
      obtain ⟨hd, hcorner⟩ := hok
      have step := corner_bound_S e B sg ns (fun i hi => by
        have := hd i hi
        cases hs : sg i with
        | true => rw [hs] at this; obtain ⟨_, _, r, hl⟩ := this; rw [← hs]; exact hs ▸ mono_up r hl
        | false => rw [hs] at this; obtain ⟨_, _, r, hh⟩ := this; rw [← hs]; exact hs ▸ mono_down r hh) p hp
      have same : SLe (fun n => evalN n (cornerOn B sg ns p) e) (fun n => evalN n (corner B sg) e) := by
        intro k; refine ⟨0, fun n _ => ?_⟩
        show qle (qsub (evalN n (cornerOn B sg ns p) e) (evalN n (corner B sg) e)) (qeps k)
        rw [evalN_dep n _ _ e (fun j hj => cornerOn_agrees B sg ns p j (hns j hj))]
        have := qeps_nonneg k; unfold qsub; have := qadd_neg (evalN n (corner B sg) e); rat_linarith
      have atc : InBox qOrd (cornerBox B sg) (corner B sg) := fun j => ⟨qle_refl _, qle_refl _⟩
      exact SLe_trans step (SLe_trans same (iv_le hcorner _ atc))

/-- The same as the real order, at a point some value reading covers. -/
theorem certificate_sound_R (e : G) (ns : List Nat) (c : QExpr) (hns : ∀ j, Uses e j → List.Mem j ns)
    (t : Tree QExpr Leaf) (B : Box QExpr) (hacc : Accepts (LeafOK e ns c) B t) (p : Point QExpr)
    (hp : InBox qOrd B p) {B' : Box QExpr} {l h : QExpr} (hp' : InBox qOrd B' p) (r : VRead B' e l h) :
    rle (valR hp' r) (rofQ c) :=
  certificate_sound e ns c hns t B hacc p hp

/-- Nonvacuity: `1/x` on `[1, 2]` falls. The kernel's quotient reading: `Du·V = [0, 0]`, `U·Dv = [1, 1]`,
numerator `[−1, −1]`, `V·V = [1, 4]`, its reciprocal read `[0, 1]`, the derivative `[−1, 0]` — non-positive. -/
example : ∀ p, InBox qOrd (fun _ => (qone, qnat 2)) p →
    SLe (fun n => evalN n p (.div (.const qone) (.var 0)))
        (fun n => evalN n (upd p 0 (endOf (fun _ => (qone, qnat 2)) false 0)) (.div (.const qone) (.var 0))) :=
  mono_down (l := qneg qone) (h := qzero)
    (DRead.div (lu := qone) (hu := qone) (lv := qone) (hv := qnat 2) (du1 := qzero) (du2 := qzero)
      (dv1 := qone) (dv2 := qone) (m1 := qzero) (M1 := qzero) (m2 := qone) (M2 := qone)
      (n1 := qneg qone) (n2 := qneg qone) (w1 := qone) (w2 := qnat 4) (r1 := qzero) (r2 := qone)
      (VRead.const (by decide) (by decide)) (VRead.var (by decide) (by decide))
      (DRead.const (by decide) (by decide)) (DRead.self (by decide) (by decide))
      (by unfold Corners; decide) (by unfold Corners; decide) (by decide) (by decide)
      (by unfold Corners; decide) (by unfold RecipOK; decide) (by unfold Corners; decide))
    (by decide)

set_option maxRecDepth 200000 in
/-- Nonvacuity: `ln x` on `[1, 2]` rises. Value `[0, 1]` (`exp 0 ≤ 1`, `exp 1 ≥ 2`, certified), the reciprocal of
`[1, 2]` read `[0, 1]`, the derivative `[0, 1]·[1, 1]` — non-negative. -/
example : ∀ p, InBox qOrd (fun _ => (qone, qnat 2)) p →
    SLe (fun n => evalN n p (.ln (.var 0)))
        (fun n => evalN n (upd p 0 (endOf (fun _ => (qone, qnat 2)) true 0)) (.ln (.var 0))) :=
  mono_up (l := qzero) (h := qone)
    (DRead.ln (lu := qone) (hu := qnat 2) (Li := qzero) (Hi := qone) (du1 := qone) (du2 := qone)
      (m := qzero) (M := qone)
      (VRead.var (by decide) (by decide)) (by decide) (by unfold RecipOK; decide)
      (DRead.self (by decide) (by decide)) (by unfold Corners; decide) (by decide) (by decide))
    (by decide)

set_option maxRecDepth 200000 in
/-- The value reading of `ln x` on `[1, 2]`: `[0, 1]`, its ends certified through `exp`. -/
example : VRead (fun _ => (qone, qnat 2)) (.ln (.var 0)) qzero qone :=
  VRead.ln (lu := qone) (hu := qnat 2) (zl := qone) (wl := qone) (wh := qnat 2) (zh := qnat 3) (VRead.var (by decide) (by decide)) (by decide)
    (Or.inl ⟨by decide, 1, by unfold Good; decide, by decide, by decide⟩) (by decide)
    (Or.inl ⟨by decide, 3, by unfold Good; decide, by decide, by decide⟩) (by decide)

/-- Nonvacuity: `√x` on `[1, 4]` reads `[1, 2]` (`1² ≤ 1`, `4 ≤ 2²`). -/
example : VRead (fun _ => (qone, qnat 4)) (.sqrt (.var 0)) qone (qnat 2) :=
  VRead.sqrt (lu := qone) (hu := qnat 4) (VRead.var (by decide) (by decide)) (by decide)
    (by decide) (by unfold sq; decide) (by decide) (by unfold sq; decide)

/-- Nonvacuity: `√x` on `[1, 4]` rises. `2·√U` read `[2, 4]`, its reciprocal `[0, 1]`, the derivative
`[1, 1]·[0, 1] = [0, 1]` — non-negative. -/
example : ∀ p, InBox qOrd (fun _ => (qone, qnat 4)) p →
    SLe (fun n => evalN n p (.sqrt (.var 0)))
        (fun n => evalN n (upd p 0 (endOf (fun _ => (qone, qnat 4)) true 0)) (.sqrt (.var 0))) :=
  mono_up (l := qzero) (h := qone)
    (DRead.sqrt (lu := qone) (hu := qnat 4) (SL := qone) (SH := qnat 2) (w1 := qnat 2) (w2 := qnat 4)
      (r1 := qzero) (r2 := qone) (du1 := qone) (du2 := qone) (m := qzero) (M := qone)
      (VRead.var (by decide) (by decide)) (by decide) (by decide) (by unfold sq; decide) (by decide)
      (by unfold sq; decide) (by decide) (by decide) (by unfold RecipOK; decide)
      (DRead.self (by decide) (by decide)) (by unfold Corners; decide) (by decide) (by decide))
    (by decide)

end ZSlopeSqrt

#print axioms ZSlopeSqrt.value_sound
#print axioms ZSlopeSqrt.quot_diff
#print axioms ZSlopeSqrt.slope_sound
#print axioms ZSlopeSqrt.evalN_cauchy
#print axioms ZSlopeSqrt.mono_up
#print axioms ZSlopeSqrt.mono_down
#print axioms ZSlopeSqrt.certificate_sound
#print axioms ZSlopeSqrt.certificate_sound_R
