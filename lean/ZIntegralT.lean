import ZTaylor2
import ZIntegralR

/-!
# ZIntegralT — the Taylor leaf of order 2 (the midpoint rule), on VR's operational reals. Zero axioms.

`zintegral.py`'s leaf `{"taylor": 2}` on a piece `[m − h, m + h]` encloses the integral by
`L = 2h·C0lo + 2·C2lo·h³/3`, `U = 2h·C0hi + 2·C2hi·h³/3`: `C0` the kernel's value reading at the midpoint, `C2` its
reading of `f''/2` over the piece. Its claim is about the LIMIT of Riemann sums (a coarse sum can leave `[L, U]`), so
the theorem carries the mesh:

  * `taylor2_leaf` — every SYMMETRIC tagged sum `Σ (b − a)·(f(m + s) + f(m − s))` over a refinement of `[0, h]` with
    mesh `μ` lies, to every precision `ε_k` from some index on, in `[L − 2Kμh² − 3h·ε_k, U + 2Kμh² + 3h·ε_k]`
    (`K ≥ |C2|`). As `μ → 0` that is `[L, U]`.

The proof: the sum is `2h·f(m) + Σ (b − a)·sd` (`sd` the symmetric second difference, `ZTaylor2.sd_sound`: in
`2s²·[C2]`), and `Σ (b − a)·s²` is within `μh²` of `h³/3` (`cube_sum`: per cell `3(b − a)s² − (b³ − a³)` lies within
`±3μ(b² − a²)`, which telescopes) — rational algebra, no limit taken inside.

NOT covered, said rather than hidden: tagged sums that are not symmetric about `m` (for a Lipschitz integrand —
which the first-order reading certifies — every Riemann sum shares the limit; that transfer is classical and not
proved here); orders above 2 (`zintegral.py` also uses 4, 6, …); the grammar beyond `const var + − × exp` for the
second coefficient (`ZTaylor2`: `/`, `sqrt`, `ln` not yet).
-/

namespace ZIntegralT

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZTaylor2 ZIntegralR

/-- A cell of a refinement of `[0, h]`: `(a, b, s)`, its ends and its tag. -/
abbrev Cell := QExpr × QExpr × QExpr

/-- The cells run from `x` to `y`, each starting where the last ended. -/
def Chain : QExpr → QExpr → List Cell → Prop
  | x, y, [] => qEq x y
  | x, y, (a, b, _) :: cs => qEq a x ∧ Chain b y cs

/-- A cell `0 ≤ a ≤ s ≤ b`, `b − a ≤ μ`. -/
def CellOK (μ : QExpr) (c : Cell) : Prop :=
  qle qzero c.1 ∧ qle c.1 c.2.2 ∧ qle c.2.2 c.2.1 ∧ qle (qsub c.2.1 c.1) μ

/-- `Σ (b − a)·g(cell)`. -/
def csum (g : Cell → QExpr) : List Cell → QExpr
  | [] => qzero
  | c :: cs => qadd (qmul (qsub c.2.1 c.1) (g c)) (csum g cs)

def three : QExpr := qadd (qadd qone qone) qone
def cube (x : QExpr) : QExpr := qmul x (sq x)

/-! ## Sums over the cells -/

theorem csum_mono {g g' : Cell → QExpr} :
    ∀ cs : List Cell, (∀ c, List.Mem c cs → qle c.1 c.2.1 ∧ qle (g c) (g' c)) → qle (csum g cs) (csum g' cs)
  | [], _ => qle_refl _
  | c :: cs, h => by
      have hc := h c (List.Mem.head cs)
      have ih := csum_mono cs (fun z hz => h z (List.Mem.tail c hz))
      have f := scale_l hc.2 (by unfold qsub; have := hc.1; rat_linarith : qle qzero (qsub c.2.1 c.1))
      show qle (qadd (qmul (qsub c.2.1 c.1) (g c)) (csum g cs)) (qadd (qmul (qsub c.2.1 c.1) (g' c)) (csum g' cs))
      rat_linarith

theorem csum_congr {g g' : Cell → QExpr} :
    ∀ cs : List Cell, (∀ c, List.Mem c cs → qEq (g c) (g' c)) → qEq (csum g cs) (csum g' cs)
  | [], _ => qEq_refl _
  | c :: cs, h => qadd_respects (qmul_respects (qEq_refl _) (h c (List.Mem.head cs)))
      (csum_congr cs (fun z hz => h z (List.Mem.tail c hz)))

/-- `Σ w·(g + g') = Σ w·g + Σ w·g'`. -/
theorem csum_add (g g' : Cell → QExpr) :
    ∀ cs : List Cell, qEq (csum (fun c => qadd (g c) (g' c)) cs) (qadd (csum g cs) (csum g' cs))
  | [] => by show qEq qzero (qadd qzero qzero); rat_ring
  | c :: cs => by
      have ih := csum_add g g' cs
      show qEq (qadd (qmul (qsub c.2.1 c.1) (qadd (g c) (g' c))) (csum (fun c => qadd (g c) (g' c)) cs))
        (qadd (qadd (qmul (qsub c.2.1 c.1) (g c)) (csum g cs)) (qadd (qmul (qsub c.2.1 c.1) (g' c)) (csum g' cs)))
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (by unfold qsub; rat_ring)

/-- `Σ w·(k·g) = k·Σ w·g`. -/
theorem csum_scale (k : QExpr) (g : Cell → QExpr) :
    ∀ cs : List Cell, qEq (csum (fun c => qmul k (g c)) cs) (qmul k (csum g cs))
  | [] => by show qEq qzero (qmul k qzero); rat_ring
  | c :: cs => by
      have ih := csum_scale k g cs
      show qEq (qadd (qmul (qsub c.2.1 c.1) (qmul k (g c))) (csum (fun c => qmul k (g c)) cs))
        (qmul k (qadd (qmul (qsub c.2.1 c.1) (g c)) (csum g cs)))
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (by unfold qsub; rat_ring)

/-- The total width runs `x` to `y`. -/
theorem width_chain : ∀ (cs : List Cell) (x y : QExpr), Chain x y cs → qEq (csum (fun _ => qone) cs) (qsub y x)
  | [], x, y, h => by
      show qEq qzero (qsub y x)
      have hh : qEq x y := h
      unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | (a, b, s) :: cs, x, y, h => by
      have ih := width_chain cs b y h.2
      have ha := h.1
      show qEq (qadd (qmul (qsub b a) qone) (csum (fun _ => qone) cs)) (qsub y x)
      have e := qmul_one (qsub b a)
      unfold qsub at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- Every cell lies in `[x, y]`. -/
theorem cells_within {μ : QExpr} : ∀ (cs : List Cell) (x y : QExpr), Chain x y cs → (∀ c, List.Mem c cs → CellOK μ c) →
    qle x y ∧ ∀ c, List.Mem c cs → qle x c.1 ∧ qle c.2.1 y
  | [], x, y, h, _ => ⟨qle_of_qEq h, fun c hc => by cases hc⟩
  | (a, b, s) :: cs, x, y, h, hok => by
      have hc := hok (a, b, s) (List.Mem.head cs)
      obtain ⟨hby, ih⟩ := cells_within cs b y h.2 (fun z hz => hok z (List.Mem.tail _ hz))
      have ha := h.1
      have hab : qle a b := qle_trans hc.2.1 hc.2.2.1
      refine ⟨by rat_linarith, fun c hm => ?_⟩
      cases hm with
      | head => exact ⟨by rat_linarith, hby⟩
      | tail _ hm => obtain ⟨u, v⟩ := ih c hm; exact ⟨by rat_linarith, v⟩

/-! ## `Σ (b − a)·s²` is within `μ·h²` of `h³/3` -/

/-- One cell: `3(b − a)s² − (b³ − a³)` lies within `±3μ(b² − a²)`. -/
theorem cell_err {a b s μ : QExpr} (h0 : qle qzero a) (has : qle a s) (hsb : qle s b) (hw : qle (qsub b a) μ) :
    qle (qneg (qmul (qmul three μ) (qsub (sq b) (sq a)))) (qsub (qmul three (qmul (qsub b a) (sq s))) (qsub (cube b) (cube a)))
    ∧ qle (qsub (qmul three (qmul (qsub b a) (sq s))) (qsub (cube b) (cube a))) (qmul (qmul three μ) (qsub (sq b) (sq a))) := by
  have hab : qle a b := qle_trans has hsb
  have w0 : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  have μ0 : qle qzero μ := qle_trans w0 hw
  have s0 : qle qzero s := qle_trans h0 has
  have q1 := sq_mono h0 has
  have q2 := sq_mono s0 hsb
  -- w·s² between w·a² and w·b²
  have m1 := scale_l q1 w0
  have m2 := scale_l q2 w0
  -- w·w ≤ μ·w, times (2b + a) ≥ 0 and (2a + b) ≥ 0
  have ww := ZExp.scale hw w0
  have g1 : qle qzero (qadd (qadd b b) a) := by rat_linarith
  have g2 : qle qzero (qadd (qadd a a) b) := by rat_linarith
  have n1 := ZExp.scale ww g1
  have n2 := ZExp.scale ww g2
  -- μ·w·(2b + a) ≤ μ·w·3(a + b), μ·w·(2a + b) ≤ μ·w·3(a + b)
  have μw : qle qzero (qmul μ (qsub b a)) := qmul_nonneg μ0 w0
  have k1 := scale_l (by unfold three; rat_linarith : qle (qadd (qadd b b) a) (qmul three (qadd a b))) μw
  have k2 := scale_l (by unfold three; rat_linarith : qle (qadd (qadd a a) b) (qmul three (qadd a b))) μw
  unfold three cube sq qsub at *
  constructor <;> rat_linarith

/-- The cells from `x ≥ 0` to `y`: `3·Σ (b − a)s²` lies within `±3μ(y² − x²)` of `y³ − x³`. -/
theorem cube_sum {μ : QExpr} : ∀ (cs : List Cell) (x y : QExpr), qle qzero x → Chain x y cs →
    (∀ c, List.Mem c cs → CellOK μ c) →
    qle (qneg (qmul (qmul three μ) (qsub (sq y) (sq x)))) (qsub (qmul three (csum (fun c => sq c.2.2) cs)) (qsub (cube y) (cube x)))
    ∧ qle (qsub (qmul three (csum (fun c => sq c.2.2) cs)) (qsub (cube y) (cube x))) (qmul (qmul three μ) (qsub (sq y) (sq x)))
  | [], x, y, _, h, _ => by
      have e1 := sq_respects h
      have e2 : qEq (cube x) (cube y) := qmul_respects h e1
      -- no cell: x = y, every side is 0
      have e3 : qEq (qmul (qmul three μ) (sq y)) (qmul (qmul three μ) (sq x)) := qmul_respects (qEq_refl _) (qEq_symm e1)
      show qle _ (qsub (qmul three qzero) (qsub (cube y) (cube x))) ∧ qle (qsub (qmul three qzero) (qsub (cube y) (cube x))) _
      unfold three cube sq qsub at *
      constructor <;> rat_linarith
  | (a, b, s) :: cs, x, y, hx, h, hok => by
      have hc := hok (a, b, s) (List.Mem.head cs)
      obtain ⟨c0, cas, csb, cw⟩ := hc
      have ha : qEq a x := h.1
      have hb0 : qle qzero b := qle_trans c0 (qle_trans cas csb)
      have ih := cube_sum cs b y hb0 h.2 (fun z hz => hok z (List.Mem.tail _ hz))
      have ce := cell_err c0 cas csb cw
      obtain ⟨i1, i2⟩ := ih
      obtain ⟨ce1, ce2⟩ := ce
      have e1 := sq_respects ha
      have e2 : qEq (cube a) (cube x) := qmul_respects ha e1
      have e3 : qEq (qmul μ (sq a)) (qmul μ (sq x)) := qmul_respects (qEq_refl μ) e1
      show qle _ (qsub (qmul three (qadd (qmul (qsub b a) (sq s)) (csum (fun c => sq c.2.2) cs))) (qsub (cube y) (cube x)))
        ∧ qle (qsub (qmul three (qadd (qmul (qsub b a) (sq s)) (csum (fun c => sq c.2.2) cs))) (qsub (cube y) (cube x))) _
      unfold three cube sq qsub at *
      constructor <;> rat_linarith

/-! ## The leaf -/

/-- The symmetric tagged sum at index `n`: `Σ (b − a)·(f(m + s) + f(m − s))`. -/
def ssum (n : Nat) (e : G) (p : Point QExpr) (i : Nat) (m : QExpr) (cs : List Cell) : QExpr :=
  csum (fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs

/-- The second difference at the tag `s` of a cell, eventually in `2s²·[l, u]`. -/
theorem cell_sd {e : G} {p : Point QExpr} {i : Nat} {m h l u s : QExpr} {B : Box QExpr}
    (hT : T2Read B i e l u) (hB : ∀ t, qle (qsub m h) t → qle t (qadd m h) → InBox qOrd B (upd p i t))
    (hs0 : qle qzero s) (hsh : qle s h) :
    Ev (fun n => sd n (upd p i m) (upd p i (qadd m s)) (upd p i (qsub m s)) e)
      (qmul l (two_sq s)) (qmul u (two_sq s)) := by
  have h0 : qle qzero h := qle_trans hs0 hsh
  have b0 := hB m (by unfold qsub; rat_linarith) (by rat_linarith)
  have bp := hB (qadd m s) (by unfold qsub; rat_linarith) (by rat_linarith)
  have bm := hB (qsub m s) (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
  have hs : qle qzero (qsub (upd p i (qadd m s) i) (upd p i m i)) := by
    rw [upd_self, upd_self]; unfold qsub; rat_linarith
  have hsym : qEq (qsub (upd p i m i) (upd p i (qsub m s) i)) (qsub (upd p i (qadd m s) i) (upd p i m i)) := by
    rw [upd_self, upd_self, upd_self]; unfold qsub; rat_ring
  have E := sd_sound b0 bp bm (upd_fix p i m (qadd m s)) (upd_fix p i (qsub m s) m) hs hsym hT
  rw [upd_self, upd_self] at E
  have q : qEq (two_sq (qsub (qadd m s) m)) (two_sq s) := by unfold two_sq qsub; rat_ring
  exact Ev_widen E (qle_of_qEq (qmul_respects (qEq_refl l) (qEq_symm q))) (qle_of_qEq (qmul_respects (qEq_refl u) q))

/-- THE TAYLOR LEAF OF ORDER 2. The kernel's value reading `[c0, C0]` at the midpoint `m`, its second-coefficient
reading `[l, u]` over the piece `[m − h, m + h]` (`|l|, |u| ≤ K`), a refinement of `[0, h]` with mesh `μ`, and
`t3 = h³/3`: every symmetric tagged sum lies, to every precision from some index on, in
`[2h·c0 + 2l·t3 − (2Kμh² + 3h·ε_k), 2h·C0 + 2u·t3 + (2Kμh² + 3h·ε_k)]`. -/
theorem taylor2_leaf {e : G} {p : Point QExpr} {i : Nat} {m h μ t3 K c0 C0 l u : QExpr} {B B0 : Box QExpr}
    {cs : List Cell}
    (hT : T2Read B i e l u) (hV : VRead B0 e c0 C0) (h0 : InBox qOrd B0 (upd p i m))
    (hB : ∀ t, qle (qsub m h) t → qle t (qadd m h) → InBox qOrd B (upd p i t))
    (hch : Chain qzero h cs) (hok : ∀ c, List.Mem c cs → CellOK μ c) (hμ : qle qzero μ)
    (ht3 : qEq (qmul three t3) (cube h)) (hK0 : qle qzero K)
    (hl1 : qle (qneg K) l) (hl2 : qle l K) (hu1 : qle (qneg K) u) (hu2 : qle u K) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qadd (qmul (qadd h h) c0) (qmul (qadd l l) t3))
              (qadd (qmul (qadd K K) (qmul μ (sq h))) (qmul (qmul three h) (qeps k))))
          (ssum n e p i m cs) ∧
      qle (ssum n e p i m cs)
          (qadd (qadd (qmul (qadd h h) C0) (qmul (qadd u u) t3))
              (qadd (qmul (qadd K K) (qmul μ (sq h))) (qmul (qmul three h) (qeps k)))) := by
  intro k
  obtain ⟨hh0, hin⟩ := cells_within cs qzero h hch hok
  have hcell : ∀ c, List.Mem c cs → ∃ N, ∀ n, N ≤ n →
      qle (qsub (qmul l (two_sq c.2.2)) (qeps k)) (sd n (upd p i m) (upd p i (qadd m c.2.2)) (upd p i (qsub m c.2.2)) e) ∧
      qle (sd n (upd p i m) (upd p i (qadd m c.2.2)) (upd p i (qsub m c.2.2)) e) (qadd (qmul u (two_sq c.2.2)) (qeps k)) := by
    intro c hc
    obtain ⟨c0', cas, csb, _⟩ := hok c hc
    obtain ⟨_, cb⟩ := hin c hc
    exact cell_sd hT hB (qle_trans c0' cas) (qle_trans csb cb) k
  obtain ⟨Nc, hNc⟩ := ev_list _ cs hcell
  obtain ⟨Nv, hNv⟩ := value_sound h0 hV k
  refine ⟨Nc + Nv, fun n hn => ?_⟩
  have cellb := hNc n (Nat.le_trans (Nat.le_add_right Nc Nv) hn)
  obtain ⟨v1, v2⟩ := hNv n (Nat.le_trans (Nat.le_add_left Nv Nc) hn)
  -- the sum is Σ w·sd + (f0 + f0)·Σ w
  have id1 : qEq (ssum n e p i m cs)
      (csum (fun c => qadd (sd n (upd p i m) (upd p i (qadd m c.2.2)) (upd p i (qsub m c.2.2)) e)
        (qadd (evalN n (upd p i m) e) (evalN n (upd p i m) e))) cs) :=
    csum_congr cs (fun c _ => by unfold sd qsub; rat_ring)
  have id2 := csum_add (fun c => sd n (upd p i m) (upd p i (qadd m c.2.2)) (upd p i (qsub m c.2.2)) e)
    (fun _ => qadd (evalN n (upd p i m) e) (evalN n (upd p i m) e)) cs
  have id3 : qEq (csum (fun _ => qadd (evalN n (upd p i m) e) (evalN n (upd p i m) e)) cs)
      (qmul (qadd (evalN n (upd p i m) e) (evalN n (upd p i m) e)) (csum (fun _ => qone) cs)) :=
    qEq_trans (csum_congr cs (fun c _ => qEq_symm (qmul_one _)))
      (csum_scale (qadd (evalN n (upd p i m) e) (evalN n (upd p i m) e)) (fun _ => qone) cs)
  have W := width_chain cs qzero h hch
  have Wh : qEq (csum (fun _ => qone) cs) h := qEq_trans W (by unfold qsub; rat_ring)
  have id4 := qmul_respects (qEq_refl (qadd (evalN n (upd p i m) e) (evalN n (upd p i m) e))) Wh
  -- Σ w·sd between Σ w·(l·2s² − ε) and Σ w·(u·2s² + ε)
  have lo1 := csum_mono (g := fun c => qsub (qmul l (two_sq c.2.2)) (qeps k))
    (g' := fun c => sd n (upd p i m) (upd p i (qadd m c.2.2)) (upd p i (qsub m c.2.2)) e) cs
    (fun c hc => ⟨qle_trans (hok c hc).2.1 (hok c hc).2.2.1, (cellb c hc).1⟩)
  have hi1 := csum_mono (g := fun c => sd n (upd p i m) (upd p i (qadd m c.2.2)) (upd p i (qsub m c.2.2)) e)
    (g' := fun c => qadd (qmul u (two_sq c.2.2)) (qeps k)) cs
    (fun c hc => ⟨qle_trans (hok c hc).2.1 (hok c hc).2.2.1, (cellb c hc).2⟩)
  -- Σ w·(l·2s² − ε) = (l + l)·Σ w·s² − ε·Σ w
  have lo2 : qEq (csum (fun c => qsub (qmul l (two_sq c.2.2)) (qeps k)) cs)
      (qadd (qmul (qadd l l) (csum (fun c => sq c.2.2) cs)) (qmul (qneg (qeps k)) (csum (fun _ => qone) cs))) := by
    have a := csum_congr (g := fun c => qsub (qmul l (two_sq c.2.2)) (qeps k))
      (g' := fun c => qadd (qmul (qadd l l) (sq c.2.2)) (qmul (qneg (qeps k)) qone)) cs
      (fun c _ => by
        show qEq (qsub (qmul l (two_sq c.2.2)) (qeps k)) (qadd (qmul (qadd l l) (sq c.2.2)) (qmul (qneg (qeps k)) qone))
        unfold two_sq sq qsub; rat_ring)
    have b := csum_add (fun c => qmul (qadd l l) (sq c.2.2)) (fun _ => qmul (qneg (qeps k)) qone) cs
    have c1 := csum_scale (qadd l l) (fun c => sq c.2.2) cs
    have c2 := csum_scale (qneg (qeps k)) (fun _ => qone) cs
    exact qEq_trans a (qEq_trans b (qadd_respects c1 c2))
  have hi2 : qEq (csum (fun c => qadd (qmul u (two_sq c.2.2)) (qeps k)) cs)
      (qadd (qmul (qadd u u) (csum (fun c => sq c.2.2) cs)) (qmul (qeps k) (csum (fun _ => qone) cs))) := by
    have a := csum_congr (g := fun c => qadd (qmul u (two_sq c.2.2)) (qeps k))
      (g' := fun c => qadd (qmul (qadd u u) (sq c.2.2)) (qmul (qeps k) qone)) cs
      (fun c _ => by
        show qEq (qadd (qmul u (two_sq c.2.2)) (qeps k)) (qadd (qmul (qadd u u) (sq c.2.2)) (qmul (qeps k) qone))
        unfold two_sq sq; rat_ring)
    have b := csum_add (fun c => qmul (qadd u u) (sq c.2.2)) (fun _ => qmul (qeps k) qone) cs
    have c1 := csum_scale (qadd u u) (fun c => sq c.2.2) cs
    have c2 := csum_scale (qeps k) (fun _ => qone) cs
    exact qEq_trans a (qEq_trans b (qadd_respects c1 c2))
  have ew1 := qmul_respects (qEq_refl (qneg (qeps k))) Wh
  have ew2 := qmul_respects (qEq_refl (qeps k)) Wh
  -- Σ w·s² within μh² of t3
  obtain ⟨cs1, cs2⟩ := cube_sum cs qzero h (qle_refl qzero) hch hok
  have S2lo : qle (qneg (qmul μ (sq h))) (qsub (csum (fun c => sq c.2.2) cs) t3) := by
    unfold three cube sq qsub at *; rat_linarith
  have S2hi : qle (qsub (csum (fun c => sq c.2.2) cs) t3) (qmul μ (sq h)) := by
    unfold three cube sq qsub at *; rat_linarith
  have μh : qle qzero (qmul μ (sq h)) := qmul_nonneg hμ (qmul_self_nonneg h)
  have Kμh := qmul_nonneg hK0 μh
  have Llo : qle (qneg (qmul K (qmul μ (sq h)))) (qmul l (qsub (csum (fun c => sq c.2.2) cs) t3)) :=
    mul_lo hl1 hl2 S2lo S2hi (by rat_linarith) (by rat_linarith) (by rat_linarith) (by rat_linarith)
  have Uhi : qle (qmul u (qsub (csum (fun c => sq c.2.2) cs) t3)) (qmul K (qmul μ (sq h))) :=
    mul_hi hu1 hu2 S2lo S2hi (by rat_linarith) (by rat_linarith) (by rat_linarith) (by rat_linarith)
  -- 2h·f0 against 2h·c0, 2h·C0
  have h2 : qle qzero (qadd h h) := by rat_linarith
  have F1 := scale_l v1 h2
  have F2 := scale_l v2 h2
  unfold three sq qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZIntegralT

#print axioms ZIntegralT.csum_mono
#print axioms ZIntegralT.width_chain
#print axioms ZIntegralT.cells_within
#print axioms ZIntegralT.cell_err
#print axioms ZIntegralT.cube_sum
#print axioms ZIntegralT.cell_sd
#print axioms ZIntegralT.taylor2_leaf
