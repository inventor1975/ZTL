import ZRoot
/-!
# ZRootP — part 1: the divided difference in ONE variable of a polynomial in many. Zero axioms.

For the root of `g(x, p) = 0` at every real parameter point `p` (the existence premise of `ZImplicit`), the
bounds come from divided differences in one variable at a time: in `x` (the slope) and in each parameter
(continuity). `ddv v Y f` is the divided difference of `f` in the variable `v`, the second point read from
the variable `Y`:

    f(e) − f(e[v := e Y]) = (e v − e Y) · (ddv v Y f)(e)          (ddv_ident, any `Y`, in every `OH`)
-/

namespace ZRootP
open VR.CSR ZNumBin ZField ZPoly ZIv ZRoot

variable {α : Type} (S : CF α)

/-- `p` with `v` read from `Y`. -/
def atY (v Y : Nat) (p : PE) : PE := p.subst (fun i => cond (Nat.beq i v) (.var Y) (.var i))

def ddvPow (v Y : Nat) (p dp : PE) : Nat → PE
  | 0 => c0
  | k + 1 => .add (.mul dp (.pow p k)) (.mul (atY v Y p) (ddvPow v Y p dp k))

def ddv (v Y : Nat) : PE → PE
  | .var i => cond (Nat.beq i v) c1 c0
  | .cst _ => c0
  | .add p q => .add (ddv v Y p) (ddv v Y q)
  | .sub p q => .sub (ddv v Y p) (ddv v Y q)
  | .mul p q => .add (.mul (ddv v Y p) q) (.mul (atY v Y p) (ddv v Y q))
  | .pow p k => ddvPow v Y p (ddv v Y p) k

/-- `e` with `v` set to `x`. -/
def setv (e : Nat → α) (v : Nat) (x : α) : Nat → α := fun i => cond (Nat.beq i v) x (e i)

section
variable (e : Nat → α) (v Y : Nat)

theorem eval_atY (p : PE) : S.r (eval S.toOH e (atY v Y p)) (eval S.toOH (setv e v (e Y)) p) := by
  refine S.trans (eval_subst S.toOH e _ p) (ZNone.eval_congr_env S (fun i => ?_) p)
  show S.r (eval S.toOH e (cond (Nat.beq i v) (.var Y) (.var i))) (cond (Nat.beq i v) (e Y) (e i))
  cases Nat.beq i v <;> exact S.refl _

theorem c0_ev : S.r (eval S.toOH e c0) S.zero := by
  show S.r (S.mul (S.add S.zero (S.neg S.zero)) S.one) S.zero; cr_ring S.toCR
theorem c1_ev : S.r (eval S.toOH e c1) S.one := dv_one S

theorem ddvPow_ident (p dp : PE)
    (hp : S.r (S.add (eval S.toOH e p) (S.neg (eval S.toOH (setv e v (e Y)) p)))
      (S.mul (S.add (e v) (S.neg (e Y))) (eval S.toOH e dp))) :
    ∀ k, S.r (S.add (powS S.toOH (eval S.toOH e p) k) (S.neg (powS S.toOH (eval S.toOH (setv e v (e Y)) p) k)))
      (S.mul (S.add (e v) (S.neg (e Y))) (eval S.toOH e (ddvPow v Y p dp k)))
  | 0 => by
      have z := c0_ev S e
      show S.r (S.add S.one (S.neg S.one)) (S.mul (S.add (e v) (S.neg (e Y))) (eval S.toOH e c0))
      have h1 : S.r (S.add S.one (S.neg S.one)) S.zero := by cr_ring S.toCR
      have h2 : S.r (S.mul (S.add (e v) (S.neg (e Y))) S.zero) S.zero := by cr_ring S.toCR
      exact S.trans h1 (S.symm (S.trans (S.mul_congr (S.refl _) z) h2))
  | k + 1 => by
      have ih := ddvPow_ident p dp hp k
      have a1 := eval_atY S e v Y p
      show S.r (S.add (S.mul (eval S.toOH e p) (powS S.toOH (eval S.toOH e p) k))
          (S.neg (S.mul (eval S.toOH (setv e v (e Y)) p) (powS S.toOH (eval S.toOH (setv e v (e Y)) p) k))))
        (S.mul (S.add (e v) (S.neg (e Y))) (S.add (S.mul (eval S.toOH e dp) (powS S.toOH (eval S.toOH e p) k))
          (S.mul (eval S.toOH e (atY v Y p)) (eval S.toOH e (ddvPow v Y p dp k)))))
      generalize eval S.toOH e p = X at *
      generalize eval S.toOH (setv e v (e Y)) p = Yv at *
      generalize eval S.toOH e dp = DP at *
      generalize eval S.toOH e (ddvPow v Y p dp k) = DK at *
      generalize powS S.toOH X k = XK at *
      generalize powS S.toOH Yv k = YK at *
      refine S.trans ?_ (S.symm (S.mul_congr (S.refl _) (S.add_congr (S.refl _) (S.mul_congr a1 (S.refl _)))))
      have t : S.r (S.add (S.mul X XK) (S.neg (S.mul Yv YK)))
          (S.add (S.mul (S.add X (S.neg Yv)) XK) (S.mul Yv (S.add XK (S.neg YK)))) := by cr_ring S.toCR
      refine S.trans t (S.trans (S.add_congr (S.mul_congr hp (S.refl _)) (S.mul_congr (S.refl _) ih)) ?_)
      cr_ring S.toCR

/-- **THE DIVIDED DIFFERENCE IN `v`.** -/
theorem ddv_ident : ∀ f : PE, S.r (S.add (eval S.toOH e f) (S.neg (eval S.toOH (setv e v (e Y)) f)))
    (S.mul (S.add (e v) (S.neg (e Y))) (eval S.toOH e (ddv v Y f)))
  | .var i => by
      show S.r (S.add (e i) (S.neg (cond (Nat.beq i v) (e Y) (e i))))
        (S.mul (S.add (e v) (S.neg (e Y))) (eval S.toOH e (cond (Nat.beq i v) c1 c0)))
      cases hb : Nat.beq i v with
      | true =>
          have := Nat.eq_of_beq_eq_true hb; subst this
          have o := c1_ev S e
          have h : S.r (S.mul (S.add (e i) (S.neg (e Y))) S.one) (S.add (e i) (S.neg (e Y))) := by cr_ring S.toCR
          exact S.symm (S.trans (S.mul_congr (S.refl _) o) h)
      | false =>
          have z := c0_ev S e
          have h1 : S.r (S.add (e i) (S.neg (e i))) S.zero := by cr_ring S.toCR
          have h2 : S.r (S.mul (S.add (e v) (S.neg (e Y))) S.zero) S.zero := by cr_ring S.toCR
          exact S.trans h1 (S.symm (S.trans (S.mul_congr (S.refl _) z) h2))
  | .cst c => by
      have z := c0_ev S e
      show S.r (S.add (dv S.toOH c) (S.neg (dv S.toOH c))) (S.mul (S.add (e v) (S.neg (e Y))) (eval S.toOH e c0))
      have h1 : S.r (S.add (dv S.toOH c) (S.neg (dv S.toOH c))) S.zero := by cr_ring S.toCR
      have h2 : S.r (S.mul (S.add (e v) (S.neg (e Y))) S.zero) S.zero := by cr_ring S.toCR
      exact S.trans h1 (S.symm (S.trans (S.mul_congr (S.refl _) z) h2))
  | .add p q => by
      have hp := ddv_ident p; have hq := ddv_ident q
      show S.r (S.add (S.add (eval S.toOH e p) (eval S.toOH e q))
          (S.neg (S.add (eval S.toOH (setv e v (e Y)) p) (eval S.toOH (setv e v (e Y)) q))))
        (S.mul (S.add (e v) (S.neg (e Y))) (S.add (eval S.toOH e (ddv v Y p)) (eval S.toOH e (ddv v Y q))))
      exact S.trans (by cr_ring S.toCR) (S.trans (S.add_congr hp hq) (by cr_ring S.toCR))
  | .sub p q => by
      have hp := ddv_ident p; have hq := ddv_ident q
      show S.r (S.add (S.add (eval S.toOH e p) (S.neg (eval S.toOH e q)))
          (S.neg (S.add (eval S.toOH (setv e v (e Y)) p) (S.neg (eval S.toOH (setv e v (e Y)) q)))))
        (S.mul (S.add (e v) (S.neg (e Y))) (S.add (eval S.toOH e (ddv v Y p)) (S.neg (eval S.toOH e (ddv v Y q)))))
      exact S.trans (by cr_ring S.toCR) (S.trans (S.add_congr hp (S.neg_congr hq)) (by cr_ring S.toCR))
  | .mul p q => by
      have hp := ddv_ident p; have hq := ddv_ident q
      have a1 := eval_atY S e v Y p
      show S.r (S.add (S.mul (eval S.toOH e p) (eval S.toOH e q))
          (S.neg (S.mul (eval S.toOH (setv e v (e Y)) p) (eval S.toOH (setv e v (e Y)) q))))
        (S.mul (S.add (e v) (S.neg (e Y))) (S.add (S.mul (eval S.toOH e (ddv v Y p)) (eval S.toOH e q))
          (S.mul (eval S.toOH e (atY v Y p)) (eval S.toOH e (ddv v Y q)))))
      generalize eval S.toOH e p = PX at *
      generalize eval S.toOH (setv e v (e Y)) p = PY at *
      generalize eval S.toOH e q = QX at *
      generalize eval S.toOH (setv e v (e Y)) q = QY at *
      generalize eval S.toOH e (ddv v Y p) = DP at *
      generalize eval S.toOH e (ddv v Y q) = DQ at *
      refine S.trans ?_ (S.symm (S.mul_congr (S.refl _) (S.add_congr (S.refl _) (S.mul_congr a1 (S.refl _)))))
      have t : S.r (S.add (S.mul PX QX) (S.neg (S.mul PY QY)))
          (S.add (S.mul (S.add PX (S.neg PY)) QX) (S.mul PY (S.add QX (S.neg QY)))) := by cr_ring S.toCR
      refine S.trans t (S.trans (S.add_congr (S.mul_congr hp (S.refl _)) (S.mul_congr (S.refl _) hq)) ?_)
      cr_ring S.toCR
  | .pow p k => ddvPow_ident S e v Y p (ddv v Y p) (ddv_ident p) k
end


/-! ## Freshness: a variable a polynomial does not use does not matter -/

def uses (Y : Nat) : PE → Bool
  | .var i => Nat.beq i Y
  | .cst _ => false
  | .add p q => uses Y p || uses Y q
  | .sub p q => uses Y p || uses Y q
  | .mul p q => uses Y p || uses Y q
  | .pow p _ => uses Y p

theorem or_false_split {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem eval_fresh (e : Nat → α) (Y : Nat) (y : α) : ∀ f : PE, uses Y f = false →
    S.r (eval S.toOH (setv e Y y) f) (eval S.toOH e f)
  | .var i, h => by
      show S.r (cond (Nat.beq i Y) y (e i)) (e i)
      have h' : Nat.beq i Y = false := h
      rw [h']; exact S.refl _
  | .cst _, _ => S.refl _
  | .add p q, h => by
      obtain ⟨a, b⟩ := or_false_split h
      exact S.add_congr (eval_fresh e Y y p a) (eval_fresh e Y y q b)
  | .sub p q, h => by
      obtain ⟨a, b⟩ := or_false_split h
      exact S.add_congr (eval_fresh e Y y p a) (S.neg_congr (eval_fresh e Y y q b))
  | .mul p q, h => by
      obtain ⟨a, b⟩ := or_false_split h
      exact S.mul_congr (eval_fresh e Y y p a) (eval_fresh e Y y q b)
  | .pow p k, h => powS_congr S.toOH (eval_fresh e Y y p h) k

theorem setv_setv_same (e : Nat → α) (v : Nat) (x y : α) (i : Nat) :
    setv (setv e v x) v y i = setv e v y i := by
  show cond (Nat.beq i v) y (cond (Nat.beq i v) x (e i)) = cond (Nat.beq i v) y (e i)
  cases Nat.beq i v <;> rfl

theorem setv_comm (e : Nat → α) {v w : Nat} (hvw : Nat.beq v w = false) (x y : α) (i : Nat) :
    setv (setv e v x) w y i = setv (setv e w y) v x i := by
  show cond (Nat.beq i w) y (cond (Nat.beq i v) x (e i)) = cond (Nat.beq i v) x (cond (Nat.beq i w) y (e i))
  cases hw : Nat.beq i w with
  | false => rfl
  | true =>
      have := Nat.eq_of_beq_eq_true hw; subst this
      cases hv : Nat.beq i v with
      | false => rfl
      | true => have := Nat.eq_of_beq_eq_true hv; subst this; rw [ZKron.beq_self] at hvw; cases hvw

theorem setv_at (e : Nat → α) (v : Nat) (x : α) : setv e v x v = x := by
  show cond (Nat.beq v v) x (e v) = x; rw [ZKron.beq_self]; rfl

/-! ## One-variable differences of `f`, from the identity, as a usable statement -/

/-- `f(e[v := x]) − f(e[v := y]) = (x − y)·Q`, `Q` the divided difference read at `e[v := x][Y := y]`. -/
theorem diff_v (f : PE) (e : Nat → α) {v Y : Nat} (hvY : Nat.beq v Y = false) (hY : uses Y f = false) (x y : α) :
    S.r (S.add (eval S.toOH (setv e v x) f) (S.neg (eval S.toOH (setv e v y) f)))
      (S.mul (S.add x (S.neg y)) (eval S.toOH (setv (setv e v x) Y y) (ddv v Y f))) := by
  have id := ddv_ident S (setv (setv e v x) Y y) v Y f
  -- the left point: the extra variable is unused
  have l : S.r (eval S.toOH (setv (setv e v x) Y y) f) (eval S.toOH (setv e v x) f) := eval_fresh S _ Y y f hY
  -- the right point: v set to y, and Y unused
  have ey : setv (setv e v x) Y y Y = y := setv_at _ _ _
  have ev : setv (setv e v x) Y y v = x := by
    rw [setv_comm e hvY x y v]; exact setv_at _ _ _
  have r : S.r (eval S.toOH (setv (setv (setv e v x) Y y) v y) f) (eval S.toOH (setv e v y) f) := by
    refine S.trans (ZNone.eval_congr_env S (fun i => ?_) f) (eval_fresh S (setv e v y) Y y f hY)
    show S.r (setv (setv (setv e v x) Y y) v y i) (setv (setv e v y) Y y i)
    have h1 : setv (setv (setv e v x) Y y) v y i = setv (setv (setv e v x) v y) Y y i := by
      have := setv_comm (setv e v x) (v := Y) (w := v) (by
        cases h : Nat.beq Y v with
        | false => rfl
        | true => have := Nat.eq_of_beq_eq_true h; subst this; rw [ZKron.beq_self] at hvY; cases hvY) y y i
      exact this
    rw [h1]
    show S.r (cond (Nat.beq i Y) y (setv (setv e v x) v y i)) (cond (Nat.beq i Y) y (setv e v y i))
    rw [setv_setv_same]; exact S.refl _
  rw [ev, ey] at id
  exact S.trans (S.add_congr (S.symm l) (S.neg_congr (S.symm r))) id


/-! ## Reading the divided difference over a box -/

/-- The box `B` with the extra variable `Y` ranging over `v`'s interval. -/
def BY (B : Box) (v Y : Nat) : Box := fun j => cond (Nat.beq j Y) (B v) (B j)

theorem inbox_BY {B : Box} {e : Nat → α} {v Y : Nat} {I : Iv} (hvY : Nat.beq v Y = false) (he : InBox S B e)
    (hBv : B v = some I) {x y : α} (hx : Mem S x I) (hy : Mem S y I) :
    InBox S (BY B v Y) (setv (setv e v x) Y y) := by
  intro j J hJ
  cases hjY : Nat.beq j Y with
  | true =>
      have : BY B v Y j = B v := by unfold BY; rw [hjY]; rfl
      rw [this, hBv] at hJ; cases hJ
      show S.le _ (cond (Nat.beq j Y) y _) ∧ S.le (cond (Nat.beq j Y) y _) _
      rw [hjY]; exact hy
  | false =>
      have : BY B v Y j = B j := by unfold BY; rw [hjY]; rfl
      rw [this] at hJ
      show S.le _ (cond (Nat.beq j Y) y (setv e v x j)) ∧ S.le (cond (Nat.beq j Y) y (setv e v x j)) _
      rw [hjY]
      show S.le _ (cond (Nat.beq j v) x (e j)) ∧ S.le (cond (Nat.beq j v) x (e j)) _
      cases hjv : Nat.beq j v with
      | true =>
          have := Nat.eq_of_beq_eq_true hjv; subst this
          rw [hBv] at hJ; cases hJ; exact hx
      | false => exact he j J hJ

/-- **The difference in `v`, bounded by the reading.** `f(e[v:=x]) − f(e[v:=y]) = (x − y)·Q` with `Q ∈ K`. -/
theorem diff_read {f : PE} {B : Box} {v Y : Nat} {K I : Iv} (hvY : Nat.beq v Y = false) (hY : uses Y f = false)
    (hK : ivE (BY B v Y) (ddv v Y f) = some K) (hBv : B v = some I) {e : Nat → α} (he : InBox S B e)
    {x y : α} (hx : Mem S x I) (hy : Mem S y I) :
    ∃ Q, Mem S Q K ∧ S.r (S.add (eval S.toOH (setv e v x) f) (S.neg (eval S.toOH (setv e v y) f)))
      (S.mul (S.add x (S.neg y)) Q) :=
  ⟨_, ivE_sound S (inbox_BY S hvY he hBv hx hy) _ K hK, diff_v S f e hvY hY x y⟩


/-! ## Continuity in the parameters: one at a time, then summed -/

/-- The reading of `dd` in parameter `c.1` lies in `[−c.2, c.2]`. -/
def lipOK (f : PE) (B : Box) (Y : Nat) (c : Nat × D) : Bool :=
  !(Nat.beq c.1 Y) && (match B c.1 with
    | some _ => (match ivE (BY B c.1 Y) (ddv c.1 Y f) with
        | some K => dle (dneg c.2) K.1 && dle K.2 c.2
        | none => false)
    | none => false)

def allOK (f : PE) (B : Box) (Y : Nat) : List (Nat × D) → Bool
  | [] => true
  | c :: cs => lipOK f B Y c && allOK f B Y cs

def notIn (j : Nat) : List (Nat × D) → Bool
  | [] => true
  | c :: cs => !(Nat.beq j c.1) && notIn j cs

/-- The bound `Σ Lᵢ·δᵢ`. -/
def sumL (δ : Nat → α) : List (Nat × D) → α
  | [] => S.zero
  | c :: cs => S.add (S.mul (δ c.1) (dv S.toOH c.2)) (sumL δ cs)

def AllBd (e e' δ : Nat → α) : List (Nat × D) → Prop
  | [] => True
  | c :: cs => ZKron.Bd S.toOH (S.add (e c.1) (S.neg (e' c.1))) (δ c.1) ∧ AllBd e e' δ cs

theorem and_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := ZNumBin.and_true_split h

theorem setv_self (e : Nat → α) (i j : Nat) : setv e i (e i) j = e j := by
  show cond (Nat.beq j i) (e i) (e j) = e j
  cases h : Nat.beq j i with
  | false => rfl
  | true => have := Nat.eq_of_beq_eq_true h; subst this; rfl

theorem allBd_setv (e e' δ : Nat → α) (i : Nat) (d0 : S.le S.zero (δ i)) :
    ∀ ds, AllBd S e e' δ ds → AllBd S (setv e i (e' i)) e' δ ds
  | [], _ => trivial
  | d :: ds, ⟨b1, b2⟩ => by
      refine ⟨?_, allBd_setv e e' δ i d0 ds b2⟩
      show ZKron.Bd S.toOH (S.add (cond (Nat.beq d.1 i) (e' i) (e d.1)) (S.neg (e' d.1))) (δ d.1)
      cases h : Nat.beq d.1 i with
      | false => exact b1
      | true =>
          have := Nat.eq_of_beq_eq_true h
          rw [this]
          have z : S.r (S.add (e' i) (S.neg (e' i))) S.zero := S.add_neg _
          exact ZKron.bd_congr S.toOH (S.symm z) (S.refl _) ⟨by cr_linarith S.toOCR [d0], d0⟩

theorem lip_params (f : PE) (B : Box) (Y : Nat) (hY : uses Y f = false) :
    ∀ (cs : List (Nat × D)) (e e' δ : Nat → α), allOK f B Y cs = true → InBox S B e → InBox S B e' →
      (∀ j, notIn j cs = true → S.r (e j) (e' j)) → AllBd S e e' δ cs →
      ZKron.Bd S.toOH (S.add (eval S.toOH e f) (S.neg (eval S.toOH e' f))) (sumL S δ cs)
  | [], e, e', _, _, _, _, hag, _ => by
      have h := ZNone.eval_congr_env S (fun j => hag j rfl) f
      show ZKron.Bd S.toOH _ S.zero
      have z : S.r (S.add (eval S.toOH e f) (S.neg (eval S.toOH e' f))) S.zero :=
        S.trans (S.add_congr h (S.refl _)) (S.add_neg _)
      exact ZKron.bd_congr S.toOH (S.symm z) (S.refl _)
        ⟨S.le_respects (S.symm S.neg_zero) (S.refl _) (S.le_refl _), S.le_refl _⟩
  | c :: cs, e, e', δ, hok, he, he', hag, ⟨hb, hbs⟩ => by
      obtain ⟨h1, h2⟩ := and_split hok
      obtain ⟨hiY, hm⟩ := and_split h1
      have hiY' : Nat.beq c.1 Y = false := by
        cases h : Nat.beq c.1 Y with
        | false => rfl
        | true => rw [h] at hiY; cases hiY
      -- the interval of c.1 and the reading
      cases hB : B c.1 with
      | none => rw [hB] at hm; cases hm
      | some I =>
      rw [hB] at hm
      cases hK : ivE (BY B c.1 Y) (ddv c.1 Y f) with
      | none => rw [hK] at hm; cases hm
      | some K =>
      rw [hK] at hm
      obtain ⟨k1, k2⟩ := and_split hm
      -- step one: change parameter c.1 from e to e'
      have xI : Mem S (e c.1) I := he c.1 I hB
      have yI : Mem S (e' c.1) I := he' c.1 I hB
      obtain ⟨Q, hQ, hd⟩ := diff_read S hiY' hY hK hB he xI yI
      have QL : ZKron.Bd S.toOH Q (dv S.toOH c.2) := by
        have l := dle_sound S.toOH k1; have u := dle_sound S.toOH k2
        have n := dv_neg S.toOH c.2
        exact ⟨S.le_trans (S.le_respects n (S.refl _) l) hQ.1, S.le_trans hQ.2 u⟩
      have step := ZKron.bd_mul S.toOH hb QL
      have ee : S.r (eval S.toOH (setv e c.1 (e c.1)) f) (eval S.toOH e f) :=
        ZNone.eval_congr_env S (fun j => by rw [setv_self]; exact S.refl _) f
      -- step two: the rest, by induction, from e[c.1 := e' c.1] to e'
      have he1 : InBox S B (setv e c.1 (e' c.1)) := by
        intro j J hJ
        show Mem S (cond (Nat.beq j c.1) (e' c.1) (e j)) J
        cases h : Nat.beq j c.1 with
        | true => have := Nat.eq_of_beq_eq_true h; subst this; exact he' _ J hJ
        | false => exact he j J hJ
      have hag1 : ∀ j, notIn j cs = true → S.r (setv e c.1 (e' c.1) j) (e' j) := by
        intro j hj
        show S.r (cond (Nat.beq j c.1) (e' c.1) (e j)) (e' j)
        cases h : Nat.beq j c.1 with
        | true => have := Nat.eq_of_beq_eq_true h; subst this; exact S.refl _
        | false => exact hag j (by show (!(Nat.beq j c.1) && notIn j cs) = true; rw [h, hj]; rfl)
      have d0 : S.le S.zero (δ c.1) := by have := hb.1; have := hb.2; cr_linarith S.toOCR [hb.1, hb.2]
      have hbs1 : AllBd S (setv e c.1 (e' c.1)) e' δ cs := allBd_setv S e e' δ c.1 d0 cs hbs
      have rest := lip_params f B Y hY cs (setv e c.1 (e' c.1)) e' δ h2 he1 he' hag1 hbs1
      have tot := ZKron.bd_add S.toOH (ZKron.bd_congr S.toOH (S.symm hd) (S.refl _) step) rest
      refine ZKron.bd_congr S.toOH ?_ (S.refl _) tot
      refine S.trans (S.add_congr (S.add_congr ee (S.refl _)) (S.refl _)) ?_
      cr_ring S.toCR


/-! ## Two brackets of two nearby increasing functions are close -/

/-- `G'` increases with slope at least `c > 0` (as a divided difference), `G − G' ≤ D` at `s := t + w`,
`G(t + w) ≥ 0`, `G'(t') ≤ 0`: then `(t' − (t + w))·c ≤ D`. Constructive: by `le_of_not_pos`, no order of the
points is decided. -/
theorem bracket_close {G G' : α → α} {c D t w t' : α} (hc : S.pos c) (hD : S.le S.zero D)
    (Q : α) (hQ : S.le c Q) (hid : S.r (S.add (G' t') (S.neg (G' (S.add t w)))) (S.mul (S.add t' (S.neg (S.add t w))) Q))
    (hGG : S.le (S.add (G (S.add t w)) (S.neg (G' (S.add t w)))) D)
    (hG : S.le S.zero (G (S.add t w))) (hG' : S.le (G' t') S.zero) :
    S.le (S.mul (S.add t' (S.neg (S.add t w))) c) D := by
  have c0 := S.pos_nonneg hc
  -- (t' − s)·Q ≤ D
  have hQD : S.le (S.mul (S.add t' (S.neg (S.add t w))) Q) D := by
    have := S.le_respects hid (S.refl _) (S.le_refl _)
    cr_linarith S.toOCR [hGG, hG, hG', this]
  apply OCR.le_of_sub_nonneg S.toOCR
  apply S.le_of_not_pos
  intro hp
  -- hp : (t' − s)·c − D > 0  (in the form 0 − (D − (t' − s)·c))
  have pc : S.pos (S.mul (S.add t' (S.neg (S.add t w))) c) :=
    S.pos_mono hp (by cr_linarith S.toOCR [hD])
  -- then t' − s ≥ 0
  have nn : S.le S.zero (S.add t' (S.neg (S.add t w))) := by
    apply OCR.le_of_sub_nonneg S.toOCR
    apply S.le_of_not_pos
    intro hneg
    -- t' − s < 0 gives (t' − s)·c ≤ 0
    have hle : S.le (S.add t' (S.neg (S.add t w))) S.zero := by
      have := S.pos_nonneg hneg; cr_linarith S.toOCR [this]
    have m := le_mul_right S.toOH hle c0
    exact S.pos_not_le pc (S.le_respects (S.refl _) (by cr_ring S.toCR) m)
  have m1 := mul_le_l S nn hQ
  exact S.pos_not_le hp (by cr_linarith S.toOCR [m1, hQD])


/-- `bracket_close` at a point `s`: `(t' − s)·c ≤ D`. -/
theorem bracket_close_s {G G' : α → α} {c D s t' : α} (hc : S.pos c) (hD : S.le S.zero D)
    (Q : α) (hQ : S.le c Q) (hid : S.r (S.add (G' t') (S.neg (G' s))) (S.mul (S.add t' (S.neg s)) Q))
    (hGG : S.le (S.add (G s) (S.neg (G' s))) D) (hG : S.le S.zero (G s)) (hG' : S.le (G' t') S.zero) :
    S.le (S.mul (S.add t' (S.neg s)) c) D := by
  have c0 := S.pos_nonneg hc
  have hQD : S.le (S.mul (S.add t' (S.neg s)) Q) D := by
    have := S.le_respects hid (S.refl _) (S.le_refl _)
    cr_linarith S.toOCR [hGG, hG, hG', this]
  apply OCR.le_of_sub_nonneg S.toOCR
  apply S.le_of_not_pos
  intro hp
  have pc : S.pos (S.mul (S.add t' (S.neg s)) c) := S.pos_mono hp (by cr_linarith S.toOCR [hD])
  have nn : S.le S.zero (S.add t' (S.neg s)) := by
    apply OCR.le_of_sub_nonneg S.toOCR
    apply S.le_of_not_pos
    intro hneg
    have hle : S.le (S.add t' (S.neg s)) S.zero := by
      have := S.pos_nonneg hneg; cr_linarith S.toOCR [this]
    have m := le_mul_right S.toOH hle c0
    exact S.pos_not_le pc (S.le_respects (S.refl _) (by cr_ring S.toCR) m)
  have m1 := mul_le_l S nn hQ
  exact S.pos_not_le hp (by cr_linarith S.toOCR [m1, hQD])

/-- The sum of the Lipschitz constants, as a dyadic. -/
def Lsum : List (Nat × D) → D
  | [] => ⟨⟨0, 0⟩, 0⟩
  | c :: cs => dadd c.2 (Lsum cs)

theorem sumL_const (h : α) (hh : S.le S.zero h) : ∀ cs : List (Nat × D),
    S.r (sumL S (fun _ => h) cs) (S.mul h (dv S.toOH (Lsum cs)))
  | [] => by
      show S.r S.zero (S.mul h (S.mul (S.add S.zero (S.neg S.zero)) S.one)); cr_ring S.toCR
  | c :: cs => by
      have ih := sumL_const h hh cs
      show S.r (S.add (S.mul h (dv S.toOH c.2)) (sumL S (fun _ => h) cs)) (S.mul h (dv S.toOH (dadd c.2 (Lsum cs))))
      refine S.trans (S.add_congr (S.refl _) ih) (S.symm (S.trans (S.mul_congr (S.refl _) (dv_add S.toOH _ _)) ?_))
      cr_ring S.toCR

end ZRootP

#print axioms ZRootP.bracket_close_s
#print axioms ZRootP.sumL_const

#print axioms ZRootP.bracket_close

#print axioms ZRootP.lip_params

#print axioms ZRootP.diff_read

#print axioms ZRootP.diff_v

#print axioms ZRootP.ddv_ident
