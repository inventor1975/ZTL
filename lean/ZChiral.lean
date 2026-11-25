import ZTL

/-!
# ZChiral — chirality as identity RELATIVE TO PROBES. Zero axioms. (2026-11-25)

THE CURATOR'S POINT (25.11): intensional identity in naive sets (VR N18) is not a defect but a use — a construction
can carry a difference its extension does not show.  Chirality is the physical instance: a left hand and a right
hand have the same parts at the same mutual distances, yet are not the same.

THE READING IN ZTL.  Identity of two figures is judged by a family of PROBES (measurements):

    T   the same construction (here: the same figure);
    F   a probe in the family gives different readings — a WITNESSED difference;
    Z   neither: different constructions, no probe in the family tells them apart.

    enantiomers_Z_achiral   a scalene triangle and its mirror image: every DISTANCE probe agrees — identity Z
                            (not T: the constructions differ; not F: no witness);
    enantiomers_F_chiral    add the ORIENTATION probe (sign of the cross product) — identity F, witnessed;
    collinear_Z_chiral      a collinear figure and its mirror: even orientation agrees (both 0) — Z stays.  The
                            figure IS achiral (a half-turn carries the mirror image back), but T would need that
                            proper motion as a witness of sameness — not modelled here, so Z is the honest verdict;
    mirror_twice_T          mirror twice = the same figure — T;
    sharpen_F / sharpen_T / sharpen_Z_not_T   adding probes never revokes a verdict: F stays F, T stays T, Z can
                            become F but never T.  Z → F only, by a new witness.

Contrast with VR N12 (`Levels.revoked`): identity read off a level of MEMBERSHIPS was earned and then refuted.
Witness-identity cannot be revoked: a new probe can only add a witness.

THE CHEMISTRY (as it is, not claimed by the file): enantiomers agree in every achiral measurement (boiling point,
achiral spectra); a chiral probe — polarised light, an enzyme, another chiral molecule — tells them apart.

NOT NEW: Kant 1768, "incongruent counterparts" (against Leibniz's identity of indiscernibles); Kelvin 1904 named
chirality; Black 1952, two spheres.  `ZIndisc` already shows that indiscernible ≠ identical on marks.  New here only:
identity as a ZTL verdict relative to a probe family, and that this verdict only sharpens (Z → F) and is never
revoked.

CAVEAT: as point SETS in the plane, a figure and its mirror differ trivially — different coordinates.  The reading
is for descriptions by RELATIONS (distances, orientation), which is what Kant's argument is about.  The geometry is
checked on concrete figures (core `Int` algebra carries `propext`); the verdict structure is general.
-/

namespace ZChiral

open V

/-- A labelled triangle: three points with integer coordinates. -/
structure Fig where
  ax : Int
  ay : Int
  bx : Int
  b_y : Int
  cx : Int
  cy : Int
deriving DecidableEq

/-- The mirror image in the y-axis. -/
def mirror (f : Fig) : Fig := ⟨-f.ax, f.ay, -f.bx, f.b_y, -f.cx, f.cy⟩

/-- A probe: a measurement of a figure. -/
abbrev Probe := Fig → Int

def dAB : Probe := fun f => (f.ax - f.bx) * (f.ax - f.bx) + (f.ay - f.b_y) * (f.ay - f.b_y)
def dBC : Probe := fun f => (f.bx - f.cx) * (f.bx - f.cx) + (f.b_y - f.cy) * (f.b_y - f.cy)
def dCA : Probe := fun f => (f.cx - f.ax) * (f.cx - f.ax) + (f.cy - f.ay) * (f.cy - f.ay)
/-- Orientation: the cross product (B − A) × (C − A); its sign is the handedness. -/
def orient : Probe := fun f => (f.bx - f.ax) * (f.cy - f.ay) - (f.b_y - f.ay) * (f.cx - f.ax)

/-- Achiral probes: the three squared distances. -/
def achiral : List Probe := [dAB, dBC, dCA]
/-- Add the chiral probe. -/
def chiral : List Probe := achiral ++ [orient]

/-- Some probe in the family gives different readings (a witness). -/
def differs : List Probe → Fig → Fig → Bool
  | [], _, _ => false
  | p :: ps, f, g => if p f = p g then differs ps f g else true

/-- The identity verdict relative to a probe family. -/
def idv (P : List Probe) (f g : Fig) : V :=
  if f = g then T else if differs P f g = true then F else Z

/-! ## The verdict only sharpens — general -/

theorem differs_append : ∀ (P Q : List Probe) (f g : Fig), differs P f g = true → differs (P ++ Q) f g = true
  | [], _, _, _, h => Bool.noConfusion h
  | p :: ps, Q, f, g, h => by
    show (if p f = p g then differs (ps ++ Q) f g else true) = true
    by_cases e : p f = p g
    · rw [if_pos e]
      have h' : differs ps f g = true := by
        have : (if p f = p g then differs ps f g else true) = true := h
        rw [if_pos e] at this
        exact this
      exact differs_append ps Q f g h'
    · rw [if_neg e]

/-- A witnessed difference stays witnessed under more probes. -/
theorem sharpen_F (P Q : List Probe) (f g : Fig) (h : idv P f g = F) : idv (P ++ Q) f g = F := by
  by_cases e : f = g
  · have : idv P f g = T := by show (if f = g then T else _) = T; rw [if_pos e]
    rw [this] at h; exact V.noConfusion h
  · by_cases d : differs P f g = true
    · show (if f = g then T else if differs (P ++ Q) f g = true then F else Z) = F
      rw [if_neg e, if_pos (differs_append P Q f g d)]
    · have : idv P f g = Z := by
        show (if f = g then T else if differs P f g = true then F else Z) = Z
        rw [if_neg e, if_neg d]
      rw [this] at h; exact V.noConfusion h

/-- Sameness of construction does not depend on the probes. -/
theorem sharpen_T (P Q : List Probe) (f g : Fig) (h : idv P f g = T) : idv Q f g = T := by
  by_cases e : f = g
  · show (if f = g then T else _) = T; rw [if_pos e]
  · have : idv P f g ≠ T := by
      show (if f = g then T else if differs P f g = true then F else Z) ≠ T
      rw [if_neg e]
      by_cases d : differs P f g = true
      · rw [if_pos d]; exact fun h => V.noConfusion h
      · rw [if_neg d]; exact fun h => V.noConfusion h
    exact absurd h this

/-- Z never becomes T by more probes: probes can only witness a difference. -/
theorem sharpen_Z_not_T (P Q : List Probe) (f g : Fig) (h : idv P f g = Z) : idv (P ++ Q) f g ≠ T :=
  fun hT => by
    have := sharpen_T (P ++ Q) P f g hT
    rw [this] at h; exact V.noConfusion h

/-! ## The geometry, on concrete figures -/

/-- A scalene right triangle: A = (0,0), B = (2,0), C = (0,1). -/
def t0 : Fig := ⟨0, 0, 2, 0, 0, 1⟩
/-- Three collinear points. -/
def line0 : Fig := ⟨0, 0, 1, 0, 3, 0⟩

/-- **The enantiomers agree in every distance** — and they are different constructions. -/
theorem enantiomers_same_distances : dAB (mirror t0) = dAB t0 ∧ dBC (mirror t0) = dBC t0 ∧
    dCA (mirror t0) = dCA t0 ∧ mirror t0 ≠ t0 := by decide

/-- **Achiral probes: identity Z** — not earned, not refuted. -/
theorem enantiomers_Z_achiral : idv achiral t0 (mirror t0) = Z := by decide

/-- **The chiral probe witnesses the difference: identity F.** Orientation +2 against −2. -/
theorem enantiomers_F_chiral : idv chiral t0 (mirror t0) = F ∧ orient t0 = 2 ∧ orient (mirror t0) = -2 := by
  decide

/-- A collinear figure: orientation 0 on both sides — even the chiral probe leaves Z. -/
theorem collinear_Z_chiral : idv chiral line0 (mirror line0) = Z := by decide

/-- Mirror twice: the same figure — T. -/
theorem mirror_twice_T : idv chiral t0 (mirror (mirror t0)) = T := by decide

/-- Mirror twice is the identity on every figure (only `Int.neg_neg`, which is clean). -/
theorem mirror_mirror (f : Fig) : mirror (mirror f) = f := by
  cases f with
  | mk ax ay bx b_y cx cy =>
    show (⟨-(-ax), ay, -(-bx), b_y, -(-cx), cy⟩ : Fig) = ⟨ax, ay, bx, b_y, cx, cy⟩
    rw [Int.neg_neg, Int.neg_neg, Int.neg_neg]

end ZChiral

#print axioms ZChiral.differs_append
#print axioms ZChiral.sharpen_F
#print axioms ZChiral.sharpen_T
#print axioms ZChiral.sharpen_Z_not_T
#print axioms ZChiral.enantiomers_same_distances
#print axioms ZChiral.enantiomers_Z_achiral
#print axioms ZChiral.enantiomers_F_chiral
#print axioms ZChiral.collinear_Z_chiral
#print axioms ZChiral.mirror_twice_T
#print axioms ZChiral.mirror_mirror
