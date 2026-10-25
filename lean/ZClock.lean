import ZTime

/-!
# ZClock — physical time enters ZTL as ground (the scheduler contract)

ZTL has no clock: its only tick is `verify` (ZTime, E24, "logic below, time on top"). Deadlines in
agent tasks ("in exactly 3 minutes, if she has not replied, ...") therefore do not need a new kernel.
They need a CONTRACT for whatever sits on top and owns the clock (a scheduler): a deadline is an atom
`d` = "window w has closed"; while the window is open `d` is marked `Z`; when the clock passes the
window's end, the scheduler performs one ordinary tick `verify m d T`. Revoking an authority is NOT a
tick: it takes earned ground back (`expire`, E25's anti-tick).

What this file proves, for every formula, marking and tick sequence:

  1. `clock_tick_refines` — closing a window is an ordinary verification tick (keeps all earned ground).
  2. `open_window_blocks` — an action guarded by `d ∧ ψ` is never permitted (never `T`) while `d` is
     still `Z`: no act before its time, whatever `ψ` is.
  3. `closed_window_stays` — once closed, a window stays closed along every future path: no later
     event or tick reopens it.
  4. `permit_survives_clock` — a hereditary verdict (permit or refusal) is unchanged by ANY sequence of
     clock/event ticks: what was rightly decided is not undone by the passage of time.
  5. `only_revocation_takes_back` — if a hereditary verdict ever changes, the new state is not a
     refinement: some earned ground was taken back. Time alone cannot do it.
  6. `revocation_breaks_hereditary` — and revocation really can: a witness where one `expire` turns a
     hereditary `T` into `Z` (the E25 measurement, as a theorem).

Honest size: 1–5 are short consequences of ZTime's definitions; their value is that the scheduler's
obligations are now kernel-checked statements, not prose. They say nothing about whether a given
natural-language instruction was formalized correctly, nor about clock accuracy.

Discipline: no mathlib; `#print axioms` at the end — target: the empty axiom list.
-/

namespace ZClock
open ZTime ZTime.V

/-- Revocation: an atom's earned value is taken back to the mark `Z` (E25's anti-tick). -/
def expire (m : Marking) (a : Nat) : Marking :=
  fun n => if n = a then V.Z else m n

/-- **1. Closing a window is an ordinary tick.** -/
theorem clock_tick_refines {m : Marking} {d : Nat} {v : V} (h : m d = V.Z) :
    Refines (verify m d v) m :=
  verify_refines h

/-- `Z ∧ x` is never `T` in ZTL (zero-trust conjunction). -/
theorem zand_Z_left_ne_T (x : V) : zand V.Z x ≠ V.T := by
  cases x <;> decide

/-- **2. No act before its time.** A guard that includes an open window is not `T`. -/
theorem open_window_blocks {m : Marking} {d : Nat} (h : m d = V.Z) (ψ : Fm) :
    evalF m (.conj (.atom d) ψ) ≠ V.T := by
  show zand (m d) (evalF m ψ) ≠ V.T
  rw [h]
  exact zand_Z_left_ne_T _

/-- **3. A closed window stays closed** along every future path. -/
theorem closed_window_stays {m m' : Marking} {d : Nat} {v : V}
    (hv : v ≠ V.Z) (hr : Refines m' (verify m d v)) : m' d = v := by
  have hd : verify m d v d = v := if_pos rfl
  have hne : verify m d v d ≠ V.Z := by rw [hd]; exact hv
  rw [hr d hne, hd]

/-- Run a sequence of ticks (clock closings or event arrivals). -/
def run : Marking → List (Nat × V) → Marking
  | m, [] => m
  | m, (a, v) :: t => run (verify m a v) t

/-- Every step of the sequence resolves a mark that was still `Z` (honest ticks only). -/
def Ticks : Marking → List (Nat × V) → Prop
  | _, [] => True
  | m, (a, v) :: t => m a = V.Z ∧ Ticks (verify m a v) t

theorem run_refines : ∀ {m : Marking} {l : List (Nat × V)}, Ticks m l → Refines (run m l) m
  | m, [], _ => refines_refl m
  | m, (a, v) :: t, ⟨ha, ht⟩ => by
      show Refines (run (verify m a v) t) m
      exact refines_trans (run_refines ht) (verify_refines ha)

/-- **4. A rightly decided verdict is not undone by time.** -/
theorem permit_survives_clock {φ : Fm} {m : Marking} {l : List (Nat × V)}
    (hH : Hereditary φ m) (ht : Ticks m l) : evalF (run m l) φ = evalF m φ :=
  hH _ (run_refines ht)

/-- **5. Only revocation takes a hereditary verdict back.** -/
theorem only_revocation_takes_back {φ : Fm} {m m' : Marking}
    (hH : Hereditary φ m) (hne : evalF m' φ ≠ evalF m φ) : ¬ Refines m' m :=
  fun hr => hne (hH m' hr)

/-- **6. Revocation can take it back** — the witness. -/
theorem revocation_breaks_hereditary :
    Hereditary (.atom 0) (fun _ => V.T) ∧
    evalF (expire (fun _ => V.T) 0) (.atom 0) ≠ evalF (fun _ => V.T) (.atom 0) ∧
    ¬ Refines (expire (fun _ => V.T) 0) (fun _ => V.T) := by
  refine ⟨grounded_hereditary (fun _ => by decide), by decide, ?_⟩
  intro hr
  have h0 : V.Z = V.T := hr 0 (by decide)
  cases h0

end ZClock

#print axioms ZClock.clock_tick_refines
#print axioms ZClock.zand_Z_left_ne_T
#print axioms ZClock.open_window_blocks
#print axioms ZClock.closed_window_stays
#print axioms ZClock.run_refines
#print axioms ZClock.permit_survives_clock
#print axioms ZClock.only_revocation_takes_back
#print axioms ZClock.revocation_breaks_hereditary
