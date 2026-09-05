/-
  ZFlow.lean — E52: INFORMATION FLOW — DENNING'S LATTICE AS THE COMMON
  TARGET, AND THREE POSITIONS ON DECLASSIFICATION.

  THE TRADITION. Denning (1976), "A lattice model of secure information
  flow": security classes form a lattice; the class of a computed value is
  the JOIN of the classes of its operands; a flow from a to b is permitted
  iff class(a) ⊑ class(b). Perl's taint mode (perlsec): a value derived from
  any tainted input is tainted; tainted data may not reach a sink (a shell,
  a file, a process); "the only way to bypass the tainting mechanism is by
  referencing subpatterns from a regular expression match" — a FUNCTION
  clears the bit. TaintDroid runs the same bit through a phone. §1 lists the
  three together as the third tradition: "a distrust mark flows through
  computations, and only an explicit check sanitizes". `ZTaint` (E40) proved
  the laundering ban in ZTL's own terms; by §1's ceiling that is a worked
  case, not an embedding. This file is the embedding — the sixth and last.

  THE COMMON TARGET. Denning's lattice is formalised in its two-point
  fragment `Lvl = L ⊑ H` (untainted ⊑ tainted), with its join proved a
  lattice join (`decide`). Perl's datum and ZTL's element are both mapped
  INTO it, and the propagation of each is proved to be Denning's join:
  Perl's operations (`lvl_perlOp`), ZTL's pointwise functions on pedigreed
  elements (`lvl_taint`, E7's `taint`) and ZTL's `+ −` on marked integers
  (`lvl_zadd`, `lvl_zsub`). Denning's flow check to a low sink is the T-sign
  of ZTL's "verified" atom (`sink_signT`): once more the boundary is a sign.

  WHAT IS PROVED, and where the three part — the point of the file:

    DECLASSIFICATION. Denning's rule never lowers a class: join only goes
    up (`join_absorbs_H`). Perl lowers it BY CONVENTION: `regexCapture`
    clears the bit while its payload still depends on the tainted input
    (`perl_launders`) — a flow the lattice forbids, sanctioned by the
    language. ZTL lowers it BY PROOF or not at all: no pointwise function
    clears a mark (`no_laundering_mark`, E40, re-stated here in the
    lattice), and the one place ZTL's `×` returns a clean value from a
    marked operand — `0 · mark = 0` — is the place the value is FORCED for
    every reading (`zero_forced : ∀ n, 0 * n = 0`): no information about the
    mark flows, so nothing is declassified; Denning's syntactic join still
    says H there (`denning_overtaints_forced`). Two rules, two readings of
    one cell: the lattice tracks dependence in the SYNTAX, ZTL earns
    independence in the VALUE.

  WHAT IS NOT DONE. Multi-level lattices (the general Denning model), implicit
  flows through control (Denning's program-counter label; Perl tracks data
  only), TaintDroid's sources and sinks: not modelled. The two-point lattice
  and explicit data flow — one algebraic core, the sixth. With it every one
  of §1's six traditions has a formalised semantics and a theorem placing
  ZTL's verdict inside it.

  FORM. All match cells explicit; `∀` over `Lvl` gets its own Decidable
  instance; `Int.zero_mul` carries propext (measured), so `zero_forced` is proved
  by cases on `Int` with `Nat.zero_mul`.
-/
import ZTaint
import ZNaN

namespace ZFlow

open V
open ZNaN

/-! ### Denning's lattice, two points -/

/-- Security classes: low (untainted) and high (tainted). -/
inductive Lvl where
  | L | H
  deriving DecidableEq, Repr

instance (p : Lvl → Prop) [DecidablePred p] : Decidable (∀ x : Lvl, p x) :=
  decidable_of_iff (p Lvl.L ∧ p Lvl.H)
    ⟨fun ⟨a, b⟩ x => match x with | Lvl.L => a | Lvl.H => b,
     fun h => ⟨h Lvl.L, h Lvl.H⟩⟩

/-- The class of a computed value: the join of its operands' classes. -/
def join : Lvl → Lvl → Lvl
  | Lvl.L, Lvl.L => Lvl.L | Lvl.L, Lvl.H => Lvl.H
  | Lvl.H, Lvl.L => Lvl.H | Lvl.H, Lvl.H => Lvl.H

/-- The flow relation: L flows anywhere, H only to H. -/
def le : Lvl → Lvl → Bool
  | Lvl.L, Lvl.L => true  | Lvl.L, Lvl.H => true
  | Lvl.H, Lvl.L => false | Lvl.H, Lvl.H => true

/-- A flow into an object of class `b` is permitted iff the source flows to it. -/
def flowOK (a b : Lvl) : Bool := le a b

/-- **`join` IS A LATTICE JOIN** on the two points: commutative, associative,
idempotent, the least upper bound for `le`. -/
theorem join_comm  : ∀ a b, join a b = join b a := by decide
theorem join_assoc : ∀ a b c, join (join a b) c = join a (join b c) := by decide
theorem join_idem  : ∀ a, join a a = a := by decide
theorem join_lub   : ∀ a b c, le (join a b) c = (le a c && le b c) := by decide
/-- Denning's rule never lowers a class. -/
theorem join_absorbs_H : ∀ a, join a Lvl.H = Lvl.H ∧ join Lvl.H a = Lvl.H := by decide

/-! ### Perl's taint mode, as perlsec states it -/

/-- A Perl scalar: a payload with a taint bit. -/
inductive Datum where
  | clean : Nat → Datum
  | dirty : Nat → Datum
  deriving DecidableEq, Repr

def lvlP : Datum → Lvl
  | Datum.clean _ => Lvl.L
  | Datum.dirty _ => Lvl.H

def payload : Datum → Nat
  | Datum.clean n => n
  | Datum.dirty n => n

/-- "Any value derived from a tainted value is tainted." -/
def perlOp (f : Nat → Nat → Nat) : Datum → Datum → Datum
  | Datum.clean a, Datum.clean b => Datum.clean (f a b)
  | Datum.clean a, Datum.dirty b => Datum.dirty (f a b)
  | Datum.dirty a, Datum.clean b => Datum.dirty (f a b)
  | Datum.dirty a, Datum.dirty b => Datum.dirty (f a b)

/-- A sink — a shell, a file, a process — accepts untainted data only. -/
def perlSink : Datum → Bool
  | Datum.clean _ => true
  | Datum.dirty _ => false

/-- "The only way to bypass the tainting mechanism": a regular-expression
capture returns the matched substring UNTAINTED. Here: the payload,
unchanged, with the bit cleared. -/
def regexCapture : Datum → Datum
  | Datum.clean n => Datum.clean n
  | Datum.dirty n => Datum.clean n

/-- **PERL'S PROPAGATION IS DENNING'S JOIN.** -/
theorem lvl_perlOp (f : Nat → Nat → Nat) :
    ∀ x y, lvlP (perlOp f x y) = join (lvlP x) (lvlP y)
  | Datum.clean _, Datum.clean _ => rfl
  | Datum.clean _, Datum.dirty _ => rfl
  | Datum.dirty _, Datum.clean _ => rfl
  | Datum.dirty _, Datum.dirty _ => rfl

/-- Perl's sink is Denning's flow check into a low object. -/
theorem perlSink_flow : ∀ x, perlSink x = flowOK (lvlP x) Lvl.L
  | Datum.clean _ => rfl
  | Datum.dirty _ => rfl

/-- **PERL LAUNDERS BY CONVENTION.** The capture lowers H to L while its
payload is exactly the tainted input's — a flow the lattice forbids
(`le H L = false`), sanctioned by the language. -/
theorem perl_launders (n : Nat) :
    lvlP (regexCapture (Datum.dirty n)) = Lvl.L
  ∧ payload (regexCapture (Datum.dirty n)) = payload (Datum.dirty n)
  ∧ le (lvlP (Datum.dirty n)) (lvlP (regexCapture (Datum.dirty n))) = false := ⟨rfl, rfl, rfl⟩

/-! ### ZTL's elements and quantities, into the same lattice -/

/-- The class of a pedigreed element (E7): verified is low, a mark is high. -/
def lvlE : El → Lvl
  | El.v _ => Lvl.L
  | El.z _ => Lvl.H

/-- The class of a marked integer (§15, bare mode). -/
def lvlQ : ZQ → Lvl
  | ZQ.val _ => Lvl.L
  | ZQ.mark  => Lvl.H

/-- **A POINTWISE FUNCTION IS DENNING'S JOIN WITH A LOW OPERAND**: the class
of `f(x)` is the class of `x`. -/
theorem lvl_taint (f : Nat → Nat) : ∀ x, lvlE (taint f x) = join (lvlE x) Lvl.L
  | El.v _ => rfl
  | El.z _ => rfl

/-- **`+` AND `−` ON MARKED INTEGERS ARE DENNING'S JOIN.** -/
theorem lvl_zadd : ∀ x y, lvlQ (zadd x y) = join (lvlQ x) (lvlQ y)
  | ZQ.val _, ZQ.val _ => rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

theorem lvl_zsub : ∀ x y, lvlQ (zsub x y) = join (lvlQ x) (lvlQ y)
  | ZQ.val _, ZQ.val _ => rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-- The "verified" atom of an element: T on a verified value, the mark on a
mark. -/
def isVer : El → V
  | El.v _ => T
  | El.z _ => Z

/-- **THE SINK IS A SIGN.** Denning's flow check into a low object is `SignT`
of ZTL's "verified" atom — refuse unless earned. -/
theorem sink_signT : ∀ x, flowOK (lvlE x) Lvl.L = SignT (isVer x)
  | El.v _ => rfl
  | El.z _ => rfl

/-! ### Declassification: never / by convention / by proof -/

/-- **ZTL LAUNDERS BY NO FUNCTION.** E40's ban, in the lattice: whatever
chain of pointwise functions is applied to a mark, its class stays H. -/
theorem ztl_no_laundering (fs : List (Nat → Nat)) (i : Nat) :
    lvlE (ZTaint.taints fs (El.z i)) = Lvl.H :=
  match ZTaint.no_laundering fs i with
  | ⟨_, hj⟩ => by rw [hj]; rfl

/-- The one clean value ZTL's `×` returns from a marked operand… -/
theorem ztl_clears_forced : lvlQ (zmul (ZQ.val 0) ZQ.mark) = Lvl.L := rfl

/-- …is the value FORCED for every reading of the mark: nothing about the
mark flows into it, so nothing is declassified. -/
theorem zero_forced : ∀ n : Int, 0 * n = 0
  | Int.ofNat m => by
      show Int.ofNat (0 * m) = Int.ofNat 0
      rw [Nat.zero_mul]
  | Int.negSucc m => by
      show Int.negOfNat (0 * Nat.succ m) = Int.ofNat 0
      rw [Nat.zero_mul]
      rfl

/-- **DENNING'S SYNTACTIC JOIN OVER-TAINTS THE FORCED CELL.** The lattice
says H where the value provably does not depend on the mark; ZTL earns L.
Two rules, two readings of one cell: dependence in the syntax against
independence in the value. -/
theorem denning_overtaints_forced :
    join (lvlQ (ZQ.val 0)) (lvlQ ZQ.mark) = Lvl.H ∧ lvlQ (zmul (ZQ.val 0) ZQ.mark) = Lvl.L := ⟨rfl, rfl⟩

/-- Off the forced cell, ZTL's `×` is Denning's join too. -/
theorem lvl_zmul_nonzero (a : Int) (h : decide (a = 0) = false) :
    lvlQ (zmul (ZQ.val a) ZQ.mark) = join (lvlQ (ZQ.val a)) (lvlQ ZQ.mark) := by
  show lvlQ (match decide (a = 0) with | true => ZQ.val 0 | false => ZQ.mark) = Lvl.H
  rw [h]
  rfl

theorem lvl_zmul_vals (a b : Int) :
    lvlQ (zmul (ZQ.val a) (ZQ.val b)) = join (lvlQ (ZQ.val a)) (lvlQ (ZQ.val b)) := rfl

end ZFlow

#print axioms ZFlow.join_lub
#print axioms ZFlow.join_absorbs_H
#print axioms ZFlow.lvl_perlOp
#print axioms ZFlow.perlSink_flow
#print axioms ZFlow.perl_launders
#print axioms ZFlow.lvl_taint
#print axioms ZFlow.lvl_zadd
#print axioms ZFlow.lvl_zsub
#print axioms ZFlow.sink_signT
#print axioms ZFlow.ztl_no_laundering
#print axioms ZFlow.ztl_clears_forced
#print axioms ZFlow.zero_forced
#print axioms ZFlow.denning_overtaints_forced
#print axioms ZFlow.lvl_zmul_nonzero
#print axioms ZFlow.lvl_zmul_vals
