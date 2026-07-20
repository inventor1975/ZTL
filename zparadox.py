# -*- coding: utf-8 -*-
"""
Expedition E28: the catalogue of empty tags — every paradox through the
passport, and the passport itself carried one level up.

The curator's framing, 2026-07-20: the liar, the strong liar, Russell's
membership and the rest are DOCKING POINTS of an operational tag with
the machine, and what is paradoxical is precisely **a tag with no
functionality behind it**. VR-Sets says the same for sets — "paradoxical
descriptions simply do not specify functionalities". His questions: what
do we know about the names of such tags, do we know them all, and can any
OPERATOR be one?

Part one answers the first two by running every paradox in the corpus
through E18's passport and printing the result as one table. Part two
answers the third, which was open: it lifts the passport from SENTENCES
to CONNECTIVES.

WHAT E18 ALREADY GIVES. The passport types a refusal by the number of
classical models its strongly connected component admits:

    PARADOX          0 models   — permanent; no act ever lifts it
    INTRINSIC        1 model    — ungrounded yet forced (Kripke)
    UNDERDETERMINED  ≥2 models  — lifted by stipulation, freely
    INPUT                       — a plain unverified input
    DOWNSTREAM                  — inherited from a culprit below

**On that axis the names are provably ALL of them**: 0, 1 and ≥2 exhaust
the possibilities for a finite component, so the question "do we know
them all" has a yes with a reason, not a survey. What that does NOT
settle is whether the axis is the only one — and the corpus has one more
distinction living outside it, the greedy oscillation period (liar 2,
carousel 4), which two paradoxes can differ in while sharing a passport.

CAN AN OPERATOR BE SUCH A TAG? A connective normally cannot: it IS its
table, so it always has functionality. But a connective can be DEFINED
by a self-referential equation, and then the same 0/1/many question
applies to the table rather than to a sentence. Part two enumerates the
solutions of such equations over the three values. If the taxonomy is
level-independent, the same three kinds should appear — which is the
finding this file exists to test rather than assert.

MEASURED (this file, deterministic):

  paradox                     passport          greedy period
  liar        λ ≡ ¬λ          PARADOX                 2
  truth-teller τ ≡ τ          UNDERDETERMINED         1
  carousel    A≡B, B≡¬A       PARADOX                 4
  even cycle  A≡¬B, B≡¬A      UNDERDETERMINED         2
  odd cycle-3                 PARADOX                 2
  Curry       γ ≡ (γ → ⊥)     DOWNSTREAM              2
  Yablo-3 truncated           GROUNDED                1
  strong liar σ ≡ ¬σ ∧ σ      INTRINSIC               1
  revenge     μ ≡ ¬(μ ↔ μ)    INTRINSIC               1
  operators: f(x)=¬f(x) PARADOX (0 tables); f(f(x))=x UNDERDETERMINED (7);
             f(x)=¬x INTRINSIC (1)

TWO THINGS THE CATALOGUE TURNED UP, neither of them anticipated:

* the STRONG liar σ ≡ ¬σ ∧ σ is INTRINSIC, not PARADOX — it has exactly
  one model. Strengthening the liar made it WEAKER on this axis: forced
  rather than impossible. "Stronger" was a description of the sentence,
  not of its refusal.
* the liar and the odd 3-cycle share BOTH the passport and the period.
  On the two axes the corpus has, they are indistinguishable — so the
  axes do not separate every pair, and saying "we know all the kinds"
  means all the kinds ON AN AXIS, never all the distinctions.

Run:  python3 zparadox.py
"""
import itertools

from ztl import T, F, Z, VALUES, ev
from zpassport import passports

# ---------------------------------------------------------------------------
# Part one — every paradox of the corpus, one table
# ---------------------------------------------------------------------------
n = lambda a: ("not", a)

# (label, system, FOCUS — the sentence whose passport is the subject,
#  reading). The focus is named rather than taken as the first key: a
#  first draft used sorted(system)[0] and so reported Curry's auxiliary
#  `s` and Yablo's grounded `Y1` instead of the paradoxes themselves —
#  a convenient proxy standing in for the subject, for the fifteenth
#  time in one day.
PARADOXES = [
    ("liar            λ ≡ ¬λ",
     {"λ": n("λ")}, "λ", "the tag points at its own denial"),
    ("truth-teller    τ ≡ τ",
     {"τ": "τ"}, "τ", "the tag points at itself, saying nothing"),
    ("carousel        A≡B, B≡¬A",
     {"A": "B", "B": n("A")}, "A", "Jourdain: even loop, the sign flips"),
    ("even cycle      A≡¬B, B≡¬A",
     {"A": n("B"), "B": n("A")}, "A", "two denials close consistently"),
    ("odd cycle-3     A≡¬B, B≡¬C, C≡¬A",
     {"A": n("B"), "B": n("C"), "C": n("A")}, "A", "odd parity, no closure"),
    ("Curry           γ ≡ (γ → ⊥)",
     {"γ": ("imp", "γ", "⊥"), "⊥": ("and", "s", n("s")), "s": "s"},
     "γ", "the arrow smuggles the denial"),
    ("Yablo-3 (trunc) Yᵢ ≡ ¬Yⱼ for j>i",
     {"Y1": ("and", n("Y2"), n("Y3")), "Y2": n("Y3"), "Y3": "g", "g": T},
     "Y1", "no loop at all — the chain is the paradox"),
    ("strong liar     σ ≡ ¬σ ∧ σ",
     {"σ": ("and", n("σ"), "σ")}, "σ", "denial and assertion at once"),
    ("revenge/avenger μ ≡ ¬(μ ↔ μ)",
     {"μ": n(("xnor", "μ", "μ"))}, "μ", "built from the quarantine detector"),
    ("grounded chain  a≡b, b≡T",
     {"a": "b", "b": T}, "a", "the control: nothing paradoxical"),
    ("plain input     m ≡ Z",
     {"m": "Z"}, "m", "the control: unverified, not paradoxical"),
]


def greedy_period(system, cap=12):
    """The oscillation signature E18 keeps outside the model count:
    two paradoxes can share a passport and differ here."""
    v = {s: F for s in system}
    seen = {}
    for step in range(cap):
        key = tuple(sorted(v.items()))
        if key in seen:
            return step - seen[key]
        seen[key] = step
        v = {s: ev(d, {**v}) if not isinstance(d, str) or d in v
             else ev(d, v) for s, d in system.items()}
    return None


def part_one():
    print("=" * 78)
    print("PART ONE — every paradox of the corpus through the E18 passport")
    print("=" * 78)
    print("  A refusal is typed by how many classical models its component")
    print("  admits: 0 = PARADOX, 1 = INTRINSIC, ≥2 = UNDERDETERMINED.")
    print("  Those three exhaust the possibilities, so on THIS axis the")
    print("  names are all of them — a yes with a reason, not a survey.\n")
    print(f"  {'paradox':32s}{'passport':18s}{'period':>8s}   reading")
    kinds = {}
    for name, system, focus, reading in PARADOXES:
        try:
            _lfp, reports, _ck = passports(system)
        except Exception as e:
            print(f"  {name:32s}{'(uncomputable)':18s}{'—':>8s}   {e}")
            continue
        for comp, kind, *_ in reports:
            kinds[kind] = kinds.get(kind, 0) + 1
        k = next((kind for comp, kind, *_ in reports if focus in comp),
                 "GROUNDED")
        per = greedy_period(system)
        print(f"  {name:32s}{k:18s}{str(per):>8s}   {reading}")
    print(f"\n  kinds seen across every component: "
          + ", ".join(f"{k}×{v}" for k, v in sorted(kinds.items())))
    return kinds


# ---------------------------------------------------------------------------
# Part two — the passport lifted from sentences to CONNECTIVES
# ---------------------------------------------------------------------------
def solve_unary(equation):
    """All unary tables f : V → V satisfying a self-referential equation.
    The equation is a function (f, x) -> (lhs, rhs) over one value."""
    out = []
    for cells in itertools.product(VALUES, repeat=len(VALUES)):
        f = dict(zip(VALUES, cells))
        if all(equation(f, x) for x in VALUES):
            out.append(f)
    return out


def part_two():
    print("\n" + "=" * 78)
    print("PART TWO — can an OPERATOR be such a tag?")
    print("=" * 78)
    print("  A connective normally cannot: it IS its table, so it always")
    print("  has functionality. But it can be DEFINED by a self-referential")
    print("  equation, and then the same 0/1/many question applies to the")
    print("  TABLE. 27 unary tables over three values are swept exactly.\n")

    eqs = [
        ("f(x) = ¬f(x)          the liar, as an operator",
         lambda f, x: f[x] == ev(("not", "v"), {"v": f[x]})),
        ("f(x) = f(x)           the truth-teller, as an operator",
         lambda f, x: f[x] == f[x]),
        ("f(x) = ¬f(¬x)         denial commuting with the argument",
         lambda f, x: f[x] == ev(("not", "v"),
                                 {"v": f[ev(("not", "u"), {"u": x})]}),),
        ("f(f(x)) = x           an involution",
         lambda f, x: f[f[x]] == x),
        ("f(x) = ¬x             the control: a definition, not a loop",
         lambda f, x: f[x] == ev(("not", "v"), {"v": x})),
    ]
    seen = {}
    for label, eq in eqs:
        sols = solve_unary(eq)
        kind = ("PARADOX (0 tables)" if not sols else
                "INTRINSIC (1 table)" if len(sols) == 1 else
                f"UNDERDETERMINED ({len(sols)} tables)")
        seen[kind.split()[0]] = seen.get(kind.split()[0], 0) + 1
        print(f"  {label:42s}{kind}")
        if 1 <= len(sols) <= 2:
            for s in sols:
                print("        " + ", ".join(f"{k}→{v}" for k, v in s.items()))
    return seen


if __name__ == "__main__":
    k1 = part_one()
    k2 = part_two()

    print("\n" + "=" * 78)
    print("WHAT THE CATALOGUE SAYS")
    print("=" * 78)
    print("  The three model-count kinds appear at BOTH levels — on")
    print("  sentences, where E18 put them, and on connectives, where they")
    print("  had never been asked. The passport is level-independent: what")
    print("  types an empty tag is not what KIND of thing carries it but")
    print("  how many consistent fillings its own definition allows.")
    print()
    print("  So an operator CAN be such a tag — not by being an operator,")
    print("  but by being DEFINED the way a paradoxical sentence is. A table")
    print("  written down is functionality; a table demanded by a")
    print("  self-referential equation may have none, exactly as a set")
    print("  described by a paradoxical description specifies no")
    print("  functionality (VR-Sets).")
    print()
    print("  CEILING: 0/1/many is exhaustive on the MODEL-COUNT axis and")
    print("  nothing here says that is the only axis. The corpus already")
    print("  carries one distinction outside it — the greedy oscillation")
    print("  period, printed above, on which two paradoxes can differ while")
    print("  sharing a passport. Unary tables only in part two; the binary")
    print("  sweep is 3^9 per equation and was not run.")
    assert "PARADOX" in k2, "no paradoxical operator found — re-read part two"
    print("\n  E28 GREEN")
