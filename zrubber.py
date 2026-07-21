# -*- coding: utf-8 -*-
"""
zrubber — E35: the RUBBER SEAM ENGINE. One mechanism, sixteen seams.

The seam of E29 was one seam — the ∧ seam, "join iff jointly warranted".
The curator's next move: the request itself names the operator. A pairwise
seam joins two warranted claims with ONE lifted binary connective, chosen
from a CLOSED, FINITE set — the sixteen of §3.8 — so the engine cannot be
handed "a list of a million" and cannot fall; anything outside the sixteen
is turned away with a reason code, not a crash. The request is unverified
input, and the sixteen are the customs.

The rubber has a spine: **a seam is TYPED BY ITS OPERATOR.** "Sewn" by ∧
means "jointly earned"; "sewn" by ↔ means "the verdicts concur"; "sewn" by
∨ means "at least one holds". These are different claims, and the passport
records WHICH operator sewed, so an ↔ seam is never read as an ∧ seam.
This is where the old bug dissolves: ↔ was never wrong — reading its answer
as ∧'s answer was. The cell (F,F) — two earned-negatives — is not joint
warrant (∧ rejects it) but is genuine concordance (↔ accepts it, and says
so honestly).

Zero-trust applied to the engine itself: it does not FORBID the excessive
or "killer" seam a researcher wants to build — it MARKS it. The passport
diagnoses each operator's character, including the ZTL-native one:

    sews_on_credit — does this operator return T where NEITHER side is
                     earned (both non-T)? ∧ never does; ↔, →, ↑, ⊤ do.
                     A seam that sews on credit grants meaning neither
                     claim paid for — the knife's edge, always labelled.

Three layers (A. Miteiko's typed spec): (1) admissibility — is the operator
in the sixteen, do the certificates compare; (2) warrant under the chosen
operator — SEWN / CONTRADICTION / CANNOT with a reason code; (3) structural
relation — the entailment annotation, a directed graph over an otherwise
symmetric join. Lean is deliberately NOT started: the object is still being
specified.

Run:  python3 zrubber.py
"""
import os
import sys
from itertools import product

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, VALUES, CLASSICAL, lift2, ev           # noqa: E402
from entailment import entails                                 # noqa: E402

# ---- the sixteen lifted binary connectives, a closed finite enum ----------
_INKEYS = [(T, T), (T, F), (F, T), (F, F)]     # classical input corners
_NAMES = {
    (T, F, F, F): "∧", (T, T, T, F): "∨", (F, T, T, F): "⊕", (T, F, F, T): "↔",
    (T, F, T, T): "→", (T, T, F, T): "←", (F, T, F, F): "↛", (F, F, T, F): "↚",
    (F, T, T, T): "↑", (F, F, F, T): "↓", (F, F, F, F): "⊥", (T, T, T, T): "⊤",
    (T, T, F, F): "A", (T, F, T, F): "B", (F, F, T, T): "¬A", (F, T, F, T): "¬B",
}


def _op_from_bits(bits):
    tbl = dict(zip(_INKEYS, bits))
    return lift2(lambda a, b: tbl[(a, b)])


OPS = {name: _op_from_bits(bits) for bits, name in _NAMES.items()}
_BITS = {name: bits for bits, name in _NAMES.items()}


# ---- operator CHARACTER (menu-level, precomputed once per operator) --------
def reads_both(op):
    ra = any(op(a1, b) != op(a2, b)
             for b in CLASSICAL for a1 in CLASSICAL for a2 in CLASSICAL)
    rb = any(op(a, b1) != op(a, b2)
             for a in CLASSICAL for b1 in CLASSICAL for b2 in CLASSICAL)
    return ra and rb


def sews_FF(op):
    """Does the operator sew two earned-negatives? (concordance, not warrant)"""
    return op(F, F) == T


def sews_on_credit(op):
    """Does it return T where NEITHER side is earned (both non-T)? The
    zero-trust signature of a seam: does it grant meaning on credit?"""
    return any(op(a, b) == T for a in VALUES for b in VALUES
               if a != T and b != T)


def character(name):
    op = OPS[name]
    return {"reads_both": reads_both(op),
            "sews_FF": sews_FF(op),
            "sews_on_credit": sews_on_credit(op)}


# ---------------------------------------------------------------------------
class Claim:
    """A party's submission: a formula and a marking (atom → T/F/Z)."""
    def __init__(self, formula, marking):
        self.formula = formula
        self.marking = dict(marking)


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi in VALUES:
            return acc
        acc.add(phi)
    else:
        for s in phi[1:]:
            _atoms(s, acc)
    return acc


def _refinements(marking):
    """All ways to resolve the marks (Z) of a marking to classical T/F."""
    marks = [a for a, v in marking.items() if v == Z]
    if not marks:
        yield dict(marking)
        return
    for combo in product(CLASSICAL, repeat=len(marks)):
        m = dict(marking)
        m.update(dict(zip(marks, combo)))
        yield m


def seam(A, B, op_name):
    """The rubber seam. Returns a typed passport (dict). The three layers of
    the spec are its sections; the operator's character is stamped on every
    passport, whatever the status."""
    p = {"operator": op_name}

    # ---- layer 1: admissibility ------------------------------------------
    if op_name not in OPS:
        p.update(status="CANNOT", reason="unsupported_operator",
                 reading=f"{op_name!r} is not one of the sixteen lifted "
                         f"connectives; the request is turned away, not run")
        return p
    op = OPS[op_name]
    p["character"] = character(op_name)

    # ground clash: a shared leaf verified two incompatible classical ways
    shared = A.marking.keys() & B.marking.keys()
    clash = {k for k in shared
             if A.marking[k] != B.marking[k]
             and Z not in (A.marking[k], B.marking[k])}
    if clash:
        p.update(status="CONTRADICTION", reason="grounds",
                 leaves={k: (A.marking[k], B.marking[k]) for k in sorted(clash)},
                 reading="the same leaf is verified two ways; no operator can "
                         "repair that, and none is consulted")
        return p

    merged = {**A.marking, **B.marking}
    for k in shared:                         # prefer a verified value over a mark
        merged[k] = A.marking[k] if A.marking[k] != Z else B.marking[k]

    # ---- layer 2: warrant under the chosen operator ----------------------
    vA, vB = ev(A.formula, merged), ev(B.formula, merged)
    v = op(vA, vB)
    p["verdict"] = v
    p["sides"] = (vA, vB)

    # warranty of the seam: is its verdict hereditary (stable under every
    # resolution of the remaining marks)?
    seam_vals = {op(ev(A.formula, m), ev(B.formula, m))
                 for m in _refinements(merged)}
    if v == T and seam_vals == {T}:
        p["warranty"] = "hereditary"
    elif v == T:
        p["warranty"] = "until-verification"   # sewn now, on credit
    else:
        p["warranty"] = "—"

    # ---- layer 3: structural relation (marking-free entailment) ----------
    ab = entails([A.formula], B.formula) is None
    ba = entails([B.formula], A.formula) is None
    p["direction"] = ("A≡B" if ab and ba else "A⊨B" if ab
                      else "B⊨A" if ba else "incomparable")

    # ---- status ----------------------------------------------------------
    if v == T:
        p.update(status="SEWN",
                 reading=f"the {op_name}-claim is earned under the merged "
                         f"marking; sewn AS {op_name}, not as ∧ unless "
                         f"{op_name} is ∧")
    elif vA != vB and Z not in (vA, vB):
        p.update(status="CONTRADICTION", reason="derivation",
                 reading="both sides answered and their verdicts conflict; the "
                         "clash is in what was concluded, not in the grounds")
    elif Z in (vA, vB):
        p.update(status="CANNOT", reason="mark_reached",
                 unverified=sorted(k for k, x in merged.items() if x == Z),
                 reading="a mark reached the join: sewing is denied on credit, "
                         "not refused — nobody spoke against, somebody did not "
                         "speak")
    else:
        p.update(status="CANNOT", reason="verified_unmet",
                 reading=f"both sides are verified and agree, yet the "
                         f"{op_name}-claim is not met (e.g. neither holds for "
                         f"∨): a definite no, without conflict")
    return p


def show(p):
    op = p["operator"]
    print(f"    operator {op:>2} → {p['status']}"
          + (f" ({p.get('reason')})" if p.get("reason") else ""))
    if "character" in p:
        c = p["character"]
        tags = []
        if not c["reads_both"]:
            tags.append("IGNORES ONE SIDE")
        if c["sews_FF"]:
            tags.append("sews (F,F)=concordance")
        if c["sews_on_credit"]:
            tags.append("SEWS ON CREDIT")
        desc = ", ".join(tags) if tags else "reads both; never on credit"
        print(f"         character: {desc}")
    if p["status"] == "SEWN":
        print(f"         verdict {p['verdict']}, warranty {p['warranty']}, "
              f"{p['direction']}")
    elif "reading" in p:
        print(f"         {p['reading']}")


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    print("=" * 76)
    print("E35 — THE RUBBER SEAM ENGINE: one mechanism, sixteen seams")
    print("=" * 76)

    # ---- the menu: all sixteen with their character ----------------------
    print("\n### The closed menu of sixteen (the operator field is an enum)")
    print(f"    {'op':>3}  reads_both  sews(F,F)  sews_on_credit")
    joiners = credit = 0
    for name in ["∧", "∨", "⊕", "↔", "→", "←", "↛", "↚",
                 "↑", "↓", "A", "B", "¬A", "¬B", "⊤", "⊥"]:
        c = character(name)
        if c["reads_both"]:
            joiners += 1
        if c["sews_on_credit"]:
            credit += 1
        print(f"    {name:>3}  {str(c['reads_both']):>10}  "
              f"{str(c['sews_FF']):>9}  {str(c['sews_on_credit']):>14}")
    print(f"\n    {joiners} of 16 genuinely read BOTH claims (the rest are "
          f"projections/constants);")
    print(f"    {credit} of 16 can sew ON CREDIT (T with neither side earned).")
    print("    ∧ is the one zero-trust joiner: reads both, never on credit.")

    # ---- demonstrations --------------------------------------------------
    print("\n### Seams, typed by operator")

    print("\n  ∧ — the joint-warrant seam (reference). Two earned claims:")
    show(seam(Claim("p", {"p": T}), Claim("q", {"q": T}), "∧"))

    print("\n  ∧ on two earned-NEGATIVES (¬p, ¬q both F) — NOT jointly warranted:")
    show(seam(Claim(("not", "p"), {"p": T}), Claim(("not", "q"), {"q": T}), "∧"))

    print("\n  ↔ on the SAME two earned-negatives — concordance, honestly typed:")
    show(seam(Claim(("not", "p"), {"p": T}), Claim(("not", "q"), {"q": T}), "↔"))
    print("       ← the old bug: reading THIS as an ∧ seam. The passport says")
    print("         'sews (F,F)=concordance' and 'SEWS ON CREDIT' — labelled.")

    print("\n  ∨ — the quorum seam. One side holds, one does not:")
    show(seam(Claim("p", {"p": T}), Claim("q", {"q": F}), "∨"))

    print("\n  A — a degenerate 'seam' that ignores the second claim:")
    show(seam(Claim("p", {"p": T}), Claim("q", {"q": F}), "A"))

    print("\n  ⊤ — the killer: sews anything, on pure credit:")
    show(seam(Claim("p", {"p": F}), Claim("q", {"q": F}), "⊤"))
    print("       ← the engine does NOT refuse it; it stamps 'SEWS ON CREDIT'.")

    print("\n  ground clash — the same leaf verified both ways:")
    show(seam(Claim("p", {"p": T}), Claim("p", {"p": F}), "∧"))

    print("\n  a mark reaches an ∧ seam — CANNOT, on credit:")
    show(seam(Claim("p", {"p": Z}), Claim("q", {"q": T}), "∧"))

    print("\n  an unsupported operator — turned away with a reason, not a crash:")
    show(seam(Claim("p", {"p": T}), Claim("q", {"q": T}), "NAND3000"))

    # ---- the robust facts, asserted --------------------------------------
    print("\n" + "=" * 76)
    print("THE CONTRACT, ASSERTED")
    print("=" * 76)
    assert len(OPS) == 16, "the operator enum is not the closed sixteen"
    assert not character("∧")["sews_on_credit"], "∧ sewed on credit"
    assert character("↔")["sews_FF"] and character("↔")["sews_on_credit"], \
        "↔ lost its concordance/credit character"
    assert seam(Claim("p", {"p": T}), Claim("q", {"q": T}),
                "nonsense")["status"] == "CANNOT", "bad operator was not refused"
    assert seam(Claim("p", {"p": T}), Claim("p", {"p": F}),
                "∧")["status"] == "CONTRADICTION", "ground clash not caught"
    # the (F,F) cell: ∧ refuses, ↔ sews — the dissolved bug, both honest
    ff_and = seam(Claim(("not", "p"), {"p": T}),
                  Claim(("not", "q"), {"q": T}), "∧")
    ff_xnor = seam(Claim(("not", "p"), {"p": T}),
                   Claim(("not", "q"), {"q": T}), "↔")
    assert ff_and["status"] != "SEWN" and ff_xnor["status"] == "SEWN", \
        "the ∧/↔ split on (F,F) moved"
    print("  16 closed · ∧ never on credit · ↔ typed as concordance ·")
    print("  bad operator refused (not crashed) · ground clash caught ·")
    print("  (F,F): ∧ refuses, ↔ sews — one cell, two honest answers.")
    print("\n  ZRUBBER GREEN — one engine, sixteen seams, every one labelled.")
