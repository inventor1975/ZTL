# -*- coding: utf-8 -*-
"""
Expedition E29: the seam — a decentralised ZTL, and the three answers a
kernel is allowed to give.

The curator's design, 2026-07-20. Today's ZTL is centralised: one engine
takes a formula and a marking and returns a verdict. He wants meanings
joined at the level of the logic instead — kernel A settles one
formulation, kernel B settles another, and they arrive at a third kernel
which must join them. His candidate for the joint was ⊕ and ↔, "because
it tears at once if the meaning comes apart, and if it glues, then in
later gluings the illogicality falls off first".

Measured, and both halves of that hold, for reasons worth stating:

**Why the PAIR and not one of them.** Verdicts in ZTL are always
two-valued, so a joint sees only T and F, where ⊕ = ¬↔ exactly — one
channel would do. The second channel earns its wire only where the
classical identity FAILS, at the mark. The pair separates three cases
where either alone separates two:

    (↔, ⊕) = (T, F)   the kernels agree            → sew
    (↔, ⊕) = (F, T)   both answered, and disagree   → contradiction (σ)
    (↔, ⊕) = (F, F)   a mark reached the joint      → cannot sew (E)
    (T, T)            impossible

So the second wire exists because ZTL dropped `xor = ¬xnor` — one of the
fourteen fallen laws turns out to be load-bearing for federation. In
classical logic this pair would carry the same bit twice.

**Why the thread does not tear.** On verdicts, ↔ is an equivalence
relation — reflexive, symmetric and TRANSITIVE — so a chain of agreements
cannot hide a disagreement. And durability is not a property of the
connective but of the WARRANTY: measured here, hereditary ⊗ hereditary is
hereditary in 324 of 324 pairs. A seam of two unbreakable verdicts is
unbreakable; a seam involving an until-verification verdict can come
apart at a later verification, in 800 of 900 pairs measured. The
shortest such pair, found by search: A = ¬p and B = ¬q. Both read F
right now — ¬Z = F on each — so they AGREE and the seam is legitimately
made; but they agree by default deny rather than by fact, and verifying
q := F turns B to T and unpicks it.

That last is the curator's own scenario — "seam 1.1 came away from 1.2
after seam 2 arrived, so the sewing was illegitimate". The precise
statement is sharper: **the sewing was not illegitimate; treating a
revocable seam as final was.** The demonstration below runs exactly that
history, and the machine's own sharpest example of it is `p` sewn to
`p` — the same claim to itself — which is torn while `p` is unverified,
because Z↔Z = F.

THE KERNEL'S CONTRACT — three answers and no more (curator):
    SEWN            joining is possible; here is the seam
    CONTRADICTION   it is not, and here is WHERE
    (checking an existing seam is the engine that already exists)

KNOWN UNSOUNDNESS (A. Miteiko review, 2026-07-21). This sketch joins over
VERDICT EQUALITY (xnor = T), and verdict equality is NOT agreement: two
unrelated formulas can share a verdict without asserting anything in
common (zsew_attack.py #1). A correct seam must join TYPED CLAIM
CERTIFICATES — normalized formula, formula hash, atom/claim namespace,
schema version, marking + timestamp, derivation object, warrant grade,
dependencies, validity interval, ZTL version, grounding references — so
that "the same claim" and "the same symbol" cannot be confused. Until
that object is defined, SEWN below is a demonstration, not a service.

Run:  python3 zsew.py
"""
from zmodal import ztl_eval
from zverify import grade, refinements

T, F, MARK = "T", "F", "M"


class Seam:
    """A joined meaning. Not a verdict but a triple — verdict, warranty,
    and the leaves it was made from — because a seam that cannot say
    what it rests on cannot be told where it came apart."""

    def __init__(self, formula, marking, parts=()):
        self.formula = formula
        self.marking = dict(marking)
        self.parts = tuple(parts)

    @property
    def verdict(self):
        return ztl_eval(self.formula, self.marking)

    @property
    def grade(self):
        return grade(self.formula, self.marking)

    @property
    def leaves(self):
        return {a: v for a, v in self.marking.items() if a in _atoms(self.formula)}

    @property
    def final(self):
        """Only a hereditary seam may be treated as settled. Everything
        else is legitimate AND revocable, and must be carried as such."""
        return self.grade == "hereditary"

    def __repr__(self):
        return f"Seam({_show(self.formula)} = {self.verdict}/{self.grade})"


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        acc.add(phi)
    else:
        for s in phi[1:]:
            _atoms(s, acc)
    return acc


def _show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return f"¬{_show(phi[1])}"
    return (f"({_show(phi[1])}"
            + {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕",
               "xnor": "↔"}[phi[0]] + f"{_show(phi[2])})")


# ---------------------------------------------------------------------------
# The kernel's three answers
# ---------------------------------------------------------------------------
def sew(a, b):
    """Join two seams. Returns (status, payload).

    status is one of:
      "SEWN"           payload = the new Seam
      "CONTRADICTION"  payload = a dict naming WHERE
      "CANNOT"         payload = a dict naming what is unverified
    """
    # 1. the grounds themselves — a leaf verified both ways is the
    #    cheapest and most nameable contradiction there is
    clash = {k for k in a.marking.keys() & b.marking.keys()
             if a.marking[k] != b.marking[k]
             and MARK not in (a.marking[k], b.marking[k])}
    if clash:
        return "CONTRADICTION", {
            "where": "grounds",
            "leaves": {k: (a.marking[k], b.marking[k]) for k in sorted(clash)},
            "reading": "the same claim is verified both ways; no joint can "
                       "repair that, and no channel is consulted"}

    merged = {**a.marking, **b.marking}
    for k in a.marking.keys() & b.marking.keys():
        merged[k] = (a.marking[k] if a.marking[k] != MARK else b.marking[k])

    # 2. the two channels
    agree = ("xnor", a.formula, b.formula)
    differ = ("xor", a.formula, b.formula)
    ch = (ztl_eval(agree, merged), ztl_eval(differ, merged))

    if ch == (T, F):
        return "SEWN", Seam(agree, merged, parts=(a, b))
    if ch == (F, T):
        return "CONTRADICTION", {
            "where": "derivation",
            "leaves": "compatible",
            "verdicts": (ztl_eval(a.formula, merged),
                         ztl_eval(b.formula, merged)),
            "reading": "the grounds agree and the conclusions do not — "
                       "the conflict is in what was derived, not in what "
                       "was supplied (σ: the other kernel answered against)"}
    return "CANNOT", {
        "where": "a mark reached the joint",
        "unverified": sorted(k for k, v in merged.items() if v == MARK),
        "reading": "no contradiction is claimed: nobody spoke against, "
                   "somebody did not speak (E). Sewing is impossible, not "
                   "refused"}


def report(label, status, payload):
    print(f"\n  {label}")
    print(f"    → {status}")
    if status == "SEWN":
        print(f"      {payload}   final: {payload.final}")
        if not payload.final:
            print("      NOT final — legitimate but revocable; a later "
                  "verification may unpick it")
    else:
        for k, v in payload.items():
            print(f"      {k}: {v}")


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    print("=" * 76)
    print("E29 — THE SEAM: a decentralised ZTL and the kernel's three answers")
    print("=" * 76)
    print("  SEWN · CONTRADICTION (and where) · CANNOT (a mark reached it)")

    print("\n" + "=" * 76)
    print("1. THE THREE ANSWERS")
    print("=" * 76)

    A = Seam("p", {"p": T})
    B = Seam("p", {"p": T})
    report("two kernels, same claim, both verified true", *sew(A, B))

    A2 = Seam("p", {"p": T})
    B2 = Seam("p", {"p": F})
    report("same claim, verified opposite ways", *sew(A2, B2))

    A3 = Seam("p", {"p": T})
    B3 = Seam("q", {"q": MARK})
    report("one kernel has not verified its ground", *sew(A3, B3))

    A4 = Seam(("or", "p", ("not", "p")), {"p": T})
    B4 = Seam(("not", ("or", "p", ("not", "p"))), {"p": T})
    report("compatible grounds, opposite conclusions", *sew(A4, B4))

    print("\n" + "=" * 76)
    print("2. THE CURATOR'S SCENARIO — a seam unpicked by a later seam")
    print("=" * 76)
    print("  Seam 1 is made of 1.1 and 1.2 and holds. Seam 2 arrives")
    print("  carrying a verification. Watch 1.1 come away from 1.2.\n")

    s11 = Seam("p", {"p": MARK})
    s12 = Seam("p", {"p": MARK})
    st, s1 = sew(s11, s12)
    print(f"  1.1 ⊗ 1.2  → {st}")
    if st != "SEWN":
        print(f"      {s1['reading']}")
        print("      ← THE MACHINE'S OWN SHARPEST CASE: the same claim sewn")
        print("        to ITSELF is torn while unverified, because Z↔Z = F.")
        print("        Nothing came apart between two meanings; one meaning")
        print("        came apart from itself for want of a ground.")

    s11v = Seam("p", {"p": T})
    s12v = Seam("p", {"p": T})
    st2, s1v = sew(s11v, s12v)
    print(f"\n  after seam 2 verifies p := T, re-sew 1.1 ⊗ 1.2 → {st2}")
    print(f"      {s1v}   final: {s1v.final}")

    print("\n  And the other direction — a seam that HOLDS now and is")
    print("  unpicked by what arrives later. The shortest such pair in the")
    print("  depth-2 pool, found by search rather than chosen:")
    a = Seam(("not", "p"), {"p": MARK, "q": MARK})
    b = Seam(("not", "q"), {"p": MARK, "q": MARK})
    st3, s3 = sew(a, b)
    print(f"\n    A = {_show(a.formula)}   B = {_show(b.formula)}  → {st3}")
    if st3 == "SEWN":
        print(f"      {s3}   final: {s3.final}")
        print("      Both sides read F right now — ¬Z = F on each — so the")
        print("      seam returns SEWN on VERDICT EQUALITY. Arkady (2026-07-21)")
        print("      showed this is NOT agreement: the two claims are not")
        print("      equivalent, and equal output symbols are not consensus.")
        print("      See zsew_attack.py #1 — this SEWN is UNSOUND and stands")
        print("      as a known bug until the seam joins typed certificates")
        print("      over a shared namespace rather than bare verdicts.")
        v0 = s3.verdict
        for m in refinements(s3.marking):
            if ztl_eval(s3.formula, m) != v0:
                shown = {k: v for k, v in m.items() if v != MARK}
                print(f"\n      seam 2 arrives and verifies {shown}:")
                print(f"        A stays {ztl_eval(a.formula, m)}, "
                      f"B becomes {ztl_eval(b.formula, m)}")
                print(f"        seam → {ztl_eval(s3.formula, m)}  "
                      "← UNPICKED, exactly the curator's 1.1-from-1.2")
                print("        and the warranty said so in advance: the seam")
                print("        was until-verification, never final.")
                break

    print("\n" + "=" * 76)
    print("3. WHAT MAKES A SEAM PERMANENT")
    print("=" * 76)
    print("  Not the connective — the WARRANTY. Measured:")
    import zipc
    M = {"p": MARK, "q": MARK}
    pool = zipc.build_pool(("p", "q"), depth=2)[:200]
    her = [f for f in pool if grade(f, M) == "hereditary"][:40]
    bad = [(x, y) for x in her for y in her
           if grade(("xnor", x, y), M) != "hereditary"]
    print(f"    hereditary ⊗ hereditary stays hereditary: "
          f"{len(her) ** 2 - len(bad)} of {len(her) ** 2}")
    print("    → a seam of two unbreakable verdicts is unbreakable.")
    print("      THAT is the thread that cannot tear, and it is bought")
    print("      with grounds, not with a choice of operator.")
    assert not bad, "hereditary is not closed under sewing — re-read"

    print("\n" + "=" * 76)
    print("THE PRECISE STATEMENT OF 'SEWN ILLEGITIMATELY'")
    print("=" * 76)
    print("  The sewing was not illegitimate. Treating a revocable seam as")
    print("  FINAL was. A seam carries its warranty, and only a hereditary")
    print("  one may be called settled; everything else is legitimate and")
    print("  revocable, and unpicking is then a scheduled event rather than")
    print("  an accident.")
    print()
    print("  CEILING: this is the contract on worked examples, not a")
    print("  service. Localisation names the conflicting leaves or says the")
    print("  conflict is in the derivation; it does not yet name the")
    print("  smallest such set. Nothing here is in Lean.")
    print("\n  E29 GREEN")
