# -*- coding: utf-8 -*-
"""rambam — divine foreknowledge vs free will, through the core.

The question Maimonides settles by postulate (Hilchot Teshuva 5:5): God
knows in advance what a person will choose, yet the person chooses freely;
pressed for the mechanism, he answers "His knowledge is not like our
knowledge" — an explicit refusal to explain.

FORMALIZATION (agreed in words before the run):
  The world is the person's sequence of choices, horizon H bits; atom ak =
  "at moment k the person chooses 1". A stage is the revealed prefix; the
  world-law L is the set of admitted worlds (LAWLESS = nothing predecided).

  FREE(s,k)      both continuations of ak admitted at stage s.
  KNOWLEDGE(s,k) stage(ak,s,L) is classical — forced on EVERY admitted
                 continuation: a verdict whose warranty is presentable.
  ORACLE         asserts a future ak when it is NOT forced; the unerring
                 oracle is right on the actual continuation every time.

Three instruments, one target:
  * the skeleton cells (zhunt.judge) — where the classical DILEMMA
    "either He knows or He is not omniscient" keeps its credit;
  * the stage court of E22 (zchoice.stage) — what knowledge-with-ground
    does to an open future;
  * the bullet and the marksman — the top system's own liar tried at
    every door (unclosable → guessing is the forced mode), and the sound
    policy (answer on ground, withhold on the free) verified to never lie.

MEASURED verdict, in one line: the dilemma's inference frame is free
(hereditary), but its fuel K∨¬K over an unverified K is credit — the very
cell of "who is not with us is against us"; and inside the fork,
knowledge-with-ground ⟺ a closed future (exact partition, 0 exceptions).
Maimonides' postulate reads as the refusal to take LEM on credit, seven
centuries before a third honest state existed to say it with.
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from itertools import product

from ztl import T, F, Z, ev
from zchoice import H, ATOMS, completions, stage, LAWLESS, EXACTLY_ONE
from zhunt import judge
from pengine import diagnose

WORLDS = list(product((0, 1), repeat=H))


# --- layer 1: the skeleton of the dilemma (read the warranty) --------------

def skeleton():
    print("SKELETON — the classical dilemma through judge (warranty, not verdict)\n")
    lem = ("or", "K", ("not", "K"))
    frame = ("imp", ("and", ("imp", "K", "D"), ("imp", ("not", "K"), "N")),
             ("or", "D", "N"))
    cogito = ("imp", ("imp", ("not", "K"), "K"), "K")
    reductio = ("imp", ("imp", "K", ("not", "K")), ("not", "K"))
    cells = [
        ("fork's fuel   K∨¬K            ", lem),
        ("fork's frame  (K→D)∧(¬K→N)→D∨N", frame),
        ("cogito twin   (¬K→K)→K        ", cogito),
        ("reductio twin (K→¬K)→¬K       ", reductio),
    ]
    got = {}
    for name, phi in cells:
        marks = {a: "M" for a in ("K", "D", "N") if _mentions(phi, a)}
        v, grade, counter, depth = judge(phi, marks)
        got[name.split()[0] + name.split()[1]] = (v, grade)
        print(f"  {name}  →  {v}, {grade}")
    print("\n  the frame is earned; the FUEL is on credit — the same cell as")
    print("  'who is not with us is against us': an unverified K stamped settled.")
    assert got["fork'sfuel"] == ("F", "until-verification")
    assert got["fork'sframe"][1] == "hereditary"
    assert got["cogitotwin"] == ("F", "until-verification")
    assert got["reductiotwin"] == ("T", "hereditary")


def _mentions(phi, a):
    if phi == a:
        return True
    return isinstance(phi, tuple) and any(_mentions(x, a) for x in phi[1:])


# --- layer 2: inside the fork — the stage court ----------------------------

def free(prefix, k, law):
    return {w[k] for w in completions(prefix, law)} == {0, 1}


def all_laws():
    """Every nonempty set of admitted worlds is a law (255 laws)."""
    for mask in range(1, 1 << len(WORLDS)):
        allowed = {WORLDS[i] for i in range(len(WORLDS)) if mask >> i & 1}
        yield lambda w, s=allowed: w in s


def reachable_prefixes(law):
    for t in range(H):
        for p in product((0, 1), repeat=t):
            if completions(p, law):
                yield p


def court():
    print("STAGE COURT — knowledge-with-ground vs the open future\n")

    # C1: a free world, stage 0 — the honest verdict on tomorrow's choice
    assert free((), 0, LAWLESS) and stage("a0", (), LAWLESS) == Z
    print("  C1  lawless stage 0: FREE, court says Z — honest 'not yet known'")

    # C2: the closure identity, total over all laws x stages x future bits
    total = viol = know = fr = 0
    for law in all_laws():
        for p in reachable_prefixes(law):
            for k in range(len(p), H):
                total += 1
                knows = stage(ATOMS[k], p, law) in (T, F)
                is_free = free(p, k, law)
                know += knows
                fr += is_free
                viol += (knows == is_free)
    print(f"  C2  all 255 laws, {total} cells: KNOWLEDGE ⟺ UNFREEDOM, "
          f"{viol} violations")
    print(f"      ({know} knowledge cells + {fr} freedom cells — exact partition)")
    assert viol == 0 and know + fr == total

    # C3: the unerring oracle is consistent with freedom — as credit
    for w in WORLDS:                       # oracle asserts w[k]: right by fiat
        assert all(free((), k, LAWLESS) for k in range(H))
        assert all(stage(ATOMS[k], (), LAWLESS) == Z for k in range(H))
    print(f"  C3  unerring oracle, {len(WORLDS)}/{len(WORLDS)} worlds: record "
          "clean, freedom intact,")
    print("      every assertion unforced (Z) — credit that never defaults")

    # C4: a clean record never raises the warranty grade
    raised = checked = 0
    for p in reachable_prefixes(LAWLESS):
        if 0 < len(p) < H:
            checked += 1
            k = len(p)
            raised += (stage(ATOMS[k], p, LAWLESS) != Z
                       or not free(p, k, LAWLESS))
    print(f"  C4  after an unerring streak ({checked} prefixes): grade raised "
          f"{raised} times — induction buys no ground")
    assert raised == 0

    # C5: where foreknowledge DOES exist — knowledge of the law, end of freedom
    assert stage("a1", (1,), EXACTLY_ONE) == F and not free((1,), 1, EXACTLY_ONE)
    print("  C5  law 'exactly one 1', after choosing 1: court F on a1, FREE "
          "false —")
    print("      foreknowledge lives exactly where the law closed the future")


# --- layer 3: the bullet and the marksman ----------------------------------

def bullet():
    """The top system's own liar, tried at every door. A system that
    contains its own truth cannot close this cell — and the topmost system
    has no metalanguage above to hand it to (no notary). Hence guessing is
    its forced MODE over whatever it cannot ground."""
    print("THE BULLET — the system's own liar, every door tried\n")
    nets = [("liar     S=¬S", {"S": ("not", "S")}),
            ("avenger  M=¬M∨¬(M↔M)",
             {"M": ("or", ("not", "M"), ("not", ("xnor", "M", "M")))})]
    for name, net in nets:
        d = diagnose(net)
        n0 = next(iter(net))
        stip = {v: ev(net[n0], {n0: v}) == v for v in (T, F)}
        print(f"  {name}: solutions {d['n']}, ground "
              f"{list(d['ground'].values())[0]}, stipulate T/F fixed? "
              f"{stip[T]}/{stip[F]}, inputs to verify: none")
        assert d["n"] == 0 and list(d["ground"].values())[0] == Z
        assert not stip[T] and not stip[F]
    tt = diagnose({"S": "S"})
    assert tt["n"] == 2 and ev("S", {"S": T}) == T
    print("  truth-teller S=S (contrast): 2 solutions — STIPULABLE; "
          "the liar is not.")
    print("\n  unclosable by decision, stipulation, or verification — "
          "the refusal is permanent.")


def marksman():
    """The sound policy — answer where the stage forces, withhold (Z)
    where it does not: verified to never lie, and its silences sit exactly
    on the freedom cells. 'Never misses' is bought by the discipline of
    the shot, not by a warranty on tomorrow."""
    lies = answers = stalls = 0
    for law in all_laws():
        for p in reachable_prefixes(law):
            for k in range(len(p), H):
                v = stage(ATOMS[k], p, law)
                if v == Z:
                    stalls += 1
                    lies += (not free(p, k, law))     # silence off a free cell?
                else:
                    answers += 1
                    want = 1 if v == T else 0
                    lies += any(w[k] != want
                                for w in completions(p, law))
    print("THE MARKSMAN — the sound policy over all 255 laws\n")
    print(f"  answers {answers} (each right in EVERY admitted world), "
          f"withholds {stalls},")
    print(f"  lies or misplaced silences: {lies}")
    assert lies == 0 and answers == 986 and stalls == 1507
    print("\n  he never misses because he never lies: ground → answer, "
          "no ground → Z —\n  and the Z-cells are exactly the freedom cells: "
          "not missed targets, OUR cells.")


if __name__ == "__main__":
    print("FOREKNOWLEDGE vs FREE WILL — the Rambam dilemma through the core\n")
    skeleton()
    print()
    court()
    print()
    bullet()
    print()
    marksman()
    print("\nVERDICT: no paradox — an identity read from two sides. To know in")
    print("advance with a warranty is to have taken the choice away; whoever")
    print("leaves the choice open does not know — he aims, unerringly. The")
    print("dilemma demanding an answer runs on credit (its LEM fuel), and the")
    print("postulate 'His knowledge is not like our knowledge' is the refusal")
    print("to take that credit.")
