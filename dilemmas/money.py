# -*- coding: utf-8 -*-
"""money — "money rules the world": the sign layer, run.

The curator's insight: money is SIGNS — the very F=F truth banned for
humans a step earlier (solved/truths), circulating legally; sign-dust.
And the count is literal: with T and F equally spread, the sign layer is
exactly HALF the world — one bit is lost, and it is the LEVEL bit.
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from itertools import product

from ztl import T, F, Z, ev
from pengine import diagnose
from zhunt import judge


def truth_teller():
    print("THE NOTE — 'the bill is worth what it is held worth': V=V\n")
    d = diagnose({"V": "V"})
    hold_T = ev("V", {"V": T}) == T
    hold_F = ev("V", {"V": F}) == F
    print(f"  solutions {d['n']}, the world's court: {d['ground']['V']}")
    print(f"  stipulate WORTHY — holds: {hold_T}; stipulate WORTHLESS — "
          f"holds: {hold_F}")
    assert d["n"] == 2 and d["ground"]["V"] == Z and hold_T and hold_F
    print("\n  money is a truth-teller net: its value is real but CHOSEN —")
    print("  mankind's largest joint stipulation (the honest common ground")
    print("  of strangers). And it is BISTABLE: confidence and collapse are")
    print("  two fixed points of one net — hyperinflation is not a breakage,")
    print("  it is the world jumping to the other solution.")


def mimetic_pair():
    print("THE PAIR — 'I value it because you value it'\n")
    d = diagnose({"V": "A", "A": "V"})
    g = list(d["ground"].values())
    print(f"  solutions {d['n']}, grounds {g}")
    assert d["n"] == 2 and g == [Z, Z]
    print("\n  the mutual-valuation chain carries no ground of its own —")
    print("  price as crystallized mimesis (Girard's cell in a wallet).")


def leak():
    print("THE LEAK — the priced '=' migrating to value cells\n")
    v = judge(("imp", "paid", "right"), {"paid": "T", "right": "M"})
    print(f"  'paid → right', rightness unverified → {v[0]}, {v[1]}")
    assert v[:2] == ("F", "until-verification")
    print("\n  on exchange cells 'paid → delivered' is the most verified")
    print("  implication in history; migrated to worth ('rich = deserving',")
    print("  the retribution stamp; 'expensive = valuable', the ungrounded")
    print("  pair) it is credit — the grade leak that makes money a judge.")


def sign_layer():
    print("THE SIGN LAYER — the lost bit\n")
    pre = {}
    for a, b in product((T, F), repeat=2):
        s = ev(("xnor", "x", "y"), {"x": a, "y": b})
        pre.setdefault(s, []).append((a, b))
    print(f"  sign T ← preimages {pre[T]}")
    print(f"  sign F ← preimages {pre[F]}")
    print(f"  world states 4 → signs {len(pre)} — exactly half")
    assert pre[T] == [(T, T), (F, F)] and len(pre) == 2
    print("\n  the '=' sign cannot distinguish value=value from")
    print("  emptiness=emptiness: a solid market and a bubble emit THE SAME")
    print("  SIGN. The receipt is genuine — money truly pays for the sign —")
    print("  but the sign carries no LEVEL bit: 'equal' is paid, 'equal at")
    print("  what' is not. F=F, banned for humans (solved/truths), circulates")
    print("  here legally: paper (F) = promise (F) → a working T. Sign-dust.")


def the_stones():
    """The curator's construction, stone by stone: how it CAN be done.
    The honest sign carries the level (∧, not ↔); money is a receipt for
    a deed (M=D — as much money as truth); the single root leak is
    issuance without a deed (money built on money); default is the
    grounding day of an unrooted pyramid."""
    print("THE STONES — the curator's construction\n")
    blind_tt = ev(("xnor", "a", "b"), {"a": T, "b": T})
    blind_ff = ev(("xnor", "a", "b"), {"a": F, "b": F})
    hon_tt = ev(("and", "a", "b"), {"a": T, "b": T})
    hon_ff = ev(("and", "a", "b"), {"a": F, "b": F})
    print(f"  1. the blind sign ↔ : T=T→{blind_tt}, F=F→{blind_ff} — level lost")
    print(f"     the honest sign ∧ : T∧T→{hon_tt}, F∧F→{hon_ff} — level carried")
    assert (blind_tt, blind_ff, hon_tt, hon_ff) == (T, T, T, F)

    receipt = {v: ev("D", {"D": v}) for v in (T, F, Z)}
    print(f"  2. money as a receipt for a deed, M=D: deed done → {receipt[T]},"
          f" no deed → {receipt[F]},")
    print(f"     deed unverified → {receipt[Z]} — as much money as truth,"
          " by construction")
    assert receipt == {T: T, F: F, Z: Z}

    pyr = diagnose({"M3": "M2", "M2": "M1", "M1": "M1"})
    unrooted = list(pyr["ground"].values())
    rooted_T = [ev("D", {"D": T})] * 3
    default = [ev("D", {"D": F})] * 3
    print(f"  3. the pyramid M3=M2=M1, no deed below: {unrooted}")
    print(f"     same chain rooted in a deed T:      {rooted_T} — every "
          "floor earned")
    print(f"     DEFAULT — the deed below was F:     {default} — every "
          "floor dies at once")
    assert unrooted == [Z, Z, Z] and rooted_T == [T, T, T] and default == [F, F, F]
    print("\n  the single root leak is issuance without a deed (the blind ↔")
    print("  mints on F=F too); credit rooted in a deed is honest investment;")
    print("  default does not break the pyramid — it reads it to the end.")
    print("  Money making money — harm; deeds making money — good.")


if __name__ == "__main__":
    print("MONEY RULES THE WORLD — through the core\n")
    truth_teller()
    print()
    mimetic_pair()
    print()
    leak()
    print()
    sign_layer()
    print()
    the_stones()
    print()
    print("DIAGNOSIS: money rules honestly as the common stipulated ground")
    print("of strangers — and dishonestly as a judge, wherever the priced")
    print("'=' migrates to cells that demand collation. The root, made")
    print("precise: a world ruled by money is ruled by a layer in which the")
    print("difference between the earned and the empty DOES NOT EXIST by")
    print("construction — minus one bit, and it is the bit ZTL was built for.")