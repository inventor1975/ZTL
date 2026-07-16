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
    print("DIAGNOSIS: money rules honestly as the common stipulated ground")
    print("of strangers — and dishonestly as a judge, wherever the priced")
    print("'=' migrates to cells that demand collation. The root, made")
    print("precise: a world ruled by money is ruled by a layer in which the")
    print("difference between the earned and the empty DOES NOT EXIST by")
    print("construction — minus one bit, and it is the bit ZTL was built for.")