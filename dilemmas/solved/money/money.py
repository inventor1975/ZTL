# -*- coding: utf-8 -*-
"""money — "money rules the world": the sign layer, run.

The curator's insight: money is SIGNS — the very F=F truth banned for
humans a step earlier (solved/truths), circulating legally; sign-dust.
And the count is literal: with T and F equally spread, the sign layer is
exactly HALF the world — one bit is lost, and it is the LEVEL bit.
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))
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
    """The curator's construction, revised stone by stone. Money is a
    receipt for an EARNED BIT — and an earned NO has the same nominal as
    an earned YES (the information equivalent); the unverified mints
    nothing. The sign must carry the level (∧, not the blind ↔). The
    single root leak is issuance without a bit (money built on money);
    default is the grounding day of an unrooted pyramid."""
    print("THE STONES — the curator's construction (revised)\n")
    yes = judge("p", {"p": "T"})
    no = judge("p", {"p": "F"})
    z = judge("p", {"p": "M"})
    print(f"  1. NOMINAL: earned YES → {yes[0]}, {yes[1]}; earned NO → "
          f"{no[0]}, {no[1]}")
    print(f"     — one grade, one bit, ONE NOMINAL (polarity does not price);")
    print(f"     unverified → {z[0]}, {z[1]} — the note is not issued")
    assert yes[:2] == ("T", "hereditary") and no[:2] == ("F", "hereditary")
    assert z[1] == "until-verification"

    blind_ff = ev(("xnor", "a", "b"), {"a": F, "b": F})
    hon_ff = ev(("and", "a", "b"), {"a": F, "b": F})
    print(f"  2. the blind sign ↔ mints T on F=F ({blind_ff}) — level lost;")
    print(f"     the honest sign ∧ carries it (F∧F→{hon_ff}): a receipt must")
    print("     say WHAT bit it certifies, not merely 'equal'")
    assert blind_ff == T and hon_ff == F

    pyr = diagnose({"M3": "M2", "M2": "M1", "M1": "M1"})
    unrooted = list(pyr["ground"].values())
    rooted = [ev("D", {"D": T})] * 3
    default = [ev("D", {"D": F})] * 3
    print(f"  3. the pyramid M3=M2=M1, no bit below: {unrooted}")
    print(f"     rooted in an earned bit:            {rooted} — every floor "
          "earned")
    print(f"     DEFAULT — the root read out as F:   {default} — every floor "
          "dies at once")
    assert unrooted == [Z, Z, Z] and rooted == [T, T, T] and default == [F, F, F]
    print("\n  as much money as EARNED BITS; credit rooted in a bit is honest")
    print("  investment; default does not break the pyramid — it reads it to")
    print("  the end. Money making money — harm; deeds making money — good.")


def ruling():
    """Who may rule: the receipts or the stipulator. Money REGISTERS the
    earned; power STIPULATES the free cells and HOLDS THE LAWS — and the
    laws, measured, are the cash-out infrastructure of refutations."""
    print("THE RULING — receipts do not rule\n")
    from zchoice import stage, EXACTLY_ONE, LAWLESS
    with_law = stage("a2", (0, 0), EXACTLY_ONE)
    lawless = stage("a2", (0, 0), LAWLESS)
    print(f"  cash-out of an F-bundle: two earned NOs under the law "
          f"'exactly one 1' force → {with_law}")
    print(f"  the same two NOs with no law               → {lawless}")
    assert with_law == T and lawless == Z
    free_denial = ev(("not", "g"), {"g": Z})
    print(f"  power's native coin: the free denial ¬Z = {free_denial} — "
          "ruling by prohibition is cheap;")
    print("  real power begins where a T must be grounded")
    assert free_denial == F
    print("""
  the honest split:
    MONEY  registers earned bits (equal nominal for YES and NO) — it
           records, it does not decide;
    POWER  stipulates the common free cells (the king the book of
           Judges lacked) and holds the laws — the infrastructure that
           cashes F-bundles into forced Ts.
  the two leaks, one in each direction:
    the receipt in the judge's seat — money buying stipulations;
    the printing press — power minting receipts without bits, or
    rewriting an earned bit by decree (no decree makes a grounded F
    into T: the stones above do not move).
  'money rules the world' is a category error: a receipt has taken
  the stipulator's chair — and a receipt that rules mints itself.""")


def equilibrium():
    """The three bars — where the system stands, holds, or starves.
    S = signs (money), B = earned bits (deeds)."""
    print("EQUILIBRIUM — the three bars\n")
    with_sign = judge("R", {"R": "T"})
    without = judge("D", {"D": "M"})
    print(f"  a receipt in any hands        → {with_sign[0]}, {with_sign[1]}"
          "   money = PORTABLE warranty")
    print(f"  another's bit, no receipt     → {without[0]}, {without[1]}"
          "   every trade re-pays verification")
    assert with_sign[:2] == ("T", "hereditary")
    assert without[:2] == ("Z", "until-verification")
    roots = {v: [ev("D", {"D": v})] * 3 for v in (Z, T, F)}
    print(f"  credit chain, root unread     → {roots[Z]}   deferred, not dead")
    print(f"  credit chain, root read T     → {roots[T]}   converts to earned")
    print(f"  credit chain, root read F     → {roots[F]}   cascade default")
    assert roots[Z] == [Z] * 3 and roots[T] == [T] * 3 and roots[F] == [F] * 3
    print("""
  S = B   the CONFIDENCE bar: every sign hereditary, zero possible deaths
  S > B   the CREDIT bar: the overhang lives on Z — still holds, its fate
          is the reading of the roots; fragility = the share of Z-roots
  S < B   the HUNGER bar: earned bits are non-portable — commerce
          throttles, the common ground shrinks back to mutual checks""")


def realtime():
    """The loan is a stage quantity: re-judged at every revealed bit.
    An annual emission plan is a greedy verdict 12 months forward — the
    measured over-assertion of the future (the ¬¬a0 cell, E22)."""
    print("REAL TIME — the loan is judged by revelation, not by calendar\n")
    from zchoice import stage, EXACTLY_ONE
    verdicts = [stage("a2", p, EXACTLY_ONE) for p in ((), (0,), (0, 0))]
    print(f"  revealed () → {verdicts[0]}, (0) → {verdicts[1]}, "
          f"(0,0) → {verdicts[2]}")
    assert verdicts == [Z, Z, T]
    print("""
  the verdict arrives exactly when the bits do; heredity is native to
  the stage court (forces_mono, machine-checked) — what the stage grants
  is never revoked, the loan's corridor narrows monotonically. The
  calendar guesses and breaks; the stage court reads and never backs up.
  THE EXIT, complete:
    the press   — to a rule (not to the chair)
    issuance    — per earned bit (a receipt, either polarity)
    the loan    — a stage court in real time, fragility on the dashboard""")


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
    ruling()
    print()
    equilibrium()
    print()
    realtime()
    print()
    print("DIAGNOSIS: money rules honestly as the common stipulated ground")
    print("of strangers — and dishonestly as a judge, wherever the priced")
    print("'=' migrates to cells that demand collation. The root, made")
    print("precise: a world ruled by money is ruled by a layer in which the")
    print("difference between the earned and the empty DOES NOT EXIST by")
    print("construction — minus one bit, and it is the bit ZTL was built for.")
    print()
    print("CAPSTONE (the curator's, final): «Деньги делают деньги — инфляция.")
    print("Дела делают деньги — стабильность. Деньги и дела делают деньги —")
    print("процветание!» Counted on the core, the three lines land on three")
    print("grades — and they ARE the three bars in aphorism form:")
    v1 = judge(("imp", "M", "M"), {"M": "M"})
    v2 = judge("D", {"D": "T"})
    v3 = judge(("imp", ("and", "M", "D"), "M"), {"M": "M", "D": "M"})
    print(f"  money makes money   M→M            → {v1[0]}, {v1[1]}   CREDIT")
    print(f"  deeds make money    receipt-per-bit → {v2[0]}, {v2[1]}   EARNED")
    print(f"  money∧deeds → money (M∧D)→M        → {v3[0]}, {v3[1]}   A LAW")
    assert v1[:2] == ("F", "until-verification")
    assert v2[:2] == v3[:2] == ("T", "hereditary")
    print("  inflation is literally p→p — the fallen identity in a wallet")
    print("  (the credit bar torn from its roots); stability is the one")
    print("  earned line (parity, zero possible deaths); and prosperity is")
    print("  guaranteed BY LAW when both are present (hereditary) — parity")
    print("  plus the loan grown into deeds: the exit formula with an")
    print("  exclamation mark. Inflation — credit; stability — earnings;")
    print("  prosperity — law. (Kept finding: the same projection read at")
    print("  the SEAT is the dark twin — the chair is paid in tautology;")
    print("  see THE RULING.)")