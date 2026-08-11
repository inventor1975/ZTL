# -*- coding: utf-8 -*-
"""
The ledger against classical logic: what we share, what we lost, what we
gained — all four columns measured, none of them argued.

The corpus has always carried the loss column (audit.py: 12 laws alive,
14 fallen) and it gets quoted at us. The other three columns were never
in one place, so this stand puts them there:

  SHARED      on Z-free markings ZTL and classical logic agree, cell for
              cell. Verify everything and the classical machine is back,
              untouched — nothing is taken away on solid ground.
  LOST        as a system of LAWS we are strictly weaker: every ZTL
              tautology is a classical one, never the reverse.
  GAINED      not a single new law — and that is provable, not merely
              unobserved — but a twelvefold refinement of DISTINCTIONS:
              formulas classical logic cannot tell apart, we can.
  ONLY HERE   the mark is expressible inside the object language:
              ~(p <-> p) says "this is unverified". A two-valued logic
              has no words for that at all.

And the punchline for the docket: both paradoxes resolved this week run
on moves that are classically valid and MISSING here. Our poverty is
exactly the poverty of free truth.

Run:  python3 zledger.py
"""
import os
import sys
from collections import defaultdict

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, ev                                  # noqa: E402
from ztime import depth2_pool                                # noqa: E402

V = (T, F, Z)
CL = (T, F)


def sig(phi, values):
    return tuple(ev(phi, {"p": a, "q": b}) for a in values for b in values)


def sec1_shared():
    print("-" * 72)
    print("1. SHARED: on verified ground we ARE classical logic")
    pool = list(depth2_pool())
    # a classical evaluator written independently of ztl.py, so the
    # agreement is a comparison and not a tautology about one function
    def classical(phi, env):
        if isinstance(phi, str):
            return env[phi] if phi in env else phi
        op = phi[0]
        a = classical(phi[1], env)
        if op == "not":
            return F if a == T else T
        b = classical(phi[2], env)
        return {"and": T if a == T and b == T else F,
                "or": T if a == T or b == T else F,
                "imp": T if a == F or b == T else F,
                "xor": T if a != b else F,
                "xnor": T if a == b else F}[op]
    cells = bad = 0
    for phi in pool:
        for a in CL:
            for b in CL:
                cells += 1
                if ev(phi, {"p": a, "q": b}) != classical(phi, {"p": a,
                                                                "q": b}):
                    bad += 1
    print(f"   {len(pool)} formulas x 4 verified markings = {cells} cells;"
          f"  divergences: {bad}")
    assert bad == 0
    print("   so nothing is taken away where everything is checked. The")
    print("   third value is a discipline about UNVERIFIED ground, not a")
    print("   rival arithmetic of truth.")
    # and the answer to the question everyone actually asks — "so you
    # abolished De Morgan?" — is a schedule, not a yes or a no: the
    # classical toolbox comes back as the atoms are paid for.
    cl = [phi for phi in pool if all(sig(phi, CL))
          and all(v == T for v in sig(phi, CL))]
    one = [phi for phi in cl
           if all(ev(phi, {"p": a, "q": Z}) == T for a in CL)]
    none = [phi for phi in cl if all(v == T for v in sig(phi, V))]
    print(f"   classical tautologies in this pool: {len(cl)}")
    print(f"     hold with BOTH atoms verified : {len(cl)} (100%) — the theorem")
    print(f"     hold with ONE of two verified : {len(one)} "
          f"({100 * len(one) // len(cl)}%)")
    print(f"     hold with nothing verified    : {len(none)} "
          f"({100 * len(none) // len(cl)}%)")
    assert len(cl) == 584 and len(one) == 379 and len(none) == 212
    dm = ("xnor", ("not", ("and", "p", "q")),
          ("or", ("not", "p"), ("not", "q")))
    print("   De Morgan itself: " + "   ".join(
        f"p={a},q={b} -> {ev(dm, {'p': a, 'q': b})}"
        for a, b in ((T, T), (T, Z), (Z, Z))))
    assert ev(dm, {"p": T, "q": T}) == T and ev(dm, {"p": T, "q": Z}) == F
    print("   so the licence is granted per FORMULA and needs EVERY atom in")
    print("   it verified — not most of them. Pay for both and De Morgan is")
    print("   yours; leave one unpaid and it is gone. Nothing was abolished:")
    print("   a classical law costs exactly the verification of its atoms.")
    return pool


def sec2_lost_and_gained(pool):
    print("-" * 72)
    print("2. LAWS: strictly fewer, and provably no new ones")
    cl_taut = [phi for phi in pool if all(v == T for v in sig(phi, CL))]
    ztl_taut = [phi for phi in pool if all(v == T for v in sig(phi, V))]
    new = [phi for phi in ztl_taut if not all(v == T for v in sig(phi, CL))]
    print(f"   tautologies in this pool — classical {len(cl_taut)}, "
          f"ZTL {len(ztl_taut)}, NEW in ZTL: {len(new)}")
    assert len(new) == 0 and len(ztl_taut) < len(cl_taut)
    print("   and the zero is not an absence of evidence: a ZTL tautology")
    print("   holds under every marking, hence under the Z-free ones, where")
    print("   section 1 shows we are classical. Our validities are a SUBSET")
    print("   by construction — the gain column of LAWS is closed forever.")


def sec3_distinctions(pool):
    print("-" * 72)
    print("3. DISTINCTIONS: where the gain actually lives")
    classes = defaultdict(set)
    for phi in pool:
        classes[sig(phi, CL)].add(sig(phi, V))
    ztl_classes = {sig(phi, V) for phi in pool}
    split = [k for k, v in classes.items() if len(v) > 1]
    print(f"   equivalence classes on two variables: classical "
          f"{len(classes)}, ZTL {len(ztl_classes)}")
    print(f"   classical classes that ZTL splits: {len(split)} of "
          f"{len(classes)}")
    assert len(classes) == 16 and len(ztl_classes) > 190
    assert len(split) == len(classes)          # every single one
    print("   the curator's own instance — one classical class, two fates:")
    for name, phi in (("p -> p   ", ("imp", "p", "p")),
                      ("~p -> ~p ", ("imp", ("not", "p"), ("not", "p")))):
        print(f"     {name}: " + "  ".join(
            f"{v}->{ev(phi, {'p': v})}" for v in V))
    print("   both are classical tautologies; only the first can fail. The")
    print("   second CANNOT — negation burns the mark — which is why")
    print("   proving p -> p through ~p -> ~p is a forgery (the Job test).")


def sec4_only_here(pool):
    print("-" * 72)
    print("4. ONLY HERE: the mark is sayable in the object language")
    isz = ("not", ("xnor", "p", "p"))
    print("   ~(p <-> p): " + "  ".join(f"{v}->{ev(isz, {'p': v})}"
                                        for v in V))
    assert [ev(isz, {"p": v}) for v in V] == [F, F, T]
    print("   T and F both answer F, the mark answers T: the formula says")
    print("   'this is unverified' from inside. Classical logic cannot even")
    print("   phrase the question — not 'unprovable there', but no words.")


def sec5_poverty_is_the_point():
    print("-" * 72)
    print("5. THE MISSING TOOLS ARE THE PARADOX ENGINES")
    # the sorites' engine: rewriting a failed implication as a cliff
    lhs, rhs = ("not", ("imp", "p", "q")), ("and", "p", ("not", "q"))
    cl_same = sig(lhs, CL) == sig(rhs, CL)
    ztl_same = sig(lhs, V) == sig(rhs, V)
    print(f"   ~(p -> q)  ==  p & ~q :  classically {cl_same}, "
          f"here {ztl_same}   <- the sorites' engine")
    # the surprise exam's engine: a conclusion drawn from an unearned premise
    mp = ("and", ("imp", "p", "q"), "p")
    from_mark = ev(("imp", mp, "q"), {"p": Z, "q": Z})
    lem = ("or", "p", ("not", "p"))
    print(f"   p | ~p at an unverified p : {ev(lem, {'p': Z})}"
          f"                    <- case analysis on the unchecked")
    assert cl_same and not ztl_same
    assert ev(lem, {"p": Z}) == F
    assert from_mark == T                      # MP itself survives, note
    print(f"   and modus ponens itself is untouched ({from_mark}) — we did")
    print("   not buy the resolutions by breaking inference. What is gone")
    print("   is exactly the free-truth kit: excluded middle on an")
    print("   unchecked atom, and the rewriting that turns 'this step")
    print("   failed' into 'here is the cliff'. Both paradoxes of this")
    print("   week run on precisely those two moves.")


def sec6_tomova():
    print("-" * 72)
    print("6. THE FIRST OBJECTION A LOGICIAN WILL MAKE: 'p → p fails'")
    # Tomova's four criteria for a NATURAL implication (Reports on Math.
    # Logic 47, 2012; the normality clause is Łukasiewicz–Tarski 1930,
    # p. 134). p → p is nowhere a primitive of the definition — it is the
    # diagonal case of criterion (3).
    from ztl import IMP
    designated = (T,)
    c1 = all(IMP(a, b) == (T if (a == F or b == T) else F)
             for a in (T, F) for b in (T, F))
    c2 = all((not (a in designated and IMP(a, b) in designated))
             or b in designated for a in V for b in V)
    order = {F: 0, Z: 1, T: 2}
    broken = [(a, b) for a in V for b in V
              if order[a] <= order[b] and IMP(a, b) not in designated]
    print(f"   (1) C-extending, classical on T/F        : {c1}")
    print(f"   (2) Łukasiewicz-Tarski normality (MP)    : {c2}")
    print(f"   (3) p <= q  =>  p -> q designated        : "
          f"{not broken}   violations: {broken}")
    assert c1 and c2 and broken == [(Z, Z)]
    print("   two of three met, and the third broken in ONE cell. That")
    print("   cell is the diagonal of an ORDER condition, which presupposes")
    print("   the middle value is a DEGREE of truth between F and T")
    print("   (Łukasiewicz's ½: 'possible, not yet determined'). Ours is a")
    print("   status mark barred from compounds, so Z <= Z does not say")
    print("   'equally true' but 'neither side examined' — designating the")
    print("   conditional there is exactly granting truth on credit.")
    print("   The constitutive test lives elsewhere and we pass it: the")
    print("   consequence relation is Tarskian, so p |= p holds where")
    print("   |= p -> p fails (entailment.py). The price is named: the")
    print("   deduction theorem holds left to right only.")


def sec7_the_card():
    print("-" * 72)
    print("7. THE CARD (what to answer when asked 'how do you compare?')")
    print("   We are NOT a stronger logic. On verified ground we are the")
    print("   classical one, cell for cell; as a system of laws we are a")
    print("   strict fragment and can never gain a law. What we add is")
    print("   sight on unverified ground: twelve times as many")
    print("   distinctions, a name for the mark inside the language, and")
    print("   a refusal to make the two moves that manufacture free truth.")
    print("   The honest boundary: this makes a good AUDITOR and a poor")
    print("   MATHEMATICIAN. Case analysis on an undecided proposition is")
    print("   ordinary mathematical practice and we cannot do it — from an")
    print("   empty ledger nothing is derivable here, not even a guarded")
    print("   tautology (E26). Narrow search is a virtue when judging")
    print("   claims and a cage when building proofs.")


if __name__ == "__main__":
    print("=" * 72)
    print("ZTL vs CLASSICAL — the four-column ledger, measured")
    print("=" * 72)
    pool = sec1_shared()
    sec2_lost_and_gained(pool)
    sec3_distinctions(pool)
    sec4_only_here(pool)
    sec5_poverty_is_the_point()
    sec6_tomova()
    sec7_the_card()
    print("=" * 72)
    print("ZLEDGER GREEN — shared on verified ground (0 divergences);")
    print("strictly fewer laws and provably no new ones; 16 classical")
    print("classes split into 195; the mark sayable from inside; and the")
    print("two moves we lack are the engines of the two paradoxes we")
    print("resolved. Poverty in laws, sight on unpaid ground.")
