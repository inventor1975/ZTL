# -*- coding: utf-8 -*-
"""agrippa_critics — every objection to "only the primary act gives knowledge", run through the instrument.

THE THESIS UNDER FIRE (lean/Agrippa.lean, `knowledge_iff_ground`, 2026-10-23): on a finite base a statement has
exactly one reading iff its chain of reasons reaches a nullary ground. Read as the curator reads Agrippa — the
trilemma is about KNOWLEDGE — regress, circle and dogma give none; the primary act (the nullary ground) is the one
place that does.

THE METHOD, the same as dilemmas/agrippa.py F1-F7, one critic at a time:
  1. LOGIC. The critic's inference "premises -> ~K" is judged with nothing granted. EARNED = his logic is conceded.
  2. SOUNDNESS. His premises are judged under the marking the MEASUREMENTS give. Every value in a marking comes
     from a computation in this file — the number of readings of a small justification system, the criterion the
     Lean file proves — never typed in. A premise nothing here can compute stays Z.
       premises REFUTED  -> the objection has a false premise: it fails, and the failing premise is named;
       premises EARNED   -> the objection stands: its conclusion is delivered;
       premises OPEN     -> the weak link is named, and E27's stamp says whether any operation could ever settle it
                            (Z_REDEEMABLE) or none can (Z_PERMANENT: credit forever, on BOTH sides).
  3. Where a critic hits, it is said so, and what the thesis must give up is written down.

THE MODEL'S REACH, said once for all critics: the counts are of justification systems on a finite base. A value
measured here is a value IN THE MODEL; whether a real act, a real belief or a real postulate is such a system is
the modelling step, and it is the critic's to contest. Where an objection is about that step and not about the
counts, its premise is Z here and the verdict says so.

THE LAST CRITIC (the curator, 2026-10-23). "Agrippa may have meant something else by knowledge." He did: the modes
are aimed at dogma, assent about how THINGS are. Then the horns stand — the control rows below already show it:
Albert's argument STANDS against the dogma and against a posit (posit_relative). The thesis defended here is about
ACTS; for Things Agrippa is right, and that is the formal register's signature.

Run:  python3 dilemmas/agrippa_critics.py        (asserts every measurement)
"""

import os
import sys
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import stamp           # noqa: E402

Z = "Z"

# ---------------------------------------------------------------- the counter
# A justification system: node -> ("ground", bool) | ("ref", target, negated). The same two kinds of support as
# Agrippa.lean's `Just`. A READING of x is a valuation obeying every support on x's chain.


def chain(system, x):
    seen, out = set(), []
    while x not in seen:
        seen.add(x)
        out.append(x)
        kind = system[x]
        if kind[0] == "ground":
            break
        x = kind[1]
    return out


def readings(system, x):
    """0 = no reading, 1 = exactly one value for x, 2 = readings that disagree on x (Agrippa.lean's count)."""
    nodes = chain(system, x)
    values = set()
    for bits in product((False, True), repeat=len(nodes)):
        v = dict(zip(nodes, bits))
        ok = True
        for n in nodes:
            kind = system[n]
            want = kind[1] if kind[0] == "ground" else (v[kind[1]] != kind[2])
            if v[n] != want:
                ok = False
                break
        if ok:
            values.add(v[x])
    return len(values)


def realize(system, beta):
    """A base fixes every POSIT ("posit", i) to beta[i]; an ACT ("act", m, n) is computed (m == n) — no base's to fix.
    Mirrors Agrippa.lean's `realize`."""
    out = {}
    for n, k in system.items():
        if k[0] == "act":
            out[n] = ("ground", k[1] == k[2])
        elif k[0] == "posit":
            out[n] = ("ground", beta[k[1]])
        else:
            out[n] = k
    return out


def values_across_bases(system, x):
    """x's single-reading values over EVERY base (each posit either way). One value = base-invariant."""
    posits = sorted({k[1] for k in system.values() if k[0] == "posit"})
    seen = set()
    for bits in product((False, True), repeat=len(posits)):
        r = realize(system, dict(zip(posits, bits)))
        if readings(r, x) == 1:
            for vb in product((False, True), repeat=len(r)):
                v = dict(zip(r, vb))
                if all(v[n] == (k[1] if k[0] == "ground" else v[k[1]] != k[2]) for n, k in r.items()):
                    seen.add(v[x])
                    break
    return seen


def tv(b):
    return "T" if b else "F"


SYSTEMS = {
    # the primary act: x rests on a nullary ground
    "act":            {"x": ("ref", "g", False), "g": ("ground", True)},
    # the chosen stop "p because p"
    "dogma":          {"x": ("ref", "f", False), "f": ("ref", "f", False)},
    # Fichte's self-positing I: "I = I" — I rests on I
    "fichte_I":       {"I": ("ref", "I", False)},
    # an even circle: a because b, b because a (BonJour's coherent pair; Hegel's "the true is the whole", smallest)
    "circle":         {"a": ("ref", "b", False), "b": ("ref", "a", False)},
    # Descartes: clear-and-distinct perception C is guaranteed by God G; G is proved by C (the Cartesian circle)
    "cartesian":      {"C": ("ref", "G", False), "G": ("ref", "C", False)},
    # the liar
    "liar":           {"l": ("ref", "l", True)},
    # the same act, with the ground's value set the other way — same shape, another base
    "act_other_base": {"x": ("ref", "g", False), "g": ("ground", False)},
    # an axiom taken as a foundation: the theorem rests on the axiom, the axiom asks for nothing
    "axiom_ground":   {"t": ("ref", "A", False), "A": ("ground", True)},
    # the same axiom taken as a chosen stop: "A because A"
    "axiom_chosen":   {"t": ("ref", "A", False), "A": ("ref", "A", False)},
}
COUNT = {name: readings(s, next(iter(s))) for name, s in SYSTEMS.items()}
# the same chain, its ground an ACT (a constructed claim, "1 = 1") or a POSIT (an axiom the base sets)
BASED = {
    "act":   {"x": ("ref", "g", False), "g": ("act", 1, 1)},
    "posit": {"x": ("ref", "g", False), "g": ("posit", 0)},
}
ACROSS = {name: values_across_bases(s, "x") for name, s in BASED.items()}



def value_of(name):
    s = SYSTEMS[name]
    x = next(iter(s))
    for bits in product((False, True), repeat=len(s)):
        v = dict(zip(s, bits))
        if all(v[n] == (k[1] if k[0] == "ground" else v[k[1]] != k[2]) for n, k in s.items()):
            return v[x]
    return None


# ---------------------------------------------------------------- one critic
ROWS = []


def critic(name, objection, inference, premises, marking, sources, repertoire, expect, lesson):
    """inference: "rule & premises -> conclusion" as one formula (step 1, the logic); premises: the critic's
    FACTUAL premises alone (step 2) — the rule linking them to the conclusion is conceded in step 1."""
    logic = judge(inference, None)
    sound = judge(premises, marking)
    weak = sorted(sound["unverified"])
    stamps = {a: stamp(a, {**{w: Z for w in weak}, **marking}, repertoire) for a in weak}
    if sound["disposition"] == "REFUTED":
        outcome = "FAILS"
    elif sound["disposition"] == "EARNED":
        outcome = "STANDS"
    else:
        outcome = "OPEN"
    print(f"\n### {name}")
    print(f"    objection : {objection}")
    print(f"    logic     : {logic['disposition']} ({logic['grade']})")
    for atom, src in sources.items():
        print(f"    measured  : {atom} = {marking.get(atom, Z):<2} <- {src}")
    print(f"    premises  : {sound['disposition']}  weak={weak or '—'}  "
          f"{' '.join(f'{a}:{s}' for a, s in stamps.items())}")
    print(f"    OUTCOME   : {outcome} — {lesson}")
    assert logic["disposition"] == "EARNED", f"{name}: the critic's logic must be conceded"
    assert outcome == expect[0], f"{name}: expected {expect[0]}, got {outcome}"
    if len(expect) > 1:
        assert stamps == expect[1], f"{name}: expected stamps {expect[1]}, got {stamps}"
    ROWS.append((name, outcome, weak, stamps))


def run():
    print("AGRIPPA'S CRITICS — every objection to 'only the primary act gives knowledge', judged")
    print("=" * 100)
    print("\n### the counts every marking below is taken from")
    for n, c in COUNT.items():
        print(f"    {n:<15} readings = {c}")
    assert COUNT == {"act": 1, "dogma": 2, "fichte_I": 2, "circle": 2, "cartesian": 2, "liar": 0,
                     "act_other_base": 1, "axiom_ground": 1, "axiom_chosen": 2}
    assert value_of("act") is True and value_of("act_other_base") is False
    print(f"    over every base: act -> {sorted(ACROSS['act'])}, posit -> {sorted(ACROSS['posit'])}")
    assert ACROSS == {"act": {True}, "posit": {False, True}}

    chosen = lambda n: tv(COUNT[n] == 2)     # "the stop is a choice" = it has two readings

    # ---- A. "every stop is chosen" ---------------------------------------------------------------
    critic("Albert (Muenchhausen trilemma): the act is a dogmatic break-off",
           "stopping at the act is breaking off the procedure; a break-off is a choice; a choice is not knowledge",
           "(((s & c) -> ~k) & s & c) -> ~k", "s & c",
           {"s": "T", "c": chosen("act")},
           {"s": "the chain stops at the act (given)", "c": f"act has {COUNT['act']} reading(s): no rival"},
           set(), ("FAILS",),
           "his premise 'the stop is chosen' is false of the act (one reading)")
    critic("Albert, the same argument against the DOGMA (control)",
           "stopping at 'p because p' is a choice",
           "(((s & c) -> ~k) & s & c) -> ~k", "s & c",
           {"s": "T", "c": chosen("dogma")},
           {"s": "the chain stops at the dogma (given)", "c": f"dogma has {COUNT['dogma']} readings"},
           set(), ("STANDS",),
           "against the dogma he is RIGHT — the same instrument that clears the act convicts the dogma")
    critic("Popper (fallibilism): every knowledge claim is a conjecture with a rival",
           "nothing is beyond revision, so nothing is knowledge in the strong sense",
           "(((r -> ~k) & r)) -> ~k", "r",
           {"r": chosen("act")}, {"r": f"act has {COUNT['act']} reading(s): no rival reading in the model"},
           set(), ("FAILS",),
           "as a universal it is refuted by one exhibit — the act; for every chosen premise he stands")
    critic("Quine (web of belief, no first philosophy): every node is revisable",
           "no statement is immune; a privileged ground is a myth",
           "(((w -> ~k) & w)) -> ~k", "w",
           {"w": chosen("act")}, {"w": f"act has {COUNT['act']} reading(s): nothing to revise it to"},
           set(), ("FAILS",),
           "the same exhibit; inside the web every circle is a fork, and he is right about those")

    # ---- B. "the base is chosen" -----------------------------------------------------------------
    critic("Albert, second move: who chose the base?",
           "the act reads once — given its base; the base itself is chosen",
           "(((b -> ~a) & b)) -> ~a", "b",
           {"b": tv(len(ACROSS["act"]) > 1)},
           {"b": f"a value resting on an ACT, over every base: {sorted(ACROSS['act'])} (Lean: act_absolute)"},
           set(), ("FAILS",),
           "an act's value is computed, no base sets it. What remains someone's is WHICH claim is constructed")
    critic("Albert, second move, against a POSIT (control)",
           "the axiom reads once — given its base; another base reads it the other way",
           "(((b -> ~a) & b)) -> ~a", "b",
           {"b": tv(len(ACROSS["posit"]) > 1)},
           {"b": f"a value resting on a POSIT, over every base: {sorted(ACROSS['posit'])} (Lean: posit_relative)"},
           set(), ("STANDS",),
           "against an axiom he is RIGHT: a posit is optional, its knowledge only relative to the base")
    critic("Kant: the categories and the forms of intuition are the given base",
           "the act of synthesis works on a given table of categories — the base again",
           "(((t -> ~a) & t)) -> ~a", "t",
           {}, {"t": "whether a table of categories is a chosen base: no operation here computes it"},
           {"t"}, ("OPEN", {"t": "Z_REDEEMABLE_STABLE"}),
           "the same hole as Albert's second move, at the level of a fixed table; redeemable only by "
           "exhibiting the table as forced (one reading) — not done")

    # ---- C. "an act carries no value" ------------------------------------------------------------
    critic("Sellars (myth of the given) / Davidson: only what bears a truth value can justify",
           "an act is not a proposition; only a belief can be a reason for a belief",
           "(((g & n) -> ~k) & g & n) -> ~k", "g & n",
           {"g": "T", "n": tv(value_of("act") is None)},
           {"g": "granted: justifiers bear values", "n": f"the act's ground carries the value {value_of('act')}"},
           set(), ("FAILS",),
           "in the model the ground BEARS a value (ground b); that a real act yields one is the modelling step "
           "he really contests — the next row")
    critic("Sellars, the modelling step: does a real act yield a value?",
           "a 'ground b' is already a proposition in disguise; the act itself is valueless",
           "(((m -> ~k) & m)) -> ~k", "m",
           {}, {"m": "whether a real act is a valued ground: outside every count here"},
           set(), ("OPEN", {"m": "Z_PERMANENT"}),
           "permanent credit — on BOTH sides: he cannot exhibit it either. Our answer is philosophical (VR's "
           "doing-not-being), not a measurement")
    critic("Sextus (Pyrrhonism): the act is only an appearance — suspend judgement",
           "what appears is not what is; from appearance no value follows",
           "(((p -> ~k) & p)) -> ~k", "p",
           {}, {"p": "'mere appearance' has no operation that settles it"},
           set(), ("OPEN", {"p": "Z_PERMANENT"}),
           "the skeptic's engine again (agrippa.py F7): unredeemable, refutable by any exhibited knowledge, "
           "earnable never")

    # ---- D. "the base is infinite" ---------------------------------------------------------------
    critic("Klein (infinitism) / Peirce (no first cognition): regress gives knowledge",
           "reasons need not end; every cognition is determined by a previous one",
           "(((i & q) -> ~e) & i & q) -> ~e", "i & q",
           {"q": "T"}, {"q": "granted: an infinite chain is available to him",
                        "i": "an actually infinite base: no finite operation exhibits it"},
           set(), ("OPEN", {"i": "Z_PERMANENT"}),
           "no_regress is relative to a FINITE base; on his infinite base the theorem says nothing. He cannot "
           "exhibit the infinity either — AC-class credit both ways (agrippa.py F4)")

    # ---- E. "coherence selects a reading" --------------------------------------------------------
    critic("BonJour (coherentism): a coherent circle justifies",
           "mutual support of the whole confers justification",
           "(((h -> k) & h)) -> k", "h",
           {"h": tv(COUNT["circle"] == 1)}, {"h": f"the even circle has {COUNT['circle']} readings"},
           set(), ("FAILS",),
           "coherence leaves two readings; it does not select one. Coherence is a fork, not knowledge")
    critic("Hegel: the true is the whole; the beginning is mediated",
           "only the completed circle of mediations is knowledge",
           "(((h -> k) & h)) -> k", "h",
           {"h": tv(COUNT["circle"] == 1)}, {"h": f"a closed circle of mediations: {COUNT['circle']} readings"},
           set(), ("FAILS",),
           "a closed whole without a ground reads twice; reading Hegel's whole as such a circle is ours to "
           "defend — the measurement is only about circles")

    # ---- F. "the ground is a self-evident proposition" -------------------------------------------
    critic("Foundationalism: the ground is a self-evident proposition, not an act",
           "an axiom that asks for nothing ends the chain as well as your act does",
           "(((e -> k) & e)) -> k", "e",
           {"e": tv(COUNT["axiom_ground"] == 1 and len(ACROSS["posit"]) == 1)},
           {"e": f"an axiom as a ground reads {COUNT['axiom_ground']} time(s) — but as a POSIT its value over "
                 f"every base is {sorted(ACROSS['posit'])}"},
           set(), ("FAILS",),
           "his axiom reads once only GIVEN a base, and a rival base reads it the other way (posit_relative). "
           "If his self-evident truth is constructed, not posited, it is an act — then he and we agree")

    # ---- G/H. allies whose act is not ours -------------------------------------------------------
    critic("Descartes: the cogito, then God guarantees clear and distinct perception",
           "knowledge beyond the cogito needs a guarantor",
           "(((d -> k) & d)) -> k", "d",
           {"d": tv(COUNT["cartesian"] == 1)}, {"d": f"the Cartesian circle has {COUNT['cartesian']} readings"},
           set(), ("FAILS",),
           "the guarantee runs in a circle and reads twice; the cogito itself, read as a performance, is the "
           "act — the circle built on it is not")
    critic("Fichte: the primary act is the I positing itself (I = I)",
           "the first principle is a self-positing act — so the act rests on itself",
           "(((f -> k) & f)) -> k", "f",
           {"f": tv(COUNT["fichte_I"] == 1)}, {"f": f"'I rests on I' has {COUNT['fichte_I']} readings"},
           set(), ("FAILS",),
           "a SELF-POSITING act is 'p because p' — the fork. The act that reads once rests on NOTHING. This is "
           "why the thesis must not say 'self-supporting'")

    # ---- I. "the ground is not knowledge" --------------------------------------------------------
    critic("Wittgenstein (On Certainty): at the bottom is acting, and it is not knowledge",
           "the end of giving grounds is unfounded certainty, not a known proposition",
           "(((u -> ~k) & u)) -> ~k", "u",
           {}, {"u": "whether the ground ITSELF is called 'known' is a decision about the word"},
           set(), ("OPEN", {"u": "Z_PERMANENT"}),
           "a word, not a count: both sides stipulate. The thesis is safer as 'knowledge RESTS only on the act' "
           "than as 'the act IS knowledge'")

    print("\n" + "=" * 100)
    print(f"{'critic':<72} {'outcome':<8} weak link")
    for name, outcome, weak, stamps in ROWS:
        w = ", ".join(f"{a}:{s}" for a, s in stamps.items()) or "—"
        print(f"{name[:71]:<72} {outcome:<8} {w}")
    fails = sum(1 for r in ROWS if r[1] == "FAILS")
    stands = sum(1 for r in ROWS if r[1] == "STANDS")
    opens = sum(1 for r in ROWS if r[1] == "OPEN")
    print(f"\n{len(ROWS)} rows: {fails} fail on a measured premise, {stands} stand, {opens} rest on credit.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
