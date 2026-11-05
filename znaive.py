# -*- coding: utf-8 -*-
"""
znaive — naive set definitions in front of the passport office.

A universe is a finite list of NAMES. Every name is a set, and every set is
also an object that can be a member (naive: sets are things). A set is given
in one of three ways:

  list   {"list": [a, b]}           — extensional, closed: a and b are in,
                                      every other name is out (F);
  data   {"data": {"a": "T", "b": "Z"}} — given cell by cell; an unlisted cell
                                      is UNKNOWN (Z, an unverified input);
  abs    {"abs": φ}                 — by a property: {x : φ}, with NO
                                      restriction on φ (it may mention the set
                                      being defined, x ∈ x, anything).

Formulas (JSON lists): ["in", s, t], ["not", φ], ["and", φ, ψ], ["or", φ, ψ],
["imp", φ, ψ], ["iff", φ, ψ], ["all", "y", φ], ["ex", "y", φ], ["eq", s, t]
(identity by extension: ∀z (z∈s ↔ z∈t)), ["true"], ["false"]. A term is a
bound variable or a name. Quantifiers range over the universe's names — a
finite range, as ZTL requires (a universal over an unsurveyed range is not an
act).

What happens: every cell "a∈S" becomes a sentence of a fixedpoint system (an
abs set's cell is its property instantiated at a, constants folded in); the
LAZY least fixed point grounds the cells (Kripke); the E18 passport office
(zpassport) gives every quarantined cell its kind — PARADOX (no stipulation
can repair it), UNDERDETERMINED (a stipulation is owed; it is consistent),
INTRINSIC, INPUT (verify the given cell), DOWNSTREAM (inherits a quarantine).
A CLAIM is a closed formula: its lazy value gives EARNED / REFUTED; otherwise
its dirty cells are completed every way (each cell one value), giving
EARNED IF STABLE / REFUTED IF STABLE / OPEN — the ztljudge rule — and the
cells it rests on are listed WITH their passports. For a universal claim the
residue (the instances left undecided) is named.

This is the finite, executable twin of VR/SetsNaive (Lean, all on []): the
same lazy fixed point (Ground), the same passport (Passport), the same
completions (Judge) and residue (Residue). Two boundaries carried over:
completions are free at dirty cells, so a claim's disposition depends on how
it is spelled (atom vs definition — SetsNaive N8); and identity by extension
is lazily earned only between sets that decide every probe (N10).

Neighbour, not duplicate: zsets.py (E5, ZTL-sets) is the EXTENSIONAL side — finite sets of observed
elements, some of them dirty marks, membership an ∃-fold of identity atoms. znaive is the
INTENSIONAL side — sets by a property, self-reference allowed; it does not use E5.

Run:  python3 znaive.py UNIVERSE.json      python3 znaive.py   (no argument: the self-test)
Stdlib only; reuses fixedpoint.py and zpassport.py.
"""

import itertools
import json
import sys

from ztl import T, F, Z, VALUES
from fixedpoint import LAZY, ev_reg, least_fp_lazy, jump
from zpassport import passports, sccs, deps

CAP_COMPONENT = 16   # a quarantined component larger than this is not searched
CAP_STABLE = 12      # at most 2^12 completions per claim


class UniverseError(ValueError):
    pass


def cell(a, s):
    return f"{a}∈{s}"


# ------------------------------------------------------------ constant folding
def _not(p):
    if p == T:
        return F
    if p == F:
        return T
    return ("not", p)


def _and(p, q):
    if p == F or q == F:
        return F
    if p == T:
        return q
    if q == T:
        return p
    return ("and", p, q)


def _or(p, q):
    if p == T or q == T:
        return T
    if p == F:
        return q
    if q == F:
        return p
    return ("or", p, q)


def _imp(p, q):
    return _or(_not(p), q)


def _iff(p, q):
    if p in (T, F) and q in (T, F):
        return T if p == q else F
    if p == T:
        return q
    if q == T:
        return p
    if p == F:
        return _not(q)
    if q == F:
        return _not(p)
    return ("xnor", p, q)


# ------------------------------------------------------------------- grounding
class Universe:
    def __init__(self, spec):
        sets = spec.get("sets")
        if not isinstance(sets, dict) or not sets:
            raise UniverseError("a universe needs a non-empty 'sets' object")
        self.names = list(sets)
        self.spec = sets
        self.const = {}          # cell -> T/F/Z for list/data sets
        self.abs = {}            # set name -> formula
        for s, d in sets.items():
            if not isinstance(d, dict) or len(d) != 1:
                raise UniverseError(f"set {s!r}: give exactly one of list / data / abs")
            (kind, body), = d.items()
            if kind == "list":
                bad = [m for m in body if m not in sets]
                if bad:
                    raise UniverseError(f"set {s!r} lists unknown names {bad} — no subject")
                for a in self.names:
                    self.const[cell(a, s)] = T if a in body else F
            elif kind == "data":
                bad = [m for m in body if m not in sets]
                if bad:
                    raise UniverseError(f"set {s!r} gives cells for unknown names {bad}")
                for a in self.names:
                    v = body.get(a, Z)
                    if v not in VALUES:
                        raise UniverseError(f"set {s!r}: cell {a} has value {v!r}, not T/F/Z")
                    self.const[cell(a, s)] = v
            elif kind == "abs":
                self.abs[s] = body
            else:
                raise UniverseError(f"set {s!r}: unknown kind {kind!r}")

    def _term(self, t, env):
        if t in env:
            return env[t]
        if t in self.spec:
            return t
        raise UniverseError(f"term {t!r} is neither a bound variable nor a name — no subject")

    def _atom(self, a, s):
        c = cell(a, s)
        v = self.const.get(c)
        if v in (T, F):
            return v          # fold a given clean cell in
        return c              # an abs cell, or an unknown (Z) given cell

    def ground(self, phi, env):
        if not isinstance(phi, list) or not phi:
            raise UniverseError(f"malformed formula {phi!r}")
        op = phi[0]
        if op == "true":
            return T
        if op == "false":
            return F
        if op == "in":
            return self._atom(self._term(phi[1], env), self._term(phi[2], env))
        if op == "not":
            return _not(self.ground(phi[1], env))
        if op in ("and", "or", "imp", "iff"):
            p, q = self.ground(phi[1], env), self.ground(phi[2], env)
            return {"and": _and, "or": _or, "imp": _imp, "iff": _iff}[op](p, q)
        if op in ("all", "ex"):
            var = phi[1]
            acc = T if op == "all" else F
            for n in self.names:
                g = self.ground(phi[2], {**env, var: n})
                acc = _and(acc, g) if op == "all" else _or(acc, g)
            return acc
        if op == "eq":
            a, b = self._term(phi[1], env), self._term(phi[2], env)
            acc = T
            for z in self.names:
                acc = _and(acc, _iff(self._atom(z, a), self._atom(z, b)))
            return acc
        raise UniverseError(f"unknown connective {op!r}")

    def system(self):
        sysm = {}
        for c, v in self.const.items():
            sysm[c] = v
        for s, phi in self.abs.items():
            for a in self.names:
                sysm[cell(a, s)] = self.ground(phi, {"x": a})
        return sysm


# -------------------------------------------------------------------- analysis
def analyse(spec):
    """Ground the universe, compute the lazy least fixed point and passports.
    Returns (universe, system, lfp, kind) with kind[cell] a passport word."""
    u = Universe(spec)
    sysm = u.system()
    for comp in sccs(sysm):
        if len(comp) > CAP_COMPONENT:
            raise UniverseError(f"a component of {len(comp)} cells exceeds the cap of "
                                f"{CAP_COMPONENT} — passport not searched (2^{len(comp)} models)")
    lfp, _reports, comp_kind = passports(sysm)
    kind = {}
    for c in sysm:
        if lfp[c] in (T, F):
            kind[c] = "GROUNDED"          # grounded cells keep their own label even
        else:                             # inside a mixed component
            kind[c] = comp_kind[c][0]
    return u, sysm, lfp, kind


def judge_claim(analysis, claim):
    """Disposition of a closed claim, the cells it rests on (with passports),
    and — for a universal claim — its residue."""
    u, _sysm, lfp, kind = analysis
    g = u.ground(claim, {})
    lv = ev_reg(g, lfp, LAZY) if g not in VALUES else g
    dirty = sorted(d for d in deps(g) if lfp.get(d) == Z) if g not in VALUES else []
    bearing = {d: kind[d] for d in dirty}
    if lv == T:
        disp = "EARNED"
    elif lv == F:
        disp = "REFUTED"
    elif len(dirty) > CAP_STABLE:
        disp = "OPEN"
    else:
        seen = set()
        for bits in itertools.product((T, F), repeat=len(dirty)):
            v = {**lfp, **dict(zip(dirty, bits))}
            seen.add(ev_reg(g, v, LAZY))
            if len(seen) > 1:
                break
        only = seen.pop() if len(seen) == 1 else None
        disp = {T: "EARNED IF STABLE", F: "REFUTED IF STABLE"}.get(only, "OPEN")
    residue = None
    if claim[0] == "all":
        residue = []
        for n in u.names:
            gi = u.ground(claim[2], {claim[1]: n})
            vi = gi if gi in VALUES else ev_reg(gi, lfp, LAZY)
            if vi == Z:
                residue.append(n)
    return {"lazy": lv, "disposition": disp, "rests_on": bearing, "residue": residue}


def report(spec):
    analysis = analyse(spec)
    u, _sysm, lfp, kind = analysis
    lines = []
    for s in u.names:
        ins = [a for a in u.names if lfp[cell(a, s)] == T]
        outs = [a for a in u.names if lfp[cell(a, s)] == F]
        dirty = [f"{a} ({kind[cell(a, s)]})" for a in u.names if lfp[cell(a, s)] == Z]
        lines.append(f"{s}: in {ins}; out {outs}" + (f"; quarantined {dirty}" if dirty else ""))
    for i, claim in enumerate(spec.get("claims", [])):
        r = judge_claim(analysis, claim)
        lines.append(f"claim {i}: {r['disposition']}"
                     + (f"; rests on {r['rests_on']}" if r["rests_on"] else "")
                     + (f"; residue {r['residue']}" if r["residue"] else ""))
    return "\n".join(lines)


# --------------------------------------------------------------- the mutant
def closed_world(sysm, lfp):
    """The sabotage the self-test must catch: read every quarantined cell as F
    (closed-world / negation-as-failure without stratification). Returns the
    cells whose own definition then disagrees with the value assigned."""
    cwa = {c: (F if v == Z else v) for c, v in lfp.items()}
    j = jump(sysm, cwa, LAZY)
    return sorted(c for c in sysm if j[c] != cwa[c])


# ----------------------------------------------------------- independent oracle
def _rand_formula(rng, names, vars_, depth):
    terms = list(names) + list(vars_)
    if depth == 0 or rng.random() < 0.3:
        return ["in", rng.choice(terms), rng.choice(terms)]
    op = rng.choice(["not", "and", "or", "imp", "iff", "all", "ex"])
    if op == "not":
        return ["not", _rand_formula(rng, names, vars_, depth - 1)]
    if op in ("all", "ex"):
        v = f"v{depth}"
        return [op, v, _rand_formula(rng, names, vars_ + [v], depth - 1)]
    return [op, _rand_formula(rng, names, vars_, depth - 1), _rand_formula(rng, names, vars_, depth - 1)]


def _rand_universe(rng):
    names = [f"n{i}" for i in range(rng.choice([2, 3]))]
    sets = {}
    for n in names:
        k = rng.random()
        if k < 0.25:
            sets[n] = {"list": [m for m in names if rng.random() < 0.5]}
        elif k < 0.4:
            sets[n] = {"data": {m: rng.choice([T, F, Z]) for m in names if rng.random() < 0.6}}
        else:
            sets[n] = {"abs": _rand_formula(rng, names, ["x"], 2)}
    return {"sets": sets}


def full_models(sysm, lfp, cap=10):
    """Every classical (two-valued) valuation that is a fixed point of the system, with the
    unverified inputs (cells given as Z) read freely. None if too many free cells."""
    free = sorted(c for c, v in lfp.items() if v == Z)
    if len(free) > cap:
        return None
    models = []
    for bits in itertools.product((T, F), repeat=len(free)):
        v = {**lfp, **dict(zip(free, bits))}
        if all((sysm[c] == Z) or ev_reg(sysm[c], v, LAZY) == v[c] for c in sysm):
            models.append(v)
    return models


def oracle_check(trials=300, seed=20261105):
    import random
    rng = random.Random(seed)
    checked = paradox_seen = stable_seen = 0
    for _ in range(trials):
        spec = _rand_universe(rng)
        try:
            a = analyse(spec)
        except UniverseError:
            continue
        u, sysm, lfp, kind = a
        assert jump(sysm, lfp, LAZY) == lfp, "I1: the lfp is a fixed point"
        models = full_models(sysm, lfp)
        if models is None:
            continue
        checked += 1
        for m in models:
            for c, v in lfp.items():
                if v in (T, F):
                    assert m[c] == v, "I2: a full model disagrees with a grounded cell"
        if any(k == "PARADOX" for k in kind.values()):
            paradox_seen += 1
            assert models == [], "I3: a PARADOX cell, yet a full classical model exists"
        claim = _rand_formula(rng, u.names, [], 2)
        r = judge_claim(a, claim)
        g = u.ground(claim, {})
        for m in models:
            val = g if g in VALUES else ev_reg(g, m, LAZY)
            if r["disposition"] in ("EARNED", "EARNED IF STABLE"):
                assert val == T, ("I4: EARNED but false in a full model", claim, r)
            if r["disposition"] in ("REFUTED", "REFUTED IF STABLE"):
                assert val == F, ("I4: REFUTED but true in a full model", claim, r)
        if r["disposition"].endswith("IF STABLE"):
            stable_seen += 1
    return checked, paradox_seen, stable_seen


# ------------------------------------------------------------------ self-test
RUSSELL = {"sets": {
    "a": {"list": []},
    "b": {"list": ["b"]},
    "R": {"abs": ["not", ["in", "x", "x"]]},
    "S": {"abs": ["in", "x", "x"]},
}}

# Grelling–Nelson on real adjectives: each word is the set of words it truly
# describes (checked by hand on the words themselves: "short" is short, "long"
# is not long, "English" is English, "German" is not German, "polysyllabic"
# has many syllables, "monosyllabic" has five).
WORDS = ["short", "long", "English", "German", "polysyllabic", "monosyllabic", "Het", "Aut"]
GRELLING = {"sets": {
    "short": {"list": ["short", "long"]},
    "long": {"list": ["polysyllabic", "monosyllabic", "Het", "Aut"]},
    "English": {"list": ["short", "long", "English", "German", "polysyllabic",
                         "monosyllabic", "Het", "Aut"]},
    "German": {"list": []},
    "polysyllabic": {"list": ["English", "German", "polysyllabic", "monosyllabic", "Het", "Aut"]},
    "monosyllabic": {"list": ["short", "long"]},
    "Het": {"abs": ["not", ["in", "x", "x"]]},       # heterological: does not describe itself
    "Aut": {"abs": ["in", "x", "x"]},                # autological: describes itself
}}

# A web of trust: a key is the set of its signers; a key is trusted if it is
# a root or is signed by a trusted key. mallory1 and mallory2 sign each other.
TRUST = {"sets": {
    "Keys": {"list": ["root", "alice", "bob", "carol", "mallory1", "mallory2"]},
    "Roots": {"list": ["root"]},
    "root": {"list": []},
    "alice": {"list": ["root"]},
    "bob": {"list": ["alice"]},
    "carol": {"list": []},
    "mallory1": {"list": ["mallory2"]},
    "mallory2": {"list": ["mallory1"]},
    "Trusted": {"abs": ["and", ["in", "x", "Keys"],
                        ["or", ["in", "x", "Roots"],
                         ["ex", "j", ["and", ["in", "j", "Trusted"], ["in", "j", "x"]]]]]},
}, "claims": [
    ["not", ["in", "carol", "Trusted"]],
    ["all", "k", ["imp", ["in", "k", "Keys"], ["or", ["in", "k", "Trusted"], ["not", ["in", "k", "Trusted"]]]]],
    ["in", "mallory1", "Trusted"],
]}

# A self-referential access policy with a real bug: "a user is an admin unless
# they are a flagged admin".
POLICY = {"sets": {
    "Users": {"list": ["u1", "u2", "u3"]},
    "Flagged": {"list": ["u2"]},
    "u1": {"list": []}, "u2": {"list": []}, "u3": {"list": []},
    "Admin": {"abs": ["and", ["in", "x", "Users"],
                      ["not", ["and", ["in", "x", "Admin"], ["in", "x", "Flagged"]]]]},
    "Unknown": {"data": {"u1": "T"}},
}}


def _selftest():
    # Russell / truth-teller
    u, sysm, lfp, kind = analyse(RUSSELL)
    assert lfp["a∈R"] == T and lfp["b∈R"] == F, "Russell works as a set for everyone else"
    assert lfp["R∈R"] == Z and kind["R∈R"] == "PARADOX", kind["R∈R"]
    assert lfp["S∈S"] == Z and kind["S∈S"] == "UNDERDETERMINED", kind["S∈S"]
    assert jump(sysm, lfp, LAZY) == lfp, "the lfp is a fixed point"
    caught = closed_world(sysm, lfp)
    assert "R∈R" in caught, "the closed-world mutant must contradict Russell's own definition"
    print("  Russell: a∈R T, b∈R F, R∈R PARADOX, S∈S UNDERDETERMINED; "
          f"closed-world mutant caught at {caught}")

    # Grelling–Nelson on real words
    u, sysm, lfp, kind = analyse(GRELLING)
    assert lfp["short∈Het"] == F and lfp["long∈Het"] == T, "short is autological, long heterological"
    assert lfp["English∈Het"] == F and lfp["German∈Het"] == T
    assert lfp["polysyllabic∈Aut"] == T and lfp["monosyllabic∈Aut"] == F
    assert kind["Het∈Het"] == "PARADOX", kind["Het∈Het"]
    assert kind["Aut∈Aut"] == "UNDERDETERMINED", kind["Aut∈Aut"]
    caught = closed_world(sysm, lfp)
    assert "Het∈Het" in caught
    r = judge_claim(analyse(GRELLING), ["in", "Het", "Het"])
    assert r["disposition"] == "OPEN" and r["rests_on"] == {"Het∈Het": "PARADOX"}, r
    print("  Grelling (real words): short/English/polysyllabic autological, long/German/monosyllabic "
          "heterological; Het∈Het PARADOX, Aut∈Aut UNDERDETERMINED; mutant caught")

    # Web of trust
    a = analyse(TRUST)
    _u, sysm, lfp, kind = a
    for k in ("root", "alice", "bob"):
        assert lfp[f"{k}∈Trusted"] == T, k
    assert lfp["carol∈Trusted"] == F, "an unsigned key is earned untrusted"
    for k in ("mallory1", "mallory2"):
        assert lfp[f"{k}∈Trusted"] == Z and kind[f"{k}∈Trusted"] == "UNDERDETERMINED", kind[f"{k}∈Trusted"]
    r0 = judge_claim(a, TRUST["claims"][0])
    assert r0["disposition"] == "EARNED", r0
    r1 = judge_claim(a, TRUST["claims"][1])
    assert r1["disposition"] == "EARNED IF STABLE", r1
    assert r1["residue"] == ["mallory1", "mallory2"], r1["residue"]
    assert set(r1["rests_on"].values()) == {"UNDERDETERMINED"}, r1
    r2 = judge_claim(a, TRUST["claims"][2])
    assert r2["disposition"] == "OPEN", r2
    print("  web of trust: root/alice/bob EARNED trusted, carol EARNED untrusted, the mutually signing "
          "mallorys UNDERDETERMINED (a stipulation, not a fact); 'every key trusted or not' EARNED IF STABLE "
          "with residue [mallory1, mallory2]")

    # Policy bug
    a = analyse(POLICY)
    _u, sysm, lfp, kind = a
    assert lfp["u1∈Admin"] == T and lfp["u3∈Admin"] == T
    assert kind["u2∈Admin"] == "PARADOX", kind["u2∈Admin"]
    assert kind["u2∈Unknown"] == "INPUT" and lfp["u1∈Unknown"] == T
    caught = closed_world(sysm, lfp)
    assert "u2∈Admin" in caught
    print("  policy 'admin unless a flagged admin': u1, u3 EARNED admins; u2 PARADOX — the rule is broken "
          "for flagged users, no stipulation repairs it; an unknown given cell is INPUT")

    # error paths: no subject
    for bad in ({"sets": {"A": {"abs": ["in", "x", "ghost"]}}},
                {"sets": {"A": {"list": ["ghost"]}}}):
        try:
            analyse(bad)
        except UniverseError:
            pass
        else:
            raise AssertionError("an unknown name must be refused (no subject)")
    # grounded cells keep their own label inside a mixed component
    _u, _s, lfp_t, kind_t = analyse(TRUST)
    assert kind_t["root∈Trusted"] == "GROUNDED" and kind_t["carol∈Trusted"] == "GROUNDED"

    # the independent oracle: brute-force classical models of random universes
    checked, paradox_seen, stable_seen = oracle_check()
    assert checked >= 150 and paradox_seen >= 10 and stable_seen >= 5, (checked, paradox_seen, stable_seen)
    print(f"  oracle: {checked} random universes checked against brute-force classical models "
          f"(lfp fixed; grounded cells absolute; PARADOX ⇒ no model, seen {paradox_seen}; "
          f"EARNED/REFUTED [IF STABLE] hold in every model, IF STABLE seen {stable_seen})")
    # the oracle has teeth: two sabotages it must catch
    g = globals()
    honest_judge, honest_analyse = g["judge_claim"], g["analyse"]

    def open_as_stable(an, claim):
        r = honest_judge(an, claim)
        if r["disposition"] == "OPEN":
            r["disposition"] = "EARNED IF STABLE"
        return r

    def all_paradox(spec):
        uu, ss, ll, kk = honest_analyse(spec)
        return uu, ss, ll, {c: (k if k == "GROUNDED" else "PARADOX") for c, k in kk.items()}

    for label, key, bad in (("OPEN read as EARNED IF STABLE", "judge_claim", open_as_stable),
                            ("every dirty cell PARADOX", "analyse", all_paradox)):
        g[key] = bad
        try:
            oracle_check()
        except AssertionError:
            print(f"  sabotage caught: {label}")
        else:
            raise AssertionError(f"the oracle missed the sabotage: {label}")
        finally:
            g["judge_claim"], g["analyse"] = honest_judge, honest_analyse
    print("ZNAIVE GREEN")


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["--selftest"]:
        _selftest()
    elif len(sys.argv) == 2 and sys.argv[1] not in ("-h", "--help"):
        with open(sys.argv[1], encoding="utf-8") as fh:
            print(report(json.load(fh)))
    else:
        print(__doc__)
