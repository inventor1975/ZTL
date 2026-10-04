# -*- coding: utf-8 -*-
"""kochen_specker — the Mermin–Peres square as a NEGATIVE CONTROL for the mechanical grounding rule.

ONE-CRITERION.md listed the missing test: "No case was tested where the rule could have picked the wrong step;
Kochen–Specker contextuality and the PBR theorem are candidates." KS has a known right answer that a careless
lens gets wrong: KS refutes NON-CONTEXTUAL hidden values, while CONTEXTUAL hidden values (Bohm) are consistent
with quantum mechanics. A lens that refutes contextual values over-refutes; one that cannot refute
non-contextual ones misses KS. The prediction was written BEFORE this file ran
(ztl-private/notes/KS-PREDICTION-2026-10-04.md, ~21:30).

  THE SQUARE. row1: XI, IX, XX;  row2: IZ, ZI, ZZ;  row3: XZ, ZX, YY. Each row and each column is a CONTEXT
  (three commuting observables, measurable together). Products: rows +I, columns 1-2 +I, column 3 -I.

  THE GROUNDING RULE (hardy.py's rule, extended before this run to commuting-but-unasked atoms). A run asks one
  context and gets three answers (+1 <-> T):
    - an atom of an asked observable: T/F by the answer (witnessed);
    - an atom of an unasked observable: Z — REDEEMABLE if its projector commutes with ALL asked projectors,
      PERMANENT if it fails to commute with at least one. Computed, not declared.
  E1 NON-CONTEXTUAL: one atom per observable.  E2 CONTEXTUAL: one atom per (observable, context).

  K1  THE PHYSICS, from 4x4 matrices: the six identities, the contexts commute inside, the square's
      cross pairs do not.
  K2  E1, a run asking row 1: answers EARNED; the six unasked Z_PERMANENT; the six laws together false in
      EVERY completion (kernel grade 'sound'; brute force 0/64), but NOT hereditary: after checking four of the
      six (v21=F, v22=T, v31=F, v32=T) the verdict reads T, because the two still unchecked cells make their
      laws hold ON CREDIT (Z<->Z is F in the greedy register, so its negation is T). A verdict some path of
      checks revokes is not established, so judge() says OPEN, as the kernel's theorems require (hereditary is
      the only grade no check revokes). My prediction point 1 (REFUTED) FAILED: I assumed the KS contradiction
      is hereditary like Hardy's. (I first called OPEN a judge defect — wrong, retracted the same evening.)
  K3  E2, the same run: the six laws together NOT false in every completion — contextual completions exist.
      THE CONTROL: had this come out refuted (or 'sound' F), the lens would kill Bohm, i.e. pick the wrong step.
  K4  The run space: 6 contexts x every outcome with P > 0 x two states — no law is ever refuted under E1.

  PRIOR ART, plainly: Kochen & Specker (1967); Bell (1966); Mermin, PRL 65, 3373 (1990); Peres (1990); Bohm (1952).
  quantum_ladder.py already counted the 0/512 assignments; what is new here is the run-level grounding by the
  rule and the contextual encoding as a control.

Run:  python3 dilemmas/kochen_specker.py        (asserts every measurement)
"""

import itertools
import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import ceiling, stamp  # noqa: E402

I2 = [[1, 0], [0, 1]]
PX = [[0, 1], [1, 0]]
PY = [[0, -1j], [1j, 0]]
PZ = [[1, 0], [0, -1]]
P1 = {"I": I2, "X": PX, "Y": PY, "Z": PZ}
SQUARE = [["XI", "IX", "XX"], ["IZ", "ZI", "ZZ"], ["XZ", "ZX", "YY"]]


def kron(a, b):
    return [[a[i // 2][j // 2] * b[i % 2][j % 2] for j in range(4)] for i in range(4)]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]


def op(name):
    return kron(P1[name[0]], P1[name[1]])


ID4 = [[1 if i == j else 0 for j in range(4)] for i in range(4)]


def proj(name, s):                                   # projector onto eigenvalue s (+1/-1)
    o = op(name)
    return [[(ID4[i][j] + s * o[i][j]) / 2 for j in range(4)] for i in range(4)]


def dist(a, b):
    return max(abs(a[i][j] - b[i][j]) for i in range(4) for j in range(4))


def comm(a, b):
    return dist(mul(a, b), mul(b, a))


def expect(m, psi):
    v = [sum(m[i][j] * psi[j] for j in range(4)) for i in range(4)]
    return sum((psi[i].conjugate() if isinstance(psi[i], complex) else psi[i]) * v[i] for i in range(4)).real


CONTEXTS = [("row", r, [(r, c) for c in range(3)]) for r in range(3)] + \
           [("col", c, [(r, c) for r in range(3)]) for c in range(3)]
SIGN = {("row", 0): 1, ("row", 1): 1, ("row", 2): 1, ("col", 0): 1, ("col", 1): 1, ("col", 2): -1}


def law(atoms, sign):
    a, b, c = atoms
    f = f"{a} <-> ({b} <-> {c})"                       # product +1 <-> an even number of -1 (F)
    return f if sign == 1 else f"~({f})"


def e1(pos):
    return f"v{pos[0] + 1}{pos[1] + 1}"


def e2(pos, kind):
    return f"{kind[0]}{pos[0] + 1}{pos[1] + 1}"


LAWS_E1 = [law([e1(p) for p in ps], SIGN[(k, n)]) for k, n, ps in CONTEXTS]
LAWS_E2 = [law([e2(p, k) for p in ps], SIGN[(k, n)]) for k, n, ps in CONTEXTS]
CHAIN_E1 = " & ".join(f"({x})" for x in LAWS_E1)
CHAIN_E2 = " & ".join(f"({x})" for x in LAWS_E2)


def outcomes(ctx, psi):
    k, n, ps = ctx
    out = []
    for signs in itertools.product((1, -1), repeat=3):
        m = ID4
        for p, s in zip(ps, signs):
            m = mul(m, proj(SQUARE[p[0]][p[1]], s))
        pr = expect(m, psi)
        if pr > 1e-12:
            out.append((signs, pr))
    return out


def ground_e1(ctx, signs):
    """THE RULE, non-contextual encoding."""
    k, n, ps = ctx
    asked = {p: s for p, s in zip(ps, signs)}
    asked_proj = [proj(SQUARE[p[0]][p[1]], s) for p, s in asked.items()]
    m, rep, kind = {}, set(), {}
    for r, c in itertools.product(range(3), repeat=2):
        a = e1((r, c))
        if (r, c) in asked:
            m[a] = "T" if asked[(r, c)] == 1 else "F"
            rep.add(a)
        else:
            m[a] = "Z"
            mine = proj(SQUARE[r][c], 1)
            if all(comm(mine, q) < 1e-9 for q in asked_proj):
                rep.add(a)                             # could still be asked jointly
                kind[a] = "redeemable"
            else:
                kind[a] = "permanent"
    return m, rep, kind


def ground_e2(ctx, signs):
    """THE RULE, contextual encoding: only the atoms of the asked (observable, context) are witnessed."""
    k, n, ps = ctx
    m = {}
    for kk, nn, pps in CONTEXTS:
        for p in pps:
            m[e2(p, kk)] = "Z"
    for p, s in zip(ps, signs):
        m[e2(p, k)] = "T" if s == 1 else "F"
    return m, {a for a, v in m.items() if v != "Z"}


def completions(chain, m):
    """Independent brute force: how many completions of the Z atoms make the conjunction true."""
    unk = [a for a in m if m[a] == "Z"]
    good = 0
    for combo in itertools.product("TF", repeat=len(unk)):
        mm = dict(m)
        mm.update(zip(unk, combo))
        good += judge(chain, mm)["verdict"] == "T"
    return good, 2 ** len(unk)


def run():
    print("KOCHEN–SPECKER — the Mermin–Peres square as a negative control for the grounding rule")
    print("=" * 72)

    print("\n### K1. The physics, from 4x4 matrices")
    for k, n, ps in CONTEXTS:
        prod = ID4
        for p in ps:
            prod = mul(prod, op(SQUARE[p[0]][p[1]]))
        target = [[SIGN[(k, n)] * x for x in row] for row in ID4]
        assert dist(prod, target) < 1e-12
        assert all(comm(op(SQUARE[a[0]][a[1]]), op(SQUARE[b[0]][b[1]])) < 1e-12 for a, b in itertools.combinations(ps, 2))
    cross = sum(1 for a, b in itertools.combinations(itertools.product(range(3), repeat=2), 2)
                if a[0] != b[0] and a[1] != b[1] and comm(op(SQUARE[a[0]][a[1]]), op(SQUARE[b[0]][b[1]])) > 1e-9)
    print(f"ok  six identities: rows +I, columns 1-2 +I, column 3 -I; each context commutes inside; "
          f"cross pairs (other row AND other column) not commuting: {cross} of 18")
    assert cross == 18

    psi0 = [1, 0, 0, 0]
    s3 = 1 / math.sqrt(3)
    psi1 = [s3, 1j * s3, 0, s3]                          # an entangled state (KS is state-independent)
    row1 = CONTEXTS[0]
    signs, pr = outcomes(row1, psi0)[0]

    print(f"\n### K2. E1 (non-contextual), a run asking row 1 on |00>: answers {signs} (P = {pr:.3f})")
    m, rep, kind = ground_e1(row1, signs)
    r = judge(CHAIN_E1, m)
    c = ceiling(CHAIN_E1, m, rep)
    unasked = sorted(a for a in m if m[a] == "Z")
    st = {a: stamp(a, m, rep) for a in unasked}
    alone = {x: judge(x, m)["disposition"] for x in LAWS_E1}
    good, total = completions(CHAIN_E1, m)
    print(f"ok  unasked atoms: {unasked}, stamps {sorted(set(st.values()))}")
    print(f"ok  the six laws together: verdict {r['verdict']}, grade {r['grade']!r}, disposition {r['disposition']}; "
          f"ceiling frozen = {c['ceiling_frozen']}; brute force: {good} of {total} completions satisfy them")
    print(f"ok  each law alone: {sorted(set(alone.values()))}")
    assert set(st.values()) == {"Z_PERMANENT"} and set(kind.values()) == {"permanent"}
    assert r["verdict"] == "F" and r["grade"] == "sound" and good == 0 and c["ceiling_frozen"]
    assert "REFUTED" not in alone.values()
    # PREDICTION POINT 1 FAILED (2026-10-04): I predicted REFUTED. The kernel grades the F 'sound' (false in
    # every completion; brute force 0/64) but not hereditary: the path below reads T on the way. OPEN is right.
    path = dict(m, v21="F", v22="T", v31="F", v32="T")
    on_way = judge(CHAIN_E1, path)["verdict"]
    print(f"ok  on the way: after checking v21=F, v22=T, v31=F, v32=T (v23, v33 unchecked) the verdict reads {on_way};"
          f" so the F is revocable on a path -> not hereditary -> judge: {r['disposition']}")
    assert on_way == "T" and r["disposition"] == "OPEN"
    assert all(judge(a, m)["disposition"] == "EARNED" for a in m if m[a] == "T") and \
        all(judge(a, m)["disposition"] == "REFUTED" for a in m if m[a] == "F")

    print("\n### K3. E2 (contextual), the same run — THE CONTROL (refuted here = the lens kills Bohm)")
    m2, rep2 = ground_e2(row1, signs)
    r2 = judge(CHAIN_E2, m2)
    c2 = ceiling(CHAIN_E2, m2, rep2)
    good2, total2 = completions(CHAIN_E2, m2)
    print(f"ok  the six laws together: verdict {r2['verdict']}, grade {r2['grade']!r}, disposition {r2['disposition']}; "
          f"brute force: {good2} of {total2} completions satisfy them")
    assert r2["disposition"] != "REFUTED" and r2["grade"] != "sound" and good2 > 0
    print("ok  READING: non-contextual values are false in every completion (E1), contextual ones are not (E2) — what falls is")
    print("    NON-CONTEXTUAL value definiteness, exactly the content of Kochen–Specker; Bohm's contextual values stand")

    print("\n### K4. The run space: no law is ever refuted under E1")
    runs, bad, earned = 0, [], 0
    for psi_name, psi in (("|00>", psi0), ("entangled", psi1)):
        nrm = sum(abs(x) ** 2 for x in psi)
        assert abs(nrm - 1) < 1e-12
        for ctx in CONTEXTS:
            outs = outcomes(ctx, psi)
            assert abs(sum(p for _, p in outs) - 1) < 1e-9
            for sg, _ in outs:
                runs += 1
                m, _, _ = ground_e1(ctx, sg)
                for x in LAWS_E1:
                    d = judge(x, m)["disposition"]
                    earned += d == "EARNED"
                    bad += [(psi_name, ctx[:2], sg, x)] if d == "REFUTED" else []
                r1 = judge(CHAIN_E1, m)
                assert r1["verdict"] == "F" and r1["grade"] in ("sound", "hereditary")
                r2_ = judge(CHAIN_E2, ground_e2(ctx, sg)[0])
                assert r2_["disposition"] != "REFUTED" and r2_["grade"] != "sound"
    print(f"ok  {runs} possible runs x 6 laws: refuted {len(bad)}, earned {earned}, the rest open; "
          f"in every run E1's conjunction false in every completion and E2's not")
    assert not bad and earned > 0

    print("\nKOCHEN–SPECKER: all measurements hold.")
    print("Non-contextual values fall, contextual values stand: the lens picks Kochen–Specker's step, not a wider one.")


if __name__ == "__main__":
    run()
