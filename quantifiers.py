# -*- coding: utf-8 -*-
"""
Кванторы ZTL на конечных доменах.

По порождающему принципу:
    ∀x φ = большая конъюнкция: T, если КАЖДЫЙ экземпляр строго T, иначе F
           (один Z-свидетель отравляет универсалию — она не заслужена);
    ∃x φ = большая дизъюнкция: T, если ХОТЬ ОДИН экземпляр строго T, иначе F
           (Z-кандидат свидетелем не считается).
Жадность распространяется: составные формулы (в т.ч. кванторные) не
принимают Z; Z живёт только на атомарных фактах P(a).

Промеры (MEASURED): законы и правила с кванторами на всех интерпретациях
унарных P,Q (домены 1..3) и бинарного R (домены 1..2).
"""

from itertools import product

from ztl import T, F, Z, VALUES, NOT, OPS2


def ev_fo(phi, dom, interp, env):
    """Значение формулы первого порядка.
    interp: имя предиката -> кортеж значений (унарный: по элементам;
    бинарный: interp[имя][i][j]). env: переменная -> индекс элемента."""
    op = phi[0]
    if op == "all":
        vals = [ev_fo(phi[2], dom, interp, {**env, phi[1]: d}) for d in dom]
        return T if all(v == T for v in vals) else F
    if op == "ex":
        vals = [ev_fo(phi[2], dom, interp, {**env, phi[1]: d}) for d in dom]
        return T if any(v == T for v in vals) else F
    if op == "not":
        return NOT(ev_fo(phi[1], dom, interp, env))
    if op in OPS2:
        return OPS2[op](ev_fo(phi[1], dom, interp, env),
                        ev_fo(phi[2], dom, interp, env))
    # атомарный факт: ('P', 'x') или ('R', 'x', 'y')
    if len(phi) == 2:
        return interp[op][env[phi[1]]]
    return interp[op][env[phi[1]]][env[phi[2]]]


def unary_interps(dom, names):
    """Все интерпретации унарных предикатов names на домене."""
    per_pred = list(product(VALUES, repeat=len(dom)))
    for combo in product(per_pred, repeat=len(names)):
        yield dict(zip(names, combo))


def binary_interps(dom, name):
    """Все интерпретации одного бинарного предиката."""
    n = len(dom)
    for flat in product(VALUES, repeat=n * n):
        yield {name: tuple(tuple(flat[i * n + j] for j in range(n))
                           for i in range(n))}


def preds_of(phi, acc=None):
    if acc is None:
        acc = {}
    op = phi[0]
    if op in ("all", "ex"):
        preds_of(phi[2], acc)
    elif op == "not":
        preds_of(phi[1], acc)
    elif op in OPS2:
        preds_of(phi[1], acc)
        preds_of(phi[2], acc)
    else:
        acc[op] = len(phi) - 1
    return acc


def interps_for(formulas, dom):
    """Все совместные интерпретации всех предикатов набора формул."""
    arity = {}
    for f in formulas:
        arity.update(preds_of(f))
    unary = sorted(n for n, a in arity.items() if a == 1)
    binary = sorted(n for n, a in arity.items() if a == 2)
    assert len(binary) <= 1, "поддержан один бинарный предикат"
    if binary:
        for bi in binary_interps(dom, binary[0]):
            if unary:
                for ui in unary_interps(dom, unary):
                    yield {**bi, **ui}
            else:
                yield bi
    else:
        yield from unary_interps(dom, unary)


def fo_equal(lhs, rhs, max_dom=3):
    """Первый контрпример к тождеству, иначе None."""
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for([lhs, rhs], dom):
            a, b = ev_fo(lhs, dom, interp, {}), ev_fo(rhs, dom, interp, {})
            if a != b:
                return (dom, interp, a, b)
    return None


def fo_valid(phi, max_dom=3):
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for([phi], dom):
            if ev_fo(phi, dom, interp, {}) != T:
                return (dom, interp)
    return None


def fo_entails(premises, conclusion, max_dom=3):
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for(premises + [conclusion], dom):
            if all(ev_fo(p, dom, interp, {}) == T for p in premises) \
                    and ev_fo(conclusion, dom, interp, {}) != T:
                return (dom, interp)
    return None


# --- батарея: P(a) кодируем атомом (P, x) при env {x: 0} — «a» = элемент 0 ---
P, Q = "P", "Q"
x, y = "x", "y"


def fo_entails_const(premises, conclusion, max_dom=3):
    """Как fo_entails, но свободная переменная x читается как константа 0."""
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for(premises + [conclusion], dom):
            env = {x: 0}
            if all(ev_fo(p, dom, interp, env) == T for p in premises) \
                    and ev_fo(conclusion, dom, interp, env) != T:
                return (dom, interp)
    return None


def fo_valid_const(phi, max_dom=3):
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for([phi], dom):
            if ev_fo(phi, dom, interp, {x: 0}) != T:
                return (dom, interp)
    return None


IDENTITIES = [
    ("Де Морган ∀:  ¬∀xP = ∃x¬P",
     ("not", ("all", x, (P, x))), ("ex", x, ("not", (P, x)))),
    ("Де Морган ∃:  ¬∃xP = ∀x¬P",
     ("not", ("ex", x, (P, x))), ("all", x, ("not", (P, x)))),
    ("дистрибуция ∀ по ∧: ∀x(P∧Q) = ∀xP ∧ ∀xQ",
     ("all", x, ("and", (P, x), (Q, x))),
     ("and", ("all", x, (P, x)), ("all", x, (Q, x)))),
    ("дистрибуция ∃ по ∨: ∃x(P∨Q) = ∃xP ∨ ∃xQ",
     ("ex", x, ("or", (P, x), (Q, x))),
     ("or", ("ex", x, (P, x)), ("ex", x, (Q, x)))),
]

VALIDITIES_C = [
    ("UI-закон: ∀yP(y) → P(a)",
     ("imp", ("all", y, (P, y)), (P, x))),
    ("EG-закон: P(a) → ∃yP(y)",
     ("imp", (P, x), ("ex", y, (P, y)))),
    ("непустота: ∀yP(y) → ∃yP(y)",
     ("imp", ("all", y, (P, y)), ("ex", y, (P, y)))),
    ("кв. LEM: ∀y(P(y)∨¬P(y))",
     ("all", y, ("or", (P, y), ("not", (P, y))))),
    ("пьяница: ∃y(P(y)→∀zP(z))",
     ("ex", y, ("imp", (P, y), ("all", "z", (P, "z"))))),
]

RULES_FO = [
    ("UI-правило: ∀yP ⊨ P(a)",
     [("all", y, (P, y))], (P, x), fo_entails_const),
    ("EG-правило: P(a) ⊨ ∃yP",
     [(P, x)], ("ex", y, (P, y)), fo_entails_const),
    ("∀¬ ⊨ ¬∃:  ∀y¬P ⊨ ¬∃yP",
     [("all", y, ("not", (P, y)))], ("not", ("ex", y, (P, y))), fo_entails),
    ("¬∃ ⊨ ∀¬:  ¬∃yP ⊨ ∀y¬P",
     [("not", ("ex", y, (P, y)))], ("all", y, ("not", (P, y))), fo_entails),
    ("смена кванторов: ∃x∀yR(x,y) ⊨ ∀y∃xR(x,y)",
     [("ex", x, ("all", y, ("R", x, y)))],
     ("all", y, ("ex", x, ("R", x, y))),
     lambda p, c, max_dom=2: fo_entails(p, c, max_dom)),
]


def fmt_interp(dom, interp):
    parts = []
    for name, val in sorted(interp.items()):
        parts.append(f"{name}={val}")
    return f"|D|={len(dom)}: " + "; ".join(parts)


if __name__ == "__main__":
    print("=" * 72)
    print("КВАНТОРЫ ZTL: ∀ = все строго T; ∃ = есть строгий T-свидетель")
    print("=" * 72)

    print("\n-- ТОЖДЕСТВА --")
    for name, lhs, rhs in IDENTITIES:
        cex = fo_equal(lhs, rhs)
        if cex is None:
            print(f"  ✓ {name}")
        else:
            dom, interp, a, b = cex
            print(f"  ✗ {name}   [{fmt_interp(dom, interp)} → {a} vs {b}]")

    print("\n-- ЗАКОНЫ (общезначимость; a — элемент 0) --")
    for name, phi in VALIDITIES_C:
        cex = fo_valid_const(phi)
        if cex is None:
            print(f"  ✓ {name}")
        else:
            dom, interp = cex
            print(f"  ✗ {name}   [{fmt_interp(dom, interp)}]")

    print("\n-- ПРАВИЛА (следования) --")
    for name, prems, concl, checker in RULES_FO:
        cex = checker(prems, concl)
        if cex is None:
            print(f"  ✓ {name}")
        else:
            dom, interp = cex
            print(f"  ✗ {name}   [{fmt_interp(dom, interp)}]")
