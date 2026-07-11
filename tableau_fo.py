# -*- coding: utf-8 -*-
"""
Кванторные таблó ZTL (конечный домен).

Правила — продолжение подписи нулевого доверия: ослабленные знаки
(N={F,Z}) только в F-полярности, T-полярность требует строгих:

    T:∀xφ → T:φ(a₁),…,T:φ(aₙ)      F:∀xφ → N:φ(a₁) | … | N:φ(aₙ)
    T:∃xφ → T:φ(a₁) | … | T:φ(aₙ)  F:∃xφ → N:φ(a₁),…,N:φ(aₙ)

Жадность: кванторные формулы классичны (P≡T, N≡F на составных).
Сверка (MEASURED): решения таблó против семантического перебора всех
интерпретаций (fo-батарея из quantifiers.py + дополнения), домены 1–2.
"""

from itertools import product

from ztl import T, F, Z, VALUES, OPS2
from tableau import ST, SF, SP, SN, CLASSIC, TABLEAU_RULES
from quantifiers import ev_fo, interps_for, RULES_FO, VALIDITIES_C, P, Q, x, y


def subst(phi, var, val):
    op = phi[0]
    if op in ("all", "ex"):
        if phi[1] == var:
            return phi                      # переменная затенена
        return (op, phi[1], subst(phi[2], var, val))
    if op == "not":
        return ("not", subst(phi[1], var, val))
    if op in OPS2:
        return (op, subst(phi[1], var, val), subst(phi[2], var, val))
    return (op,) + tuple(val if t == var else t for t in phi[1:])


def closes(nodes, dom):
    """True, если таблó закрывается. nodes: список (знак, замкнутая формула)."""
    atom_signs = {}
    first = None
    rest = []
    for sign, phi in nodes:
        op = phi[0]
        if op == "not" or op in OPS2 or op in ("all", "ex"):
            s = sign & CLASSIC              # жадность: составная не Z
            if not s:
                return True
            if s == CLASSIC:
                continue                    # неинформативный знак
            if first is None:
                first = (s, phi)
            else:
                rest.append((s, phi))
        else:                               # атомарный факт P(a…)
            cur = atom_signs.get(phi, frozenset(VALUES)) & sign
            if not cur:
                return True
            atom_signs[phi] = cur
    if first is None:
        return False                        # насыщенная открытая ветвь
    s, phi = first
    base = rest + [(sg, at) for at, sg in sorted(atom_signs.items())]
    op = phi[0]
    if op in ("all", "ex"):
        v, body = phi[1], phi[2]
        insts = [subst(body, v, d) for d in dom]
        strict_all = (op == "all") == (s == ST)   # ∀ при T и ∃ при F — одной ветвью
        lax = SN if s == SF else ST
        if strict_all:
            sg = ST if s == ST else SN
            branches = [[(sg, inst) for inst in insts]]
        else:
            sg = ST if s == ST else SN
            branches = [[(sg, inst)] for inst in insts]
        for br in branches:
            if not closes(base + br, dom):
                return False
        return True
    polarity = T if s == ST else F
    args = phi[1:]
    for branch in TABLEAU_RULES[op][polarity]:
        new_nodes = base + [(sign, args[slot]) for slot, sign in branch]
        if not closes(new_nodes, dom):
            return False
    return True


def prove_fo(premises, conclusion, dom, const=0):
    """Γ ⊢ φ на домене dom; свободная переменная x читается как элемент const."""
    g = lambda f: subst(f, x, const)
    nodes = [(ST, g(p)) for p in premises] + [(SN, g(conclusion))]
    return closes(nodes, dom)


def sem_entails(premises, conclusion, dom):
    """Семантическое следование на фиксированном домене (перебор)."""
    for interp in interps_for(premises + [conclusion], dom):
        env = {x: 0}
        if all(ev_fo(p, dom, interp, env) == T for p in premises) \
                and ev_fo(conclusion, dom, interp, env) != T:
            return False
    return True


BATTERY = [(name, prems, concl) for name, prems, concl, _ in RULES_FO] + \
          [(name, [], phi) for name, phi in VALIDITIES_C] + [
    ("дистрибуция ∀∧ туда", [("all", y, ("and", (P, y), (Q, y)))],
     ("and", ("all", y, (P, y)), ("all", y, (Q, y)))),
    ("дистрибуция ∀∧ обратно", [("and", ("all", y, (P, y)), ("all", y, (Q, y)))],
     ("all", y, ("and", (P, y), (Q, y)))),
    ("∃ из ∀", [("all", y, (P, y))], ("ex", y, (P, y))),
    ("кв. Де Морган как правило", [("not", ("all", y, (P, y)))],
     ("ex", y, ("not", (P, y)))),
]


if __name__ == "__main__":
    print("=" * 72)
    print("КВАНТОРНЫЕ ТАБЛÓ ZTL: сверка с семантикой по доменам 1–2")
    print("=" * 72)
    total, mism = 0, []
    for n in (1, 2):
        dom = list(range(n))
        for name, prems, concl in BATTERY:
            skip = any("R" in str(f) for f in prems + [concl]) and n > 2
            sem = sem_entails(prems, concl, dom)
            syn = prove_fo(prems, concl, dom)
            total += 1
            mark = "✓" if sem == syn else "✗ РАСХОЖДЕНИЕ"
            if sem != syn:
                mism.append((n, name, sem, syn))
            if n == 2:
                verdict = "выводимо" if syn else "не выводимо"
                print(f"  |D|={n}  {mark} {name}: {verdict}")
    print(f"\nПроверено пар (таблó против перебора): {total}")
    if mism:
        for m in mism:
            print("  ✗", m)
        raise SystemExit("Расхождение — стоп.")
    print("  ✓ решения совпали ВСЕ: кванторные таблó корректны и полны на батарее")
