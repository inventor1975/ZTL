# -*- coding: utf-8 -*-
"""
Знаковые таблó для ZTL (архитектура Rousseau/Hähnle для конечнозначных логик).

Знаки — множества значений:
    T = {T}        строгая истина
    F = {F}        строгая ложь
    P = {T, Z}     «возможно T» (не-ложь)
    N = {F, Z}     «не заслужил T» (не-истина)

Правила выведены из прообразов таблиц ZTL и НЕСУТ подпись нулевого доверия:
T-полярность требует строгих сертификатов (только знаки T/F),
F-полярность довольствуется ослабленными (P/N). Классические таблó — это
то же самое с P≡T и N≡F; ослабление — весь вклад Z.

Теорема жадности вырождает знаки на составных формулах: P≡T, N≡F
(составная не бывает Z); Z выживает только на атомах — открытая ветвь
с парой знаков P и N на атоме даёт Z-контрмодель.

Проверки (MEASURED):
  * rule_coverage_check — каждое правило точно покрывает прообраз таблицы;
  * cross_check — решения таблó совпадают с ⊨ (перебором) на батарее
    из entailment.py и на всех парах формул порождённого пула.
"""

from itertools import product

from ztl import T, F, Z, VALUES, OPS2, ev, atoms, all_envs
from entailment import entails, RULES as RULE_BATTERY

ST = frozenset({T})
SF = frozenset({F})
SP = frozenset({T, Z})   # P: «возможно T»
SN = frozenset({F, Z})   # N: «не заслужил T»
CLASSIC = frozenset({T, F})

# Правила: op -> полярность ('T'/'F') -> список ветвей;
# ветвь = список пар (номер аргумента, знак).
TABLEAU_RULES = {
    "not": {
        T: [[(0, SF)]],
        F: [[(0, SP)]],
    },
    "and": {
        T: [[(0, ST), (1, ST)]],
        F: [[(0, SN)], [(1, SN)]],
    },
    "or": {
        T: [[(0, ST)], [(1, ST)]],
        F: [[(0, SN), (1, SN)]],
    },
    "imp": {
        T: [[(0, SF)], [(1, ST)]],
        F: [[(0, SP), (1, SN)]],
    },
    "xor": {
        T: [[(0, ST), (1, SF)], [(0, SF), (1, ST)]],
        F: [[(0, SP), (1, SP)], [(0, SN), (1, SN)]],
    },
    "xnor": {
        T: [[(0, ST), (1, ST)], [(0, SF), (1, SF)]],
        F: [[(0, SP), (1, SN)], [(0, SN), (1, SP)]],
    },
}


def rule_coverage_check():
    """Каждое правило обязано ТОЧНО покрывать прообраз своей таблицы:
    ветви ∪-покрывают все комбинации значений с нужным выходом и не
    задевают ни одной с ненужным."""
    problems = []
    for op, per_sign in TABLEAU_RULES.items():
        arity = 1 if op == "not" else 2
        for target, branches in per_sign.items():
            for combo in product(VALUES, repeat=arity):
                if op == "not":
                    from ztl import NOT
                    out = NOT(combo[0])
                else:
                    out = OPS2[op](*combo)
                covered = any(all(combo[slot] in sign for slot, sign in br)
                              for br in branches)
                if (out == target) != covered:
                    problems.append((op, target, combo, out, covered))
    return problems


def _is_atom(phi):
    return isinstance(phi, str) and phi not in VALUES


def tableau_closes(nodes):
    """True, если таблó закрывается (нет модели для набора знаковых формул).
    nodes: список пар (знак, формула)."""
    atom_signs = {}
    first_compound = None
    rest = []
    for sign, phi in nodes:
        if _is_atom(phi):
            cur = atom_signs.get(phi, frozenset(VALUES)) & sign
            if not cur:
                return True
            atom_signs[phi] = cur
        elif isinstance(phi, str):           # константа T/F/Z
            if phi not in sign:
                return True
        else:
            s = sign & CLASSIC               # жадность: составная не Z
            if not s:
                return True
            if s == CLASSIC:                 # неинформативный знак — отбросить
                continue
            if first_compound is None:
                first_compound = (s, phi)
            else:
                rest.append((s, phi))
    if first_compound is None:
        return False                          # насыщенная открытая ветвь
    s, phi = first_compound
    polarity = T if s == ST else F
    args = phi[1:]
    base = rest + [(sg, at) for at, sg in sorted(atom_signs.items())]
    for branch in TABLEAU_RULES[phi[0]][polarity]:
        new_nodes = base + [(sign, args[slot]) for slot, sign in branch]
        if not tableau_closes(new_nodes):
            return False
    return True


def prove(premises, conclusion):
    """Γ ⊢ φ по таблó: старт T:Γ и N:φ; True = выводимо (все ветви закрыты)."""
    nodes = [(ST, g) for g in premises] + [(SN, conclusion)]
    return tableau_closes(nodes)


def _pool():
    """Пул формул для перекрёстной сверки: глубина ≤ 2 над p, q."""
    a = ["p", "q", ("not", "p"), ("not", "q")]
    pool = list(a)
    for op in ("and", "or", "imp", "xor", "xnor"):
        for x in a[:2]:
            for y in a:
                pool.append((op, x, y))
    return pool


def cross_check():
    """Совпадение таблó с ⊨ (перебором): батарея правил + пул пар."""
    mismatches = []
    for name, prems, concl in RULE_BATTERY:
        sem = entails(prems, concl) is None
        syn = prove(prems, concl)
        if sem != syn:
            mismatches.append(("battery: " + name, sem, syn))
    pool = _pool()
    n = 0
    for A in pool:
        for B in pool:
            sem = entails([A], B) is None
            syn = prove([A], B)
            n += 1
            if sem != syn:
                mismatches.append((f"{A} |- {B}", sem, syn))
    for A in pool[:8]:
        for B in pool[:8]:
            for C in pool[:8]:
                sem = entails([A, B], C) is None
                syn = prove([A, B], C)
                n += 1
                if sem != syn:
                    mismatches.append((f"{A},{B} |- {C}", sem, syn))
    return n + len(RULE_BATTERY), mismatches


if __name__ == "__main__":
    print("=" * 72)
    print("ЗНАКОВЫЕ ТАБЛÓ ZTL: T, F, P={T,Z}, N={F,Z}")
    print("=" * 72)

    probs = rule_coverage_check()
    print("\n-- ПОКРЫТИЕ ПРООБРАЗОВ ПРАВИЛАМИ --")
    if not probs:
        print("  ✓ все 12 правил точно совпадают с прообразами таблиц")
    else:
        for pr in probs:
            print("  ✗", pr)
        raise SystemExit("Правила не совпадают с таблицами — стоп.")

    total, mism = cross_check()
    print("\n-- ПЕРЕКРЁСТНАЯ СВЕРКА ТАБЛÓ ПРОТИВ ⊨ --")
    print(f"  проверено следований: {total}")
    if not mism:
        print("  ✓ решения совпали ВСЕ: исчисление корректно и полно на батарее")
    else:
        for m in mism[:10]:
            print("  ✗", m)
        raise SystemExit("Расхождение таблó и семантики — стоп.")
