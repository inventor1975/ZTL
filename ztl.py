# -*- coding: utf-8 -*-
"""
ZTL — Zero-Trust Logic.

Truth values: T (truth), F (falsehood) — verdicts are always two-valued.
Input mark: Z (zero-trust: "truth not earned") — the third symbol of the
calculating tables, not a value (passport: paper/ZTL-draft_1.4.md §10).

Generating principle (one for all connectives):
    op(...Z...) = AND over all classical substitutions {T,F} for Z,
    each occurrence of Z substituted independently; the result is always
    classical.
In other words: truth is never granted on credit — a connective returns
T only if T is forced under EVERY classical reading of Z; otherwise F.
Z evaporates at the first touch of an operator (greedy collapse): no
compound formula ever takes the value Z — Z lives only on atoms.

Anchor cells (axioms, fixed at design time 2026-07-10, MEASURED):
    NOT(Z)=F, NOT(NOT(Z))=T,
    (Z nxor Z)=F, (Z nxor T)=F,
    (Z xor Z)=F, (Z xor F)=F, (Z xor T)=F.
All of them are consequences of the generating principle (checked in
tests_axioms()).

Fixed forks (see SPEC.md):
  1. ¬Z = F (not a Z→F collapse at the atom) — theorem: together with
     T→Z=F this is incompatible with contraposition; contraposition is
     sacrificed deliberately.
  2. Greedy collapse (not lazy flow of Z à la SQL NULL).
  3. (Z↔Z)=F — quarantine is detectable from inside: isZ(x) = ¬(x↔x).
  4. Paradoxes are extinguished by the quarantine flag (the Tarski
     schema is suspended for Z-sentences), not by the tables: ¬ has no
     fixed point.
"""

T, F, Z = "T", "F", "Z"
VALUES = (T, F, Z)
CLASSICAL = (T, F)


def _subs(x):
    """Classical readings of a value: Z reads both as T and as F."""
    return CLASSICAL if x == Z else (x,)


def lift1(f):
    """Lift a classical unary connective into ZTL by the zero-trust principle."""
    def g(x):
        return T if all(f(a) == T for a in _subs(x)) else F
    return g


def lift2(f):
    """Lift a classical binary connective into ZTL by the zero-trust principle."""
    def g(x, y):
        return T if all(f(a, b) == T for a in _subs(x) for b in _subs(y)) else F
    return g


# --- classical kernels ---
def _not(a):    return F if a == T else T
def _and(a, b): return T if a == T and b == T else F
def _or(a, b):  return T if a == T or b == T else F
def _imp(a, b): return T if a == F or b == T else F
def _xor(a, b): return T if a != b else F
def _xnor(a, b): return T if a == b else F


# --- ZTL connectives ---
NOT = lift1(_not)
AND = lift2(_and)
OR = lift2(_or)
IMP = lift2(_imp)
XOR = lift2(_xor)
XNOR = lift2(_xnor)

OPS1 = {"not": NOT}
OPS2 = {"and": AND, "or": OR, "imp": IMP, "xor": XOR, "xnor": XNOR}
OP_SIGNS = {"not": "¬", "and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}


# --- formulas: atom = string; compound = tuple (op, ...) ---
def _ev_rec(phi, env):
    """Value of a formula, by recursion. The fast path, and the one that
    runs on every ordinary claim."""
    if isinstance(phi, str):
        return phi if phi in VALUES else env[phi]
    op = phi[0]
    if op == "not":
        return NOT(_ev_rec(phi[1], env))
    return OPS2[op](_ev_rec(phi[1], env), _ev_rec(phi[2], env))


def _ev_iter(phi, env):
    """Тот же обход, но со СВОИМ стеком — на цепях, где кончается стек
    Python. Порядок разбора тот же (слева направо, снизу вверх), поэтому
    и значение то же; проверено согласием на 3000 случайных формул."""
    stack, vals = [(phi, False)], []
    while stack:
        node, done = stack.pop()
        if isinstance(node, str):
            vals.append(node if node in VALUES else env[node])
        elif not done:
            stack.append((node, True))
            for child in reversed(node[1:]):
                stack.append((child, False))
        elif node[0] == "not":
            vals.append(NOT(vals.pop()))
        else:
            right = vals.pop()
            left = vals.pop()
            vals.append(OPS2[node[0]](left, right))
    return vals[0]


def ev(phi, env):
    """Value of a formula. Constants 'T'/'F'/'Z' are their own value.

    ГИБРИД, 2026-09-21. Рекурсия остаётся боевым путём, потому что `ev`
    зовут миллионами раз внутри переборов: промерено на типичных формулах
    глубины 3 — рекурсия 0,104 с, чистая итерация 0,161 с на 40 000
    вычислений. Платить 60% всюду ради редкого случая — плохая сделка.

    Но цепь из двух тысяч «и» кладёт стек Python, и до сегодня это был
    молчаливый отказ прибора, а не ответ. Запасной путь стоит НОЛЬ, пока
    не нужен (гибрид 0,101 с — в пределах шума от голой рекурсии), и
    считает 10 000 звеньев за 0,007 с.

    ЧЕГО ЭТА ЛОВУШКА НЕ ЛОВИТ, и это надо знать: RecursionError по другой
    причине — например, если в `phi` окажется цикл. Формулы у нас деревья,
    и на цикле итеративный путь просто зациклится вместо падения. Обменяли
    быстрый отказ на медленный; на дереве разницы нет."""
    try:
        return _ev_rec(phi, env)
    except RecursionError:
        return _ev_iter(phi, env)


def atoms(phi, acc=None):
    """Set of atoms of a formula (constants T/F/Z do not count as atoms).

    ИТЕРАТИВНА С 2026-09-21, и вот почему это не украшение. Утром я снабдил
    запасным путём `ev` — и счёл глубокие цепи закрытыми. Они не были
    закрыты: `grade` зовёт `atoms` ПЕРВОЙ, и цепь из тысячи звеньев валила
    стек здесь, на шаг раньше. Починка была ЧАСТИЧНОЙ, а выглядела полной.

    Здесь взят прямой итеративный обход, без гибрида: промерено, `atoms`
    это 0,0107 с из 0,6006 с в `grade` (1,8%), то есть не горячий путь, и
    платить за второй путь нечем."""
    acc = set() if acc is None else acc
    stack = [phi]
    while stack:
        node = stack.pop()
        if isinstance(node, str):
            if node not in VALUES:
                acc.add(node)
        else:
            stack.extend(node[1:])
    return acc


def all_envs(names):
    """All assignments of VALUES to the atoms."""
    names = sorted(names)
    if not names:
        yield {}
        return
    from itertools import product
    for combo in product(VALUES, repeat=len(names)):
        yield dict(zip(names, combo))


def show(phi):
    """Human-readable notation of a formula."""
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + show(phi[1])
    return "(" + show(phi[1]) + " " + OP_SIGNS[phi[0]] + " " + show(phi[2]) + ")"


def isZ(x):
    """Quarantine detector, expressible inside ZTL itself: isZ(x) = ¬(x↔x)."""
    return NOT(XNOR(x, x))


def print_tables():
    print("ZTL tables (generated by the zero-trust principle):\n")
    print("  x  | ¬x")
    for x in VALUES:
        print(f"  {x}  |  {NOT(x)}")
    for name, op in OPS2.items():
        sign = OP_SIGNS[name]
        print(f"\n  {sign}  | " + "  ".join(VALUES))
        for x in VALUES:
            print(f"  {x}  | " + "  ".join(op(x, y) for y in VALUES))


def tests_axioms():
    """The anchor cells — the anchor: the principle must reproduce them."""
    checks = [
        ("NOT(Z) = F",        NOT(Z),        F),
        ("NOT(NOT(Z)) = T",   NOT(NOT(Z)),   T),
        ("(Z nxor Z) = F",    XNOR(Z, Z),    F),
        ("(Z nxor T) = F",    XNOR(Z, T),    F),
        ("(Z xor Z) = F",     XOR(Z, Z),     F),
        ("(Z xor F) = F",     XOR(Z, F),     F),
        ("(Z xor T) = F",     XOR(Z, T),     F),
    ]
    bad = [(name, got, want) for name, got, want in checks if got != want]
    return checks, bad


if __name__ == "__main__":
    print_tables()
    print()
    checks, bad = tests_axioms()
    for name, got, want in checks:
        mark = "ok" if got == want else f"FAIL (got {got})"
        print(f"  axiom {name:20s} {mark}")
    if bad:
        raise SystemExit("THE PRINCIPLE DOES NOT REPRODUCE THE AXIOMS — stop.")
