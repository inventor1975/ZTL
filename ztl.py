# -*- coding: utf-8 -*-
"""
ZTL — Zero-Trust Logic / логика нулевого доверия.

Значения истинности: T (истина), F (ложь) — вердикты всегда двузначны.
Метка входа: Z (zero-trust: «истина не заслужена») — третий символ
таблиц-калькуляторов, не значение (паспорт: paper/ZTL-draft.md §10).

Порождающий принцип (один на все связки):
    op(...Z...) = И по всем классическим подстановкам {T,F} вместо Z,
    каждое вхождение Z подставляется независимо; результат всегда классичен.
Иначе: истина не выдаётся в кредит — связка возвращает T, только если T
вынуждена при ЛЮБОЙ классической расшифровке Z; иначе F.
Z испаряется при первом касании оператора (жадный коллапс): ни одна
составная формула не имеет значения Z — Z живёт только на атомах.

Опорные клетки (аксиомы, продиктованы куратором 2026-07-10, MEASURED):
    NOT(Z)=F, NOT(NOT(Z))=T,
    (Z nxor Z)=F, (Z nxor T)=F,
    (Z xor Z)=F, (Z xor F)=F, (Z xor T)=F.
Все они — следствия порождающего принципа (проверяется в tests_axioms()).

Зафиксированные развилки (см. SPEC.md):
  1. ¬Z = F (а не схлопывание Z→F на атоме) — теорема: вместе с T→Z=F это
     несовместимо с контрапозицией; контрапозицией жертвуем сознательно.
  2. Жадный коллапс (а не ленивое протекание Z а-ля SQL NULL).
  3. (Z↔Z)=F — карантин детектируем изнутри: isZ(x) = ¬(x↔x).
  4. Парадоксы гасятся карантинным флагом (схема Тарского приостановлена
     для Z-предложений), не таблицами: у ¬ нет неподвижной точки.
"""

T, F, Z = "T", "F", "Z"
VALUES = (T, F, Z)
CLASSICAL = (T, F)


def _subs(x):
    """Классические расшифровки значения: Z читается и как T, и как F."""
    return CLASSICAL if x == Z else (x,)


def lift1(f):
    """Поднять классическую унарную связку в ZTL по принципу нулевого доверия."""
    def g(x):
        return T if all(f(a) == T for a in _subs(x)) else F
    return g


def lift2(f):
    """Поднять классическую бинарную связку в ZTL по принципу нулевого доверия."""
    def g(x, y):
        return T if all(f(a, b) == T for a in _subs(x) for b in _subs(y)) else F
    return g


# --- классические ядра ---
def _not(a):    return F if a == T else T
def _and(a, b): return T if a == T and b == T else F
def _or(a, b):  return T if a == T or b == T else F
def _imp(a, b): return T if a == F or b == T else F
def _xor(a, b): return T if a != b else F
def _xnor(a, b): return T if a == b else F


# --- связки ZTL ---
NOT = lift1(_not)
AND = lift2(_and)
OR = lift2(_or)
IMP = lift2(_imp)
XOR = lift2(_xor)
XNOR = lift2(_xnor)

OPS1 = {"not": NOT}
OPS2 = {"and": AND, "or": OR, "imp": IMP, "xor": XOR, "xnor": XNOR}
OP_SIGNS = {"not": "¬", "and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}


# --- формулы: атом = строка; составная = кортеж (op, ...) ---
def ev(phi, env):
    """Значение формулы. Константы 'T'/'F'/'Z' — сами себе значение."""
    if isinstance(phi, str):
        return phi if phi in VALUES else env[phi]
    op = phi[0]
    if op == "not":
        return NOT(ev(phi[1], env))
    return OPS2[op](ev(phi[1], env), ev(phi[2], env))


def atoms(phi, acc=None):
    """Множество атомов формулы (константы T/F/Z атомами не считаются)."""
    if acc is None:
        acc = set()
    if isinstance(phi, str):
        if phi not in VALUES:
            acc.add(phi)
    else:
        for part in phi[1:]:
            atoms(part, acc)
    return acc


def all_envs(names):
    """Все распределения значений VALUES по атомам."""
    names = sorted(names)
    if not names:
        yield {}
        return
    from itertools import product
    for combo in product(VALUES, repeat=len(names)):
        yield dict(zip(names, combo))


def show(phi):
    """Формула в человеческой записи."""
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + show(phi[1])
    return "(" + show(phi[1]) + " " + OP_SIGNS[phi[0]] + " " + show(phi[2]) + ")"


def isZ(x):
    """Детектор карантина, выразим внутри самой ZTL: isZ(x) = ¬(x↔x)."""
    return NOT(XNOR(x, x))


def print_tables():
    print("Таблицы ZTL (порождены принципом нулевого доверия):\n")
    print("  x  | ¬x")
    for x in VALUES:
        print(f"  {x}  |  {NOT(x)}")
    for name, op in OPS2.items():
        sign = OP_SIGNS[name]
        print(f"\n  {sign}  | " + "  ".join(VALUES))
        for x in VALUES:
            print(f"  {x}  | " + "  ".join(op(x, y) for y in VALUES))


def tests_axioms():
    """Опорные клетки куратора — якорь: принцип обязан их воспроизводить."""
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
        mark = "ok" if got == want else f"FAIL (получено {got})"
        print(f"  аксиома {name:20s} {mark}")
    if bad:
        raise SystemExit("ПРИНЦИП НЕ ВОСПРОИЗВОДИТ АКСИОМЫ — стоп.")
