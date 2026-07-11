# -*- coding: utf-8 -*-
"""
Экспедиция Э5: множества с непроверенными элементами (ZTL-множества).

Множества НЕ постулируются — выводятся из логики:
  * равенство элементов eq(a,b) — АТОМ со значением T/F/Z
    (verified-vs-verified — классика; любая метка — Z: тождество
    не заработано, даже метки с самой собой);
  * членство mem(x,S) = ∃-свёртка eq-атомов (строгий T-свидетель);
  * включение sub(S,T) = ∀-свёртка mem (все строго T);
  * равенство множеств seteq = sub ∧ sub.
Всё считается таблицами ztl.py — ни одного специального правила.

Представление: ZSet = (core: frozenset проверенных, quar: кортеж меток).
Метка ('Z', id) — непроверенное наблюдение; id — происхождение,
в равенстве НЕ участвует (zero-trust: провенанс не доказывает тождество).

Промеры: {Z,Z} против {Z}; Z ∉ {Z}; законы множеств на чистых и
меченых; два уровня равенства (репрезентация против вердикта);
интервальная мощность; сверка с SQL (NULL: = / IN / DISTINCT).
"""

from ztl import T, F, Z, OPS2, NOT

OR, AND, XNOR = OPS2["or"], OPS2["and"], OPS2["xnor"]


# --- элементы ---
def V_(x):
    return ("V", x)          # проверенное значение


def M_(ident):
    return ("Z", ident)      # непроверенная метка (карантин)


def eq_atom(a, b):
    """Равенство элементов — атом: T/F для проверенных, Z при любой метке."""
    if a[0] == "V" and b[0] == "V":
        return T if a[1] == b[1] else F
    return Z                 # тождество не заработано — даже метки с собой


# --- множества ---
class ZSet:
    def __init__(self, core=(), quar=()):
        self.core = frozenset(core)
        self.quar = tuple(quar)

    def elements(self):
        return [V_(x) for x in sorted(self.core, key=repr)] + \
               [M_(i) for i in self.quar]

    def __repr__(self):
        c = "{" + ", ".join(map(repr, sorted(self.core, key=repr))) + "}"
        return f"ZSet(core={c}, quar={len(self.quar)} меток)"

    # представление-уровень (машинное, не вердиктное)
    def repr_eq(self, other):
        return self.core == other.core and \
            sorted(self.quar) == sorted(other.quar)


def mem(x, S):
    """x ∈ S: ∃-свёртка eq-атомов по таблицам (строгий свидетель)."""
    v = F
    for el in S.elements():
        v = OR(v, eq_atom(x, el))
    return v


def sub(S, Tset):
    """S ⊆ T: ∀-свёртка членств (все строго T)."""
    v = T
    for el in S.elements():
        v = AND(v, mem(el, Tset))
    return v


def seteq(S, Tset):
    """S = T (вердикт): взаимное включение."""
    return AND(sub(S, Tset), sub(Tset, S))


# --- операции (представление-уровень) ---
def union(S, Tset):
    return ZSet(S.core | Tset.core, S.quar + Tset.quar)


def intersect(S, Tset):
    # пересечение требует ДОКАЗАННОГО совпадения: метки не доказывают
    return ZSet(S.core & Tset.core, ())


def diff(S, Tset):
    # вычитание требует доказанного членства в T: метки S остаются
    return ZSet(S.core - Tset.core, S.quar)


def card_bounds(S):
    lo = len(S.core) if S.core else (1 if S.quar else 0)
    return (lo, len(S.core) + len(S.quar))


def distinct(S):
    """SQL-DISTINCT по-нашему: ядро дедуплицировано классикой,
    метки склеивать нельзя (склейка не заработана)."""
    return ZSet(S.core, S.quar)


# ---------------------------------------------------------------- промеры
def hdr(t):
    print("\n### " + t)


if __name__ == "__main__":
    print("=" * 72)
    print("Э5. МНОЖЕСТВА С НЕПРОВЕРЕННЫМИ ЭЛЕМЕНТАМИ")
    print("=" * 72)

    z1, z2 = M_("сенсор#1"), M_("сенсор#2")
    S_zz = ZSet((), ("сенсор#1", "сенсор#1"))     # {Z, Z} (одна и та же метка дважды)
    S_z = ZSet((), ("сенсор#1",))                  # {Z}
    A = ZSet((1, 2), ("m1",))                      # {1, 2, Z}
    CLEAN = ZSet((1, 2))                           # {1, 2}

    hdr("Опорные вопросы разведки")
    print(f"  {{Z,Z}} = {{Z}} (вердикт): {seteq(S_zz, S_z)}   "
          f"(репрезентация: {S_zz.repr_eq(S_z)}) — склейка не заработана")
    print(f"  Z ∈ {{Z}} (та же метка!): {mem(M_('сенсор#1'), S_z)} — "
          f"членство не заработано (SQL: NULL IN (NULL) — не true)")
    print(f"  1 ∈ {{1,2,Z}}: {mem(V_(1), A)}   3 ∈ {{1,2,Z}}: {mem(V_(3), A)}")

    hdr("Законы множеств: чистые против меченых (вердикт seteq)")
    laws = [
        ("S ∪ S = S (идемпотентность)", lambda S: (union(S, S), S)),
        ("S ∩ S = S", lambda S: (intersect(S, S), S)),
        ("S \\ S = ∅", lambda S: (diff(S, S), ZSet())),
        ("S = S (рефлексивность)", lambda S: (S, S)),
        ("S ∪ T = T ∪ S (T={2,3})",
         lambda S: (union(S, ZSet((2, 3))), union(ZSet((2, 3)), S))),
    ]
    print(f"  {'закон':38s} {'чистое':8s} {'меченое':8s} {'репр.(меч.)'}")
    for name, f in laws:
        l1, r1 = f(CLEAN)
        l2, r2 = f(A)
        print(f"  {name:38s} {seteq(l1, r1):8s} {seteq(l2, r2):8s} "
              f"{l2.repr_eq(r2)}")

    hdr("Включение: даже S ⊆ S падает на меченом")
    print(f"  {{1,2}} ⊆ {{1,2}}: {sub(CLEAN, CLEAN)}")
    print(f"  {{1,2,Z}} ⊆ {{1,2,Z}}: {sub(A, A)} — метка не доказуемо")
    print("  принадлежит даже собственному множеству (наследие Z∉{Z})")

    hdr("Мощность — только интервал (точное число не заработано)")
    for nm, S in [("{1,2}", CLEAN), ("{1,2,Z}", A),
                  ("{Z,Z}", S_zz), ("{Z}", S_z)]:
        lo, hi = card_bounds(S)
        verdict = T if lo == hi else F
        print(f"  |{nm}|: [{lo}, {hi}]   вердикт «|S|={hi}»: {verdict}")

    hdr("Сверка с SQL (его знаменитая непоследовательность)")
    print("  SQL: NULL = NULL → not true;  NULL IN (NULL) → not true;")
    print("  но DISTINCT/GROUP BY СКЛЕИВАЮТ NULL'ы — подмена равенства")
    print("  значений равенством меток внутри одного синтаксиса.")
    d = distinct(ZSet((1,), ("a", "b")))
    lo, hi = card_bounds(d)
    print(f"  Наш DISTINCT({{1, Z, Z}}): ядро дедуплицировано, меток "
          f"{len(d.quar)} — |·| ∈ [{lo},{hi}]; склейка меток не заработана,")
    print("  непоследовательность SQL не наследуется (метки живут отдельно).")

    hdr("Итог")
    print("  На чистых множествах — классическая теория множеств клетка в")
    print("  клетку (C-расширяемость). Метка ломает ровно законы тождества")
    print("  (идемпотентность, рефлексивность, вычитание себя) — те же семьи,")
    print("  что пали в логике: множества УНАСЛЕДОВАЛИ прейскурант от таблиц,")
    print("  ни одно правило не постулировалось отдельно.")
