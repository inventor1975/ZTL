# -*- coding: utf-8 -*-
"""
Экспедиция Э7: функции над мечеными множествами.

Функция — вычисление, не вердикт ⇒ по двухрегистровой теореме ведёт
себя ЛЕНИВО: метка течёт сквозь функцию (f(непроверенное) =
непроверенное с родословной). Это в точности taint tracking из
безопасности (Деннинг-1976): Z-метка = таинт, вердикты = санитайзеры.

Промеры: образ (проверенные коллизии зарабатывают склейку, метки — с
кратностью), два прообраза (вердиктный/решательный), композиция и
транзитивность таинта, инъективность (даже id не сертифицируется),
наследование законов.
"""

from ztl import T, F, Z, OPS2
from zsets import ZSet, V_, M_, eq_atom, mem, sub, seteq, union, card_bounds

OR, AND = OPS2["or"], OPS2["and"]


class ZFun:
    """Проверенная функция: таблица на проверенных значениях.
    На метках — таинт: выход есть новая метка с родословной."""

    def __init__(self, name, table):
        self.name = name
        self.table = dict(table)

    def __call__(self, el):
        if el[0] == "V":
            return V_(self.table[el[1]])
        return M_(f"{self.name}({el[1]})")     # таинт с родословной


def image(f, S):
    core = {f.table[x] for x in S.core}        # коллизии ЗАРАБОТАНЫ
    quar = tuple(f"{f.name}({i})" for i in S.quar)
    return ZSet(core, quar)


def compose(g, f, name=None):
    return ZFun(name or f"{g.name}∘{f.name}",
                {x: g.table[y] for x, y in f.table.items()})


def preimage_verdict(f, Tset, S):
    """Вердиктный прообраз: только элементы S, ЗАРАБОТАВШИЕ f(x) ∈ T."""
    core = {x for x in S.core if mem(V_(f.table[x]), Tset) == T}
    return ZSet(core, ())                      # метки не зарабатывают

def preimage_possible(f, Tset, S):
    """Решательный прообраз: кандидаты (ядро по классике + все метки)."""
    core = {x for x in S.core if mem(V_(f.table[x]), Tset) == T}
    return ZSet(core, S.quar)


def injective_verdict(f, S):
    """Инъективность на S — ∀-свёртка по парам: eq(f a, f b) → eq(a, b)?
    Вердиктно: для пар с меткой посылка/заключение — Z-атомы."""
    els = S.elements()
    v = T
    for i, a in enumerate(els):
        for b in els[i + 1:]:
            # «различны на входе ⇒ различны на выходе», контрапозитивно:
            # eq(f a, f b) → eq(a, b); атомы через eq_atom
            prem = eq_atom(f(a), f(b))
            concl = eq_atom(a, b)
            v = AND(v, OPS2["imp"](prem, concl))
    return v


if __name__ == "__main__":
    print("=" * 72)
    print("Э7. ФУНКЦИИ НАД МЕЧЕНЫМИ МНОЖЕСТВАМИ (таинт-режим)")
    print("=" * 72)

    S = ZSet((1, 2, 3), ("m1",))               # {1,2,3,Z}
    f = ZFun("f", {1: 10, 2: 10, 3: 30})        # коллизия: f(1)=f(2)=10
    g = ZFun("g", {10: 100, 30: 100})           # коллапс всего
    ident = ZFun("id", {1: 1, 2: 2, 3: 3})

    print("\n### Образ: проверенные коллизии зарабатывают склейку")
    fS = image(f, S)
    print(f"  f{{1,2,3,Z}} = {fS}")
    lo, hi = card_bounds(fS)
    print(f"  |f(S)| ∈ [{lo},{hi}] — ядро склеилось (f(1)=f(2) ДОКАЗАНО),")
    print("  метка осталась меткой: таинт не отмывается функцией.")

    print("\n### Композиция: таинт транзитивен, образ ассоциативен")
    gfS1 = image(g, image(f, S))
    gfS2 = image(compose(g, f), S)
    print(f"  g(f(S)) = {gfS1}")
    print(f"  (g∘f)(S) = {gfS2}")
    print(f"  репрезентация совпала: {gfS1.core == gfS2.core and len(gfS1.quar) == len(gfS2.quar)}"
          f"   вердикт seteq: {seteq(gfS1, gfS2)} — снова два уровня")
    print(f"  родословная метки после g∘f: {gfS1.quar[0]}")

    print("\n### Прообраз раздвоился (двухрегистровость)")
    Tgt = ZSet((10,))
    pv = preimage_verdict(f, Tgt, S)
    pp = preimage_possible(f, Tgt, S)
    print(f"  вердиктный f⁻¹({{10}}) = {pv} — метки отброшены (default deny)")
    print(f"  решательный f⁻¹({{10}}) = {pp} — метка остаётся кандидатом")
    print(f"  вердикт «прообраз покрывает кандидатов»: {sub(pp, pv)}")

    print("\n### Инъективность: даже id не сертифицируется на меченом")
    print(f"  id инъективна на {{1,2,3}} (чистое): "
          f"{injective_verdict(ident, ZSet((1, 2, 3)))}")
    print(f"  id инъективна на {{1,2,3,Z}} (меченое): "
          f"{injective_verdict(ident, S)}")
    print(f"  f (с коллизией) на чистом: "
          f"{injective_verdict(f, ZSet((1, 2, 3)))} — коллизия заработана")
    print("  Пара (метка, что-угодно) даёт Z-атомы → импликация Z→Z = F →")
    print("  ∀-свёртка рушится: сертификат инъективности требует ПОЛНОЙ")
    print("  проверенности домена. Эхо «S ⊆ S пало».")

    print("\n### Отмывание таинта запрещено, санитайзер = внешняя проверка")
    m = M_("сенсор")
    print(f"  f(метка) = {f(m)} — метка (родословная растёт)")
    print(f"  g(f(метка)) = {g(f(m))} — таинт транзитивен")
    print("  Единственный способ снять метку — ВНЕШНЯЯ верификация значения")
    print("  (не функция): в терминах безопасности — declassification только")
    print("  через доказательство. Perl taint mode, TaintDroid, IFC-решётка")
    print("  Деннинг — третий инженерный близнец ZTL после NaN и NULL.")
