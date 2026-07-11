# -*- coding: utf-8 -*-
"""
Экспедиция Э8: арифметика с метками.

Числа: проверенные ('V', n) и метки ('M', id, lo, hi) — непроверенные
с интервалом частичного знания (None = неограничено). Операции —
вычисления ⇒ ленивые: интервалы ТЕКУТ (интервальная арифметика,
декоррелированно — каждое вхождение метки читается независимо).
Атомы сравнения — по порождающему принципу: T, если вынуждено при
всех прочтениях; F, если вынуждена ложь; иначе Z.

Близнец №4: абстрактная интерпретация (Cousot & Cousot 1977) —
интервальный анализ значений + проверка ассертов.
"""

from ztl import T, F, Z, OPS2

AND, OR, IMP = OPS2["and"], OPS2["or"], OPS2["imp"]

NEG_INF, POS_INF = float("-inf"), float("inf")


def V_(n):
    return ("V", n, n, n)


def M_(ident, lo=None, hi=None):
    return ("M", ident,
            NEG_INF if lo is None else lo,
            POS_INF if hi is None else hi)


def bounds(x):
    return x[2], x[3]


def is_verified(x):
    return x[0] == "V"


def name(x):
    if is_verified(x):
        return str(x[1])
    lo, hi = bounds(x)
    rng = "" if (lo, hi) == (NEG_INF, POS_INF) else f"∈[{lo},{hi}]"
    return f"{x[1]}{rng}"


# --- операции: интервалы текут (лениво), родословная растёт ---
def add(x, y):
    lo, hi = x[2] + y[2], x[3] + y[3]
    if is_verified(x) and is_verified(y):
        return V_(x[1] + y[1])
    return ("M", f"({name(x)}+{name(y)})", lo, hi)


def sub_(x, y):
    lo, hi = x[2] - y[3], x[3] - y[2]      # декорреляция!
    if is_verified(x) and is_verified(y):
        return V_(x[1] - y[1])
    if lo == hi:                            # вынужденное значение — заработано
        return V_(lo)
    return ("M", f"({name(x)}-{name(y)})", lo, hi)


def mul(x, y):
    # на ℤ: 0·x = 0 всегда (в т.ч. для неограниченных меток)
    cands = [0 if (a == 0 or b == 0) else a * b
             for a in (x[2], x[3]) for b in (y[2], y[3])]
    lo, hi = min(cands), max(cands)
    if is_verified(x) and is_verified(y):
        return V_(x[1] * y[1])
    if lo == hi:                            # вынуждено (например, 0·m)
        return V_(int(lo))
    return ("M", f"({name(x)}·{name(y)})", lo, hi)


# --- атомы сравнения: порождающий принцип на интервалах ---
def lt_atom(x, y):
    if x[3] < y[2]:
        return T                            # вынуждено при всех прочтениях
    if x[2] >= y[3]:
        return F                            # вынуждена ложь
    return Z


def eq_atom(x, y):
    if is_verified(x) and is_verified(y):
        return T if x[1] == y[1] else F
    if x[3] < y[2] or y[3] < x[2]:
        return F                            # апартность ЗАРАБОТАНА интервалами
    return Z


if __name__ == "__main__":
    print("=" * 72)
    print("Э8. АРИФМЕТИКА С МЕТКАМИ (интервалы текут, вердикты зарабатываются)")
    print("=" * 72)

    m = M_("m", 0, 9)         # сенсор, частично проверен: [0,9]
    w = M_("w")               # дикая метка, ничего не известно
    five = V_(5)
    zero = V_(0)

    print("\n### Течение интервалов (ленивый регистр)")
    s1 = add(five, m)
    print(f"  5 + m∈[0,9] = {name(s1)}")
    s2 = add(five, w)
    print(f"  5 + w(∅ информации) = {name(s2)} — голый NaN-режим")

    print("\n### Вынужденность зарабатывает даже на метках")
    p = mul(zero, w)
    print(f"  0 · w = {name(p)}  ← ЗАРАБОТАННЫЙ ноль (вынужден при всех")
    print("  прочтениях; IEEE тут отвечает NaN — их домен с inf/nan, наш ℤ)")
    d = sub_(m, m)
    print(f"  m − m = {name(d)} — НЕ ноль: декорреляция (два независимых")
    print("  прочтения одной метки; ровно как NaN−NaN и как {Z,Z}≠{Z})")

    print("\n### Атомы сравнения: три судьбы (T заработано / F заработано / Z)")
    a, b = M_("a", 3, 5), M_("b", 10, 12)
    print(f"  a∈[3,5] < b∈[10,12]: {lt_atom(a, b)} — заработано (разнесены)")
    print(f"  a∈[3,5] = b∈[10,12]: {eq_atom(a, b)} — апартность заработана!")
    c = M_("c", 4, 6)
    print(f"  a∈[3,5] < c∈[4,6]: {lt_atom(a, c)} — не вынуждено (перекрытие)")
    print(f"  a∈[3,5] = a∈[3,5] (та же метка): {eq_atom(a, a)} — тождество")
    print("  не зарабатывается интервалами (совпадение границ ≠ совпадение)")

    print("\n### Верификация = сужение интервала: вердикты зарабатываются")
    four = V_(4)
    for lo, hi in [(0, 9), (3, 7), (5, 7), (5, 5)]:
        mm = M_("m", lo, hi)
        atom = lt_atom(four, mm)   # «4 < m»
        note = {T: "заработано T", F: "заработана ложь", Z: "ещё не вынуждено"}[atom]
        print(f"  m∈[{lo},{hi}]:  атом «4 < m» = {atom}  ({note})")
    print("  Сужение никогда не отменяет заработанное — монотонность")
    print("  ленивого регистра, теперь в числах.")

    print("\n### Законы: наследование прейскуранта")
    x, y = M_("x", 1, 3), M_("y", 2, 4)
    lhs, rhs = add(x, y), add(y, x)
    print(f"  x+y = {name(lhs)};  y+x = {name(rhs)}")
    print(f"  коммутативность: интервалы совпали ({bounds(lhs) == bounds(rhs)}),")
    print(f"  вердикт eq(x+y, y+x): {eq_atom(lhs, rhs)} — два уровня, снова")
    xz = add(x, zero)
    print(f"  x+0 = {name(xz)}: интервал тот же ({bounds(xz) == bounds(x)}),")
    print(f"  вердикт eq(x+0, x): {eq_atom(xz, x)} — нейтраль пала вердиктно")

    print("\n### Итог")
    print("  Арифметика ZTL = интервальная арифметика (решатель) + вердикты")
    print("  порождающего принципа (таможня). Всё унаследовано, ничего не")
    print("  постулировано. Близнец №4 — абстрактная интерпретация (Cousot):")
    print("  анализ значений интервалами + проверка ассертов = наш ленивый")
    print("  регистр + жадные вердикты. Дополнение к Э6: апартность чисел")
    print("  зарабатывается интервалами — как апартность вещественных")
    print("  префиксами; тождество не зарабатывается ничем, кроме полной")
    print("  верификации ([x,x] — метка становится значением).")
