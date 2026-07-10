# -*- coding: utf-8 -*-
"""
Карантин как неподвижная точка (à la Крипке) над ZTL.

Язык с предикатом истинности: система предложений s_i, каждое определено
формулой над атомами Tr(s_j) (и константами). «Скачок» J переоценивает
все предложения по текущей оценке v. Неподвижные точки J — само-
согласованные оценки; Z-множество наименьшей точки = карантин.

Два регистра:
  * ЖАДНЫЙ (ZTL): Z испаряется на каждом операторе — регистр вердиктов;
  * ЛЕНИВЫЙ (сильный Клини): Z течёт (¬Z=Z и т.д.) — регистр заземления.

Гипотезы (проверяются перебором, MEASURED):
  H1. Жадный регистр немонотонен по информационному порядку (Z ⊑ T, Z ⊑ F);
  H2. На лжеце (и любом нечётном цикле) жадный скачок НЕ имеет неподвижных
      точек — итерация осциллирует (карусель, формально);
  H3. Ленивый скачок монотонен и всюду имеет наименьшую неподвижную точку
      (Кнастер–Тарский), парадоксы получают Z;
  H4. Двухрегистровая архитектура обязательна: заземление — лениво,
      вердикты (в т.ч. пуля мстителя «содержание T, истины нет») — жадно.
"""

from itertools import product

from ztl import T, F, Z, VALUES, OPS2, NOT

# --- ленивый регистр: сильный Клини ---
def k_not(a):
    return {T: F, F: T, Z: Z}[a]

def k_and(a, b):
    return F if F in (a, b) else (Z if Z in (a, b) else T)

def k_or(a, b):
    return T if T in (a, b) else (Z if Z in (a, b) else F)

def k_imp(a, b):
    return k_or(k_not(a), b)

def k_xor(a, b):
    return Z if Z in (a, b) else (T if a != b else F)

def k_xnor(a, b):
    return Z if Z in (a, b) else (T if a == b else F)

LAZY = {"not": k_not, "and": k_and, "or": k_or,
        "imp": k_imp, "xor": k_xor, "xnor": k_xnor}
EAGER = {"not": NOT, **OPS2}


def ev_reg(phi, v, ops):
    """Значение формулы при оценке v (имя предложения -> значение)."""
    if isinstance(phi, str):
        return phi if phi in VALUES else v[phi]   # константа или Tr(имя)
    op = phi[0]
    if op == "not":
        return ops["not"](ev_reg(phi[1], v, ops))
    return ops[op](ev_reg(phi[1], v, ops), ev_reg(phi[2], v, ops))


def jump(system, v, ops):
    return {name: ev_reg(defn, v, ops) for name, defn in system.items()}


def fixed_points(system, ops):
    names = sorted(system)
    result = []
    for combo in product(VALUES, repeat=len(names)):
        v = dict(zip(names, combo))
        if jump(system, v, ops) == v:
            result.append(v)
    return result


def leq_info(a, b):
    """Информационный порядок: Z ⊑ всё, T и F несравнимы."""
    return a == b or a == Z


def v_leq(v, w):
    return all(leq_info(v[k], w[k]) for k in v)


def monotone_witness(system, ops):
    """Пара оценок v ⊑ w с J(v) ⋢ J(w), если есть."""
    names = sorted(system)
    vals = [dict(zip(names, c)) for c in product(VALUES, repeat=len(names))]
    for v in vals:
        for w in vals:
            if v_leq(v, w) and not v_leq(jump(system, v, ops),
                                         jump(system, w, ops)):
                return v, w
    return None


def iterate(system, ops, steps=12):
    """Итерация скачка из всюду-Z; хвост траектории."""
    v = {name: Z for name in system}
    trace = [v]
    for _ in range(steps):
        v = jump(system, v, ops)
        if v in trace:
            i = trace.index(v)
            return trace, i          # цикл: trace[i:] повторяется
        trace.append(v)
    return trace, None


def least_fp_lazy(system):
    """Наименьшая неподвижная точка ленивого скачка (итерацией из Z)."""
    trace, loop = iterate(system, LAZY, steps=64)
    assert loop == len(trace) - 1 or loop is None, "ленивый скачок зациклился?"
    return trace[-1]


# --- зоопарк систем ---
ZOO = {
    "лжец            λ: ¬Tr(λ)": {
        "λ": ("not", "λ")},
    "правдолюб       τ: Tr(τ)": {
        "τ": "τ"},
    "карусель        A: Tr(B); B: ¬Tr(A)": {
        "A": "B", "B": ("not", "A")},
    "чётный цикл     A: ¬Tr(B); B: ¬Tr(A)": {
        "A": ("not", "B"), "B": ("not", "A")},
    "заземлённые     g0: T; g1: Tr(g0); g2: ¬Tr(g1)∨Tr(g0)": {
        "g0": "T", "g1": "g0", "g2": ("or", ("not", "g1"), "g0")},
    "мститель        μ: ¬Tr(μ) ∨ ¬(Tr(μ)↔Tr(μ))": {
        "μ": ("or", ("not", "μ"), ("not", ("xnor", "μ", "μ")))},
}


def fmt_v(v):
    return "{" + ", ".join(f"{k}={v[k]}" for k in sorted(v)) + "}"


if __name__ == "__main__":
    print("=" * 74)
    print("КАРАНТИН КАК НЕПОДВИЖНАЯ ТОЧКА: жадный и ленивый скачки")
    print("=" * 74)

    for title, system in ZOO.items():
        print(f"\n### {title}")

        fps_e = fixed_points(system, EAGER)
        fps_l = fixed_points(system, LAZY)
        print(f"  неподвижные точки ЖАДНОГО скачка: "
              + (", ".join(map(fmt_v, fps_e)) if fps_e else "НЕТ"))
        print(f"  неподвижные точки ЛЕНИВОГО скачка: "
              + (", ".join(map(fmt_v, fps_l)) if fps_l else "НЕТ"))

        mw = monotone_witness(system, EAGER)
        ml = monotone_witness(system, LAZY)
        if mw:
            v, w = mw
            print(f"  жадный скачок НЕмонотонен: {fmt_v(v)} ⊑ {fmt_v(w)}, "
                  f"но J(v)={fmt_v(jump(system, v, EAGER))} ⋢ "
                  f"J(w)={fmt_v(jump(system, w, EAGER))}")
        if ml:
            print("  !! ленивый скачок немонотонен — противоречит H3")

        trace, loop = iterate(system, EAGER)
        if loop is None:
            print("  итерация жадного из Z: не сошлась за лимит")
        else:
            period = len(trace) - loop
            if period == 1:
                print(f"  итерация жадного из Z: сошлась к {fmt_v(trace[-1])}")
            else:
                cyc = trace[loop:]
                print(f"  итерация жадного из Z: ЦИКЛ периода {period}: "
                      + " → ".join(fmt_v(x) for x in cyc))

        lfp = least_fp_lazy(system)
        quarantine = [k for k, val in lfp.items() if val == Z]
        print(f"  ленивое заземление (наименьшая т.): {fmt_v(lfp)}"
              + (f"   карантин: {{{', '.join(quarantine)}}}" if quarantine
                 else "   карантин пуст"))

        # жадный вердикт-читка поверх ленивой точки
        for name in sorted(system):
            content = ev_reg(system[name], lfp, EAGER)
            if lfp[name] == Z:
                bullet = " ← ПУЛЯ: содержание T, истины нет" \
                    if content == T else ""
                print(f"    вердикт ZTL по содержанию {name}: {content}"
                      f" (само предложение в карантине){bullet}")
