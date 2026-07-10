# -*- coding: utf-8 -*-
"""
Обойма парадоксов для ZTL: лжец, карусель A/B, мститель.

Демонстрирует зафиксированное в SPEC.md разделение труда:
  * таблицы НЕ гасят лжеца (у ¬ нет неподвижной точки — показываем перебором);
  * гасит карантинный флаг: Z-предложения изъяты из-под схемы Тарского;
  * мститель выразим (детектор isZ = ¬(x↔x)) — и флаг платит по счёту:
    содержание вычисляется в T, а истина предложению не выдаётся.
"""

from ztl import T, F, Z, VALUES, NOT, OR, XNOR, isZ


def liar_fixed_points():
    """Лжец λ ↔ ¬λ: ищем значение v с v = ¬v среди всех трёх."""
    print("-- ЛЖЕЦ: λ утверждает ¬λ; нужно v(λ) = v(¬λ) --")
    found = []
    for v in VALUES:
        nv = NOT(v)
        mark = "МОДЕЛЬ" if v == nv else "мимо"
        print(f"  λ={v}:  ¬λ={nv}   → {mark}")
        if v == nv:
            found.append(v)
    if not found:
        print("  Неподвижной точки нет — таблицы лжеца НЕ гасят (как и задумано).")
        print("  Гасит флаг: λ получает Z и изымается из-под схемы Тарского.")
    return found


def liar_revision(steps=6):
    """Ручная прокрутка карусели: v ← ¬v. Осцилляция, которую флаг замораживает."""
    print("\n-- РЕВИЗИЯ (прокрутка лжеца руками) --")
    v = F
    trace = [v]
    for _ in range(steps):
        v = NOT(v)
        trace.append(v)
    print("  " + " → ".join(trace) + " → ... (период 2, не останавливается)")


def carousel():
    """Карусель Журдена: A ↔ B и B ↔ ¬A. Перебираем все 9 пар, включая Z."""
    print("\n-- КАРУСЕЛЬ A/B: нужно v(A)=v(B) и v(B)=v(¬A) --")
    models = []
    for a in VALUES:
        for b in VALUES:
            ok1 = (XNOR(a, b) == T)      # «совпадаем» выполнено
            ok2 = (XNOR(b, NOT(a)) == T) # «различаемся» выполнено
            if ok1 and ok2:
                models.append((a, b))
            print(f"  A={a} B={b}:  A↔B={XNOR(a, b)}  B↔¬A={XNOR(b, NOT(a))}"
                  + ("   МОДЕЛЬ" if ok1 and ok2 else ""))
    if not models:
        print("  Моделей нет даже с Z — обе вершины уходят в карантин флагом.")
    return models


def revenge():
    """Мститель μ: «μ ложно ИЛИ μ в карантине», content = ¬μ ∨ isZ(μ)."""
    print("\n-- МСТИТЕЛЬ: μ утверждает ¬μ ∨ isZ(μ), где isZ(x)=¬(x↔x) --")
    for v in VALUES:
        content = OR(NOT(v), isZ(v))
        verdict = "совпало бы" if content == v else "не совпадает"
        print(f"  μ={v}:  содержание={content}   ({verdict})")
    print("  При μ=Z содержание вычисляется в T — а истины предложению не даём:")
    print("  это счёт, который карантин оплачивает сознательно (SPEC.md, развилка 3).")


if __name__ == "__main__":
    liar_fixed_points()
    liar_revision()
    carousel()
    revenge()
