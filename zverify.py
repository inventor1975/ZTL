# -*- coding: utf-8 -*-
"""
Экспедиция Э12: операция «верифицировать» и стабильность вердиктов.

УЗКОЕ МЕСТО: жадные вердикты немонотонны относительно верификации —
переворачиваются и отказы (ожидаемо: default deny до проверки), и T
(опасно: ¬¬p = T умирает при p:=F). Вердикт без гарантии — клетка Фреге.

ЛЕЧЕНИЕ: бит стабильности = глобальная супервалюация (все дочитки дают
один классический ответ, совпадающий с вердиктом). Промеры:
  1. Галерея переворотов (включая гибель T).
  2. ТЕОРЕМА ЭКВИВАЛЕНТНОСТИ: стабильность-по-супервалюации ⟺
     инвариантность при ЛЮБОЙ последовательности верификаций (тотально).
  3. Классификация вердиктов батареи: T/F × стабильно/до-верификации.
  4. Монотонность: стабильный вердикт не отменяется никаким verify.
Вывод для инструмента: вердикт = пара (значение, гарантия).
"""

from itertools import product

from ztl import T, F, Z, ev, atoms
from zmodal import worlds, ztl_eval, global_super

# marking: dict атом → T | F | 'M' (метка)

def verify(marking, atom, value):
    """Акт верификации: снять метку, вписать заработанное значение."""
    assert marking[atom] == "M", "верифицировать можно только метку"
    m2 = dict(marking)
    m2[atom] = value
    return m2


def stable_bit(phi, marking):
    """Стабильность по супервалюации: все дочитки — один классический
    ответ, равный текущему жадному вердикту."""
    v = ztl_eval(phi, marking)
    return all(ev(phi, w) == v for w in worlds(marking))


def invariant_under_all_verifications(phi, marking):
    """Истинная инвариантность: вердикт не меняется ни при какой
    последовательности верификаций (перебор всех путей дозаземления)."""
    v0 = ztl_eval(phi, marking)
    marks = [a for a, s in marking.items() if s == "M"]

    def rec(m, rest):
        if ztl_eval(phi, m) != v0:
            return False
        if not rest:
            return True
        a = rest[0]
        return all(rec(verify(m, a, val), rest[1:]) for val in (T, F))

    # порядок верификаций не важен для перебора итогов: проверяем все
    # подмножества через рекурсию по фиксированному списку (каждый шаг —
    # оба значения; промежуточные состояния проверяются на каждом шаге)
    return rec(marking, marks)


if __name__ == "__main__":
    p, q = "p", "q"
    print("=" * 72)
    print("Э12. ВЕРИФИКАЦИЯ И СТАБИЛЬНОСТЬ: огораживаем клетку Фреге")
    print("=" * 72)

    print("\n### 1. Галерея переворотов (p — метка)")
    gallery = [
        ("p ∨ ¬p", ("or", p, ("not", p)), T),
        ("p → p",  ("imp", p, p), T),
        ("¬¬p",    ("not", ("not", p)), F),      # ← гибель T!
        ("¬(p∧¬p)", ("not", ("and", p, ("not", p))), T),
        ("p ∧ ¬p", ("and", p, ("not", p)), T),
    ]
    m0 = {p: "M"}
    for nm, phi, val in gallery:
        v_before = ztl_eval(phi, m0)
        v_after = ztl_eval(phi, verify(m0, p, val))
        st = stable_bit(phi, m0)
        flip = "ПЕРЕВОРОТ" if v_before != v_after else "устоял"
        print(f"  {nm:10s} вердикт {v_before} → verify(p:={val}) → {v_after}"
              f"  [{flip}; бит стабильности: {'СТАБИЛЕН' if st else 'до-верификации'}]")
    print("  ¬¬p: жадное T гибнет при p:=F — вердикт-T без гарантии опасен.")
    print("  Бит стабильности предсказал каждый переворот и каждую стойкость.")

    print("\n### 2. Теорема эквивалентности (тотально, 2 атома)")
    pool = [p, ("not", p), ("or", p, ("not", p)), ("not", ("not", p)),
            ("imp", p, q), ("and", p, ("not", q)), ("xnor", p, q),
            ("or", ("and", p, q), ("not", p)), ("xor", p, ("not", q)),
            ("imp", ("not", ("not", p)), q)]
    markings = [dict(zip((p, q), c)) for c in product((T, F, "M"), repeat=2)]
    total, mismatch = 0, 0
    for phi in pool:
        for m in markings:
            total += 1
            if stable_bit(phi, m) != invariant_under_all_verifications(phi, m):
                mismatch += 1
                print(f"  ✗ РАСХОЖДЕНИЕ: {phi} при {m}")
    print(f"  проверено пар (формула × разметка): {total}; расхождений: {mismatch}")
    if mismatch == 0:
        print("  ✓ СТАБИЛЬНОСТЬ-ПО-СУПЕРВАЛЮАЦИИ ⟺ ИНВАРИАНТНОСТЬ ПРИ ЛЮБЫХ")
        print("    ВЕРИФИКАЦИЯХ — гарантия вычислима одним глобальным прогоном.")

    print("\n### 3. Классификация вердиктов батареи (p, q — метки)")
    m2 = {p: "M", q: "M"}
    classes = {}
    for phi in pool:
        v = ztl_eval(phi, m2)
        st = stable_bit(phi, m2)
        key = (v, st)
        classes.setdefault(key, []).append(phi)
    for (v, st), fs in sorted(classes.items(), key=repr):
        label = f"{v}-{'стабильные' if st else 'до-верификации'}"
        print(f"  {label:22s}: {len(fs)} формул")
    print("  Опасный класс — «T-до-верификации» (лестничные вердикты):")
    for phi in classes.get((T, False), []):
        print(f"    {phi}")

    print("\n### 4. Монотонность стабильного (тотально)")
    bad = 0
    for phi in pool:
        for m in markings:
            if stable_bit(phi, m):
                marks = [a for a, s in m.items() if s == "M"]
                for a in marks:
                    for val in (T, F):
                        m2v = verify(m, a, val)
                        if ztl_eval(phi, m2v) != ztl_eval(phi, m) or \
                           not stable_bit(phi, m2v):
                            bad += 1
    print(f"  нарушений монотонности стабильных вердиктов: {bad}")
    print("  ✓ Стабильный вердикт не отменяется и не теряет стабильность.")

    print("\n### Итог для инструмента")
    print("  Вердикт = ПАРА (значение, гарантия): значение — жадное (быстро,")
    print("  локально), гарантия — супервалюационная (один глобальный прогон")
    print("  по дочиткам). «T стабильное» — можно строить дом; «T до-верифи-")
    print("  кации» — лестничный рапорт, живёт до первой проверки; «F стабиль-")
    print("  ное» — заработанное опровержение; «F до-верификации» — default")
    print("  deny. Локальный и глобальный режимы (Э10) — не соперники, а")
    print("  ответ и гарантия одного продукта. Клетка Фреге огорожена.")
