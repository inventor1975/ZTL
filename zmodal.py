# -*- coding: utf-8 -*-
"""
Экспедиция Э10: модальный слой ZTL.

Миры = классические дочитки непроверенных атомов. □φ = во всех мирах,
◇φ = хоть в одном. Промеры:
  1. Вердикты атомов = модальные пороги (T⟺□, F⟺□¬, Z⟺контингентно) +
     дуальность ◇ = ¬□¬ и S5-коллапс (□□=□).
  2. Таблó-знаки = модальные заявки: T/F строгие = □, P/N = ◇.
  3. Столбцы: классика | глобальный □ (супервалюация) | ZTL (локальный
     □ за каждым оператором) — три разных логики на одной формуле.
Бочваровские трансляции (наша → = ◇A⊃□B) получают семантику миров.
"""

from itertools import product

from ztl import T, F, Z, OPS2, NOT, ev, atoms, all_envs

# ------------------------------------------------- миры и модальности
def worlds(marked):
    """Все классические дочитки: marked — dict атом → 'V:T'/'V:F'/'M'."""
    names = sorted(marked)
    opts = [[marked[n]] if marked[n] in (T, F) else [T, F] for n in names]
    return [dict(zip(names, combo)) for combo in product(*opts)]


def classical_eval(phi, world):
    return ev(phi, world)          # на классических мирах ev классичен


def box(phi, marked):
    return all(classical_eval(phi, w) == T for w in worlds(marked))


def dia(phi, marked):
    return any(classical_eval(phi, w) == T for w in worlds(marked))


def ztl_eval(phi, marked):
    env = {n: (v if v in (T, F) else Z) for n, v in marked.items()}
    return ev(phi, env)


def global_super(phi, marked):
    """Глобальная супервалюация: один □ на всю формулу."""
    if box(phi, marked):
        return T
    if not dia(phi, marked):
        return F
    return Z                        # супер-пробел


if __name__ == "__main__":
    print("=" * 72)
    print("Э10. МОДАЛЬНЫЙ СЛОЙ: миры-дочитки, локальный □ против глобального")
    print("=" * 72)

    p, q = "p", "q"

    print("\n### 1. Атомы: вердикты = модальные пороги (тотально)")
    ok = True
    for st in (T, F, "M"):
        marked = {p: st}
        v = ztl_eval(p, marked)
        b, d = box(p, marked), dia(p, marked)
        expect = T if b else (F if not d else Z)
        ok &= (v == expect)
        print(f"  атом p[{'метка' if st == 'M' else st}]: вердикт {v},"
              f"  □p={b}, ◇p={d}  → порог {'совпал' if v == expect else 'РАСХОЖДЕНИЕ'}")
    # дуальность и S5-коллапс
    dual = all(dia(p, {p: st}) == (not box(("not", p), {p: st}))
               for st in (T, F, "M"))
    print(f"  дуальность ◇p = ¬□¬p: {'✓' if dual else '✗'};"
          f"  □□ = □ тривиально (□p классичен) — S5-коллапс вложенности")

    print("\n### 2. Таблó-знаки как модальные заявки")
    marked = {p: "M"}
    print("  знак T:φ  = □φ   (строгая заявка: вынуждено всеми дочитками)")
    print("  знак F:φ  = □¬φ  (строгое опровержение)")
    print(f"  знак P:φ = ◇φ:  для метки ◇p = {dia(p, marked)} — заявка возможности")
    print(f"  знак N:φ = ◇¬φ: для метки ◇¬p = {dia(('not', p), marked)}")
    print("  «Ослабленные знаки только в F-полярности» = опровержение")
    print("  довольствуется возможностью, доказательство требует необходимости.")

    print("\n### 3. Три логики на одних формулах: классика | глобальный □ | ZTL")
    battery = [
        ("¬¬p",        ("not", ("not", p))),
        ("p → p",      ("imp", p, p)),
        ("p ∨ ¬p",     ("or", p, ("not", p))),
        ("¬(p ∧ ¬p)",  ("not", ("and", p, ("not", p)))),
        ("p ∧ ¬p",     ("and", p, ("not", p))),
        ("(p∧q)→p",    ("imp", ("and", p, q), p)),
    ]
    marked = {p: "M", q: "M"}
    print(f"  {'формула':14s} {'классика(p=T)':14s} {'глобальный □':13s} {'ZTL':4s}")
    for nm, phi in battery:
        cl = classical_eval(phi, {p: T, q: T})
        gs = global_super(phi, marked)
        zt = ztl_eval(phi, marked)
        print(f"  {nm:14s} {cl:14s} {gs:13s} {zt:4s}")
    print("  Глобальный □ (супервалюация) сохраняет ВСЕ классические")
    print("  тавтологии (p→p, LEM — истинны «в целом», не зная p);")
    print("  ZTL ставит □ ЛОКАЛЬНО за каждым оператором — и тавтологии")
    print("  формы падают, а ¬¬p наоборот зарабатывает T (лестница этажей).")
    print("  Расщепление супервалюация/ZTL = глобальная/локальная модальность.")

    print("\n### Итог")
    print("  ZTL — локально-модальная логика над S5-рамкой миров-дочиток:")
    print("  каждый оператор несёт собственный □-коллапс. Бочваровские")
    print("  трансляции (наша → = ◇A⊃□B, ¬ = □¬) — это её модальная запись,")
    print("  теперь с семантикой миров. Знаки таблó = {□, □¬, ◇, ◇¬}.")
    print("  Родич-теоретик: эпистемическая S5 Хинтикки (□ = «знаю») —")
    print("  ZTL утверждает только знаемое, но модальность у неё")
    print("  по-операторная, а не пропозициональная.")
