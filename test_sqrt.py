# -*- coding: utf-8 -*-
"""Корень над числовым полом: маяк, зажим, отказы, третий исход.

Почему отдельным файлом и почему с маяком. Прибор, который на всём отвечает
Z, прошёл бы любую проверку «а умеет ли он сомневаться». Поэтому здесь три
группы, и слабая — первая:

    МАЯК          прибор обязан уметь сказать ТОЧНО там, где точно
    ЗАЖИМ         вилка обязана СОДЕРЖАТЬ корень и быть узкой
    ОТКАЗЫ        прибор обязан уметь сказать НЕТ, и разными способами

Последняя группа — третий исход: там, где вилка задевает порог, вердикт Z.
Это не оговорка, это ответ. Статпакет в том же месте печатает число, и
читатель ему верит.

    python3 test_sqrt.py
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import znum as N                                              # noqa: E402


def test_beacon_exact():
    """Корень точен — вилка обязана СОЙТИСЬ В ТОЧКУ, а не вернуть [2, 2.001]."""
    for x, want in ((4, "2"), (Fraction(9, 4), "3/2"), (0, "0"),
                    (144, "12"), (Fraction(1, 4), "1/2")):
        lo, hi = N._rat_sqrt(N.num(x))
        assert lo == hi, f"sqrt({x}) не сошёлся: [{N.fmt(lo)}, {N.fmt(hi)}]"
        assert N.fmt(lo) == want, f"sqrt({x}) = {N.fmt(lo)}, ждал {want}"


def test_enclosure_contains_and_narrow():
    """Зажим обязан содержать корень С ОБЕИХ сторон и быть узким.
    Проверяется возведением в квадрат — без float и без доверия к себе."""
    for x in (2, 3, 5, 10, Fraction(1, 3), Fraction(22, 7), 1000003):
        v = N.num(x)
        lo, hi = N._rat_sqrt(v)
        assert lo * lo <= v, f"sqrt({x}): нижняя граница ВЫШЕ корня"
        assert hi * hi >= v, f"sqrt({x}): верхняя граница НИЖЕ корня"
        assert hi - lo <= Fraction(2, 10 ** N.SQRT_DIGITS), \
            f"sqrt({x}): вилка шире объявленной точности"


def test_refusals_are_distinct():
    """Два РАЗНЫХ отказа, и их нельзя сливать.

    весь интервал ниже нуля  -> чтений НЕТ ВОВСЕ (четвёртый угол)
    интервал задевает нуль    -> часть чтений не определена: МЕТКА, не вердикт

    Ровно та же разница, что между «документа нет» и «документ говорит
    обратное»: одинаковый отказ, разные следующие действия.
    """
    try:
        N._iv_sqrt((N.num(-4), N.num(-1)))
        raise AssertionError("строго отрицательный интервал ПРОПУЩЕН")
    except N._NoReadings:
        pass
    assert N._iv_sqrt((N.num(-1), N.num(4))) is None, \
        "интервал, задевающий нуль, обязан дать метку, а не вердикт"


def test_units_halve_or_refuse():
    """Степени делятся пополам; нечётная — ОТКАЗ, а не m1.5."""
    for u, want in (("m2", "m"), ("m4", "m2"), (None, None),
                    ("RUB2/m2", "RUB/m")):
        assert N._unit_sqrt(u) == want, f"sqrt({u}) != {want}"
    for u in ("m3", "m", "RUB/m2"):
        try:
            N._unit_sqrt(u)
            raise AssertionError(f"нечётная степень в {u} ПРОПУЩЕНА")
        except N._NoReadings:
            pass


def test_third_outcome_is_reachable():
    """ГЛАВНОЕ. Порог ВНУТРИ вилки обязан дать Z — и этот Z обязан быть
    ДОСТИЖИМ, иначе третий исход только объявлен."""
    q = {"x": N.qty(2, 2, N.EARNED, witness="мемо-7")}
    lo, hi = N._rat_sqrt(N.num(2))
    below = N.compare("lt", ("sqrt", "x"), lo / 2, q)[0]
    inside = N.compare("lt", ("sqrt", "x"), (lo + hi) / 2, q)[0]
    above = N.compare("lt", ("sqrt", "x"), hi * 2, q)[0]
    assert (below, inside, above) == ("F", "Z", "T"), \
        f"третий исход недостижим: {(below, inside, above)}"


def test_precision_changes_the_verdict():
    """Та же формула, то же число, РАЗНАЯ объявленная точность — разный
    вердикт. Это не дефект: это причина, по которой точность обязана быть
    объявлена, а не выбрана молча внутри прибора."""
    q = {"x": N.qty(2, 2, N.EARNED)}
    thr = Fraction("1.4142")
    keep = N.SQRT_DIGITS
    try:
        N.SQRT_DIGITS = 3
        coarse = N.compare("lt", ("sqrt", "x"), thr, q)[0]
        N.SQRT_DIGITS = 12
        fine = N.compare("lt", ("sqrt", "x"), thr, q)[0]
    finally:
        N.SQRT_DIGITS = keep
    assert coarse == "Z", f"при 3 знаках ждал Z, получил {coarse}"
    assert fine == "F", f"при 12 знаках ждал F, получил {fine}"


def test_default_precision_is_pinned():
    """ОБЪЯВЛЕННАЯ точность по умолчанию прибита ЛИТЕРАЛОМ, а не собой.

    Добавлено 2026-09-21 мутационным прогоном: подмена SQRT_DIGITS 12 -> 2
    ВЫЖИЛА, все проверки остались зелёными. Причина —
    test_enclosure_contains_and_narrow меряет ширину вилки против
    N.SQRT_DIGITS, то есть против той самой величины, которую и надо
    сторожить. Эталон из себя: при любой подмене сравнение подстраивается
    и молчит.

    Поэтому здесь число стоит ГОЛЫМ. Если точность по умолчанию просядет,
    упадёт этот маяк, а не чей-то счёт через полгода."""
    assert N.SQRT_DIGITS == 12, \
        f"точность по умолчанию изменена на {N.SQRT_DIGITS} — это меняет ВЕРДИКТЫ"
    lo, hi = N._rat_sqrt(N.num(2))
    assert hi - lo <= Fraction(1, 10 ** 11), \
        f"вилка по умолчанию шире 1e-11: {float(hi - lo)}"
    assert hi - lo > 0, "вилка sqrt(2) сошлась в точку — корень иррационален"


def test_precision_has_a_ceiling():
    """Потолок точности. `decimal5000000` однажды повесил службу — тот же
    вход сюда обязан быть закрыт."""
    lo, hi = N._rat_sqrt(N.num(2), 10 ** 9)
    assert hi - lo <= Fraction(2, 10 ** N.SQRT_DIGITS_CAP), \
        "потолок точности не сработал"


def test_provenance_survives_the_root():
    """Кредит проходит СКВОЗЬ корень: число без свидетеля остаётся на вере,
    и это видно в родословной, а не теряется по дороге."""
    v, ped, _, _ = N.compare("lt", ("sqrt", "y"), Fraction(3, 2),
                             {"y": N.qty(2, 2)})
    assert ped == {"y"}, f"кредит потерян под корнем: {ped}"
    v, ped, _, _ = N.compare("lt", ("sqrt", "x"), Fraction(3, 2),
                             {"x": N.qty(2, 2, N.EARNED, witness="w")})
    assert ped == set(), f"заработанное помечено кредитом: {ped}"


# ---------------------------------------------------------------------------
# Глубокая цепь. Добавлено 2026-09-21 по третьей работе: до неё цепь из двух
# тысяч «и» клала стек Python, и это был МОЛЧАЛИВЫЙ ОТКАЗ ПРИБОРА, а не ответ.
# ---------------------------------------------------------------------------
def test_deep_chain_does_not_blow_the_stack():
    from ztl import ev
    for n, want in ((500, "T"), (3000, "T"), (10000, "T")):
        phi = "a0"
        for i in range(1, n):
            phi = ("and", phi, f"a{i}")
        env = {f"a{i}": "T" for i in range(n)}
        assert ev(phi, env) == want, f"цепь из {n} звеньев не посчиталась"
    # и F тоже, чтобы не выйти зелёным на одном значении
    phi = "a0"
    for i in range(1, 3000):
        phi = ("and", phi, f"a{i}")
    env = {f"a{i}": "T" for i in range(3000)}
    env["a1500"] = "F"
    assert ev(phi, env) == "F", "одно F внутри длинной цепи потерялось"


def test_iterative_agrees_with_recursive():
    """Запасной путь обязан давать ТО ЖЕ, а не просто не падать."""
    import random
    from ztl import _ev_rec, _ev_iter
    rnd = random.Random(3)
    ops = ["and", "or", "imp", "xor", "xnor"]
    ats = ["p", "q", "r", "s"]

    def gen(d):
        if d == 0:
            return rnd.choice(ats)
        if rnd.random() < 0.2:
            return ("not", gen(d - 1))
        return (rnd.choice(ops), gen(d - 1), gen(d - 1))

    for vals in ({a: "Z" for a in ats}, {a: "T" for a in ats},
                 {"p": "T", "q": "F", "r": "Z", "s": "T"}):
        for _ in range(500):
            phi = gen(rnd.choice([1, 2, 3, 4]))
            assert _ev_rec(phi, vals) == _ev_iter(phi, vals), \
                f"пути разошлись на {phi}"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"  ✓ {t.__name__}")
    print(f"\n  КОРЕНЬ ЗЕЛЁНЫЙ — {len(tests)} проверок, включая маяк на "
          f"точность и достижимость третьего исхода.")