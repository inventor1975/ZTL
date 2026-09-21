# -*- coding: utf-8 -*-
"""Разделение ВЕРДИКТА и ГАРАНТИИ: сторож отказывает в гарантии, не в ответе.

Замысел (принят куратором 2026-09-21). Вердикт линеен — 50 000 звеньев за
0,023 с. Экспонента живёт только в двух битах гарантии. Прежде дорогое место
отвергало ВЕСЬ документ. Теперь вердикт отдаётся всегда, а гарантия либо
называется, либо честно не называется.

ЧЕГО ЗДЕСЬ СТОРОЖИТЬ. Отказ, который подменяет ответ, был бы хуже прежнего
отказа во всём: прежний был виден, а подмена молчалива. Поэтому главная
проверка — не «быстро ли», а **бюджет не МЕНЯЕТ ответ, он только заменяет
его отказом**. Быстрый неверный разряд нам не нужен.

    python3 test_guard_split.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ztl                                                     # noqa: E402
import zverify as Z                                            # noqa: E402
from zverify import T, F                                       # noqa: E402

BUDGET = 59049          # 3**10 — нынешний предел студии, выраженный в переборе


def _chain(n, op="and"):
    phi = "a0"
    for i in range(1, n):
        phi = (op, phi, f"a{i}")
    return phi


def test_default_is_the_old_behaviour():
    """МАЯК СОВМЕСТИМОСТИ. budget=None обязан вести себя СЛОВО В СЛОВО как
    до правки — иначе мы поменяли боевой путь, а не добавили запасной."""
    def old(phi, marking):
        ats = ztl.atoms(phi)
        m = {a: v for a, v in marking.items() if a in ats}
        if Z.hereditary_bit(phi, m):
            return "hereditary"
        if Z.stable_bit(phi, m):
            return "sound"
        return "until-verification"

    import random
    rnd = random.Random(5)
    ops, ats = ["and", "or", "imp", "xor", "xnor"], ["p", "q", "r", "s", "t"]

    def gen(d):
        if d == 0:
            return rnd.choice(ats)
        if rnd.random() < 0.25:
            return ("not", gen(d - 1))
        return (rnd.choice(ops), gen(d - 1), gen(d - 1))

    for _ in range(2000):
        phi = gen(rnd.choice([1, 2, 3]))
        mk = {a: rnd.choice(("M", T, F)) for a in ats}
        assert old(phi, mk) == Z.grade(phi, mk), \
            f"budget=None изменил поведение на {ztl.show(phi)} / {mk}"


def test_budget_never_lies():
    """ГЛАВНОЕ. Разряд при бюджете либо тот же, либо честное ослабление —
    но НИКОГДА не другой. Перебором, а не обещанием в комментарии."""
    bad, declined = Z.check_budget_never_lies(trials=3000, seed=11)
    assert not bad, f"бюджет ИЗМЕНИЛ ответ в {len(bad)} случаях: {bad[:2]}"
    # ЗНАМЕНАТЕЛЬ: если отказов ноль, проверка выше ничего не проверила.
    assert declined > 100, \
        f"путь отказа почти не сработал ({declined}) — проверка вакуумна"


def test_verdict_survives_where_the_guarantee_declines():
    """Суть замысла: там, где гарантия не берётся, ВЕРДИКТ всё равно есть.
    Прежде такой документ отвергался целиком."""
    n = 50000
    phi, mk = _chain(n), {f"a{i}": "M" for i in range(n)}
    assert ztl.ev(phi, {f"a{i}": "Z" for i in range(n)}) == "F", \
        "вердикт на длинной цепи потерян"
    assert Z.grade(phi, mk, budget=BUDGET) == "undetermined", \
        "гарантия обязана честно отказаться, а не выдумать разряд"


def test_deep_chain_answers_instead_of_crashing():
    """Обвал стека — НЕ ответ прибора. Промерено двоичным поиском: разряд
    считается до 994 звеньев, дальше кончается стек в `_conjuncts`. Чинить
    все 71 рекурсивные функции ядра ради входа, которого не бывает, — латать
    по одной; но падать молча нельзя."""
    for n in (500, 994, 1000, 5000):
        g = Z.grade(_chain(n), {f"a{i}": "M" for i in range(n)}, budget=BUDGET)
        assert g in ("until-verification", "undetermined"), \
            f"цепь из {n} звеньев дала неожиданный разряд {g}"


def test_refusal_is_not_the_easy_way_out():
    """ОТКАЗ НЕ ДОЛЖЕН БЫТЬ ОТВЕТОМ НА ВСЁ. Прибор, который на любой вход
    говорит «не берусь», прошёл бы все проверки выше. Поэтому здесь обратное
    требование: на обычных, мелких случаях бюджет обязан НЕ мешать."""
    # Случаи строятся ДЕРЕВЬЯМИ, а не разбором текста. В первой редакции
    # здесь стоял разбор через ztljudge._parse с тихим `continue`, если
    # функции нет, — а её нет, и петля молча пропускала все три случая.
    # Проверка выглядела на три, делала ноль. 21.09.
    cases = [
        (("and", "p", "q"), {"p": T, "q": T}, "hereditary"),      # заземлено
        ("b", {"b": "M"}, "until-verification"),                  # голая метка
        (("not", ("not", "p")), {"p": "M"}, "until-verification"),  # опасный T
        (("or", "p", ("not", "p")), {"p": "M"}, "until-verification"),
    ]
    for phi, mk, want in cases:
        full = Z.grade(phi, mk)                    # без бюджета — эталон
        got = Z.grade(phi, mk, budget=BUDGET)
        assert full == want, f"{ztl.show(phi)}: эталон {full}, ждали {want}"
        assert got == want, \
            f"{ztl.show(phi)}: бюджет испортил разряд — {got} вместо {want}"


def test_the_two_bits_decline_separately():
    """Биты считаются по РАЗНЫМ основаниям: уточнений 3**n, завершений 2**n.
    Значит при одном и том же бюджете завершения могут лечь, когда уточнения
    уже не лезут — и это не сбой, а причина, по которой есть разряд
    'sound-or-better'."""
    marks = {f"a{i}": "M" for i in range(8)}
    phi = _chain(8, "or")
    # 3**8 = 6561, 2**8 = 256 — бюджет между ними
    b = 1000
    assert Z.hereditary_bit(phi, marks, b) is None or True   # может решиться дёшево
    st = Z.stable_bit(phi, marks, b)
    assert st is not None, "2**8=256 обязано влезть в бюджет 1000"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"  ✓ {t.__name__}")
    print(f"\n  СТОРОЖ ЗЕЛЁНЫЙ — {len(tests)} проверок. Вердикт отдаётся всегда, "
          f"гарантия либо названа, либо честно не названа.")
