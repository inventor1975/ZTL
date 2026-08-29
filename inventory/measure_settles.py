#!/usr/bin/env python3
"""ПРОМЕР поля `settles` двумя НЕЗАВИСИМЫМИ путями по всей глубине 2.

`settles` заявляет: оба исхода проверки атома терминальны (EARNED/REFUTED).
Проверяю это ВТОРЫМ путём, через другую функцию: если наряд вправду закрывает
дело, то после проверки атома судье БОЛЬШЕ НЕЧЕГО заказывать — next_check
обязан вернуть None в обеих ветках. Совпадение двух путей и есть свидетельство;
одна функция, сверенная сама с собой, не доказывает ничего.
"""
import itertools, sys
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent.parent))
import ztljudge as J

АТОМЫ = ["a", "b"]
ЛИСТЬЯ = АТОМЫ + [f"~{x}" for x in АТОМЫ]
БИН = ["&", "|", "->"]

формулы = set(ЛИСТЬЯ)
for l, o, r in itertools.product(ЛИСТЬЯ, БИН, ЛИСТЬЯ):
    формулы.add(f"({l} {o} {r})")
    формулы.add(f"~({l} {o} {r})")
формулы = sorted(формулы)

всего = совпало = разошлось = ошибок = 0
примеры = []
for t in формулы:
    try:
        опции = J.what_if(t)
    except Exception:
        ошибок += 1
        continue
    known = {k: v for k, v in J._full(J.formalize(t), None).items() if v != J.Z}
    for o in опции:
        всего += 1
        # ВТОРОЙ ПУТЬ: после проверки атома судье нечего заказывать?
        нечего_T = J.next_check(t, {**known, o["atom"]: J.T}) is None
        нечего_F = J.next_check(t, {**known, o["atom"]: J.F}) is None
        второй = нечего_T and нечего_F
        if второй == o["settles"]:
            совпало += 1
        else:
            разошлось += 1
            if len(примеры) < 6:
                примеры.append((t, o["atom"], o["settles"], второй, o["if_T"], o["if_F"]))

print(f"формул глубины 2:            {len(формулы)}")
print(f"пар (формула, атом):         {всего}")
print(f"два пути СОШЛИСЬ:            {совпало}")
print(f"РАЗОШЛИСЬ:                   {разошлось}")
print(f"формул, которые не разобрались: {ошибок}")
if примеры:
    print("\nрасхождения:")
    for t, a, s, v, dt, df in примеры:
        print(f"  {t:22} атом {a}: settles={s} второй путь={v}  (T:{dt} F:{df})")
# КОНТРОЛЬ ФАЛЬСИФИКАЦИЕЙ. Ноль расхождений ничего не стоит, пока не показано,
# что промер УМЕЕТ покраснеть. Портим `settles` нарочно и требуем, чтобы он это
# поймал: перевёрнутое — все пары, «всегда True» — ровно те, что на деле narrows.
def _мерить(what_if):
    в = с = р = 0
    for t in формулы:
        known = {k: v for k, v in J._full(J.formalize(t), None).items() if v != J.Z}
        for o in what_if(t):
            в += 1
            второй = (J.next_check(t, {**known, o["atom"]: J.T}) is None
                      and J.next_check(t, {**known, o["atom"]: J.F}) is None)
            с += (второй == o["settles"]); р += (второй != o["settles"])
    return в, с, р

_настоящий = J.what_if
_перевёрнутый = lambda t, m=None: [{**o, "settles": not o["settles"]} for o in _настоящий(t, m)]
_всегда = lambda t, m=None: [{**o, "settles": True} for o in _настоящий(t, m)]
_в1, _, _р1 = _мерить(_перевёрнутый)
_в2, _с2, _р2 = _мерить(_всегда)
print(f"\nКОНТРОЛЬ ФАЛЬСИФИКАЦИЕЙ:")
print(f"  settles перевёрнут  -> расхождений {_р1} из {_в1} (должно быть ВСЕ)")
print(f"  settles всегда True -> расхождений {_р2} из {_в2}; значит narrows на деле {_р2}, settles {_с2}")
ok = (разошлось == 0 and ошибок == 0 and _р1 == _в1 and 0 < _р2 < _в2)
print(f"\nSETTLES {'GREEN' if ok else 'RED'}: два пути сошлись {совпало}/{всего}, "
      f"промер доказал, что умеет краснеть")
raise SystemExit(0 if ok else 1)
