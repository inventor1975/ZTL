# -*- coding: utf-8 -*-
"""
The paradox gauntlet: the whole canon through the WHOLE studio.

Each case runs the full pipeline — natural language -> understanding
(AI) -> ZFL emission (AI) -> validation + bounded repair -> the core —
and the core's passport is checked against the theoretically expected
one. Boundary cases (Berry, sorites) are expected to be REFUSED
honestly at the understanding step.

AI-dependent and non-deterministic — NOT part of run_all.py; run by
hand with the studio server up:  python3 tool/gauntlet.py
"""

import json
import sys
import time
import urllib.request

BASE = "http://localhost:8190"


def api(path, payload):
    req = urllib.request.Request(BASE + path,
        data=json.dumps(payload).encode(),
        headers={"Content-Type": "application/json"})
    return json.loads(urllib.request.urlopen(req, timeout=180).read())


# ------------------------------------------------- expectation predicates
def kinds_of(report):
    return {p["kind"] for p in report.get("passports", [])}


def expect_paradox(rep):
    return "PARADOX" in kinds_of(rep)


def expect_under(rep):
    return "UNDERDETERMINED" in kinds_of(rep)


def expect_grounded(rep):
    return rep.get("genre") == "system" and not rep.get("quarantined")


def expect_deny(rep):
    return (rep.get("genre") == "statement" and rep.get("verdict") == "F"
            and rep.get("warranty") == "until-verification")


def expect_self_kind(rep):
    """Epimenides is informative: any hardened kind is acceptable."""
    return kinds_of(rep) & {"PARADOX", "INTRINSIC", "UNDERDETERMINED"}


CASES = [
    ("Лжец",
     "Это предложение ложно.", expect_paradox, "PARADOX"),
    ("Пиноккио",
     "Пиноккио говорит: «Сейчас мой нос вырастет». Нос растёт тогда и "
     "только тогда, когда Пиноккио лжёт.", expect_paradox, "PARADOX"),
    ("Правдолюб",
     "Это предложение истинно.", expect_under, "UNDERDETERMINED"),
    ("Карусель Журдена",
     "На одной стороне открытки написано: «Предложение на обороте "
     "истинно». На обороте: «Предложение на той стороне ложно».",
     expect_paradox, "PARADOX"),
    ("Сократ и Платон",
     "Платон говорит: «Сократ лжёт». Сократ говорит: «Платон говорит "
     "правду».", expect_paradox, "PARADOX"),
    ("Чётная пара",
     "Два человека. Каждый говорит про другого: «он лжёт».",
     expect_under, "UNDERDETERMINED"),
    ("Пара правдолюбов",
     "Два человека. Каждый говорит про другого: «он говорит правду».",
     expect_under, "UNDERDETERMINED"),
    ("Карри",
     "Предложение гласит: «Если это предложение истинно, то ложь». "
     "Никакого отрицания в нём нет, только импликация.",
     expect_paradox, "PARADOX"),
    ("Крокодил (пессимистка)",
     "Крокодил вернёт ребёнка тогда и только тогда, когда мать угадает, "
     "что он сделает. Мать: «ты не вернёшь».", expect_paradox, "PARADOX"),
    ("Крокодил (оптимистка)",
     "Крокодил вернёт ребёнка тогда и только тогда, когда мать угадает, "
     "что он сделает. Мать: «ты вернёшь».", expect_under,
     "UNDERDETERMINED"),
    ("Брадобрей",
     "Брадобрей бреет всех, кто не бреет себя сам, и только их. Бреет "
     "ли он себя?", expect_paradox, "PARADOX"),
    ("Рассел",
     "Множество R всех множеств, не содержащих себя. Вселенная: a = "
     "пустое множество, b = {b}, и само R. Содержит ли R себя?",
     expect_paradox, "PARADOX"),
    ("Ябло-обрезка",
     "Три предложения по порядку. Первое: «оба следующих ложны». "
     "Второе: «следующее ложно». Третье: «снег белый» (заведомо истинно).",
     expect_grounded, "grounded, no quarantine"),
    ("Эпименид",
     "Критянин Эпименид говорит: «Всё, что говорят критяне, — ложь». "
     "Это его единственное высказывание.", expect_self_kind,
     "informative (any hardened kind)"),
    ("Датчик",
     "Непроверенный датчик показывает перегрев. Если перегрев, то "
     "сработает защита. Сработает ли защита?", expect_deny,
     "statement: F until-verification"),
]

REFUSAL_CASES = [
    ("Берри",
     "Наименьшее натуральное число, которое нельзя описать менее чем "
     "тринадцатью словами. Я его только что описал двенадцатью."),
    ("Сорит (куча)",
     "Одно зерно — не куча. Если n зёрен не куча, то и n+1 не куча. "
     "Значит, миллион зёрен — не куча?"),
]

BUTTON = "Agree"


def run_case(name, text, check, want):
    r = api("/api/chat", {"history": [{"role": "user", "content": text}]})
    if not r.get("ok"):
        return (name, "CHAT FAIL", r.get("error", "")[:60], False)
    reply = r["reply"]
    if BUTTON not in reply:
        return (name, "refused/clarify", reply[:70].replace("\n", " "),
                False)
    e = api("/api/emit", {"understanding": reply})
    if not e.get("ok"):
        return (name, "EMIT FAIL", e.get("error", "")[:60], False)
    zfl = e["zfl"]
    v = api("/api/validate", {"zfl": zfl})
    passes = 0
    if not v["ok"] or v["issues"]:
        rep = api("/api/repair", {"zfl": zfl})
        if rep.get("ok"):
            zfl = rep["zfl"]
            passes = rep.get("note", "")
    run = api("/api/run", {"zfl": zfl})
    if not run.get("ok"):
        codes = [i["code"] for i in run.get("issues", [])]
        return (name, "INVALID after repair", str(codes)[:60], False)
    rep = run["report"]
    got = (", ".join(sorted(kinds_of(rep))) if rep["genre"] == "system"
           else f"{rep['verdict']}/{rep['warranty']}")
    ok = bool(check(rep))
    note = f"expected: {want}" + (f" [{passes}]" if passes else "")
    if not ok:
        note += " | ZFL: " + zfl.replace("\n", " ")[:130]
    return (name, got, note, ok)


def run_refusal(name, text):
    r = api("/api/chat", {"history": [{"role": "user", "content": text}]})
    reply = r.get("reply", r.get("error", ""))
    refused = ("не формализуется" in reply or "does not formalize" in reply
               or "не формализуеться" in reply)
    return (name, "REFUSED" if refused else "accepted (!)",
            reply[:70].replace("\n", " "), refused)


if __name__ == "__main__":
    print("=" * 74)
    print("THE PARADOX GAUNTLET: the canon through the whole studio")
    print("=" * 74)
    ok = bad = 0
    for name, text, check, want in CASES:
        time.sleep(6)                      # let the rate limit breathe
        n, got, note, good = run_case(name, text, check, want)
        ok += good
        bad += not good
        print(f"  {'✓' if good else '✗'} {n:24s} → {got}")
        if not good:
            print(f"      {note}")
    print("\n  — the boundary (must be refused) —")
    for name, text in REFUSAL_CASES:
        time.sleep(6)
        n, got, note, good = run_refusal(name, text)
        ok += good
        bad += not good
        print(f"  {'✓' if good else '✗'} {n:24s} → {got}")
        if not good:
            print(f"      {note}")
    print(f"\nTotal: {ok} ✓, {bad} ✗ of {ok + bad}")
    sys.exit(1 if bad else 0)
