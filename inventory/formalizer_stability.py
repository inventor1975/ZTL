# -*- coding: utf-8 -*-
"""
ОПЫТ 2 — УСТОЙЧИВОСТЬ ФОРМАЛИЗАТОРА.

Вопрос куратора вёл к теореме: «если судья не устоит перед этикой, значит
логика и этика не связаны». Формальная половина тривиальна — вердикт есть
функция от формулы, значит всё, чего в формуле нет, на вердикт не влияет.
Содержательная половина НЕ доказуема, она измерима, и мерить надо ровно один
шаг: ТЕКСТ → ФОРМУЛА. Если формула для одного текста скачет, то «этика вне
логики» ничего не значит — этика просто утонула в шуме перевода.

ЧТО МЕРИМ. Один текст прогоняется через ЖИВОЙ путь студии (understand →
emit, промты импортируются из tool/translator.py, а не сочиняются здесь)
N раз независимо, при рабочей температуре 0.2. Считаем, сколько РАЗНЫХ
канонических формул вышло.

КАНОНИЧЕСКАЯ ФОРМА. Вердикт не зависит от имён атомов — он функция формы и
разметки. Поэтому имена переименовываются по порядку первого появления, и
две выдачи считаются одной, если совпали форма и вектор статусов. Строгое
совпадение (с именами) считается отдельно и печатается рядом: расхождение
между двумя числами и есть цена имён.

ДВЕ КОНТРОЛЬНЫЕ ПАРЫ, БЕЗ КОТОРЫХ ЧИСЛО НИЧЕГО НЕ СТОИТ.
  ОТРИЦАТЕЛЬНЫЙ: две формализации, отличающиеся ТОЛЬКО именами атомов.
    Мера ОБЯЗАНА сказать «одно и то же». Иначе она меряет имена.
  ПОЛОЖИТЕЛЬНЫЙ: две формализации разной ФОРМЫ.
    Мера ОБЯЗАНА сказать «разное». Иначе она слепа и любое «всё совпало»
    ничего не значит.
Оба гоняются ПЕРЕД корпусом; при провале любого прогон не начинается.

ЭТИЧЕСКАЯ ПАРА. Два текста одной логической формы и разного веса: «непро-
веренный осведомитель сообщает, что подозреваемый вооружён» против «непро-
веренный поставщик сообщает, что партия испорчена». Если канон совпал —
это ПРЯМОЕ измерение того, что этическая разница в формулу не попадает, а
не рассуждение об этом.

МОДЕЛЬ. Локальная, через ollama (RTX 5070 Ti). Форк Opus не гоняем без
разрешения куратора — его ключ, его деньги.
"""

import json
import os
import sys
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "tool"))

import translator            # noqa: E402  — живые промты студии
import zfl                   # noqa: E402  — живой разбор формул

OLLAMA = "http://127.0.0.1:11434/v1/chat/completions"
TEMPERATURE = 0.2            # рабочая температура студии (translator.llm)


# ---------------------------------------------------------------- транспорт

class CallError(Exception):
    pass


def call(messages, model, temperature=TEMPERATURE, timeout=300):
    body = {"model": model, "messages": messages,
            "temperature": temperature, "stream": False}
    req = urllib.request.Request(
        OLLAMA, data=json.dumps(body).encode(),
        headers={"Content-Type": "application/json",
                 "Authorization": "Bearer ollama"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            data = json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        raise CallError(f"HTTP {e.code}: {e.read().decode()[:200]}")
    except Exception as e:
        raise CallError(str(e))
    choices = data.get("choices") or []
    if not choices:
        raise CallError("пустой choices")
    content = (choices[0].get("message") or {}).get("content")
    if content is None:
        raise CallError("пустой content")
    return content.strip()


# --------------------------------------------------------------- канон

def _canon_tree(tree, names):
    """Дерево с именами атомов, заменёнными на a0, a1, ... по первому
    появлению. `names` — накопитель порядка, он же даёт вектор статусов."""
    if isinstance(tree, str):
        if tree in ("T", "F"):
            return tree
        if tree not in names:
            names[tree] = f"a{len(names)}"
        return names[tree]
    op = tree[0]
    return (op,) + tuple(_canon_tree(x, names) for x in tree[1:])


def canon(doc):
    """ZFL-документ -> (строгий ключ, структурный ключ) или ('BAD', причина).

    Строгий ключ сохраняет имена атомов; структурный их стирает. Вердикт
    зависит только от структурного."""
    if not isinstance(doc, dict):
        return ("BAD", "не объект")
    genre = doc.get("genre")
    try:
        if genre == "statement":
            assertion = doc.get("assert")
            if not isinstance(assertion, str):
                return ("BAD", "нет assert")
            tree = zfl.parse_formula(assertion)
            names = {}
            shape = _canon_tree(tree, names)
            atoms = doc.get("atoms") or {}
            statuses = tuple((atoms.get(orig) or {}).get("status", "?")
                             for orig in names)
            strict = json.dumps(
                {"g": "statement", "f": _flat(tree),
                 "s": {k: (v or {}).get("status") for k, v in atoms.items()}},
                sort_keys=True, ensure_ascii=False)
            struct = json.dumps({"g": "statement", "f": _flat(shape),
                                 "s": statuses}, ensure_ascii=False)
            return (strict, struct)
        if genre == "system":
            sents = doc.get("sentences") or {}
            if not sents:
                return ("BAD", "нет sentences")
            order = sorted(sents)
            names = {}
            shapes = []
            for k in order:
                if k not in names:
                    names[k] = f"a{len(names)}"
            for k in order:
                shapes.append((names[k],
                               _flat(_canon_tree(zfl.parse_formula(sents[k]),
                                                 names))))
            strict = json.dumps({"g": "system",
                                 "f": {k: _flat(zfl.parse_formula(sents[k]))
                                       for k in order}},
                                sort_keys=True, ensure_ascii=False)
            struct = json.dumps({"g": "system", "f": sorted(shapes)},
                                ensure_ascii=False)
            return (strict, struct)
        return ("BAD", f"жанр {genre!r}")
    except Exception as e:
        return ("BAD", f"{type(e).__name__}: {e}")


def _flat(t):
    if isinstance(t, str):
        return t
    return [t[0]] + [_flat(x) for x in t[1:]]


# --------------------------------------------------------- контрольные пары

# ОТРИЦАТЕЛЬНЫЙ: одно и то же с точностью до имён. Структурный ключ обязан
# совпасть, строгий — обязан РАЗОЙТИСЬ (иначе строгий ключ имена не видит).
NEG_A = {"genre": "statement",
         "atoms": {"overheat": {"status": "Z"}, "shutdown": {"status": "Z"}},
         "assert": "imp(overheat, shutdown)"}
NEG_B = {"genre": "statement",
         "atoms": {"hot": {"status": "Z"}, "stop": {"status": "Z"}},
         "assert": "imp(hot, stop)"}

# ПОЛОЖИТЕЛЬНЫЙ: разная форма. Оба ключа обязаны разойтись.
POS_A = {"genre": "statement",
         "atoms": {"p": {"status": "Z"}, "q": {"status": "Z"}},
         "assert": "imp(p, q)"}
POS_B = {"genre": "statement",
         "atoms": {"p": {"status": "Z"}, "q": {"status": "Z"}},
         "assert": "and(p, q)"}

# ТРЕТИЙ КОНТРОЛЬ: та же форма, РАЗНАЯ разметка. Структурный ключ обязан
# разойтись — иначе мера не видит статусов, а они половина вердикта.
STAT_A = {"genre": "statement",
          "atoms": {"p": {"status": "Z"}, "q": {"status": "Z"}},
          "assert": "imp(p, q)"}
STAT_B = {"genre": "statement",
          "atoms": {"p": {"status": "T"}, "q": {"status": "Z"}},
          "assert": "imp(p, q)"}


def controls():
    """Прогнать контроли. Возвращает список (имя, ok, пояснение)."""
    out = []
    na, nb = canon(NEG_A), canon(NEG_B)
    out.append(("ОТРИЦАТЕЛЬНЫЙ структурный (имена не должны считаться)",
                na[1] == nb[1], f"{na[1]} vs {nb[1]}"))
    out.append(("ОТРИЦАТЕЛЬНЫЙ строгий (имена ДОЛЖНЫ считаться)",
                na[0] != nb[0], "строгие ключи разошлись"
                if na[0] != nb[0] else "строгий ключ имён не видит"))
    pa, pb = canon(POS_A), canon(POS_B)
    out.append(("ПОЛОЖИТЕЛЬНЫЙ форма (разное должно быть разным)",
                pa[1] != pb[1], f"{pa[1]} vs {pb[1]}"))
    sa, sb = canon(STAT_A), canon(STAT_B)
    out.append(("ПОЛОЖИТЕЛЬНЫЙ разметка (статус входит в канон)",
                sa[1] != sb[1], f"{sa[1]} vs {sb[1]}"))
    bad = canon({"genre": "statement", "assert": "imp(p,"})
    out.append(("МУСОР помечается BAD, а не считается формулой",
                bad[0] == "BAD", str(bad)))
    return out


# ------------------------------------------------------------------ корпус

CORPUS = [
    ("S1-modus-ponens", "en", "нейтральный, простой",
     "If A implies B, and A is true, then B is true."),
    ("S2-liar", "en", "нейтральный, самореференция",
     "This sentence is false."),
    ("E1-armed-suspect", "en", "ЭТИКА тяжёлая",
     "An unverified informant reports that the suspect is armed. "
     "If the suspect is armed, the officers force entry. Will they enter?"),
    ("E2-spoiled-cargo", "en", "ЭТИКА лёгкая, ТА ЖЕ ФОРМА",
     "An unverified supplier reports that the shipment is spoiled. "
     "If the shipment is spoiled, the warehouse discards it. "
     "Will they discard it?"),
    ("R1-sensor", "ru", "нейтральный, русский",
     "Непроверенный датчик сообщает о перегреве. Если перегрев, "
     "срабатывает отключение. Сработает ли оно?"),
    ("R2-donor", "ru", "ЭТИКА тяжёлая, русский",
     "Непроверенный анализ показывает, что донор заражён. Если донор "
     "заражён, партию крови уничтожают. Уничтожат ли её?"),
]


def one_pass(text, model, mode="par"):
    """Живой путь студии: understand -> emit. Возвращает (doc|None, сырьё)."""
    sys_u = (translator.UNDERSTAND_SYS_HYP if mode in ("hyp", "ast")
             else translator.UNDERSTAND_SYS)
    understanding = call(
        [{"role": "system", "content": sys_u},
         {"role": "user", "content": text}], model)
    if mode in ("hyp", "ast"):
        sys_e = translator.EMIT_SYS_HYP
        user = (f"The agreed understanding:\n{understanding}\n\n"
                "Emit the ZFL statement for the claimed rule.")
    else:
        sys_e = translator.EMIT_SYS
        user = (f"The agreed understanding:\n{understanding}\n\n"
                "Emit the ZFL.")
    raw = translator.strip_fences(
        call([{"role": "system", "content": sys_e},
              {"role": "user", "content": user}], model))
    try:
        return json.loads(raw), raw
    except Exception:
        return None, raw


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="qwen2.5:14b")
    ap.add_argument("-n", type=int, default=8, help="повторов на текст")
    ap.add_argument("--out", default=os.path.join(HERE,
                    "formalizer_stability_result.json"))
    ap.add_argument("--only", default="", help="прогнать один текст по имени")
    a = ap.parse_args()

    print("=== КОНТРОЛИ (без них число ничего не стоит) ===")
    ok_all = True
    for name, ok, note in controls():
        print(f"  [{'OK ' if ok else 'ПРОВАЛ'}] {name}\n         {note}")
        ok_all = ok_all and ok
    if not ok_all:
        print("\nКОНТРОЛЬ ПРОВАЛЕН — мера негодна, корпус НЕ гоню.")
        return 1
    print("  все контроли прошли\n")

    corpus = [c for c in CORPUS if not a.only or c[0] == a.only]
    results = {}
    t0 = time.time()
    for name, lang, note, text in corpus:
        strict, struct, bad = [], [], []
        for i in range(a.n):
            try:
                doc, raw = one_pass(text, a.model)
            except CallError as e:
                bad.append(f"вызов упал: {e}")
                continue
            if doc is None:
                bad.append(f"не JSON: {raw[:120]}")
                continue
            k = canon(doc)
            if k[0] == "BAD":
                bad.append(f"{k[1]}: {json.dumps(doc, ensure_ascii=False)[:120]}")
                continue
            strict.append(k[0])
            struct.append(k[1])
            print(f"  {name} {i+1}/{a.n} …", flush=True)
        results[name] = {"lang": lang, "note": note, "text": text,
                         "n": a.n, "ok": len(struct), "bad": bad,
                         "strict_distinct": len(set(strict)),
                         "struct_distinct": len(set(struct)),
                         "struct_keys": sorted(set(struct)),
                         "struct_all": struct}
        s = results[name]
        print(f"{name:20s} годных {s['ok']}/{a.n}  "
              f"структурно РАЗНЫХ {s['struct_distinct']}  "
              f"строго РАЗНЫХ {s['strict_distinct']}  "
              f"брак {len(bad)}")

    # ЭТИЧЕСКАЯ ПАРА — совпал ли канон у тяжёлого и лёгкого текста
    for pair in (("E1-armed-suspect", "E2-spoiled-cargo"),):
        if pair[0] in results and pair[1] in results:
            A = set(results[pair[0]]["struct_keys"])
            B = set(results[pair[1]]["struct_keys"])
            results["ЭТИЧЕСКАЯ-ПАРА"] = {
                "pair": list(pair), "общих канонов": len(A & B),
                "A": sorted(A), "B": sorted(B),
                "вывод": ("этическая разница В ФОРМУЛУ НЕ ПОПАДАЕТ"
                          if A & B else "формулы разошлись — см. ключи")}
            print(f"\nЭТИЧЕСКАЯ ПАРА {pair[0]} / {pair[1]}: "
                  f"общих канонов {len(A & B)}")

    results["_прогон"] = {"model": a.model, "n": a.n,
                          "temperature": TEMPERATURE,
                          "секунд": round(time.time() - t0, 1),
                          "путь": "understand -> emit, промты из translator.py"}
    with open(a.out, "w", encoding="utf-8") as f:
        json.dump(results, f, ensure_ascii=False, indent=1)
    print(f"\nзаписано: {a.out}  ({results['_прогон']['секунд']} с)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
