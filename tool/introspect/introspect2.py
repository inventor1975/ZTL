#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""introspect2 — тетрадь ПО ОБРАЗЦУ СТУДИИ: модель предлагает, ЯДРО судит.

ЗАЧЕМ ВТОРОЙ ФАЙЛ, а не правка первого. Куратор 2026-08-27: «тот интроспект,
что есть, — вообще не то, что я задумывал». И это промерено, а не вкус:
старый `introspect.py` ядро НЕ ЗОВЁТ ВООБЩЕ. Метку ставит форк, наш код лишь
считает метки регуляркой. Студия устроена наоборот — вердикт считает `zfl2`,
и в ней прямым текстом: «the core verdict never needs the AI».

  СТУДИЯ:      ИИ предлагает — КОД решает.
  СТАРАЯ ТЕТРАДЬ: ИИ решает — код считает.
  ЭТОТ ФАЙЛ:   как студия.

ЧТО ДЕЛАЕТ МОДЕЛЬ И ЧТО ДЕЛАЕТ ЯДРО — граница проведена нарочно.

Модель переводит файл в СТРОКИ документа ZFL2: имя, что значит, статус,
основание. Больше ничего. Она не выносит вердикт и не ставит ценностных меток.

Ядро (`zfl2.run`) проверяет документ, вычисляет ЖАНР (какие приборы включаются)
и выдаёт паспорт: какие входы непроверены и — поимённо — ЧЬЯ ВИНА в том, что
составное не стоит (`culprits`). Это и есть вердикт, и он воспроизводим без
модели: те же строки дадут тот же ответ завтра и у другого.

ЧЕГО ЗДЕСЬ НЕТ И ПОЧЕМУ. Ценностной оси (соблазна) в этом файле нет. Шаг
второй по слову куратора: «пошагово». Сперва логический слой, который можно
прогнать и проверить, потом верхний.

ПРЕДЕЛ, НАЗВАННЫЙ ЗАРАНЕЕ. Ядро судит СОСТАВНОЕ, а не атомарное: разметку
атомов объявляет модель, ядро её переносит. Выигрыш не в том, что атом стал
проверенным, а в том, что вердикт перестал быть мнением и что противоречивая
разметка теперь ЛОВИТСЯ валидатором, а не проходит молча.

    ./introspect2.py prepare <файл.py>     задача форку: перевести в строки
    ./introspect2.py judge <rows.json>     ядро судит; печатает паспорт
    ./introspect2.py selftest              инварианты ПРОГОНОМ
"""
import argparse, json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))          # ZTL/tool — там zfl2
import zfl2                                    # noqa: E402

STATUSES = ("verified", "refuted", "unverified", "defined")

# Наказ форку. Он НЕ просит ни вердикта, ни метки — только перевод в строки.
# Словарь статусов взят не из головы: валидатор zfl2 сам его назвал, когда
# первая проба ошиблась (E_STATUS), и там же оговорка про основание (E_NOGROUND).
RUBRIC = """Ты переводишь ИСХОДНЫЙ КОД в строки документа ZFL2. Ты НЕ выносишь
вердикт и НЕ ставишь ценностных меток — это сделает ядро.

Разложи файл на АТОМЫ: допущения, на которых он держится (что функция ожидает
от входа, что гарантирует на выходе, какой инвариант предполагает про
состояние или внешние данные). Затем — составные утверждения, которые из этих
атомов складываются («обращение безопасно», «результат в границах»).

Каждый атом — одна строка со ЧЕТЫРЬМЯ полями:

  name    короткое имя латиницей, без пробелов (p, idx_ok, buf_nonempty)
  means   что это значит по-русски, одной фразой
  status  РОВНО одно из: verified, refuted, unverified, defined
  ground  чем подтверждено

ПРАВИЛА СТАТУСА, они жёсткие:

  verified   — код это ПРОВЕРЯЕТ сам (есть assert, есть if, есть тип). В
               ground назови СВИДЕТЕЛЯ, и это ОДНО СЛОВО без пробелов — имя
               того, чем подтверждено: assert-in-main, line-18, by-assumption.
               Не фраза и не пересказ: ядро отвергает основание с пробелами
               (E_GROUND_SPACES), потому что основание ИМЕНУЕТ документ, а
               пробел разрезал бы имя пополам. Назвать нечем — ставь
               unverified, а не verified.
  refuted    — код это нарушает, и видно где.
  unverified — допущение, которое код НЕ проверяет. ground не нужен.
  defined    — составное: определяется через другие имена. В ground —
               ФОРМУЛА над именами: p & q, p | q, ~p, p -> q.

Верни ТОЛЬКО JSON, без пояснений:

{"rows": [{"name": "...", "means": "...", "status": "...", "ground": "..."}]}

Файл: {name}

```python
{code}
```"""


def prepare(target: pathlib.Path, out: pathlib.Path) -> pathlib.Path:
    """Положить задачу форку. Ключей не трогаем — судит форк или я сам."""
    code = target.read_text(encoding="utf-8")
    task = RUBRIC.replace("{name}", target.name).replace("{code}", code)
    out.write_text(task, encoding="utf-8")
    return out


def judge(doc: dict) -> dict:
    """Ядро судит. Ничего своего не добавляем — ответ zfl2 как есть, плюс
    выжимка виновников, потому что именно она и нужна тетради."""
    res = zfl2.run(doc)
    culprits = {}
    for item in (res.get("report", {}) or {}).get("passport", []) or []:
        for c in item.get("component", []):
            named = _culprits_of(item)
            if named:
                culprits[c] = named
    res["culprits"] = culprits
    return res


def _culprits_of(item: dict) -> list:
    """Достать имена виновных из строки паспорта. Формат detail задаёт ядро,
    поэтому читаем его аккуратно и не падаем, если он изменится."""
    d = item.get("detail") or ""
    if "culprits" not in d:
        return []
    try:
        frag = d.split("culprits", 1)[1]
        frag = frag[frag.index("["): frag.index("]") + 1]
        return [s.strip(" '\"") for s in frag.strip("[]").split(",") if s.strip()]
    except (ValueError, IndexError):
        return []


def render(res: dict) -> str:
    out = []
    if not res.get("ok"):
        out.append("ДОКУМЕНТ НЕ ПРОШЁЛ ПРОВЕРКУ — вердикта нет:")
        for i in res.get("issues", []):
            out.append(f"  [{i.get('code')}] {i.get('where')}: {i.get('hint')}")
        return "\n".join(out)
    ap = res.get("applies", {})
    out.append("включились приборы: " + (", ".join(k for k, v in ap.items() if v) or "—"))
    for item in (res.get("report", {}) or {}).get("passport", []) or []:
        comp = ", ".join(item.get("component", []))
        out.append(f"  {comp:16s} {item.get('kind',''):10s} {item.get('detail','')}")
    if res.get("culprits"):
        out.append("\nВИНОВНИКИ, названные ЯДРОМ (не моделью):")
        for who, why in res["culprits"].items():
            out.append(f"  {who} не стоит из-за: {', '.join(why)}")
    return "\n".join(out)



# ═══════════════════════════════════════════════════════════════════════
# СЛОЙ ВТОРОЙ — ЧТО ИЗ СОБЛАЗНА ВЫЧИСЛЯЕТСЯ, А ЧТО НЕТ
#
# Куратор: соблазн — это два пути из лабиринта, оба истинных, но один
# короткий, другой длинный. В логике это уже промерено: zderive (E26) даёт
# ЗАСЛУЖЕНО / В КРЕДИТ / СНАРУЖИ, и «в кредит» значит «верно, но всякий путь
# обязан занять».
#
# Здесь тот же вопрос над файлом, и он распадается надвое.
#
# ВЫЧИСЛИМОЕ: НАСКОЛЬКО ДАЛЕКО заявка стоит от непроверенного, на котором
# держится. Глубина 1 — дыра прямо под ногами, её видно. Глубина 3 — надо
# пройти три звена, чтобы её найти, и в точке употребления заявка выглядит
# твёрдой. Считается по цепи виновников, которую выдало ЯДРО.
#
# Берётся МИНИМУМ по путям нарочно: если хоть один короткий путь обнажает
# дыру, она видна, и заявка не прячет ничего. Нож — там, где КАЖДЫЙ путь длинный.
#
# НЕВЫЧИСЛИМОЕ: употребляется ли эта дистанция во вред. Ни ядро, ни этот файл
# такого не решают. Поэтому здесь НЕТ метки S: есть число и есть основание для
# суждения, а суждение выносит человек — и выносит отдельно, своей подписью.
#
# Так честнее, чем сегодняшняя метка S, где счёт и мнение слиты в один знак и
# не видно, где кончается одно.

def weigh(doc: dict, res: dict) -> dict:
    """Глубина от каждой заявки до непроверенного основания.

    -1 означает «непроверенного под этим нет вовсе» — заявка заземлена.
    """
    status = {r.get("name"): r.get("status") for r in doc.get("rows", [])}
    cul = res.get("culprits", {})

    def depth(name, seen=frozenset()):
        if name in seen:
            return -1                        # круг: дальше не идём
        if status.get(name) == "unverified":
            return 0
        kids = cul.get(name) or []
        if not kids:
            return -1
        below = [depth(k, seen | {name}) for k in kids]
        below = [d for d in below if d >= 0]
        return 1 + min(below) if below else -1

    out = {n: depth(n) for n in cul}
    return {"depth": out,
            "deepest": sorted((d, n) for n, d in out.items() if d >= 0)[-1:] or None}


def render_weigh(w: dict) -> str:
    d = w["depth"]
    if not d:
        return "второй слой: цепей нет — нечего взвешивать"
    out = ["ГЛУБИНА ДО НЕПРОВЕРЕННОГО (вычислено по цепи ядра):"]
    for n, v in sorted(d.items(), key=lambda kv: -kv[1]):
        note = "заземлено" if v < 0 else ("дыра прямо под заявкой" if v <= 1 else
                                          f"дыра в {v} звеньях — в точке употребления не видна")
        out.append(f"  {n:26s} {v:>2}  {note}")
    out.append("")
    out.append("ЭТО НЕ МЕТКА СОБЛАЗНА. Это одно его СЧИТАЕМОЕ слагаемое — "
               "далеко ли заявка от своей дыры.")
    out.append("Употребляется ли расстояние во вред — не считает ни ядро, ни этот "
               "файл. Судит человек, отдельно и своей подписью.")
    return "\n".join(out)

def _selftest() -> int:
    """Инварианты ПРОГОНОМ, а не чтением. Заведены сразу, с первой строки:
    у guards.py самопроверки нет, и 2026-08-26 это стоило нам ложного
    'прибор молчит — наверное сломан'."""
    ok = fail = 0

    def check(name, cond):
        nonlocal ok, fail
        if cond: ok += 1; print(f"  OK  {name}")
        else:    fail += 1; print(f"  FAIL {name}")

    # 1. Живой случай: непроверенный вход валит составное, и ядро называет его.
    doc = {"rows": [
        {"name": "p", "means": "вход непустой", "status": "verified", "ground": "by-assumption"},
        {"name": "q", "means": "индекс в границах", "status": "unverified"},
        {"name": "safe", "means": "обращение безопасно", "status": "defined", "ground": "p & q"},
    ]}
    r = judge(doc)
    check("годный документ проходит", r.get("ok") is True)
    check("жанр ВЫЧИСЛЕН: включился паспорт", r.get("applies", {}).get("passport") is True)
    check("ядро назвало виновника q у safe", r["culprits"].get("safe") == ["q"])

    # 2. Мусор от модели ловится ВАЛИДАТОРОМ, а не проходит молча.
    bad = {"rows": [{"name": "p", "means": "x", "status": "T"}]}
    rb = judge(bad)
    check("чужой статус отвергнут", rb.get("ok") is False
          and any(i.get("code") == "E_STATUS" for i in rb.get("issues", [])))

    # 3. verified без основания не проходит — иначе «проверено» ничего не значит.
    ng = {"rows": [{"name": "p", "means": "x", "status": "verified"}]}
    rn = judge(ng)
    check("verified без основания отвергнут", rn.get("ok") is False)

    # 4. Всё проверено — виновных нет.
    clean = {"rows": [
        {"name": "p", "means": "a", "status": "verified", "ground": "by-assumption"},
        {"name": "q", "means": "b", "status": "verified", "ground": "by-assumption"},
        {"name": "safe", "means": "c", "status": "defined", "ground": "p & q"},
    ]}
    rc = judge(clean)
    check("при полном грунте виновных нет", rc.get("ok") and not rc.get("culprits"))

    # ── второй слой ────────────────────────────────────────────────────
    # Лестница: conc стоит на mid, mid на base, base непроверен. Глубина
    # до дыры от conc должна быть 2, от mid — 1. Это и есть «дыру видно»
    # против «дыра в двух звеньях».
    lad = {"rows": [
        {"name": "base", "means": "нижнее допущение", "status": "unverified"},
        {"name": "mid",  "means": "среднее", "status": "defined", "ground": "base"},
        {"name": "conc", "means": "вывод", "status": "defined", "ground": "mid"},
    ]}
    rl = judge(lad)
    w = weigh(lad, rl)
    check("лестница принята ядром", rl.get("ok") is True)
    check("глубина от вывода = 2", w["depth"].get("conc") == 2)
    check("глубина от среднего = 1", w["depth"].get("mid") == 1)

    # Заземлённое не должно получать глубину: под ним нет непроверенного.
    wc = weigh(clean, rc)
    check("под заземлённым дыры нет", all(v < 0 for v in wc["depth"].values())
          or not wc["depth"])

    print(f"\n  итог: {ok} OK, {fail} FAIL")
    return 1 if fail else 0


def main() -> int:
    ap = argparse.ArgumentParser(description="тетрадь-2: модель предлагает, ядро судит")
    sub = ap.add_subparsers(dest="cmd", required=True)
    pp = sub.add_parser("prepare", help="задача форку: перевести файл в строки ZFL2")
    pp.add_argument("target"); pp.add_argument("--out", default=None)
    pj = sub.add_parser("judge", help="ядро судит строки, вернувшиеся от форка")
    pj.add_argument("rows", help="файл JSON с {\"rows\": [...]}")
    pj.add_argument("--weigh", action="store_true",
                    help="второй слой: глубина до непроверенного основания")
    sub.add_parser("selftest", help="инварианты прогоном")
    a = ap.parse_args()
    if a.cmd == "selftest":
        return _selftest()
    if a.cmd == "prepare":
        t = pathlib.Path(a.target)
        out = pathlib.Path(a.out) if a.out else t.with_suffix(t.suffix + ".task.md")
        print(f"задача -> {prepare(t, out)}", file=sys.stderr)
        return 0
    doc = json.loads(pathlib.Path(a.rows).read_text(encoding="utf-8"))
    res = judge(doc)
    print(render(res))
    if a.weigh and res.get("ok"):
        print()
        print(render_weigh(weigh(doc, res)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
