#!/usr/bin/env python3
"""Испытание УЗКОГО МОСТА (zfl2_gate) — заставы перед судьёй.

Заведено 2026-08-28, когда выяснилось, что мост построен, механически держит
инвариант G1 внешнего рецензента («внешняя посылка не входит в ядро следствия без объекта
допуска») — и при этом НЕ ИМЕЕТ НИ ТЕСТА, НИ ВЫЗОВА. Неподкреплённая застава
хуже отсутствующей: на неё ссылаются, а держит ли она — никто не знает.

КАЖДЫЙ УДАР ИДЁТ С КОНТРОЛЕМ. Ворота, которые понижают ВСЁ, прошли бы половину
проверок ниже, ничего не стерегая; поэтому первым делом проверяется, что
непричастную строку они НЕ трогают.
"""
from __future__ import annotations
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from admission import build_certificate                     # noqa: E402
from zfl2_gate import gate_document                          # noqa: E402

EP = "2026-08"
ATOMS = ["Порог памяти 64 ГиБ назван в разделе 3.", "Ниже порога прогон не годен."]


def row(name, kind, dim="evidence", status="verified"):
    return {"name": name, "means": name, "status": status,
            "ground": "src", "ground_kind": kind, "dimension": dim}


def cert_for(text):
    return build_certificate(text, "DOWNSTREAM", "ruleX", ATOMS,
                             "T", "retrieval", "multi@k=5", EP)


def main() -> int:
    ok = fail = 0

    def check(name, cond):
        nonlocal ok, fail
        print(f"  {'OK ' if cond else 'FAIL'} {name}")
        ok += bool(cond); fail += (not cond)

    def statuses(doc):
        return {r["name"]: r["status"] for r in doc["rows"]}

    # ── КОНТРОЛЬ: внутренняя строка (ground_kind=row) воротам не подсудна ──
    doc = {"claim": "A", "rows": [row("internal", "row")]}
    gated, dem = gate_document(doc, {}, "decision", EP, {"decision": ["ruleX"]})
    check("КОНТРОЛЬ: внутренняя строка НЕ понижена и не в списке",
          statuses(gated)["internal"] == "verified" and not dem)

    # ── УДАР 1: внешний источник без расписки → понижение, и оно НАЗВАНО ──
    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gated, dem = gate_document(doc, {}, "decision", EP, {"decision": ["ruleX"]})
    check("без расписки → понижено до unverified",
          statuses(gated)["ext"] == "unverified")
    check("понижение НЕ молчит: строка названа с причиной",
          len(dem) == 1 and "ext" in str(dem[0]) and len(str(dem[0])) > 20)

    # ── НАХОДКА 2026-08-28: РАЗЪЁМ СТОРОЖЕЙ НЕ ПОДАН ─────────────────────
    # zfl2_gate зовёт admit(cert, purpose, epoch, eligible) БЕЗ аргумента
    # conservation, а он у admission ОБЯЗАТЕЛЕН для допуска (admission.py:169,
    # ветка `if conservation is None` на 220). Значит застава сейчас НЕ
    # ПРОПУСКАЕТ НИЧЕГО: даже безупречная расписка кончается понижением с
    # причиной «guards.conserve_socket не подан».
    #
    # Это НЕ дыра: она падает ЗАКРЫТО и называет причину. Но это и не рабочий
    # мост — путь расписки пока мёртвый код. Тест закрепляет ПРАВДУ, а не
    # замысел: если разъём подадут, эта проверка упадёт и заставит переписать
    # её осознанно, вместо того чтобы перемена проехала молча.
    c = cert_for("ext")
    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gated, dem = gate_document(doc, {"ext": (c, c.cert_digest)},
                               "decision", EP, {"decision": ["ruleX"]})
    check("НАХОДКА: разъём сторожей не подан → даже годная расписка понижается",
          statuses(gated)["ext"] == "unverified" and len(dem) == 1)
    check("и причина названа честно (сторожа, а не расписка)",
          "сторож" in str(dem[0]) or "conserve" in str(dem[0]))

    # ── УДАР 3: подмена — расписка от ДРУГОГО предложения ──
    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gated, dem = gate_document(doc, {"ext": (c, "sha256:подделка")},
                               "decision", EP, {"decision": ["ruleX"]})
    check("расписка не сходится → понижено",
          statuses(gated)["ext"] == "unverified" and len(dem) == 1)

    # ── УДАР 4 (G3): ось ПРАВОМОЧИЯ не покрывается распиской о поддержке ──
    doc = {"claim": "A", "rows": [row("auth", "document", dim="authority")]}
    gated, dem = gate_document(doc, {"auth": (c, c.cert_digest)},
                               "decision", EP, {"decision": ["ruleX"]})
    check("G3: authority понижено ДАЖЕ с безупречной распиской",
          statuses(gated)["auth"] == "unverified" and len(dem) == 1)

    # ── РАЗЪЁМ ПОДАН 2026-08-28: теперь путь расписки ЖИВОЙ ────────────────
    # Раньше здесь стояла НАХОДКА о том, что застава не пропускает ничего.
    # Разъём подан, и находка снята — но снята ОСОЗНАННО, переписыванием
    # проверки, а не молча: вот три случая, покрывающие все ответы разъёма.
    from guards import CLEAR as G_CLEAR, NO_VERDICT as G_NO         # noqa: E402

    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gated, dem = gate_document(doc, {"ext": (c, c.cert_digest)},
                               "decision", EP, {"decision": ["ruleX"]},
                               {"ext": {"verdict": G_CLEAR, "ok": True}})
    check("CLEAR + годная расписка → ПРОПУЩЕНО (путь расписки жив)",
          statuses(gated)["ext"] == "verified" and not dem)

    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gated, dem = gate_document(doc, {"ext": (c, c.cert_digest)},
                               "decision", EP, {"decision": ["ruleX"]},
                               {"ext": {"verdict": "BLOCK", "ok": False,
                                        "disposition": "GUARD_NOT_PRESERVED",
                                        "reason": "сторож источника не доехал"}})
    check("BLOCK → понижено, и причина от СТОРОЖЕЙ, а не от расписки",
          statuses(gated)["ext"] == "unverified" and dem
          and "сторож" in str(dem[0]))

    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gated, dem = gate_document(doc, {"ext": (c, c.cert_digest)},
                               "decision", EP, {"decision": ["ruleX"]},
                               {"ext": {"verdict": G_NO, "ok": False,
                                        "reason": "разъём не сошёлся: судить не берёмся"}})
    check("NO_VERDICT → понижено: не сошёлся разъём, судить не беремся",
          statuses(gated)["ext"] == "unverified" and len(dem) == 1)

    # КОНТРОЛЬ ОБРАТНОЙ СОВМЕСТИМОСТИ: вердикт НЕ подан → по-прежнему ОТКАЗ.
    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gated, dem = gate_document(doc, {"ext": (c, c.cert_digest)},
                               "decision", EP, {"decision": ["ruleX"]})
    check("КОНТРОЛЬ: вердикт не подан → отказ, а не тихий проход",
          statuses(gated)["ext"] == "unverified" and len(dem) == 1)

    # ── УДАР 5: исходный документ НЕ ИСПОРЧЕН (ворота отдают копию) ──
    doc = {"claim": "A", "rows": [row("ext", "document")]}
    gate_document(doc, {}, "decision", EP, {"decision": ["ruleX"]})
    check("исходный документ не тронут — можно показать оба",
          doc["rows"][0]["status"] == "verified")

    print(f"\n  итог: {ok} OK, {fail} FAIL")
    if fail == 0:
        print("GATE GREEN — застава ПРОПУСКАЕТ по годной расписке при CLEAR "
              "от сторожей, и отказывает во всех прочих случаях: нет расписки, "
              "не сходится digest, BLOCK или NO_VERDICT от сторожей, вердикт "
              "не подан вовсе, ось правомочия. Исходник не портит, о каждом "
              "понижении сообщает вслух.")
    return 1 if fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
