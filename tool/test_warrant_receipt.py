# -*- coding: utf-8 -*-
"""D2 — квитанция вердикта: что она связывает и на чём валится.

Наряд внешнего рецензента §13 D2. Стенд проверяет ровно те свойства, ради которых
квитанция и заводится: она переживает передачу, и любая подмена её роняет.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json
import zfl2
import warrant_receipt as wr

СДЕЛКА = {"claim": "deal_ok", "rows": [
    {"name": "rc", "means": "реестр перечитывают",
     "status": "unverified", "ground": ""},
    {"name": "pf", "means": "не в залоге", "status": "verified",
     "ground": "vypiska", "expires_on": "rc"},
    {"name": "po", "means": "документы в порядке", "status": "verified",
     "ground": "pts"},
    {"name": "deal_ok", "means": "сделку можно закрывать",
     "status": "defined", "ground": "Tr(pf) & Tr(po)"}]}

ЛЖЕЦ = {"claim": "L", "rows": [
    {"name": "L", "means": "это предложение ложно",
     "status": "defined", "ground": "~Tr(L)"}]}


def _rec(doc, epoch="epoch-A"):
    return wr.receipt(zfl2.run(doc), doc, epoch)


if __name__ == "__main__":
    print("=" * 72)
    print("D2. КВИТАНЦИЯ ВЕРДИКТА — наименьшая привязка через передачу")
    print("=" * 72)
    fails = 0

    def check(имя, ок):
        global fails
        fails += (not ок)
        print(f"   {'FAIL' if not ок else 'OK  '} {имя}")

    print("\n### 1. Квитанция сверяется сама с собой")
    r0 = _rec(СДЕЛКА)
    check("нетронутая квитанция проходит сверку", wr.verify(r0))
    check("отпечаток есть и он шестидесятичетырёхзначный",
          len(r0["digest"]) == 64)

    print("\n### 2. ЛЮБАЯ подмена роняет сверку — все пять полей")
    for поле, правка in (
            ("claim", lambda d: d.update(claim="что-то другое")),
            ("holding", lambda d: d["holding"].update(призрак="Z")),
            ("grounds", lambda d: d["grounds"].update(
                pf={"status": "verified", "ground": "ПОДДЕЛКА"})),
            ("verdict", lambda d: d["verdict"].update(value="F")),
            ("epoch", lambda d: d.update(epoch="epoch-Z")),
            ("expiry", lambda d: d["expiry"].clear())):
        порча = json.loads(json.dumps(r0))
        правка(порча)
        check(f"подмена поля {поле} валит сверку", not wr.verify(порча))

    print("\n### 3. Эпоха входит в отпечаток — переиспользовать нельзя молча")
    rA, rB = _rec(СДЕЛКА, "epoch-A"), _rec(СДЕЛКА, "epoch-B")
    check("одна разметка в разных эпохах — РАЗНЫЕ отпечатки",
          rA["digest"] != rB["digest"])

    print("\n### 4. Погашаемость едет вместе с вердиктом")
    rl = _rec(ЛЖЕЦ)
    check("лжец несёт UNREDEEMABLE", rl["verdict"]["credit"] == "UNREDEEMABLE")
    check("и называет имя", rl["verdict"]["unredeemable"] == ["L"])
    check("сделка несёт REDEEMABLE", r0["verdict"]["credit"] == "REDEEMABLE")

    print("\n### 5. События истечения едут вместе с основанием")
    check("основание pf помечено событием rc", r0["expiry"] == {"pf": "rc"})

    print("\n### 6. Одинаковый смысл — одинаковый отпечаток (канонизация)")
    переставлено = {"rows": list(reversed(СДЕЛКА["rows"])),
                    "claim": СДЕЛКА["claim"]}
    check("порядок строк не меняет отпечаток",
          _rec(переставлено)["digest"] == r0["digest"])

    print("\n### 7. ЧЕГО ЭТО НЕ УСТАНАВЛИВАЕТ")
    print("   Квитанция не подписывает (ключи — дело потребителя), не")
    print("   устанавливает истину источника (только что форсит разметка) и")
    print("   не переносит полномочие: предъявитель получает право ПРОВЕРИТЬ,")
    print("   а не право действовать.")

    if fails:
        raise SystemExit(f"D2 RED: {fails} расхождений")
    print("\n" + "=" * 72)
    print("WARRANT RECEIPT GREEN — вердикт переживает передачу и")
    print("проверяется на той стороне, а не пересказывается.")
