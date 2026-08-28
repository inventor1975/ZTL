#!/usr/bin/env python3
"""Прогон VECTORS.json против НАШЕЙ реализации.

Векторы — договор, а не тест: они описывают ФАКТЫ о входе и ТРЕБУЕМЫЙ исход, не
трогая устройство объектов. Этот файл — переходник от договора к нашим объектам.
Чужая реализация пишет свой переходник и сдаёт ТОТ ЖЕ файл; тогда расхождение
видно прогоном, а не спором о том, кто что имел в виду.

Правило: если наш прогон разошёлся с вектором, виноват НЕ вектор по умолчанию.
Сперва смотреть, не изменилось ли поведение, и только потом править ожидание —
осознанно и с записью почему.
"""
from __future__ import annotations
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import admission as A                                        # noqa: E402
from zfl2_gate import gate_document                          # noqa: E402

HERE = pathlib.Path(__file__).resolve().parent
EP, OTHER_EP = "2026-08", "2026-07"
PURPOSE = "decision"
ELIG = {PURPOSE: ["ruleX"]}
ATOMS = ["Порог назван в разделе 3.", "Ниже порога прогон не годен."]

SUPPORT = {"SUPPORTED_BY_SOURCE": A.SUPPORTED, "NO_SUPPORT_FOUND": A.NO_SUPPORT,
           "SOURCE_SILENT": A.SOURCE_SILENT, "CONTRADICTED_BY_SOURCE": A.CONTRADICTED}
GUARDS = {"CLEAR": {"verdict": "CLEAR"},
          "GUARD_LOST": {"verdict": "GUARD_LOST", "reason": "сторож источника не доехал"}}


def cert(prop="P", support="SUPPORTED_BY_SOURCE", epoch=EP, attributed=""):
    c = A.build_certificate(prop, "DOWNSTREAM", "ruleX", ATOMS, "T", "retrieval",
                            "multi@k=5", epoch, attributed_to=attributed)
    return dataclass_with(c, support)


def dataclass_with(c, support_name):
    import dataclasses
    if SUPPORT[support_name] == c.support_relation:
        return c
    return dataclasses.replace(c, support_relation=SUPPORT[support_name])


def run_case(v):
    g = v["given"]
    if g.get("verify_only"):
        c = cert()
        claimed = "sha256:подделка" if g["proposition_bytes_changed"] else c.cert_digest
        return {"verifies": A.verify_certificate(c, claimed)}
    if g.get("conflict_of"):
        ds = [A.admit(cert(p), PURPOSE, EP, ELIG, conservation=GUARDS["CLEAR"])
              for p in g["conflict_of"]]
        d = A.resolve_conflict(ds)
        return {"admitted": d.admitted, "disposition": d.disposition}
    c = cert(support=g["support"],
             epoch=EP if g["epoch_matches"] else OTHER_EP,
             attributed="S2" if g.get("attributed_to_other_source") else "")
    elig = ELIG if g["eligible_for_purpose"] else {PURPOSE: []}
    cons = GUARDS.get(g["guards"]) if g["guards"] else None
    d = A.admit(c, PURPOSE, EP, elig, conservation=cons)
    return {"admitted": d.admitted, "disposition": d.disposition}


def run_gate_case(v):
    g = v["given"]
    row = {"name": "r", "means": "r", "status": g["status"], "ground": "src",
           "ground_kind": g["ground_kind"], "dimension": g.get("dimension", "evidence")}
    doc = {"claim": "A", "rows": [row]}
    receipts = {}
    if g.get("receipt") == "valid":
        c = cert(); receipts = {"r": (c, c.cert_digest)}
    elif g.get("receipt") == "wrong_digest":
        c = cert(); receipts = {"r": (c, "sha256:подделка")}
    gv = g.get("guard_verdict")
    cons = None
    if gv == "CLEAR":
        cons = {"ext": None}  # заполним ниже под настоящее имя строки
        cons = {"r": {"verdict": "CLEAR", "ok": True}}
    elif gv == "BLOCK":
        cons = {"r": {"verdict": "BLOCK", "ok": False,
                      "disposition": "GUARD_NOT_PRESERVED",
                      "reason": "сторож источника не доехал"}}
    gated, dem = gate_document(doc, receipts, PURPOSE, EP, ELIG, cons)
    got = {"status_after": gated["rows"][0]["status"], "demoted": bool(dem),
           "original_unchanged": doc["rows"][0]["status"] == g["status"]}
    if dem:
        got["reason_named"] = len(str(dem[0].get("reason", ""))) > 20
        got["reason_mentions_guards"] = ("сторож" in str(dem[0]) or "conserve" in str(dem[0]))
    return got


def main() -> int:
    data = json.loads((HERE / "VECTORS.json").read_text())
    ok = fail = 0
    for section, runner in (("cases", run_case), ("gate_cases", run_gate_case)):
        print(f"\n### {section}")
        for v in data[section]:
            try:
                got = runner(v)
            except Exception as e:                     # прогон упал — это провал
                print(f"  FAIL {v['id']}: {type(e).__name__}: {e}")
                fail += 1
                continue
            bad = []
            for k, want in v["expect"].items():
                if got.get(k) != want:
                    bad.append(f"{k}: ждали {want!r}, вышло {got.get(k)!r}")
            if bad:
                print(f"  FAIL {v['id']} — " + "; ".join(bad)); fail += 1
            else:
                print(f"  OK   {v['id']}"); ok += 1
    print(f"\n  итог: {ok} OK, {fail} FAIL")
    if fail == 0:
        print("VECTORS GREEN — наша реализация сдаёт собственный договор.")
    return 1 if fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
