#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""stored — тёплая служба атом-стора. Держит модель в памяти, отвечает мгновенно.

ЗАЧЕМ, И ЭТО ПРОМЕРЕНО 2026-08-27, а не предположено:

    холодный запуск, как было:            16,9 с
    горячий процесс, с переранжировкой:    4,6 с
    горячий процесс, БЕЗ переранжировки:   0,01 с

Весь расход холодного старта — загрузка модели; весь расход горячего —
переранжировщик. Служба убирает первое и делает второе необязательным.

ПОЧЕМУ НЕ АВТОМАТОМ В ХУК. Куратор предложил подкладывать атомы к каждому его
сообщению. Замер на 60 его НАСТОЯЩИХ сообщений это отменил: оценка близости
ПЕРЕВЁРНУТА — «Поищи» получает 0,861, а «Берём спелеологов» 0,455. Короткое
слово похоже на всё. Связь длины с оценкой −0,08, с разрывом top1−top5 — 0,01.
Числом не отличить «стору есть что сказать» от «нечего». Поэтому спрашивает
человек, а служба лишь делает это дёшево.

    ./stored.py serve                 поднять (сокет ~/.cache/atomstore.sock)
    ./stored.py ask "вопрос" [-k 5] [--rerank] [--corpora BOOK ZTLDOC]
    ./stored.py selftest
"""
import argparse, json, os, pathlib, socket, sys, time

HERE = pathlib.Path(__file__).resolve().parent
SOCK = pathlib.Path(os.environ.get("ATOMSTORE_SOCK",
                                   pathlib.Path.home() / ".cache/atomstore.sock"))
STORE = pathlib.Path("/media/vitaly/SSD_1000GB/Projects/ztl-private/atomstore")
MODEL = "paraphrase-multilingual-MiniLM-L12-v2"
DEFAULT_CORPORA = ["BOOK", "ZTLDOC", "BLOG", "LEDGER", "ZTL", "VR", "LAW", "LAW3"]


def serve() -> int:
    sys.path.insert(0, str(HERE))
    import atomstore
    t0 = time.time()
    atomstore.retrieve(["BOOK"], "прогрев", STORE, k=1, model_name=MODEL, rerank=False)
    print(f"[stored] модель в памяти за {time.time()-t0:.1f} с", file=sys.stderr, flush=True)

    SOCK.parent.mkdir(parents=True, exist_ok=True)
    if SOCK.exists():
        SOCK.unlink()
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(str(SOCK)); srv.listen(8)
    os.chmod(SOCK, 0o600)          # сокет только для хозяина: корпус приватный
    print(f"[stored] слушаю {SOCK}", file=sys.stderr, flush=True)
    while True:
        conn, _ = srv.accept()
        try:
            data = b""
            while not data.endswith(b"\n"):
                part = conn.recv(65536)
                if not part: break
                data += part
            req = json.loads(data.decode("utf-8") or "{}")
            a = time.time()
            hits = atomstore.retrieve(req.get("corpora") or DEFAULT_CORPORA,
                                      req.get("question", ""), STORE,
                                      k=int(req.get("k", 5)), model_name=MODEL,
                                      rerank=bool(req.get("rerank", False)))
            out = {"ok": True, "sec": round(time.time() - a, 3),
                   "hits": [{"score": round(float(s), 4),
                             "src": d.get("src"), "corpus": d.get("corpus"),
                             "chunk": d.get("chunk"), "atom": d.get("atom", "")}
                            for s, d in hits]}
        except Exception as e:                     # служба НЕ падает от кривого запроса
            out = {"ok": False, "error": f"{type(e).__name__}: {e}"}
        try:
            conn.sendall((json.dumps(out, ensure_ascii=False) + "\n").encode("utf-8"))
        finally:
            conn.close()


def ask(question: str, k: int, rerank: bool, corpora: list) -> dict:
    if not SOCK.exists():
        return {"ok": False, "error": "служба не поднята: ./stored.py serve"}
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(60); s.connect(str(SOCK))
    s.sendall((json.dumps({"question": question, "k": k, "rerank": rerank,
                           "corpora": corpora or None}, ensure_ascii=False) + "\n").encode())
    buf = b""
    while not buf.endswith(b"\n"):
        part = s.recv(65536)
        if not part: break
        buf += part
    s.close()
    return json.loads(buf.decode("utf-8"))


def _selftest() -> int:
    ok = fail = 0
    def check(n, c):
        nonlocal ok, fail
        if c: ok += 1; print(f"  OK  {n}")
        else: fail += 1; print(f"  FAIL {n}")
    up = SOCK.exists()
    check("сокет на месте", up)
    if not up:
        print("\n  служба не поднята — подними: ./stored.py serve &"); return 1
    r = ask("что такое кредит", 3, False, [])
    check("служба ответила", r.get("ok") is True)
    check("атомы пришли", bool(r.get("hits")))
    check(f"быстро (было 16,9 с холодным): {r.get('sec')} с", (r.get("sec") or 99) < 0.5)
    bad = ask("", 3, False, ["НЕТ_ТАКОГО"])
    check("кривой запрос не роняет службу", isinstance(bad, dict))
    r2 = ask("что такое кредит", 3, False, [])
    check("служба жива после кривого", r2.get("ok") is True)
    print(f"\n  итог: {ok} OK, {fail} FAIL")
    return 1 if fail else 0


def main() -> int:
    ap = argparse.ArgumentParser(description="тёплая служба атом-стора")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("serve")
    pa = sub.add_parser("ask"); pa.add_argument("question")
    pa.add_argument("-k", type=int, default=5)
    pa.add_argument("--rerank", action="store_true", help="точнее, но ~4,5 с")
    pa.add_argument("--corpora", nargs="*", default=None)
    sub.add_parser("selftest")
    a = ap.parse_args()
    if a.cmd == "serve": return serve()
    if a.cmd == "selftest": return _selftest()
    r = ask(a.question, a.k, a.rerank, a.corpora)
    if not r.get("ok"):
        print("ошибка:", r.get("error"), file=sys.stderr); return 1
    print(f"({r['sec']} с)")
    for h in r["hits"]:
        head = h["atom"].strip().split("\n")[0]
        print(f"  [{h['score']:.3f}] {h['corpus']}:{h['src']}#{h['chunk']}")
        print(f"      {head[:150]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
