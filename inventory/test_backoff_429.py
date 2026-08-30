# -*- coding: utf-8 -*-
"""Поведение студии на 429 — на ПОДДЕЛЬНОМ провайдере, без живого ключа.

ЗАЧЕМ. Ключ NVIDIA у сервера и у меня один (промерено 2026-08-31), поэтому
каждый замер против настоящего каталога отнимает лимит у посетителей
публичной студии. Значит мерить наш откат надо на своём стенде: поднимаем
локальный сервер, который ведёт себя как каталог — отбивает 429, когда
запросы идут слишком плотно, и НЕ шлёт Retry-After (настоящий не шлёт).

ЧТО ПОКАЗЫВАЕТ СТЕНД
  1. КОНТРОЛЬ: одиночный запрос проходит — значит стенд не сломан.
  2. Всплеск из двух запросов ловит 429 — значит стенд воспроизводит беду.
  3. Сколько РЕАЛЬНОГО времени наш `_post` тратит на один 429.

Ожидание до запуска: пункт 3 даст около 15 с, потому что первая ступень
отката — `time.sleep(15)`. Если выйдет иначе — читать код, а не отчёт.
"""
import os, sys, json, time, threading
from http.server import BaseHTTPRequestHandler, HTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "tool"))
import providers                                              # noqa: E402

GAP = 2.0            # плотнее этого — отбиваем, как каталог отбивает всплеск
_last = [0.0]
_hits = {"429": 0, "ok": 0}


class Fake(BaseHTTPRequestHandler):
    def log_message(self, *a):        # тишина в отчёте
        pass

    def do_POST(self):
        now = time.time()
        if now - _last[0] < GAP:
            _hits["429"] += 1
            self.send_response(429)   # БЕЗ Retry-After — как настоящий
            self.end_headers()
            self.wfile.write(b'{"error":"rate limit"}')
            return
        _last[0] = now
        _hits["ok"] += 1
        body = json.dumps({"choices": [{"message": {"content": "ok"}}],
                           "usage": {"completion_tokens": 1}}).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main():
    srv = HTTPServer(("127.0.0.1", 0), Fake)
    port = srv.server_address[1]
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    url = f"http://127.0.0.1:{port}/v1/chat/completions"
    body = {"model": "x", "messages": [{"role": "user", "content": "hi"}]}
    hdr = {"Authorization": "Bearer test", "Content-Type": "application/json"}
    fails = []

    t0 = time.time()
    providers._post(url, dict(body), hdr)
    solo = time.time() - t0
    print(f"1. КОНТРОЛЬ — одиночный запрос: прошёл за {solo:.2f} с")
    if solo > 1.0:
        fails.append("одиночный запрос уже медленный — стенд не годится")

    before = _hits["429"]
    t0 = time.time()
    providers._post(url, dict(body), hdr)      # сразу вторым — попадёт в 429
    burst = time.time() - t0
    got = _hits["429"] - before
    print(f"2. ВСПЛЕСК — второй запрос подряд: {got} отбитие(й) 429")
    if got == 0:
        fails.append("стенд не отбил всплеск — беда не воспроизведена")

    print(f"3. ЦЕНА ОДНОГО 429: {burst:.1f} с реального ожидания")
    if got and burst < 10:
        fails.append(f"откат оказался короче ожидаемых ~15 с ({burst:.1f} с)")

    srv.shutdown()
    print()
    if fails:
        print("СТЕНД КРАСНЫЙ:")
        for f in fails:
            print("  -", f)
        return 1
    print("СТЕНД ЗЕЛЁНЫЙ — беда воспроизводится БЕЗ живого ключа.")
    print(f"Один 429 стоит посетителю {burst:.0f} с; три подряд — до 90 с,")
    print("после чего отказ, потому что запасному провайдеру некуда падать.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
