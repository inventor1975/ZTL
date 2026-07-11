# -*- coding: utf-8 -*-
"""
ZTLStudio — локальная студия: человек ↔ ИИ-переводчик ↔ ZFL ↔ ядро ZTL.

Три окна: мета-чат (торг о смысле), ZFL-редактор (правится руками —
профи может миновать ИИ), результаты (ошибки валидатора + ответ ядра).

Запуск: python3 tool/ztlstudio.py   → http://localhost:8190
Zero cold start: без зависимостей, ИИ опционален (нет GROQ_API_KEY —
студия работает в режиме профи).
"""

import json
import os
import sys
import webbrowser
from http.server import HTTPServer, BaseHTTPRequestHandler
from threading import Timer

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import zfl                    # noqa: E402
import engine                 # noqa: E402
import translator             # noqa: E402

PORT = 8190

EXAMPLES = [
    {"name": "Лжец",
     "intent": "Это предложение ложно.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"L": "not(Tr(L))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Крокодил",
     "intent": "Крокодил вернёт ребёнка тогда и только тогда, когда мать "
               "угадает, что он сделает. Мать: «ты не вернёшь».",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"R": "Tr(M)", "M": "not(Tr(R))"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Правдолюб",
     "intent": "Это предложение истинно.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"tau": "Tr(tau)"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Датчик",
     "intent": "Непроверенный датчик показывает перегрев; если перегрев, "
               "то сработает защита. Сработает?",
     "zfl": json.dumps({"genre": "statement",
                        "atoms": {"overheat": {"status": "Z",
                                               "note": "датчик не поверен"},
                                  "shutdown": {"status": "Z",
                                               "note": "не наблюдалось"}},
                        "assert": "imp(overheat, shutdown)",
                        "ask": ["verdict", "warranty"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Рассел",
     "intent": "Множество всех множеств, не содержащих себя: содержит ли "
               "оно себя? Вселенная: a = ∅, b = {b}, R.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {
                            "a_in_a": "F", "a_in_b": "F",
                            "a_in_R": "not(Tr(a_in_a))",
                            "b_in_a": "F", "b_in_b": "T",
                            "b_in_R": "not(Tr(b_in_b))",
                            "R_in_a": "F", "R_in_b": "F",
                            "R_in_R": "not(Tr(R_in_R))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
]


def api_validate(payload):
    doc, parsed, issues = zfl.validate(payload.get("zfl", ""))
    ok = parsed is not None
    br = zfl.back_reading(doc, parsed) if ok else None
    return {"ok": ok, "issues": issues, "back_reading": br}


def api_run(payload):
    doc, parsed, issues = zfl.validate(payload.get("zfl", ""))
    if parsed is None:
        return {"ok": False, "issues": issues}
    report = engine.run(doc, parsed)
    return {"ok": True, "issues": issues,
            "back_reading": zfl.back_reading(doc, parsed),
            "report": report}


def api_chat(payload):
    try:
        return {"ok": True, "reply": translator.understand(
            payload.get("history", []))}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_emit(payload):
    try:
        return {"ok": True, "zfl": translator.emit(
            payload.get("understanding", ""))}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_repair(payload):
    doc, parsed, issues = zfl.validate(payload.get("zfl", ""))
    if parsed is not None:
        return {"ok": True, "zfl": payload.get("zfl", ""), "note": "уже валидно"}
    try:
        return {"ok": True, "zfl": translator.repair(
            payload.get("zfl", ""), issues)}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


ROUTES = {"/api/validate": api_validate, "/api/run": api_run,
          "/api/chat": api_chat, "/api/emit": api_emit,
          "/api/repair": api_repair}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="application/json; charset=utf-8"):
        data = body if isinstance(body, bytes) else \
            json.dumps(body, ensure_ascii=False).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            with open(os.path.join(HERE, "static", "index.html"), "rb") as f:
                self._send(200, f.read(), "text/html; charset=utf-8")
        elif self.path == "/api/examples":
            self._send(200, EXAMPLES)
        elif self.path.startswith("/static/"):
            name = os.path.basename(self.path)
            path = os.path.join(HERE, "static", name)
            if os.path.exists(path):
                ctype = ("text/css" if name.endswith(".css")
                         else "application/javascript")
                with open(path, "rb") as f:
                    self._send(200, f.read(), ctype + "; charset=utf-8")
            else:
                self._send(404, {"error": "not found"})
        else:
            self._send(404, {"error": "not found"})

    def do_POST(self):
        fn = ROUTES.get(self.path)
        if not fn:
            self._send(404, {"error": "not found"})
            return
        n = int(self.headers.get("Content-Length", 0))
        try:
            payload = json.loads(self.rfile.read(n).decode() or "{}")
        except json.JSONDecodeError:
            self._send(400, {"error": "bad json"})
            return
        try:
            self._send(200, fn(payload))
        except Exception as e:                      # никогда не умирать
            self._send(200, {"ok": False, "issues": [{
                "level": "error", "code": "E_INTERNAL",
                "where": type(e).__name__,
                "hint": f"внутренняя ошибка студии: {e}"}]})


if __name__ == "__main__":
    print(f"ZTLStudio: http://localhost:{PORT}")
    if not translator.get_key():
        print("Ключ Groq не найден (env GROQ_API_KEY или tool/.groq_key) — "
              "режим профи (ZFL руками), ИИ выключен.")
    Timer(0.7, lambda: webbrowser.open(f"http://localhost:{PORT}")).start()
    HTTPServer(("127.0.0.1", PORT), Handler).serve_forever()
