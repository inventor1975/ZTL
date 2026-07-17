# -*- coding: utf-8 -*-
"""
ZTLStudio — a local studio: human <-> AI translator <-> ZFL <-> ZTL core.

Three stacked panels: meta-chat (negotiating the meaning), the ZFL
editor (hand-editable — a pro can bypass the AI), results (validator
errors + the core's answer).

Run: python3 tool/ztlstudio.py   -> http://localhost:8190
Zero cold start: no dependencies; the AI is optional (without a Groq
key the studio runs in pro mode).
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
import humanzfl               # noqa: E402


def _coerce(payload):
    """Accept EITHER a JSON ZFL document OR a human line
    (`a=F assert (d iff !c) impl …`). Returns (zfl_json_string, issues|None).
    A leading '{' means JSON (unchanged); anything else is the human surface
    syntax, parsed to the same document."""
    text = payload.get("zfl", "")
    t = (text or "").strip()
    if not t or t.startswith("{"):
        return text, None
    try:
        return json.dumps(humanzfl.human_to_doc(t), ensure_ascii=False), None
    except Exception as e:
        return None, [{"level": "error", "code": "E_HUMAN", "where": "input",
                       "hint": f"человеческий ZFL: {e}"}]
import engine                 # noqa: E402
import translator             # noqa: E402
import providers              # noqa: E402

PORT = int(os.environ.get("PORT", "8190"))   # copy: 8191 (live studio uses 8190); preview harness sets PORT

# --- public-instance hardening (server sets ZTLSTUDIO_PUBLIC=1) --------------
import time                                                     # noqa: E402
from collections import defaultdict, deque                      # noqa: E402
PUBLIC = os.environ.get("ZTLSTUDIO_PUBLIC") == "1"
_LLM_ROUTES = {"/api/chat", "/api/emit", "/api/explain", "/api/repair"}
_RL = defaultdict(deque)          # ip -> timestamps of free-AI calls
_RL_MAX, _RL_WINDOW = 20, 600     # ≤20 free-AI calls / 10 min / IP


def _client_ip(handler):
    """Real client IP behind the Apache reverse proxy (X-Forwarded-For)."""
    xff = handler.headers.get("X-Forwarded-For", "")
    return xff.split(",")[0].strip() if xff else handler.client_address[0]


def _rate_ok(ip):
    now = time.time()
    q = _RL[ip]
    while q and q[0] < now - _RL_WINDOW:
        q.popleft()
    if len(q) >= _RL_MAX:
        return False
    q.append(now)
    return True

EXAMPLES = [
    {"name": "Liar",
     "intent": "This sentence is false.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"L": "not(Tr(L))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Crocodile",
     "intent": "The crocodile returns the child if and only if the mother "
               "guesses what he will do. The mother: 'you will not return it'.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"R": "Tr(M)", "M": "not(Tr(R))"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Truth-teller",
     "intent": "This sentence is true.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"tau": "Tr(tau)"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Sensor",
     "intent": "An unverified sensor reports overheating; if overheating, "
               "the shutdown fires. Will it fire?",
     "zfl": "assert overheat impl shutdown"},
    {"name": "Modus ponens (Carroll's tortoise)",
     "intent": "The tortoise demands the rule itself be written as a "
               "premise: if (p implies q) and p, then q. True — but watch "
               "the completion table: it is a FRAME. A rule written down "
               "is certified, yet it moves nothing; a rule must be acted, "
               "not mailed.",
     "zfl": json.dumps({"genre": "statement",
                        "atoms": {"p": {"status": "Z"},
                                  "q": {"status": "Z"}},
                        "assert": "imp(and(imp(p,q),p),q)",
                        "ask": ["verdict", "warranty"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Russell",
     "intent": "The set of all sets not containing themselves: does it "
               "contain itself? Universe: a = empty, b = {b}, R.",
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
    text, herr = _coerce(payload)
    if herr:
        return {"ok": False, "issues": herr, "back_reading": None}
    doc, parsed, issues = zfl.validate(text)
    ok = parsed is not None
    br = zfl.back_reading(doc, parsed) if ok else None
    return {"ok": ok, "issues": issues, "back_reading": br}


def api_run(payload):
    text, herr = _coerce(payload)
    if herr:
        return {"ok": False, "issues": herr}
    doc, parsed, issues = zfl.validate(text)
    if parsed is None:
        return {"ok": False, "issues": issues}
    report = engine.run(doc, parsed)
    return {"ok": True, "issues": issues,
            "back_reading": zfl.back_reading(doc, parsed),
            "report": report}


def api_chat(payload):
    try:
        return {"ok": True, "reply": translator.understand(
            payload.get("history", []), payload.get("cfg"),
            payload.get("mode", "par"))}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_emit(payload):
    try:
        return {"ok": True, "zfl": translator.emit(
            payload.get("understanding", ""), payload.get("cfg"),
            payload.get("mode", "par"))}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_providers(payload):
    return {"ok": True, "providers": providers.available(), "public": PUBLIC}


def api_savekey(payload):
    """Persist a key into tool/.<provider>_key (gitignored). Optional
    convenience — the UI can also pass keys per request without saving."""
    if PUBLIC:
        return {"ok": False, "error": "saving is off on the public instance — "
                "a key you enter is used for this session only, never stored"}
    prov = payload.get("provider", "")
    key = (payload.get("key", "") or "").strip()
    if prov not in providers.PROVIDERS:
        return {"ok": False, "error": "unknown provider"}
    if not key:
        return {"ok": False, "error": "empty key"}
    path = os.path.join(HERE, providers.PROVIDERS[prov][4])
    with open(path, "w") as f:
        f.write(key)
    os.chmod(path, 0o600)
    return {"ok": True, "saved": prov}


def api_explain(payload):
    try:
        return {"ok": True, "reply": translator.explain(
            payload.get("zfl", ""), payload.get("back_reading", ""),
            payload.get("report", {}), payload.get("history", []),
            payload.get("lang_hint", ""), payload.get("cfg"))}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_repair(payload):
    """Bounded repair loop: up to 3 passes, each fed by the fresh
    validator output (errors AND warnings)."""
    text, herr = _coerce(payload)
    if herr:
        return {"ok": False, "error": herr[0]["hint"]}
    doc, parsed, issues = zfl.validate(text)
    if parsed is not None and not issues:
        return {"ok": True, "zfl": text, "note": "already valid"}
    try:
        cfg = payload.get("cfg")
        for attempt in range(3):
            text = translator.repair(text, issues, cfg)
            doc, parsed, issues = zfl.validate(text)
            if parsed is not None and not issues:
                return {"ok": True, "zfl": text,
                        "note": f"repaired in {attempt + 1} pass(es)"}
        return {"ok": True, "zfl": text,
                "note": "3 passes spent; issues may remain"}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_refute(payload):
    """Hypotheses mode: exhaustively check a claimed law (ZFL statement)
    over {T,F,Z}. Same shape as api_run so the front reuses the flow."""
    import refuter
    text, herr = _coerce(payload)
    if herr:
        return {"ok": False, "issues": herr}
    r = refuter.refute_zfl(text)
    if not r.get("ok"):
        return {"ok": False, "issues": r.get("issues", [])}
    doc, parsed, _ = zfl.validate(text)
    return {"ok": True, "issues": [],
            "back_reading": zfl.back_reading(doc, parsed),
            "result": r}


ROUTES = {"/api/validate": api_validate, "/api/run": api_run,
          "/api/chat": api_chat, "/api/emit": api_emit,
          "/api/repair": api_repair, "/api/explain": api_explain,
          "/api/providers": api_providers, "/api/savekey": api_savekey,
          "/api/refute": api_refute}


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
        if PUBLIC and self.path in _LLM_ROUTES and \
                not _rate_ok(_client_ip(self)):
            self._send(200, {"ok": False, "error":
                "free-AI limit reached (20 / 10 min per visitor). Enter your "
                "own key in ⚙ Model for unlimited use — it stays this session "
                "only. The core verdict never needs the AI."})
            return
        n = int(self.headers.get("Content-Length", 0))
        try:
            payload = json.loads(self.rfile.read(n).decode() or "{}")
        except json.JSONDecodeError:
            self._send(400, {"error": "bad json"})
            return
        try:
            self._send(200, fn(payload))
        except Exception as e:                      # never die on input
            self._send(200, {"ok": False, "issues": [{
                "level": "error", "code": "E_INTERNAL",
                "where": type(e).__name__,
                "hint": f"internal studio error: {e}"}]})


if __name__ == "__main__":
    print(f"ZTLStudio: http://localhost:{PORT}")
    if not translator.any_key():
        print("No provider key found — pro mode (hand-written ZFL), the "
              "AI is off. Add a key in Settings or drop it into "
              "tool/.<provider>_key.")
    if not PUBLIC:
        Timer(0.7, lambda: webbrowser.open(f"http://localhost:{PORT}")).start()
    HTTPServer(("127.0.0.1", PORT), Handler).serve_forever()
