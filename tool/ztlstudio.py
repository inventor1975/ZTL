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
import re
import sys
import webbrowser
import threading
import traceback
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
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
_LLM_ROUTES = {"/api/chat", "/api/emit", "/api/explain", "/api/repair",
               "/api/v2fill", "/api/v2comment"}
_RL = defaultdict(deque)          # ip -> timestamps of free-AI calls
_RL_LOCK = threading.Lock()       # the server is threaded; the deque is not
_RL_MAX, _RL_WINDOW = 20, 600     # ≤20 free-AI calls / 10 min / IP


def _client_ip(handler):
    """Real client IP behind the Apache reverse proxy (X-Forwarded-For)."""
    xff = handler.headers.get("X-Forwarded-For", "")
    return xff.split(",")[0].strip() if xff else handler.client_address[0]


def _rate_ok(ip):
    with _RL_LOCK:
        now = time.time()
        q = _RL[ip]
        while q and q[0] < now - _RL_WINDOW:
            q.popleft()
        if len(q) >= _RL_MAX:
            return False
        q.append(now)
        return True

EXAMPLES = [
    # ------------------------------------------------ the docket: convicted
    {"name": "Liar",
     "intent": "This sentence is false.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"L": "not(Tr(L))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Barber (the liar in a barber's apron)",
     "intent": "The barber shaves exactly those who do not shave "
               "themselves. Does he shave himself?",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"shaves": "not(Tr(shaves))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Grelling's 'heterological'",
     "intent": "'Heterological' means 'not applying to itself'. Is "
               "'heterological' heterological?",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"het": "not(Tr(het))"},
                        "ask": ["passport"]},
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
    {"name": "Jourdain's postcard",
     "intent": "Front of the card: 'the sentence on the back is true'. "
               "Back: 'the sentence on the front is false'. Note the "
               "oscillation period: 4, not the liar's 2.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"front": "Tr(back)",
                                      "back": "not(Tr(front))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Crocodile",
     "intent": "The crocodile returns the child if and only if the mother "
               "guesses what he will do. The mother: 'you will not return "
               "it'. Same shape as Jourdain's postcard — and the deal "
               "itself never earns truth: the contract is void.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"R": "Tr(M)", "M": "not(Tr(R))"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Odd 3-cycle",
     "intent": "Three sentences in a ring, each denying the next: odd "
               "parity, no consistent solution. Vicious is the parity, "
               "not the circle.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"a": "not(Tr(b))",
                                      "b": "not(Tr(c))",
                                      "c": "not(Tr(a))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Curry (grounded falsum)",
     "intent": "'If this sentence is true, then falsehood.' With a real, "
               "grounded falsum Curry IS the liar in an arrow costume.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"g": "imp(Tr(g), F)"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    # --------------------------------------------- the docket: conditional
    {"name": "Curry (suspended falsum)",
     "intent": "The same Curry, but its 'falsum' is defined over an "
               "unsettled base: the refusal is INHERITED, and the culprit "
               "is named. Curry's passport depends on what feeds the arrow.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"gamma": "imp(Tr(gamma), Tr(bot))",
                                      "bot": "and(Tr(s), not(Tr(s)))",
                                      "s": "Tr(s)"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    # ------------------------------------------- the docket: forced verdict
    {"name": "Strong liar (forced FALSE)",
     "intent": "'This sentence is false AND this sentence is true.' "
               "Intuition says: worse than the liar. Measurement says: "
               "tamer — exactly one consistent solution, forced false.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"sigma":
                                      "and(not(Tr(sigma)), Tr(sigma))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Revenge / avenger (forced FALSE)",
     "intent": "'This sentence is not equivalent to itself.' One "
               "consistent solution: forced false. (The validator will "
               "flag the degenerate xnor(mu,mu) — that degeneracy IS the "
               "sentence.)",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"mu": "not(xnor(Tr(mu), Tr(mu)))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Henkin-style sentence (forced TRUE)",
     "intent": "'If this sentence is true, then this sentence is true.' "
               "The strong liar's mirror: one solution, forced TRUE.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"h": "imp(Tr(h), Tr(h))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    # ----------------------------------------------- the docket: acquitted
    {"name": "Truth-teller",
     "intent": "This sentence is true.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"tau": "Tr(tau)"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Russell's twin S∈S",
     "intent": "The set of all sets that DO contain themselves: does it "
               "contain itself? The truth-teller of set theory — two "
               "honest answers, choose by decree. Type theory bans this "
               "curable twin together with the incurable R.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"S_in_S": "Tr(S_in_S)"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Crocodile control (optimistic mother)",
     "intent": "Flip the mother's prediction to 'you WILL return it': one "
               "negation vanishes, parity flips, the sentence becomes a "
               "blank. Note WHO fills it: the deal binds nobody — the "
               "crocodile does as he pleases in both solutions.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"R": "Tr(M)", "M": "Tr(R)"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Even 2-cycle",
     "intent": "Two sentences denying each other: even parity, two lawful "
               "solutions, stipulate either.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"A": "not(Tr(B))", "B": "not(Tr(A))"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Even 4-cycle",
     "intent": "Four negations around the ring: still even, still a blank.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"a": "not(Tr(b))", "b": "not(Tr(c))",
                                      "c": "not(Tr(d))", "d": "not(Tr(a))"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Yablo (truncated at 3)",
     "intent": "An infinite queue, each sentence saying 'everyone after "
               "me lies'. EVERY finite truncation is grounded — no "
               "quarantine at all: the paradoxicality lives only in the "
               "actual infinity. Extend the queue and see for yourself.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"s0": "and(not(Tr(s1)), not(Tr(s2)))",
                                      "s1": "not(Tr(s2))",
                                      "s2": "T"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    # ------------------------------------- the contingent liar: three worlds
    {"name": "Contingent liar — world A (harmless)",
     "intent": "Smith: 'what Jones said is false.' Jones happened to say "
               "a truth about grass. Smith's sentence is plain false — "
               "everything grounded, case closed.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"S": "not(Tr(J))",
                                      "J": "Tr(g)", "g": "T"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Contingent liar — world B (unlucky)",
     "intent": "Same Smith sentence — but Jones happened to say 'Smith "
               "speaks truly'. Two honest people close Jourdain's "
               "carousel without knowing it. A paradox is an event, not "
               "a text (Kripke).",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"S": "not(Tr(J))", "J": "Tr(S)"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Contingent liar — world C (unverified)",
     "intent": "Same Smith sentence; what Jones said is not yet verified. "
               "The refusal is CONDITIONAL, and the culprit is named: "
               "verify Jones and the case resolves either way.",
     "zfl": json.dumps({"genre": "system",
                        "atoms": {"J": {"status": "Z",
                                        "means": "what Jones said is true"}},
                        "sentences": {"S": "not(Tr(J))"},
                        "ask": ["passport"]},
                       ensure_ascii=False, indent=1)},
    # ------------------------------------------------- dilemmas in the dock
    {"name": "Ship of Theseus: the title contest",
     "intent": "Repaired ship A and reassembled ship B each claim: 'the "
               "real one is me, because it is not him'. An even cycle — "
               "two lawful decrees, no paradox anywhere. (The criterion-"
               "free 'same, in itself' is the truth-teller: try same := "
               "Tr(same).)",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"theA": "not(Tr(theB))",
                                      "theB": "not(Tr(theA))"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Agrippa's dogma (foundation with a passport)",
     "intent": "A self-supporting foundation f := f with a dependent "
               "claim on top: the foundation is stipulable, and the "
               "dependent's refusal names its culprit.",
     "zfl": json.dumps({"genre": "system",
                        "sentences": {"p": "Tr(f)", "f": "Tr(f)"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Same person? (corecursion, all observations match)",
     "intent": "'The same person' = matches now AND the same henceforth: "
               "S := obs AND S. With every observation matching, the core "
               "never says 'yes' — only 'decide'. Flip obs to F and watch "
               "identity ground to false instantly: refutable by fact, "
               "confirmable only by decree.",
     "zfl": json.dumps({"genre": "system",
                        "atoms": {"obs": {"status": "T",
                                          "means": "every observation so "
                                                   "far matches"}},
                        "sentences": {"S": "and(Tr(obs), Tr(S))"},
                        "ask": ["passport", "stipulations"]},
                       ensure_ascii=False, indent=1)},
    # ------------------------------------------------ other genres, intact
    {"name": "Sensor",
     "intent": "An unverified sensor reports overheating; if overheating, "
               "the shutdown fires. Will it fire? (Also try the one-line "
               "human syntax: assert overheat impl shutdown)",
     "zfl": json.dumps({"genre": "statement",
                        "atoms": {"overheat": {"status": "Z",
                                               "means": "the sensor reads "
                                                        "overheating"},
                                  "shutdown": {"status": "Z",
                                               "means": "the shutdown "
                                                        "fires"}},
                        "assert": "imp(overheat, shutdown)",
                        "ask": ["verdict", "warranty"]},
                       ensure_ascii=False, indent=1)},
    {"name": "Modus ponens (Carroll's tortoise)",
     "intent": "The tortoise demands the rule itself be written as a "
               "premise: if (p implies q) and p, then q. True — but watch "
               "the completion table: it is a FRAME. A rule written down "
               "is certified, yet it moves nothing; a rule must be acted, "
               "not mailed.",
     "zfl": json.dumps({"genre": "statement",
                        "atoms": {"p": {"status": "Z",
                                        "means": "the premise p holds"},
                                  "q": {"status": "Z",
                                        "means": "the conclusion q holds"}},
                        "assert": "imp(and(imp(p,q),p),q)",
                        "ask": ["verdict", "warranty"]},
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


def _lang(query):
    """Which language was asked for. Checked against the spec's own list
    rather than against a pair hard-coded here: the routes were written when
    there were two languages and would have silently served English for
    every new one, which is the sort of gap that looks like a translation
    bug for a week."""
    # `query` arrives WITHOUT its leading "?" (do_GET partitions it off), so
    # anchoring on "?" matched nothing and every language fell back to
    # English — including the one that had worked for weeks. Caught by
    # checking `l=ru` after the change rather than only the new codes.
    m = re.search(r"(?:^|&)l=([A-Za-z-]{2,5})", query or "")
    want = (m.group(1).lower() if m else "en")
    try:
        # `entry[0]`, not tuple unpacking: LANGS grew a third field the day
        # the AI was tied to the interface language, and a fixed-width unpack
        # here raised inside the try, fell to the two-language default, and
        # served English for every new code while the module itself was
        # perfectly correct. Read the field you need and let the row grow.
        codes = {entry[0] for entry in _v2("zfl2").LANGS}
    except Exception:
        codes = {"en", "ru"}
    return want if want in codes else "en"



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


def api_assert(payload):
    """Assertion mode: the assertion's LOGIC MAP — statement report +
    currency (free / on-credit / contingent) + decisive checks + the
    E26 derivation audit. Same shape as api_run so the front reuses
    the flow."""
    text, herr = _coerce(payload)
    if herr:
        return {"ok": False, "issues": herr}
    doc, parsed, issues = zfl.validate(text)
    if parsed is None:
        return {"ok": False, "issues": issues}
    if doc.get("genre") != "statement":
        return {"ok": False, "issues": [
            {"level": "error", "code": "E_GENRE", "where": "genre",
             "hint": "the Assertion tab maps statement-genre documents"}]}
    report = engine.logic_map(doc, parsed)
    return {"ok": True, "issues": issues,
            "back_reading": zfl.back_reading(doc, parsed),
            "report": report}


# The modules the v2 path stands on, in dependency order. Reloading only the
# studio's own files was not enough: the fourth confusion of the day was a fix
# in `znumjudge` — the CORE — that the running server could not see, because
# reloading `zfl2` re-runs its imports and Python hands back the cached core
# module. So the whole chain is watched by file mtime and reloaded bottom-up
# when it moves.
_V2_CHAIN = ["ztl", "znum", "znumjudge", "znumsolve", "zpassport", "zbook",
             "zfl2", "zfl2examples", "zfl2doc", "translator", "translator2"]
_MTIMES = {}
_RELOAD_LOCK = threading.Lock()   # never reload a module under two threads


def _refresh_dev():
    """Reload whatever changed on disk, in dependency order. Development
    only: in public mode the process is restarted deliberately."""
    if PUBLIC:
        return
    import importlib
    with _RELOAD_LOCK:
        _refresh_locked(importlib)


def _refresh_locked(importlib):
    for name in _V2_CHAIN:
        try:
            mod = importlib.import_module(name)
            path = getattr(mod, "__file__", None)
            if not path:
                continue
            m = os.path.getmtime(path)
            if _MTIMES.get(name) != m:
                if name in _MTIMES:            # not the first sighting
                    importlib.reload(mod)
                _MTIMES[name] = m
        except Exception:
            continue


def _v2(name):
    """A v2 module, with the whole chain refreshed first in development."""
    import importlib
    _refresh_dev()
    return importlib.import_module(name)


def api_v2run(payload):
    """ZFL v2: one table in, whichever instruments apply out. The whole of
    what used to be three tabs, with no genre to declare."""
    doc = payload.get("doc") or {}
    return _v2("zfl2").run(doc)


def api_v2fill(payload):
    """A question in plain language becomes a filled table. The model never
    decides anything — it fills cells, and the core judges them after."""
    translator2 = _v2("translator2")
    try:
        return translator2.fill(payload.get("history", []),
                                payload.get("lang", "en"),
                                payload.get("cfg"))
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_v2comment(payload):
    """Commentary on a verdict the model did not produce."""
    translator2 = _v2("translator2")
    try:
        return {"ok": True, "reply": translator2.comment(
            payload.get("doc") or {}, payload.get("result") or {},
            payload.get("lang", "en"), payload.get("history", []),
            payload.get("cfg"))}
    except translator.TranslatorError as e:
        return {"ok": False, "error": str(e)}


def api_v2validate(payload):
    doc = payload.get("doc") or {}
    return {"ok": True, "issues": _v2("zfl2").validate(doc)}


ROUTES = {"/api/v2run": api_v2run, "/api/v2validate": api_v2validate,
          "/api/v2fill": api_v2fill, "/api/v2comment": api_v2comment,
          "/api/validate": api_validate, "/api/run": api_run,
          "/api/chat": api_chat, "/api/emit": api_emit,
          "/api/repair": api_repair, "/api/explain": api_explain,
          "/api/providers": api_providers, "/api/savekey": api_savekey,
          "/api/refute": api_refute, "/api/assert": api_assert}


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
        # the query string is the page's business, not the router's:
        # /zfl?l=ru must reach the same handler as /zfl. Kept, not
        # discarded — /api/formspec reads the language out of it, and the
        # first version of this line threw it away an hour after the route
        # that needed it was written.
        self.path, _, query = self.path.partition("?")
        self.path = self.path or "/"
        # v2 IS THE STUDIO from 2026-08-13; v1 stays reachable at /v1
        # rather than being deleted, because §7 of the published paradox
        # docket describes ITS flow — "press Validate … the studio shows a
        # human back-reading … then Run on the core" — and v2 has neither a
        # Validate button nor a back-reading yet. The collection itself did
        # move across, entire, and a stand asserts it. Until the back-reading
        # exists, an archived-but-live v1 is what keeps an issued sentence
        # true.
        if self.path in ("/", "/index.html", "/v2", "/studio2"):
            with open(os.path.join(HERE, "static", "studio2.html"), "rb") as f:
                self._send(200, f.read(), "text/html; charset=utf-8")
        elif self.path in ("/v1", "/v1.html", "/classic"):
            with open(os.path.join(HERE, "static", "index.html"), "rb") as f:
                self._send(200, f.read(), "text/html; charset=utf-8")
        elif self.path in ("/zfl", "/zfl.html"):
            # The ZFL reference, generated from the language itself by
            # tool/zfl2doc.py — regenerated on request in development so it
            # cannot lag the spec, read from disk when serving publicly.
            path = os.path.join(HERE, "static", "zfl.html")
            if not PUBLIC:
                try:
                    # RELOAD, not just import: a long-running dev server
                    # holds the generator from process start, so without
                    # this it regenerates the page from stale code and
                    # overwrites the freshly built file with the old one.
                    import importlib
                    import zfl2
                    import zfl2doc
                    importlib.reload(zfl2)
                    importlib.reload(zfl2doc)
                    open(path, "w", encoding="utf-8").write(zfl2doc.page())
                except Exception:
                    pass
            if os.path.exists(path):
                with open(path, "rb") as f:
                    self._send(200, f.read(), "text/html; charset=utf-8")
            else:
                self._send(404, {"error": "reference not built"})
        elif self.path == "/api/v2examples":
            zfl2examples = _v2("zfl2examples")
            self._send(200, zfl2examples.catalogue(_lang(query)))
        elif self.path == "/api/formspec":
            self._send(200, _v2("zfl2").form_spec(_lang(query)))
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
        if n > 262144:                      # 256 KB body cap (DoS guard)
            remaining = n                   # drain the proxied body first,
            while remaining > 0:            # else Apache sees a desync -> 502
                chunk = self.rfile.read(min(remaining, 65536))
                if not chunk:
                    break
                remaining -= len(chunk)
            self._send(413, {"ok": False, "error": "request too large"})
            return
        try:
            payload = json.loads(self.rfile.read(n).decode() or "{}")
        except json.JSONDecodeError:
            self._send(400, {"error": "bad json"})
            return
        try:
            self._send(200, fn(payload))
        except Exception as e:                      # never die on input
            # The TYPE goes to the client, the message does not: an
            # exception's text can carry absolute paths, module internals
            # or fragments of another visitor's input. The detail belongs
            # in the server's own log, not in a stranger's browser.
            traceback.print_exc(file=sys.stderr)
            self._send(200, {"ok": False, "issues": [{
                "level": "error", "code": "E_INTERNAL",
                "where": type(e).__name__,
                "hint": "internal studio error — the detail is in the "
                        "server log, not here"}]})


if __name__ == "__main__":
    print(f"ZTLStudio: http://localhost:{PORT}")
    if not translator.any_key():
        print("No provider key found — pro mode (hand-written ZFL), the "
              "AI is off. Add a key in Settings or drop it into "
              "tool/.<provider>_key.")
    if not PUBLIC:
        Timer(0.7, lambda: webbrowser.open(f"http://localhost:{PORT}")).start()
    # THREADED, from 2026-08-13. It was HTTPServer, which serves ONE request
    # at a time, and the AI routes wait on a provider for up to ninety
    # seconds — so a single slow completion froze the studio for everyone.
    # The security audit named this and deliberately did not fix it,
    # because threads plus module-level mutable state wants a look rather
    # than a one-word substitution. The look: the rate limiter and the
    # development module-reloader are now behind locks (a reload racing a
    # request is the dangerous one, and it only exists off the public
    # instance); everything else in the request path is per-call.
    ThreadingHTTPServer(("127.0.0.1", PORT), Handler).serve_forever()
