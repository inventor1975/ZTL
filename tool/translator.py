# -*- coding: utf-8 -*-
"""
ZTLStudio: the translator. The ONLY component allowed to hallucinate —
which is why it never judges: it negotiates understanding in Russian,
then emits ZFL, and repairs it against the validator's machine-readable
errors. The human signs off on the meaning; the deterministic
back-reading (zfl.py) audits the emission; the core judges.

Groq API, same conventions as the curator's other tools (UA header —
Cloudflare 1010; GROQ_API_KEY from the environment).
"""

import json
import os
import urllib.request

API = "https://api.groq.com/openai/v1/chat/completions"
MODEL = os.environ.get("ZTL_GROQ_MODEL", "llama-3.3-70b-versatile")
KEY_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        ".groq_key")


def get_key():
    """Env first; else the local untracked key file (the repo is public —
    the key must never live in code)."""
    key = os.environ.get("GROQ_API_KEY")
    if key:
        return key.strip()
    if os.path.exists(KEY_FILE):
        with open(KEY_FILE) as f:
            return f.read().strip()
    return None

ZFL_SPEC = """ZFL is the formal language of the ZTL core. Strict JSON:
{"genre": "statement"|"system",
 "atoms": {"name": {"status": "T"|"F"|"Z", "note": "explanation"}},
 "assert": "formula",                  // statement genre only
 "sentences": {"name": "formula"},     // system genre only
 "ask": ["verdict","warranty","passport","stipulations"]}
Formulas: not(x), and(x,y), or(x,y), imp(x,y), xor(x,y), xnor(x,y),
constants T and F, atom names; in genre=system references to sentences
go ONLY through Tr(name); bare atoms inside system formulas are
forbidden. status: T = verified-true, F = verified-false,
Z = UNVERIFIED. statement = a verdict question about a claim over
(un)verified atoms. system = a self-referential system (paradoxes:
sentences about the truth of each other and themselves)."""

FEWSHOT = """Examples.
1) "The liar: this sentence is false" ->
{"genre":"system","sentences":{"L":"not(Tr(L))"},
 "ask":["passport"]}
2) "The crocodile returns the child iff the mother guesses his action;
the mother says: you will not return it" ->
{"genre":"system","sentences":{"R":"Tr(M)","M":"not(Tr(R))"},
 "ask":["passport","stipulations"]}
3) "An unverified sensor reports overheating; if overheating, the
shutdown fires. Will it fire?" ->
{"genre":"statement",
 "atoms":{"overheat":{"status":"Z","note":"sensor unverified"},
          "shutdown":{"status":"Z","note":"consequence"}},
 "assert":"imp(overheat, shutdown)","ask":["verdict","warranty"]}"""

UNDERSTAND_SYS = """You are the meaning translator for the ZTL logic
studio (two-valued verdicts + the mark Z "unverified"; paradoxes go
into quarantine instead of exploding). Your job is ONLY to understand
the human, never to judge. ALWAYS reply in the language the user
writes in.

FIRST — THE BOUNDARY OF COMPETENCE. ZTL v1 formalizes only:
(a) claims built from logical connectives over declarative atoms
    (each atom verified-true / verified-false / UNVERIFIED);
(b) self-referential systems — and ONLY when sentences speak about
    the TRUTH of sentences (their own or others'). Conflicting
    viewpoints, physics of motion, perception are NOT self-reference.
If the essence is arithmetic, quantities, wordplay about numbers,
time, or numeric probabilities — say HONESTLY: "This does not
formalize into propositional ZTL without losing the point (here: …)",
explain why in one line, and ask: stop, or agree on a coarsened
logical shadow (listing explicitly what is lost). NEVER invent atoms
for the sake of formalizability. An atom is a declarative statement;
a question cannot be an atom.

If within the boundary — reply with a structured summary:
— ENTITIES/ATOMS: the elementary claims; what is verified, what is not;
— ASSERTED: who/what asserts what (flag self-references to truth);
— GENRE: a plain statement or a self-referential system;
— ASKED: what the human wants to know.
Ask a clarifying question ONLY if formalization is impossible without
the answer. Do NOT offer to explain, resolve or analyze — the core
judges, not you. If the understanding is complete, end with exactly
this sentence (translated into the user's language, quoting the
button name verbatim):
"If the understanding is correct — press the \u00abAgree \u2192 ZFL\u00bb button." Be brief."""

EMIT_SYS = ("You are the ZFL compiler. From the agreed understanding "
            "emit ONLY valid ZFL JSON, no explanations, no markdown. "
            "Atoms are declarative statements only; NEVER create an "
            "atom for a question. The system genre only when sentences "
            "speak about the truth of sentences.\n\n"
            + ZFL_SPEC + "\n\n" + FEWSHOT)

REPAIR_SYS = ("You repair ZFL against validator errors. Emit ONLY the "
              "corrected ZFL JSON, no explanations.\n\n" + ZFL_SPEC)


class TranslatorError(Exception):
    pass


def groq(messages, temperature=0.2):
    key = get_key()
    if not key:
        raise TranslatorError(
            "No Groq key: set GROQ_API_KEY or put the key into "
            "tool/.groq_key (gitignored). Running without AI for now "
            "(pro mode: write ZFL by hand in the middle panel).")
    body = json.dumps({"model": MODEL, "messages": messages,
                       "temperature": temperature}).encode()
    req = urllib.request.Request(API, data=body, headers={
        "Authorization": f"Bearer {key}",
        "Content-Type": "application/json",
        "User-Agent": "ZTLStudio/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            data = json.loads(r.read().decode())
    except Exception as e:
        raise TranslatorError(f"Groq is unreachable: {e}")
    return data["choices"][0]["message"]["content"].strip()


def understand(history):
    """history: [{'role': 'user'|'assistant', 'content': str}, ...]"""
    return groq([{"role": "system", "content": UNDERSTAND_SYS}] + history)


def strip_fences(s):
    s = s.strip()
    if s.startswith("```"):
        s = s.split("\n", 1)[1] if "\n" in s else s
        if s.rstrip().endswith("```"):
            s = s.rstrip()[:-3]
    return s.strip()


def emit(understanding):
    out = groq([{"role": "system", "content": EMIT_SYS},
                {"role": "user", "content":
                 f"The agreed understanding:\n{understanding}\n\n"
                 "Emit the ZFL."}])
    return strip_fences(out)


def repair(zfl_text, issues):
    errs = "\n".join(f"- {i['code']} @ {i['where']}: {i['hint']}"
                     for i in issues if i["level"] == "error")
    out = groq([{"role": "system", "content": REPAIR_SYS},
                {"role": "user", "content":
                 f"ZFL:\n{zfl_text}\n\nValidator errors:\n{errs}\n\n"
                 "Fix it and emit the ZFL."}])
    return strip_fences(out)
