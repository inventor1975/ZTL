# -*- coding: utf-8 -*-
"""
The AI side of studio v2: fills the table, and comments on the core's answer.

THE PROMPT IS GENERATED FROM THE SPEC. Every column, every allowed status,
every kind of ground and every operator the model is told about is read out
of `zfl2.COLUMNS` and the parsers — so a column added there teaches the model
about it without anyone remembering to edit a prompt. A hand-written prompt
is a second description of the language, and this project has spent the whole
day removing second descriptions.

TABLE OR JSON, the curator's question: JSON, and not by taste. A model emits
a structured object far more reliably than a bespoke table layout, the result
can be validated precisely rather than by eye, and the validator's
machine-readable issues feed straight back for one repair attempt. The human
sees the table; the model writes the object that fills it. Same split as
everywhere else here — surface for people, structure for machines.

THE LANGUAGE IS TOLD, NOT GUESSED. v1 inferred the reply language from a
sample of the user's own speech, which is a guess that fails whenever the
question is short or the terms are English. The studio knows which language
its interface is in, so it says so.

WHAT THE MODEL IS NOT ALLOWED TO DO is decide anything. It fills cells and
comments on a verdict that was computed without it. The core's answer is
never routed through the model, and the commentary says so when it disagrees.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import translator                                                # noqa: E402
import zfl2                                                      # noqa: E402
import zfl2doc                                                   # noqa: E402

LANG_NAME = {"en": "English", "ru": "Russian"}


def schema(lang="en"):
    """The language, described to a model, from the spec itself."""
    spec = zfl2.form_spec(lang)
    lines = ["A document is JSON: {\"rows\": [ ... ], \"claim\": \"...\"}.",
             "Each row is an object with these keys:"]
    for c in spec["columns"]:
        req = ("REQUIRED" if c["required"]
               else f"required when status is one of "
                    f"{c['required_when']['status']}"
               if c["required_when"] else "optional")
        bit = f'  "{c["key"]}" ({req}) — {c["help"]}'
        if c.get("options"):
            bit += ("; one of: "
                    + ", ".join(f'"{o["value"]}"' for o in c["options"]))
        if c.get("eg"):
            bit += "; e.g. " + ", ".join(str(e) for e in c["eg"])
        lines.append(bit)
    lines.append('"claim" (optional) — one formula over the row names.')
    lines.append("Operators: " + " ".join(zfl2doc.operators()))
    lines.append("Arithmetic: " + " ".join(zfl2doc.arithmetic()))
    lines.append("A value is a number, an interval like [0,10], or ? when it "
                 "is the thing being asked for.")
    return "\n".join(lines)


FILL_SYS = """You turn a person's question into one ZFL v2 document.

{schema}

RULES, and they are not stylistic:
- Reply with the JSON object ALONE. No prose, no code fence.
- NEVER INVENT A VERIFICATION, and this is the one rule the whole system
  exists for. If the person did not say what backs a fact, its status is
  "unverified" and its ground is EMPTY. Writing "verified" with a document
  name they never mentioned is granting truth on credit, which is the
  failure this machine was built to refuse.
- THE EXAMPLES IN THE SCHEMA ARE FORMS, NOT CONTENT. `inv-17` and `order-4`
  are shapes of a name; copying one into a story about sweets asserts an
  invoice that does not exist. A ground must be a word the PERSON used. If
  the fact comes from their own telling and nothing else, either leave the
  status "unverified", or — when the story itself is the source — write
  `the-story`, and nothing dressed up as a document.
- "means" is not decoration. Write what it MEANS for the row to be TRUE, in
  {language}, so a reader can catch a name that lies (a name like `fresh`
  already means "not revoked").
- Self-reference goes in "ground" with status "defined": the liar is
  {{"name": "L", "status": "defined", "ground": "~Tr(L)"}}.
- WHEN THE QUESTION IS "CHECK THIS SENTENCE", LEAVE THE CLAIM EMPTY. The row
  already says what the sentence is; the passport office answers by itself,
  and repeating the definition as a claim ("L == ~Tr(L)") asks the machine
  to judge a definition rather than to classify a sentence. Both models
  tried it, so it is written here in so many words.
- A DERIVED NUMBER is not a "defined" row. "defined" is for propositional
  self-reference only — the liar and its kin. A quantity you do not know,
  including a total that follows from other rows, has status "unverified",
  value "?", and the relation goes in "claim":
  {{"name": "total", "status": "unverified", "value": "?"}} with
  "claim": "sum(a,b) = total". Never put arithmetic in "ground".
- THE CLAIM MAY HOLD SEVERAL RELATIONS, joined by `&`, and a word problem
  needs them: one relation per fact the story states, and the machine solves
  the system. "Masha had 3 sweets, gave 1 to Vasya, how many to Petya so they
  are equal" is rows start=3, toV=1, give=?, M=?, P=? and the claim
  "M = start - toV - give & P = give & M = P". Naming the quantities without
  their relations leaves nothing to solve — the answer comes back OPEN and
  the person is told to go and measure what they were asking you to compute.
- If the person is asking for a number, give that row the value "?" and put
  the relation in "claim".
- Names must be usable in formulas: letters, digits, underscores.
- A GROUND IS ONE WORD. `inv-17`, `the-story`, `contract`. It is an
  identifier, not a sentence: two rows sharing a ground share a document and
  fall together, so `the story` with a space is not a longer name, it is a
  different one truncated.
"""

def vocabulary(lang):
    """The words the interface uses, handed to the model so it stops
    inventing its own. Measured need: with only "reply in Russian" the
    commentary came back saying "уневерифицированный", which is not a word.
    The status names come from the spec, so they cannot drift from the
    dropdown the reader is looking at."""
    spec = zfl2.form_spec(lang)
    st = [c for c in spec["columns"] if c["key"] == "status"][0]
    words = {o["value"]: o["label"] for o in st["options"]}
    extra = {
        "ru": {"EARNED": "заработано", "REFUTED": "опровергнуто",
               "OPEN": "открыто", "ON CREDIT": "в кредит", "E": "E — "
               "нечего читать", "PARADOX": "парадокс",
               "UNDERDETERMINED": "недоопределено (нужна оговорка)",
               "INTRINSIC": "вынужденно", "warranty": "гарантия",
               "weak links": "слабые звенья", "passport": "паспорт",
               "trust bracket": "вилка доверия", "ground": "основание"},
        "en": {},
    }[lang if lang in ("ru", "en") else "en"]
    pairs = [f'"{k}" = "{v}"' for k, v in {**words, **extra}.items()]
    return ("Use exactly these words, and invent none of your own:\n"
            + "; ".join(pairs)) if pairs else ""


COMMENT_SYS = """You explain what the ZTL core has already decided.

{vocabulary}

You did not compute this and you cannot change it. The verdict, the
passports, the brackets and the weak links come from the instruments; your
job is to say what they mean in plain {language}, in at most six sentences.

- MENTION ONLY WHAT IS IN THE REPORT. If there is no passport section, say
  nothing about passports; if no bracket, nothing about brackets. The
  vocabulary below is for TRANSLATING what is there, not a list of things to
  bring up. Naming an instrument that did not speak is a false report.
- Lead with the answer, then why.
- "Unverified" is not "false" and not "unknown": it means no verification was
  produced. Say it that way.
- If the report names weak links or cures, say what would settle the matter.
- If something in the report surprises you, say so plainly rather than
  smoothing it over. You are a commentator, not an advocate.
- Never restate the JSON. The reader can see the table.
"""


def _invented_grounds(doc, history):
    """Grounds the person never mentioned.

    The machine cannot know whether `inv-17` exists — but it can see that
    nobody in the conversation ever said it. A model reaching for a document
    name out of the schema's own examples is the exact failure this corpus
    refuses, so it is flagged rather than trusted. A warning, not an error:
    the person may genuinely have an invoice they did not name in so many
    words, and that judgement is theirs."""
    # the sanctioned label for "the person's own telling" is not an
    # invention — the prompt asks for it by name, and flagging it would
    # teach the model to dress the same thing up as a document instead
    TOLD = {"the-story", "the_story", "story", "рассказ", "условие",
            "со-слов", "stated"}
    said = " ".join(m.get("content", "") for m in history).lower()
    out = []
    for i, r in enumerate((doc.get("rows") or []), 1):
        g = str(r.get("ground") or "").strip()
        if not g or r.get("status") == "defined":
            continue
        stem = g.lower().replace("-", " ").split()[0]
        if g.lower() in TOLD:
            continue
        if len(stem) > 2 and stem not in said and g.lower() not in said:
            out.append({"level": "warn", "code": "W_AI_INVENTED_GROUND",
                        "where": f"row {i} / ground",
                        "hint": f"'{g}' was never mentioned — the model "
                                f"supplied it. If no such document exists, "
                                f"this row is unverified."})
    return out


def fill(history, lang="en", cfg=None):
    """A question in, a validated document out — with one repair attempt on
    the validator's own machine-readable issues, which is what those codes
    were built for."""
    sysmsg = FILL_SYS.format(schema=schema(lang),
                             language=LANG_NAME.get(lang, "English"))
    msgs = [{"role": "system", "content": sysmsg}] + [dict(m) for m in history]
    if msgs[-1]["role"] == "user":
        msgs[-1]["content"] += (
            f"\n\n[Write every \"means\" gloss in "
            f"{LANG_NAME.get(lang, 'English')}.]")
    raw = translator.strip_fences(translator.llm(msgs, cfg))
    doc, issues = _parse(raw)
    if doc is not None:
        issues = zfl2.validate(doc)
        if not any(i["level"] == "error" for i in issues):
            return {"ok": True, "doc": doc, "repaired": False,
                    "issues": issues + _invented_grounds(doc, history)}
    msgs += [{"role": "assistant", "content": raw},
             {"role": "user", "content":
              "That document was rejected:\n"
              + json.dumps(issues, ensure_ascii=False)
              + "\nReturn a corrected JSON object, alone."}]
    raw2 = translator.strip_fences(translator.llm(msgs, cfg))
    doc2, parse_issues = _parse(raw2)
    if doc2 is None:
        return {"ok": False, "issues": parse_issues}
    return {"ok": True, "doc": doc2, "repaired": True,
            "issues": zfl2.validate(doc2) + _invented_grounds(doc2, history)}


def _parse(raw):
    try:
        doc = json.loads(raw)
    except json.JSONDecodeError as exc:
        return None, [{"level": "error", "code": "E_AI_JSON",
                       "where": "model", "hint": f"not JSON: {exc}"}]
    if not isinstance(doc, dict) or "rows" not in doc:
        return None, [{"level": "error", "code": "E_AI_SHAPE",
                       "where": "model", "hint": "no rows in the object"}]
    return doc, []


def _anchor(lang):
    """A language instruction in the SYSTEM prompt loses to a wall of English
    context — measured: with the interface in Russian and the report in
    English JSON, the reply came back in English anyway. The instruction has
    to sit in the last turn, where it is the most recent thing said."""
    return (f"\n\n[Reply STRICTLY in {LANG_NAME.get(lang, 'English')}, "
            f"whatever language the data above happens to be in.]")


def comment(doc, result, lang="en", history=None, cfg=None):
    """Plain-language commentary on a verdict the model did not produce."""
    sysmsg = COMMENT_SYS.format(language=LANG_NAME.get(lang, "English"),
                                vocabulary=vocabulary(lang))
    context = ("The table:\n" + json.dumps(doc, ensure_ascii=False)
               + "\n\nWhat the instruments answered:\n"
               + json.dumps(result, ensure_ascii=False))
    msgs = [{"role": "system", "content": sysmsg},
            {"role": "user", "content": context + _anchor(lang)}]
    for m in (history or []):
        msgs.append(dict(m))
    if msgs[-1]["role"] == "user":
        msgs[-1]["content"] += _anchor(lang)
    return translator.llm(msgs, cfg)
