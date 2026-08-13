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
- Never invent a verification. If the person did not say what backs a fact,
  its status is "unverified" and its ground is empty. Writing "verified" with
  a made-up document name is the one thing you must never do here: this
  system exists to refuse truth on credit, and you would be granting it.
- "means" is not decoration. Write what it MEANS for the row to be TRUE, in
  {language}, so a reader can catch a name that lies (a name like `fresh`
  already means "not revoked").
- Self-reference goes in "ground" with status "defined": the liar is
  {{"name": "L", "status": "defined", "ground": "~Tr(L)"}}.
- A DERIVED NUMBER is not a "defined" row. "defined" is for propositional
  self-reference only — the liar and its kin. A quantity you do not know,
  including a total that follows from other rows, has status "unverified",
  value "?", and the relation goes in "claim":
  {{"name": "total", "status": "unverified", "value": "?"}} with
  "claim": "sum(a,b) = total". Never put arithmetic in "ground".
- The claim holds ONE relation. If the person asks two things at once, put
  the one they actually asked and leave the rest as rows.
- If the person is asking for a number, give that row the value "?" and put
  the relation in "claim".
- Names must be usable in formulas: letters, digits, underscores.
"""

COMMENT_SYS = """You explain what the ZTL core has already decided.

You did not compute this and you cannot change it. The verdict, the
passports, the brackets and the weak links come from the instruments; your
job is to say what they mean in plain {language}, in at most six sentences.

- Lead with the answer, then why.
- "Unverified" is not "false" and not "unknown": it means no verification was
  produced. Say it that way.
- If the report names weak links or cures, say what would settle the matter.
- If something in the report surprises you, say so plainly rather than
  smoothing it over. You are a commentator, not an advocate.
- Never restate the JSON. The reader can see the table.
"""


def fill(history, lang="en", cfg=None):
    """A question in, a validated document out — with one repair attempt on
    the validator's own machine-readable issues, which is what those codes
    were built for."""
    sysmsg = FILL_SYS.format(schema=schema(lang),
                             language=LANG_NAME.get(lang, "English"))
    msgs = [{"role": "system", "content": sysmsg}] + list(history)
    raw = translator.strip_fences(translator.llm(msgs, cfg))
    doc, issues = _parse(raw)
    if doc is not None:
        issues = zfl2.validate(doc)
        if not any(i["level"] == "error" for i in issues):
            return {"ok": True, "doc": doc, "issues": issues, "repaired": False}
    msgs += [{"role": "assistant", "content": raw},
             {"role": "user", "content":
              "That document was rejected:\n"
              + json.dumps(issues, ensure_ascii=False)
              + "\nReturn a corrected JSON object, alone."}]
    raw2 = translator.strip_fences(translator.llm(msgs, cfg))
    doc2, parse_issues = _parse(raw2)
    if doc2 is None:
        return {"ok": False, "issues": parse_issues}
    return {"ok": True, "doc": doc2, "issues": zfl2.validate(doc2),
            "repaired": True}


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


def comment(doc, result, lang="en", history=None, cfg=None):
    """Plain-language commentary on a verdict the model did not produce."""
    sysmsg = COMMENT_SYS.format(language=LANG_NAME.get(lang, "English"))
    context = ("The table:\n" + json.dumps(doc, ensure_ascii=False)
               + "\n\nWhat the instruments answered:\n"
               + json.dumps(result, ensure_ascii=False))
    msgs = [{"role": "system", "content": sysmsg},
            {"role": "user", "content": context}] + list(history or [])
    return translator.llm(msgs, cfg)
