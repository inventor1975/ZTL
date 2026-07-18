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

import providers

ZFL_SPEC = """ZFL is the formal language of the ZTL core. Strict JSON:
{"genre": "statement"|"system",
 "atoms": {"name": {"status": "T"|"F"|"Z", "note": "explanation"}},
 "assert": "formula",                  // statement genre only
 "sentences": {"name": "formula"},     // system genre only
 "ask": ["verdict","warranty","passport","stipulations"]}
Formulas: not(x), and(x,y), or(x,y), imp(x,y), xor(x,y), xnor(x,y),
constants T and F, atom names; in genre=system references to sentences
go ONLY through Tr(name); bare atoms inside system formulas are
forbidden. RESERVED — never use as atom/sentence names: T, F, Z, Tr,
not, and, or, imp, xor, xnor (pick descriptive names like "eats",
"child_truth"). status: T = verified-true, F = verified-false,
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
 "assert":"imp(overheat, shutdown)","ask":["verdict","warranty"]}
4) "X is true if and only if X is false" (compressed Russell / the
liar: encode the biconditional as the DEFINITION) ->
{"genre":"system","sentences":{"X":"not(Tr(X))"},"ask":["passport"]}
Never emit degenerate formulas like xor(A,A) or xnor(A,A) — if you are
tempted, you have mis-encoded a biconditional definition.
5) "Russell: the set R of all sets not containing themselves, over the
universe a = empty, b = {b}" ->
{"genre":"system","sentences":{
 "a_in_a":"F","a_in_b":"F","a_in_R":"not(Tr(a_in_a))",
 "b_in_a":"F","b_in_b":"T","b_in_R":"not(Tr(b_in_b))",
 "R_in_a":"F","R_in_b":"F","R_in_R":"not(Tr(R_in_R))"},
 "ask":["passport"]}"""

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
EXPLICITLY IN SCOPE (do not refuse these): the classical
self-reference paradoxes — the liar, the truth-teller, Jourdain's
carousel, Curry, Yablo truncations, the crocodile dilemma (a deal
about a future action reduces cleanly to sentences about truth —
narrative time is NOT a temporal-logic essence), Russell's paradox
over a small named universe (membership facts x_in_y as sentences,
x_in_R defined as not(Tr(x_in_x))). Refuse ONLY when numbers,
quantities or arithmetic are the POINT of the question — e.g. the
SORITES/heap (induction over n grains IS arithmetic: refuse first and
offer the coarsened shadow, do NOT silently formalize a few grain
counts as atoms), Berry, Richard. In that case
say HONESTLY: "This does not formalize into propositional ZTL without
losing the point (here: …)", explain why in one line, and ask: stop,
or agree on a coarsened logical shadow (listing explicitly what is
lost). NEVER invent atoms
for the sake of formalizability. An atom is a declarative statement;
a question cannot be an atom.

If within the boundary — reply with a structured summary:
— ENTITIES/ATOMS: the elementary claims; what is verified, what is not;
— ASSERTED: who/what asserts what (flag self-references to truth);
— GENRE: a plain statement or a self-referential system;
— ASKED: what the human wants to know.
Ask a clarifying question ONLY if formalization is impossible without
the answer. Do NOT offer to explain, resolve or analyze, and do NOT
pre-announce what the core will decide (no verdict, passport or
quarantine predictions in the understanding) — the core judges, not
you, even when you are confident. If the understanding is complete, end with exactly
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

EXPLAIN_SYS = """You are the interpreter of the ZTL core's verdicts for
a human. You receive the ZFL document, its deterministic back-reading
and the core's formal report. THE REPORT IS THE AUTHORITY: never
contradict it, never re-judge, never soften a PARADOX or promote a Z.
Your job is to retell what the core established, in plain language.
LANGUAGE RULE (strict): reply in the language of the MOST RECENT user
message in the conversation; if there is none yet, use the language of
the claim/notes inside the ZFL. Do not drift into the language of the
technical context.

Glossary you may rely on:
- verdicts are always two-valued: T (truth was EARNED) / F (not earned);
- warranty "stable" = no future verification can flip the verdict;
  "until-verification" = it can flip when unverified inputs get checked;
- passport kinds: PARADOX = no classical solutions, refusal permanent
  (the oscillation period is diagnostics, not hope); UNDERDETERMINED =
  several consistent solutions exist, an external choice (stipulation)
  can ground it; INPUT = a plain unverified input, verification lifts
  it; DOWNSTREAM = quarantine inherited from the listed culprits;
- grounded sentences carry the same classical value in EVERY solution.

If the user asks something the report does not answer, say honestly
that the core was not asked that — and, when possible, show the EXACT
ZFL change that would ask it. Any ZFL you show MUST be valid per the
specification below: only the six connectives and Tr(name), nothing
invented. NEVER predict what the core would say about a MODIFIED
system — you are not the judge and you will guess wrong; show the
edit and tell the user to run it: the core answers, not you.
Be brief and concrete.

""" + ZFL_SPEC


class TranslatorError(Exception):
    pass


def any_key():
    """True if at least one provider has a usable key."""
    return any(p["has_key"] for p in providers.available())


def llm(messages, cfg, temperature=0.2):
    """cfg: {provider, model, key} chosen in the UI (any field optional —
    falls back to env / local key file / provider default)."""
    cfg = cfg or {}
    try:
        return providers.chat(
            messages, provider=cfg.get("provider", "groq"),
            model=cfg.get("model", ""), key=cfg.get("key", ""),
            temperature=temperature)
    except providers.ProviderError as e:
        raise TranslatorError(str(e))


UNDERSTAND_SYS_HYP = """You are the meaning translator for the ZTL studio,
HYPOTHESES mode. The user states a claimed LAW, RULE or INFERENCE and wants
the core to check it. Your job is ONLY to understand and restate it, never
to judge — the core judges. ALWAYS reply in the language the user writes in.

WHAT THIS MODE CHECKS. A hypothesis is any claim built from logical
connectives (not, and, or, if-then, xor, iff) over declarative atoms — e.g.
modus ponens, De Morgan, excluded middle, distributivity, contraposition,
an access or business rule. It is NOT a self-referential paradox: do NOT ask
about self-reference, and NEVER say a claimed logical law or rule is
"outside ZTL". Each atom is a declarative statement, treated as UNVERIFIED
unless the user pins it true/false. The core checks the claim EXHAUSTIVELY
over every combination of {verified-true, verified-false, UNVERIFIED}, so the
real question it answers is: does the rule still hold when some inputs are
UNVERIFIED?

Refuse ONLY if the claim is not propositional at all — numbers, quantities
or arithmetic are the point, or a vague predicate like "heap". Then say
honestly in one line that it does not formalize into propositional ZTL
without losing the point, and offer a coarsened shadow. Never invent atoms;
a question is not an atom.

Reply with a short structured summary:
— ATOMS: the elementary declarative statements (all UNVERIFIED unless the
  user fixed one);
— CLAIM: the WHOLE rule as ONE implication — the premises together imply the
  conclusion; the conclusion is PART of the claim, not the question. An
  inference "from P1 and P2 conclude C" is (P1 and P2) → C; a premise
  "X is true" is just the atom X;
— ASKED: does this rule hold, and does it survive unverified inputs.
Ask a clarifying question ONLY if formalization is impossible without it. Do
NOT predict the verdict. If the understanding is complete, end with exactly
this sentence (translated into the user's language, quoting the button name):
"If the understanding is correct — press the «Agree → ZFL» button." Be brief."""

HYP_FEWSHOT = (
    "Examples (emit exactly this shape). KEY RULE: every premise stated as "
    "TRUE becomes a CONJUNCT in the antecedent — never drop it.\n"
    '"if A→B and A is true, then B is true" (modus ponens) ->\n'
    '{"genre":"statement","atoms":{"A":{"status":"Z"},"B":{"status":"Z"}},'
    '"assert":"imp(and(imp(A,B),A),B)"}\n'
    '"if A and B are true, and (A and B) implies C, then C is true" ->\n'
    '{"genre":"statement","atoms":{"A":{"status":"Z"},"B":{"status":"Z"},'
    '"C":{"status":"Z"}},'
    '"assert":"imp(and(and(A,B),imp(and(A,B),C)),C)"}\n'
    '   (WRONG here would be imp(imp(and(A,B),C),C) — it drops the premise '
    '"A and B are true".)\n'
    '"p or not p is always true" (excluded middle) ->\n'
    '{"genre":"statement","atoms":{"p":{"status":"Z"}},'
    '"assert":"or(p,not(p))"}')

EMIT_SYS_HYP = (
    "You are the ZFL compiler, HYPOTHESES mode. From the agreed "
    "understanding emit ONLY valid ZFL JSON, no explanations, no markdown. "
    "ALWAYS use genre \"statement\". The \"assert\" is the WHOLE claimed "
    "rule as ONE formula, INCLUDING its conclusion: an inference 'from "
    "premises P1,P2,... conclude C' is imp(and(P1,P2,...),C); a premise 'X "
    "is true' is just the atom X. Never drop a premise or the conclusion, "
    "and never encode a premise as an atom status — put it in the formula. "
    "Declare EVERY atom with status \"Z\". Never emit a self-referential "
    "\"system\". Atoms are declarative; never an atom for a question. "
    "CRITICAL: the atom names inside \"assert\" MUST be EXACTLY the keys of "
    "\"atoms\" — same letters and SAME SCRIPT. If the user wrote Cyrillic "
    "А, Б, use А, Б in the formula too (never silently switch to Latin "
    "A, B). Pick ASCII-safe names only if the user did.\n\n"
    + ZFL_SPEC + "\n\n" + HYP_FEWSHOT)


def understand(history, cfg=None, mode="par"):
    """history: [{'role': 'user'|'assistant', 'content': str}, ...]"""
    sys = UNDERSTAND_SYS_HYP if mode in ("hyp", "ast") else UNDERSTAND_SYS
    return llm([{"role": "system", "content": sys}] + history, cfg)


def strip_fences(s):
    s = s.strip()
    if s.startswith("```"):
        s = s.split("\n", 1)[1] if "\n" in s else s
        if s.rstrip().endswith("```"):
            s = s.rstrip()[:-3]
    return s.strip()


def emit(understanding, cfg=None, mode="par"):
    if mode in ("hyp", "ast"):
        sys = EMIT_SYS_HYP
        user = (f"The agreed understanding:\n{understanding}\n\n"
                "Emit the ZFL statement for the claimed rule: the WHOLE rule "
                "as one \"assert\" (premises AND conclusion), every atom "
                "status \"Z\".")
    else:
        sys = EMIT_SYS
        user = (f"The agreed understanding:\n{understanding}\n\n"
                "Emit the ZFL. [Sentences are DEFINITIONS: a claim "
                "'X holds iff PHI' becomes \"X\": \"PHI-formula\"; in "
                "particular 'X iff not X' is {\"X\": \"not(Tr(X))\"}. "
                "Never emit xor(A,A) or xnor(A,A).]")
    out = llm([{"role": "system", "content": sys},
               {"role": "user", "content": user}], cfg)
    return strip_fences(out)


LANG_ANCHOR = ("\n\n[Reply strictly in the language of THIS message; "
               "for the initial explanation — in the language of the "
               "claim/notes inside the ZFL. If this question asks what "
               "would happen if the system or its inputs were CHANGED, "
               "do NOT answer from your head — you would be guessing: "
               "show the exact ZFL edit and say the core must be re-run; "
               "the core answers, not you.]")


def explain(zfl_text, back_reading, report, history, lang_hint="", cfg=None):
    """history: follow-up chat about the result (may be empty);
    lang_hint: a sample of the user's own speech — the language anchor
    for the INITIAL explanation (the ZFL context is all-English and
    would otherwise drag the reply into English)."""
    context = (f"ZFL:\n{zfl_text}\n\nBack-reading:\n{back_reading}\n\n"
               f"The core's report (JSON):\n{json.dumps(report, ensure_ascii=False)}")
    if lang_hint:
        first_anchor = (f"\n\n[The user speaks the language of this "
                        f"phrase: \u201c{lang_hint[:200]}\u201d. Reply "
                        f"STRICTLY in that language.]")
    else:
        first_anchor = LANG_ANCHOR
    msgs = [{"role": "system", "content": EXPLAIN_SYS},
            {"role": "user", "content": context +
             "\n\nExplain the result in plain language." + first_anchor}]
    for m in history:
        msgs.append(dict(m))
    if msgs[-1]["role"] == "user":
        msgs[-1]["content"] = msgs[-1]["content"] + LANG_ANCHOR
    return llm(msgs, cfg, temperature=0.3)


def repair(zfl_text, issues, cfg=None):
    errs = "\n".join(f"- [{i['level']}] {i['code']} @ {i['where']}: {i['hint']}"
                     for i in issues)
    out = llm([{"role": "system", "content": REPAIR_SYS},
                {"role": "user", "content":
                 f"ZFL:\n{zfl_text}\n\nValidator errors:\n{errs}\n\n"
                 "Fix it and emit the ZFL."}], cfg)
    return strip_fences(out)
