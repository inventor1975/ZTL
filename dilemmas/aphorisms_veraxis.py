# -*- coding: utf-8 -*-
"""aphorisms_veraxis — the blind test: twelve aphorisms from another AI,
run through the core.

Design of the test (agreed with the curator and A., 2026-07-19): A.'s AI
was asked for twelve assertive aphorisms with NO hint that they would be
formalized — a prompt that mentions a logic engine produces defensive
writing and tests the wrong thing. The aphorisms arrived; each is encoded
here and judged by the core.

THE PROTOCOL, and it is the point: every formalization is printed BESIDE
its verdict — atoms, glosses, formula. The weak link in this pipeline is
not the core but the translation (this repository shipped a polarity bug
on the same day), so the reading is exhibited for dispute, not hidden. A
verdict without its encoding is worthless.

WHAT THIS MEASURES: logical hygiene — the currency of each claim (free
truth / on credit / contingent), whether a stated inference is earned or
borrowed, and whether the claim can fail at all.
WHAT IT DOES NOT MEASURE: whether an aphorism is wise or true about the
world. The core has no opinion on depth.

HONEST NOTE ON GENRE: an aphorism is not an argument. Most of these are
definitional or causal claims about human affairs, and a propositional
encoding necessarily flattens them. Where an aphorism does not carry a
propositional skeleton, that is reported as "does not formalize" rather
than forced into one — refusing is a correct answer here.
"""
import json
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_ROOT, "tool"))
sys.path.insert(0, _ROOT)

import zfl                                                   # noqa: E402
import engine                                                # noqa: E402

# Each entry: (n, the aphorism, encoding|None, the reading note)
APHORISMS = [
    (1, "Уверенность начинается там, где человек перестаёт проверять, "
        "достаточно ли он знает.",
     {"atoms": {"stops_checking": {"status": "Z",
                                   "means": "the person stops checking "
                                            "whether he knows enough"},
                "certainty": {"status": "Z",
                              "means": "certainty has begun"}},
      "assert": "imp(stops_checking, certainty)"},
     "Read as: ceasing to check is sufficient for certainty. The "
     "aphorism's 'begins where' is a definitional locus, encoded as the "
     "one-way conditional it asserts."),

    (2, "Знание растёт от сомнения, а заблуждение — от защиты собственной "
        "правоты.",
     {"atoms": {"doubts": {"status": "Z", "means": "the person doubts"},
                "knowledge_grows": {"status": "Z",
                                    "means": "knowledge grows"},
                "defends_own_rightness": {"status": "Z",
                                          "means": "the person defends "
                                                   "his own rightness"},
                "delusion_grows": {"status": "Z",
                                   "means": "delusion grows"}},
      "assert": "and(imp(doubts, knowledge_grows), "
                "imp(defends_own_rightness, delusion_grows))"},
     "Two causal claims conjoined. 'Grows from' encoded as a conditional; "
     "the quantitative sense of growth is outside the core's axis."),

    (3, "Доверие возникает не из обещаний, а из предсказуемости поведения "
        "под давлением.",
     {"atoms": {"promises": {"status": "Z", "means": "promises are given"},
                "predictable_under_pressure":
                    {"status": "Z",
                     "means": "behaviour is predictable under pressure"},
                "trust": {"status": "Z", "means": "trust arises"}},
      "assert": "and(imp(predictable_under_pressure, trust), "
                "not(imp(promises, trust)))"},
     "The contrast is encoded as: predictability suffices; promises do "
     "NOT suffice. The second conjunct is the negation of a conditional — "
     "the strongest available reading of 'не из'."),

    (4, "Доверие разрушается не первой ошибкой, а первой попыткой её "
        "скрыть.",
     {"atoms": {"first_error": {"status": "Z",
                                "means": "a first error occurs"},
                "concealment": {"status": "Z",
                                "means": "an attempt to conceal it occurs"},
                "trust_destroyed": {"status": "Z",
                                    "means": "trust is destroyed"}},
      "assert": "and(imp(concealment, trust_destroyed), "
                "not(imp(first_error, trust_destroyed)))"},
     "Same shape as (3): concealment suffices, the bare error does not."),

    (5, "Власть без обязанности объясняться неизбежно начинает считать себя "
        "правом.",
     {"atoms": {"power": {"status": "Z", "means": "power is held"},
                "duty_to_explain": {"status": "Z",
                                    "means": "a duty to explain is owed"},
                "takes_itself_for_right":
                    {"status": "Z",
                     "means": "the power takes itself for a right"}},
      "assert": "imp(and(power, not(duty_to_explain)), "
                "takes_itself_for_right)"},
     "'Inevitably begins' encoded as the plain conditional; the temporal "
     "'begins' and the modal 'inevitably' are outside the axis."),

    (6, "Ответственность принадлежит тому, кто мог остановить последствие, "
        "но позволил ему произойти.",
     {"atoms": {"could_stop": {"status": "Z",
                               "means": "the person could stop the "
                                        "consequence"},
                "allowed": {"status": "Z",
                            "means": "the person allowed it to happen"},
                "responsible": {"status": "Z",
                                "means": "the person is responsible"}},
      "assert": "imp(and(could_stop, allowed), responsible)"},
     "A definition of responsibility by two conditions. 'Could' is a "
     "modality flattened to an atom — the core cannot see possibility."),

    (7, "Намерение определяет выбор, но поступок определяет реальность.",
     None,
     "DOES NOT FORMALIZE. Two claims of the form 'X determines Y' where "
     "'determines' is a relation between magnitudes, not a propositional "
     "connective. Encoding it as a conditional would substitute our "
     "reading for the claim; refused."),

    (8, "Добрая цель не исправляет действие, последствия которого человек "
        "отказался учитывать.",
     {"atoms": {"good_aim": {"status": "Z", "means": "the aim is good"},
                "refused_to_weigh": {"status": "Z",
                                     "means": "the person refused to weigh "
                                              "the consequences"},
                "act_redeemed": {"status": "Z",
                                 "means": "the act is redeemed"}},
      "assert": "imp(and(good_aim, refused_to_weigh), not(act_redeemed))"},
     "'Does not redeem' as a denial of the consequent under both "
     "conditions."),

    (9, "Ошибка становится опасной только после того, как её начинают "
        "защищать.",
     {"atoms": {"defended": {"status": "Z",
                             "means": "the error is being defended"},
                "dangerous": {"status": "Z",
                              "means": "the error is dangerous"}},
      "assert": "imp(dangerous, defended)"},
     "NOTE THE DIRECTION: 'only after' is a NECESSARY condition, so the "
     "arrow runs dangerous -> defended, not the reverse. Encoding it the "
     "intuitive way round would be a translation error of exactly the "
     "kind this protocol exists to expose."),

    (10, "Исправленная ошибка увеличивает знание, скрытая — увеличивает "
         "будущий ущерб.",
     {"atoms": {"corrected": {"status": "Z",
                              "means": "the error was corrected"},
                "concealed": {"status": "Z",
                              "means": "the error was concealed"},
                "knowledge_up": {"status": "Z", "means": "knowledge increases"},
                "future_damage_up": {"status": "Z",
                                     "means": "future damage increases"}},
      "assert": "and(imp(corrected, knowledge_up), "
                "imp(concealed, future_damage_up))"},
     "Two conditionals conjoined; the quantitative 'increases' is an atom."),

    (11, "Время не меняет истину, но лишает удобства тех, кто её "
         "откладывал.",
     {"atoms": {"time_passes": {"status": "Z", "means": "time passes"},
                "truth_changes": {"status": "Z", "means": "the truth changes"},
                "postponed": {"status": "Z",
                              "means": "the person postponed the truth"},
                "loses_comfort": {"status": "Z",
                                  "means": "the person loses comfort"}},
      "assert": "and(not(imp(time_passes, truth_changes)), "
                "imp(and(time_passes, postponed), loses_comfort))"},
     "First conjunct: time does not suffice for the truth to change. "
     "Second: time plus postponement costs comfort."),

    (12, "Решение, принятое слишком поздно, часто оказывается лишь "
         "признанием уже случившегося.",
     None,
     "DOES NOT FORMALIZE. 'Often' is a frequency claim — a degree the "
     "core cannot see (it has no probability axis; a hedged generality is "
     "neither a law nor a fact here). Forcing it into a bare conditional "
     "would drop precisely the word the aphorism leans on."),
]


def judge(entry):
    n, text, enc, note = entry
    print(f"\n{'=' * 74}\n{n}. {text}")
    if enc is None:
        print(f"   ENCODING: refused.\n   {note}")
        return "refused", None
    doc = {"genre": "statement", **enc}
    d, p, issues = zfl.validate(json.dumps(doc, ensure_ascii=False))
    hard = [i for i in issues if i["level"] == "error"]
    assert not hard, f"{n}: {hard}"
    rep = engine.logic_map(d, p)
    lm = rep["logic_map"]
    print(f"   FORMULA   {lm['formula']}")
    print(f"   READING   {note}")
    for a, spec in enc["atoms"].items():
        print(f"     · {a} = T means: {spec['means']}")
    cur = lm["currency"]
    print(f"   CURRENCY  {cur['kind']}"
          + (f"   witness {cur['witness']}" if cur.get("witness") else ""))
    print(f"   VERDICT   {rep['verdict']} / {rep['warranty']}")
    if rep.get("frame"):
        print(f"   FRAME     {rep['frame'][:70]}…")
    a = lm.get("audit")
    if a:
        print(f"   AUDIT     {a['status']}"
              + (f"  loan {a['loans']}" if a.get("loans") else "")
              + (f"  counterexample {a['counterexample']}"
                 if a.get("counterexample") else ""))
    warn = [i["code"] for i in issues if i["level"] == "warning"]
    if warn:
        print(f"   WARNINGS  {', '.join(sorted(set(warn)))}")
    return cur["kind"], rep["warranty"]


if __name__ == "__main__":
    print("=" * 74)
    print("APHORISMS FROM ANOTHER AI — judged by the ZTL core (blind test)")
    print("  the encoding is shown beside every verdict, for dispute")
    print("=" * 74)
    tally = {}
    for e in APHORISMS:
        kind, _ = judge(e)
        tally[kind] = tally.get(kind, 0) + 1
    print(f"\n{'=' * 74}\nTALLY")
    for k, v in sorted(tally.items()):
        print(f"  {k:12s} {v}")
    print("\n  Read the tally as logical hygiene, not as quality of thought:")
    print("  'contingent' is the honest home of a claim about the world —")
    print("  it means the claim CAN fail, and says under which assignment.")
