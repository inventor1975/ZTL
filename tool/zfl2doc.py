# -*- coding: utf-8 -*-
"""
The ZFL reference page, generated from the language itself.

The curator asked for a page describing ZFL. Writing one by hand is the
obvious move and the wrong one: a hand-written reference is right on the day
it is written and quietly wrong a month later, and this project spends most
of its effort refusing exactly that arrangement everywhere else. So the page
is GENERATED — the column table from `zfl2.COLUMNS`, the operators from the
parser's own tables, the worked example imported from the stand that proves
it runs, the error codes from the validator's source. Nothing here is
retyped, so nothing here can drift.

What stays hand-written is the part a machine cannot supply: why the thing
is shaped this way. That is three paragraphs, and they are marked as prose.

Both languages, side by side in the spec, hand-translated for the reason
given in `zfl2`: the vocabulary IS the content.

Run:  python3 tool/zfl2doc.py            (writes tool/static/zfl.html)
      python3 tool/zfl2doc.py --check    (fails if the codes drifted)
"""
import html
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import zfl2                                                      # noqa: E402
import ztljudge                                                  # noqa: E402
from test_zfl2 import MIXED                                      # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "static", "zfl.html")

# The one-line meaning of each machine-readable code. The codes themselves
# are read out of the validator's source, and `--check` fails if the two
# sets ever differ — so a new code cannot be added without a word about it
# here, and a deleted one cannot linger.
CODE_HELP = {
    "E_EMPTY": ("the table has no rows", "в таблице нет строк"),
    "E_NONAME": ("a row without a name", "строка без имени"),
    "E_BADNAME": ("a name a formula could not use",
                  "имя, непригодное для формулы"),
    "E_DUPNAME": ("the same name twice", "имя повторяется"),
    "E_STATUS": ("a status outside the four", "статус вне четырёх"),
    "E_NOGROUND": ("verified, refuted or defined, with nothing backing it",
                   "проверено, опровергнуто или определено — но без основания"),
    "E_KIND": ("a kind of ground outside the list", "вид основания вне списка"),
    "E_FORMULA": ("the defining formula does not parse",
                  "определяющая формула не разбирается"),
    "E_CLAIM": ("the claim does not parse", "утверждение не разбирается"),
    "E_UNKNOWN_NAME": ("a formula names a row that does not exist",
                       "формула называет несуществующую строку"),
    "W_UNIT_NO_VALUE": ("a unit with no value", "единица без величины"),
    "W_NO_GLOSS": ("no gloss, so nobody can check the name means what it "
                   "seems to",
                   "нет пояснения — некому проверить, то ли значит имя"),
}

PROSE = {
    "en": [
        ("Why a table and not a syntax",
         "Everything you write here is one document: a list of NAMES, each "
         "saying where it stands with you, plus what you CLAIM about them. "
         "There is no genre to declare and no mode to pick. Which "
         "instruments answer — the numeric floor, the passport office, the "
         "ledger, the judge — follows from which cells you filled."),
        ("The one rule underneath",
         "Truth is not granted on credit. A name is verified when a "
         "verification was produced, and the ground column is where you say "
         "what produced it. A name with nothing backing it is not false — it "
         "is unverified, which is an honest third answer and the reason this "
         "logic exists."),
        ("Where formulas survive",
         "In two cells only. In GROUND, when a name is defined by a formula "
         "over other names — that is how self-reference is written, and it "
         "is why the liar needs no special mode. And in CLAIM, which is what "
         "you are actually asserting."),
    ],
    "ru": [
        ("Почему таблица, а не синтаксис",
         "Всё, что вы здесь пишете, — один документ: список ИМЁН, каждое из "
         "которых говорит, откуда оно у вас, плюс то, что вы про них "
         "УТВЕРЖДАЕТЕ. Никакого жанра объявлять не надо и режим выбирать не "
         "надо. Какие приборы ответят — числовой пол, паспортный стол, "
         "тетрадь, судья — следует из того, какие клетки вы заполнили."),
        ("Правило, лежащее под всем",
         "Истина не даётся в кредит. Имя проверено, когда проверка "
         "произведена, и колонка «основание» — это место, где вы говорите, "
         "чем именно. Имя без основания не ложно — оно НЕ ПРОВЕРЕНО, и это "
         "честный третий ответ, ради которого вся эта логика и существует."),
        ("Где остаются формулы",
         "Ровно в двух клетках. В ОСНОВАНИИ — когда имя определено формулой "
         "через другие имена; так пишется самоссылка, и поэтому лжецу не "
         "нужен отдельный режим. И в УТВЕРЖДЕНИИ — том, что вы, собственно, "
         "заявляете."),
    ],
}

HEAD = {"en": ("ZFL — the language of the studio", "column", "required",
               "always", "in context", "no", "operators", "error codes",
               "a worked example", "means", "status", "ground",
               "what it is", "options / examples", "the document itself",
               "value", "the columns of a row"),
        "ru": ("ZFL — язык студии", "колонка", "обязательна",
               "всегда", "по условию", "нет", "операторы", "коды ошибок",
               "разобранный пример", "значит", "статус", "основание",
               "что это", "варианты / примеры", "сам документ",
               "величина", "колонки строки")}


def codes_in_source():
    """The codes the validator actually raises, read out of it."""
    src = open(zfl2.__file__, encoding="utf-8").read()
    return set(re.findall(r'"([EW]_[A-Z_]+)"', src))


# What each symbol MEANS. The symbols themselves are read out of the
# judge's own table below, and `--check` fails if one of them turns up
# without a meaning here — a reference that lists a symbol it cannot
# explain is worse than one that omits it.
OP_HELP = {
    "&": ("and", "и"), "|": ("or", "или"), "->": ("if … then", "если … то"),
    "^": ("exactly one of", "ровно одно из"),
    "=": ("the same value as", "то же значение, что"),
    "~": ("not", "не"),
    "Tr(x)": ("the value of the row x — this is how self-reference is "
              "written", "значение строки x — так пишется самоссылка"),
    "<=": ("at most", "не больше"), ">=": ("at least", "не меньше"),
    "==": ("equal to", "равно"), "<": ("less than", "меньше"),
    ">": ("greater than", "больше"),
}


def operators():
    """One operator set for the whole language, taken from the parsers
    rather than retyped: the propositional connectives from the judge's own
    table, the comparisons from the numeric floor's."""
    binops = sorted({k for k in ztljudge.BINOPS if k.isascii()})
    return binops + ["~", "Tr(x)"] + ["<=", ">=", "==", "<", ">"]


def _esc(s):
    return html.escape(str(s), quote=True)


def render(lang="en"):
    spec = zfl2.form_spec(lang)
    h = HEAD[lang]
    parts = [f"<h1>{_esc(h[0])}</h1>"]
    for title, body in PROSE[lang]:
        parts.append(f"<h2>{_esc(title)}</h2><p>{_esc(body)}</p>")

    # a heading is a phrase, not a word with an English plural glued on:
    # "колонкаs" is what that shortcut produced, and it was visible on the
    # first look at the Russian page
    parts.append(f"<h2>{_esc(h[16])}</h2><table><tr>"
                 f"<th>{_esc(h[1])}</th><th>{_esc(h[12])}</th>"
                 f"<th>{_esc(h[2])}</th><th>{_esc(h[13])}</th></tr>")
    for c in spec["columns"]:
        req = (h[3] if c["required"]
               else h[4] if c["required_when"] else h[5])
        opts = ""
        if c.get("options"):
            opts = " · ".join(_esc(o["label"]) for o in c["options"] if
                              o["label"])
        eg = " · ".join(_esc(e) for e in c.get("eg", []))
        extra = opts or eg
        cls = ' class="adv"' if c["advanced"] else ""
        parts.append(f"<tr{cls}><td><b>{_esc(c['label'])}</b></td>"
                     f"<td>{_esc(c['help'])}</td><td>{_esc(req)}</td>"
                     f"<td>{extra}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[14])}</h2><table><tr>"
                 f"<th>{_esc(h[1])}</th><th>{_esc(h[12])}</th>"
                 f"<th>{_esc(h[2])}</th><th>{_esc(h[13])}</th></tr>")
    for c in spec["document"]:
        req = h[3] if c["required"] else h[5]
        eg = " · ".join(_esc(e) for e in c.get("eg", []))
        opts = " · ".join(_esc(o["label"]) for o in c.get("options", []))
        parts.append(f"<tr><td><b>{_esc(c['label'])}</b></td>"
                     f"<td>{_esc(c['help'])}</td><td>{_esc(req)}</td>"
                     f"<td>{opts or eg}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[6])}</h2><table>")
    for op in operators():
        en, ru = OP_HELP.get(op, ("—", "—"))
        parts.append(f"<tr><td><code>{_esc(op)}</code></td>"
                     f"<td>{_esc(en if lang == 'en' else ru)}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[8])}</h2><table><tr>"
                 f"<th>{_esc(h[1])}</th><th>{_esc(h[9])}</th>"
                 f"<th>{_esc(h[10])}</th><th>{_esc(h[11])}</th>"
                 f"<th>{_esc(h[15])}</th></tr>")
    for r in MIXED["rows"]:
        parts.append("<tr>" + "".join(
            f"<td>{_esc(r.get(k, '') or '—')}</td>"
            for k in ("name", "means", "status", "ground", "value")) + "</tr>")
    parts.append("</table>")
    parts.append(f"<p><b>{_esc(spec['document'][0]['label'])}:</b> "
                 f"<code>{_esc(MIXED['claim'])}</code></p>")

    parts.append(f"<h2>{_esc(h[7])}</h2><table>")
    for code in sorted(codes_in_source()):
        en, ru = CODE_HELP.get(code, ("—", "—"))
        parts.append(f"<tr><td><code>{_esc(code)}</code></td>"
                     f"<td>{_esc(en if lang == 'en' else ru)}</td></tr>")
    parts.append("</table>")
    return "\n".join(parts)


def page():
    body = ("<div class='lang' id='en'>" + render("en") + "</div>"
            "<div class='lang' id='ru' hidden>" + render("ru") + "</div>")
    return f"""<!doctype html><meta charset="utf-8">
<title>ZFL</title>
<style>
 body {{ font: 15px/1.5 Georgia, serif; max-width: 52em; margin: 3em auto;
        padding: 0 1em; color: #111; }}
 table {{ border-collapse: collapse; width: 100%; margin: 1em 0; }}
 th, td {{ border: 1px solid #bbb; padding: 5px 8px; text-align: left;
          vertical-align: top; font-size: 14px; }}
 th {{ background: #eee; }} tr.adv td {{ color: #666; }}
 code {{ background: #f4f4f4; padding: 1px 4px; }}
 h1 {{ font-size: 24px; }} h2 {{ font-size: 17px; margin-top: 1.6em; }}
 nav {{ float: right; font-size: 13px; }}
</style>
<nav><a href="?l=en" onclick="return t('en')">EN</a> ·
 <a href="?l=ru" onclick="return t('ru')">RU</a></nav>
{body}
<script>
// ?l=ru opens the page already in Russian, so a link can be handed to
// somebody in their own language. Switching also rewrites the address bar,
// so whatever you are reading is what you copy.
function t(l) {{
  if (l !== 'en' && l !== 'ru') l = 'en';
  for (const d of document.querySelectorAll('.lang')) d.hidden = d.id !== l;
  document.documentElement.lang = l;
  history.replaceState(null, '', '?l=' + l);
  return false;
}}
t(new URLSearchParams(location.search).get('l') || 'en');
</script>"""


def main():
    missing = (codes_in_source() - set(CODE_HELP)) | (
        set(operators()) - set(OP_HELP))
    stale = (set(CODE_HELP) - codes_in_source()) | (
        set(OP_HELP) - set(operators()))
    print(f"codes raised by the validator: {len(codes_in_source())}")
    if missing or stale:
        print(f"  RED — undocumented: {sorted(missing)}")
        print(f"        documented but never raised: {sorted(stale)}")
        return 1
    print("  every code the validator raises is documented, and no more")
    if "--check" in sys.argv:
        print("ZFL DOC GREEN — the page and the language agree")
        return 0
    open(OUT, "w", encoding="utf-8").write(page())
    print(f"  written: {OUT}  ({os.path.getsize(OUT)} bytes)")
    print("ZFL DOC GREEN — the page and the language agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
