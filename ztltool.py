# -*- coding: utf-8 -*-
"""
ztltool — a closed, abstract tool over the unchanged ZTL core.

Not the studio (no web, no NL, no service): a self-contained instrument
that lives in the repository, that a fork downloads and runs for itself.
It does not touch the core — it only reads a formula, formalizes it, passes
it through the kernel (`ztl.ev`, `zverify.grade`), and reports what
happened. Deliberately abstract: no Veraxis, no certificates, no
institutional apparatus — those are specialised elsewhere, on top of this.

Three operations, and they are STEPWISE, not a batch pipeline. You hand it
one formula and it is checked; you hand it a second and it is checked; you
hand it both and an operator, and they are glued:

    check(text, marking)                 → what happened to this claim
    check(other, marking)                → what happened to that one
    join(text, other, operator, marking) → glue the two by the operator

"Formalize" here means parse a formula written in plain symbols
(~ ∧→&, | ∨, -> →, ^ ⊕, = ↔, parentheses) into the kernel's own form; the
kernel is unchanged and does the judging. A marking says which atoms are
verified (T/F) and which are not (Z, the default) — truth is never granted
on credit, so an unverified atom stays a mark.

Run:  python3 ztltool.py                 (a worked stepwise session)
      python3 ztltool.py -i              (interactive: check / join / mark)
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, VALUES, NOT, AND, OR, IMP, XOR, XNOR, ev  # noqa: E402
from zverify import grade                                          # noqa: E402

# ---- the operators a join may glue by (the kernel's own connectives) -------
BINOPS = {"∧": AND, "&": AND, "∨": OR, "|": OR, "→": IMP, "->": IMP,
          "⊕": XOR, "^": XOR, "↔": XNOR, "=": XNOR}
_OP_NAME = {"∧": "∧", "&": "∧", "∨": "∨", "|": "∨", "→": "→", "->": "→",
            "⊕": "⊕", "^": "⊕", "↔": "↔", "=": "↔"}


# --------------------------------------------------------------- formalize
def _tokens(s):
    out, i = [], 0
    two = {"->"}
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1
        elif s[i:i + 2] in two:
            out.append(s[i:i + 2]); i += 2
        elif c in "()~&|^=∧∨¬→⊕↔":
            out.append("¬" if c == "~" else c); i += 1
        elif c.isalnum() or c == "_":
            j = i
            while j < len(s) and (s[j].isalnum() or s[j] == "_"):
                j += 1
            out.append(s[i:j]); i = j
        else:
            raise ValueError(f"stray character {c!r}")
    return out


_BIN = {"&": "and", "∧": "and", "|": "or", "∨": "or", "->": "imp",
        "→": "imp", "^": "xor", "⊕": "xor", "=": "xnor", "↔": "xnor"}
_PREC = {"xnor": 1, "imp": 2, "xor": 3, "or": 4, "and": 5}


def formalize(text):
    """Parse a plainly-written formula into the kernel's AST. This is the
    'formalize' step; the kernel does the rest, unchanged."""
    toks = _tokens(text)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def eat():
        t = toks[pos[0]]; pos[0] += 1; return t

    def atom():
        t = peek()
        if t == "(":
            eat(); e = expr(0)
            if peek() != ")":
                raise ValueError("missing )")
            eat(); return e
        if t in ("¬", "~"):
            eat(); return ("not", atom())
        if t is None or t in _BIN or t == ")":
            raise ValueError("expected a formula")
        return eat()

    def expr(minp):
        left = atom()
        while True:
            t = peek()
            if t in _BIN and _PREC[_BIN[t]] >= minp:
                op = _BIN[eat()]
                right = expr(_PREC[op] + 1)
                left = (op, left, right)
            else:
                return left

    e = expr(0)
    if pos[0] != len(toks):
        raise ValueError("trailing input")
    return e


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi not in VALUES:
            acc.add(phi)
    else:
        for s in phi[1:]:
            _atoms(s, acc)
    return acc


def _show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + _show(phi[1])
    sign = {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}[phi[0]]
    return f"({_show(phi[1])} {sign} {_show(phi[2])})"


def _full(phi, marking):
    """Every atom gets a value; anything unspecified is Z (default deny of
    trust — never on credit)."""
    m = {a: Z for a in _atoms(phi)}
    m.update({k: v for k, v in (marking or {}).items()})
    return m


# ------------------------------------------------------------------- report
def _grade_marking(m):
    """zverify speaks the E12 mark dialect, where the mark symbol is 'M';
    ztltool marks the unverified atom with the value Z. Translate Z→'M' so
    the warranty grade actually SEES the marks — otherwise it finds none, the
    refinement set is a singleton, and every verdict reads 'hereditary'."""
    return {a: ("M" if v == Z else v) for a, v in m.items()}


def _happened(phi, m):
    """What the kernel did with one claim, as a dict."""
    v = ev(phi, m)
    g = grade(phi, _grade_marking(m))
    unver = sorted(a for a in _atoms(phi) if m.get(a, Z) == Z)
    return {"formula": _show(phi), "verdict": v, "grade": g,
            "marking": {a: m[a] for a in sorted(_atoms(phi))},
            "unverified": unver}


def check(text, marking=None):
    """Formalize one formula, pass it through the kernel, report what
    happened."""
    phi = formalize(text)
    return _happened(phi, _full(phi, marking))


def join(text_a, text_b, operator, marking=None):
    """Check both, then glue them by `operator` and report the join."""
    a, b = formalize(text_a), formalize(text_b)
    if operator not in BINOPS:
        return {"status": "REFUSED",
                "reason": f"{operator!r} is not a connective "
                          f"({'/'.join(sorted(set(_OP_NAME.values())))})"}
    m = _full(("and", a, b), marking)          # one shared marking for both
    ra, rb = _happened(a, m), _happened(b, m)
    vj = BINOPS[operator](ra["verdict"], rb["verdict"])
    gj = grade((_BIN[operator], a, b), _grade_marking(m))
    return {"left": ra, "right": rb, "operator": _OP_NAME[operator],
            "joined_formula": _show((_BIN[operator], a, b)),
            "verdict": vj, "grade": gj,
            "glued": vj == T,
            "reading": _read(_OP_NAME[operator], ra["verdict"],
                             rb["verdict"], vj)}


def judge(text, marking=None):
    """Triage a claim by its WARRANT, not merely its truth. The verdict alone
    cannot tell 'earned' from 'true-on-credit', nor 'refuted' from 'not yet
    established' — the warranty GRADE does, and it names the weak link.

      EARNED    verdict T, hereditary — grounded; any marks are irrelevant.
      REFUTED   verdict F, hereditary — false regardless of the marks.
      ON CREDIT verdict T, but not hereditary — true only while an unverified
                link holds; if it flips, the claim can die.
      OPEN      not established — a mark actually matters; verify it.

    This is the sort a plain truth-check and a proof kernel do NOT give: which
    conclusions ride on something unchecked, and exactly which link that is."""
    r = check(text, marking)
    v, g, unv = r["verdict"], r["grade"], r["unverified"]
    if g == "hereditary":
        if v == T:
            disp = "EARNED"
            why = ("grounded outright" if not unv
                   else f"grounded; the unverified {unv} do not matter")
        elif v == F:
            disp = "REFUTED"
            why = ("grounded false" if not unv
                   else f"false regardless of the unverified {unv}")
        else:
            disp, why = "OPEN", "not established"
    elif v == T:
        disp = "ON CREDIT"
        why = (f"true only on credit — rides the unverified {unv}; "
               "if one flips, the claim can die")
    else:
        disp = "OPEN"
        why = f"not established — verify {unv} (it could still turn either way)"
    return {**r, "disposition": disp, "why": why}


def load_claims(path):
    """Read a stream of claims from a file. One per line:

        label :: formula :: marks        (marks optional; unlisted atoms = Z)

    The field separator is '::', NOT '|' — '|' is the OR operator and must be
    free to appear inside a formula. '#' starts a comment; blank lines are
    skipped. Marks are `atom=T` / `atom=F` tokens, space-separated. Returns
    [(label, text, marking), ...]."""
    claims = []
    for raw in open(path, encoding="utf-8"):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        parts = [p.strip() for p in line.split("::")]
        if len(parts) < 2 or not parts[1]:
            raise ValueError(f"claim needs 'label :: formula [:: marks]': {raw!r}")
        marking = {}
        for tok in (parts[2].split() if len(parts) >= 3 else []):
            if "=" in tok:
                k, v = tok.split("=", 1)
                if v.upper() in VALUES:
                    marking[k] = v.upper()
        claims.append((parts[0], parts[1], marking))
    return claims


DISPOSITIONS = ("EARNED", "ON CREDIT", "OPEN", "REFUTED")


def ledger(claims):
    """Judge a whole stream and bucket it by disposition. `claims` is an
    iterable of (label, text, marking). Returns {'rows': [...], 'buckets':
    {disposition: [label, ...]}}."""
    rows, buckets = [], {d: [] for d in DISPOSITIONS}
    for label, text, mk in claims:
        r = judge(text, mk)
        r["label"] = label
        rows.append(r)
        buckets[r["disposition"]].append(label)
    return {"rows": rows, "buckets": buckets}


def what_if(text, marking=None):
    """The actionable half of the judge: for each still-unverified link, what
    verifying it would do to the claim. Returns [{atom, if_T, if_F, settles}],
    where `settles` means BOTH outcomes are terminal (EARNED/REFUTED) — i.e.
    checking that link resolves the claim whichever way it turns."""
    base = check(text, marking)
    known = {k: v for k, v in _full(formalize(text), marking).items() if v != Z}
    terminal = {"EARNED", "REFUTED"}
    out = []
    for a in base["unverified"]:
        d_t = judge(text, {**known, a: T})["disposition"]
        d_f = judge(text, {**known, a: F})["disposition"]
        out.append({"atom": a, "if_T": d_t, "if_F": d_f,
                    "settles": d_t in terminal and d_f in terminal})
    return out


def next_check(text, marking=None):
    """Recommend which unverified link to check next: one that settles the
    claim either way if possible, otherwise one that can settle it in at least
    one direction, otherwise the first open link. Returns the what_if entry, or
    None if there is nothing left to verify."""
    opts = what_if(text, marking)
    if not opts:
        return None
    terminal = {"EARNED", "REFUTED"}
    settling = [o for o in opts if o["settles"]]
    partial = [o for o in opts if not o["settles"]
               and (o["if_T"] in terminal or o["if_F"] in terminal)]
    return (settling or partial or opts)[0]


def _read(op, va, vb, vj):
    if vj == T:
        return f"glued: the {op}-claim is earned ({va} {op} {vb} = T)"
    if Z in (va, vb):
        return (f"not glued: a mark reached the join ({va} {op} {vb} = {vj}); "
                f"nothing spoke against, something is unverified")
    return f"not glued: {va} {op} {vb} = {vj} — the {op}-claim is not met"


# ------------------------------------------------------------------- display
def _print_check(r):
    print(f"    {r['formula']}   →   {r['verdict']}   ({r['grade']})")
    print(f"      marking: {r['marking']}"
          + (f"   unverified: {r['unverified']}" if r['unverified'] else ""))


def _print_judge(r):
    print(f"    {r['formula']}   →   {r['verdict']}  ({r['grade']})   "
          f"[{r['disposition']}]")
    print(f"      {r['why']}")


def _print_whatif(text, marking):
    r = judge(text, marking)
    _print_judge(r)
    nc = next_check(text, marking)
    if nc is None:
        print("      settled — nothing left to verify")
        return
    for o in what_if(text, marking):
        star = " ⇐ check this next" if o["atom"] == nc["atom"] else ""
        tag = "settles" if o["settles"] else "narrows"
        print(f"      verify {o['atom']:12s} →  T: {o['if_T']:9s} "
              f"F: {o['if_F']:9s} ({tag}){star}")


def _print_join(r):
    if r.get("status") == "REFUSED":
        print(f"    REFUSED — {r['reason']}"); return
    print(f"    left  {r['left']['formula']} → {r['left']['verdict']}")
    print(f"    right {r['right']['formula']} → {r['right']['verdict']}")
    print(f"    glue by {r['operator']}:  {r['joined_formula']} → "
          f"{r['verdict']}  ({r['grade']})")
    print(f"      {r['reading']}")


def _repl():
    print("ztltool — check <formula> [| p=T q=F] · judge <formula> [| marks] "
          "· whatif <formula> [| marks] · join <A> ~ <B> ~ <op> [| marks] "
          "· quit")
    while True:
        try:
            line = input("ztl> ").strip()
        except (EOFError, KeyboardInterrupt):
            print(); break
        if not line or line in ("quit", "exit"):
            break
        body, _, mtext = line.partition("|")
        marking = {}
        for tok in mtext.split():
            if "=" in tok:
                k, v = tok.split("=", 1)
                if v.upper() in VALUES:
                    marking[k] = v.upper()
        try:
            if body.startswith("check "):
                _print_check(check(body[6:].strip(), marking))
            elif body.startswith("judge "):
                _print_judge(judge(body[6:].strip(), marking))
            elif body.startswith("whatif "):
                _print_whatif(body[7:].strip(), marking)
            elif body.startswith("join "):
                parts = [p.strip() for p in body[5:].split("~")]
                if len(parts) != 3:
                    print("    usage: join <A> ~ <B> ~ <op>")
                else:
                    _print_join(join(parts[0], parts[1], parts[2], marking))
            else:
                print("    say 'check ...' or 'join A ~ B ~ op'")
        except ValueError as e:
            print(f"    formalize error: {e}")


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    if "-i" in sys.argv:
        _repl(); sys.exit()

    print("=" * 76)
    print("ztltool — a closed tool over the ZTL core: check, check, join")
    print("=" * 76)

    print("\n1. hand it one formula — it is formalized and checked:")
    _print_check(check("p -> q", {"p": T, "q": T}))

    print("\n2. hand it a second — checked on its own:")
    _print_check(check("~r", {"r": F}))

    print("\n3. hand it both and an operator — glued, with a report:")
    _print_join(join("p -> q", "~r", "∧", {"p": T, "q": T, "r": F}))

    print("\n4. one ground left unverified — the mark reaches the join:")
    _print_join(join("p", "q", "∧", {"p": T}))                 # q left Z

    print("\n5. the same two, a different operator — glued this time:")
    _print_join(join("p", "q", "∨", {"p": T}))                 # q left Z

    # honest self-check on the worked cases
    assert check("p -> q", {"p": T, "q": T})["verdict"] == T
    assert check("~r", {"r": F})["verdict"] == T
    assert join("p -> q", "~r", "∧", {"p": T, "q": T, "r": F})["glued"]
    _mark = join("p", "q", "∧", {"p": T})                       # q = Z
    assert _mark["right"]["verdict"] == Z and not _mark["glued"]
    assert join("p", "q", "∨", {"p": T})["verdict"] == T        # ∨ needs one
    # grade must be MEANINGFUL — regression guard for the Z→'M' translation
    # zverify's mark dialect needs. Without it every grade reads 'hereditary';
    # in particular the dangerous greedy T of ¬¬p (dies at p:=F) would be
    # mislabelled the safest grade instead of until-verification.
    assert check("~~p", {})["grade"] == "until-verification"    # the dangerous T
    assert check("b", {})["grade"] == "until-verification"      # a bare mark
    assert check("p & q", {"p": T, "q": T})["grade"] == "hereditary"  # grounded
    # the warrant judge and its actionable half
    assert judge("p & q", {"p": T, "q": T})["disposition"] == "EARNED"
    assert judge("~~p", {})["disposition"] == "ON CREDIT"       # T on credit
    _nc = next_check("p & q", {"p": T})                         # q still Z
    assert _nc["atom"] == "q" and _nc["settles"]                # checking q ends it
    assert not next_check("a & b", {})["settles"]               # one of two: narrows
    print("\n  ZTLTOOL GREEN — formalize · check · check · join · judge · "
          "whatif, over an unchanged core.")
