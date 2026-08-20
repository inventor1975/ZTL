# -*- coding: utf-8 -*-
"""
ztljudge — a closed, abstract tool over the unchanged ZTL core.

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

Run:  python3 ztljudge.py                 (a worked stepwise session)
      python3 ztljudge.py -i              (interactive: check / join / mark)
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, VALUES, NOT, AND, OR, IMP, XOR, XNOR, ev  # noqa: E402
from zverify import grade                                          # noqa: E402

# The mark of a MISSING SUBJECT. Spelled out here rather than imported: `znum`
# imports this module, so the dependency may not run the other way. It is the
# same symbol and the same meaning as `znum.E` — and the same disposition the
# numeric floor has carried since 2026-08-12, where no admissible reading of a
# comparison exists. That floor could reach it (an empty domain names itself);
# this one could not, because a plain atom has no domain to be empty. Now it
# can, by DECLARATION: a marking may say `{"weapon_carries_trace": E}`.
E = "E"

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


def _kernel(m):
    """What the KERNEL is allowed to see. An absent subject reaches the
    connectives as an ordinary mark, and this is a measured decision, not a
    convenience: distinguishing 'no subject' from 'not yet checked' changes no
    verdict anywhere (`lab/desc/`), because E is not a value of the logic — it
    is a fact about the claim's subject. So the kernel is left exactly as it
    was, and the distinction is spent where it was measured to bite: on the
    DISPOSITION and on the order to verify."""
    return {a: (Z if v == E else v) for a, v in m.items()}


# ------------------------------------------------------------------- report
def _grade_marking(m):
    """zverify speaks the E12 mark dialect, where the mark symbol is 'M';
    ztljudge marks the unverified atom with the value Z. Translate Z→'M' so
    the warranty grade actually SEES the marks — otherwise it finds none, the
    refinement set is a singleton, and every verdict reads 'hereditary'."""
    return {a: ("M" if v in (Z, E) else v) for a, v in m.items()}


def _lazy(phi, m):
    """The LAZY register, and a label saying who is responsible.

    Returns (value, atoms). The greedy register decides — it burns the
    mark and answers now. This one waits: Kleene's tables, where an
    unchecked atom survives negation (~Z is Z, not F) and is ABSORBED by a
    decisive partner (Z & F is F, Z | T is T). That absorption is the
    useful part: it means a hole only keeps the answer pending while it is
    LOAD-BEARING, so the responsible atoms fall out of one evaluation
    instead of n probes.

    The label tracks UNCHECKED atoms only, and it is a SOUND
    OVER-APPROXIMATION of the load-bearing ones. The sound half is now
    PROVED, not merely measured: `lean/Receipt.lean`, `receipt_complete`,
    empty axiom list — for the whole language and every valuation, an
    unverified atom the label omits cannot change the answer. Read the
    other way, an atom that could change it is always on the receipt, so
    a refusal never withholds a verdict for a reason it failed to name.
    (The Lean `labF` is this function, asked of both engines rather than
    argued: `bridge.py`, 609 questions, zero divergences.)

    AND IT COVERS THE VERDICT, not only this column. `pending` is printed
    beside a GREEDY verdict, and `receipt_complete_greedy` proves the
    same guarantee there — an unverified atom off the label cannot move
    `ev` either. That was measured before it was proved and I had
    predicted the opposite: the greedy register is non-monotone, so a
    branch Kleene calls decisive looked like where the receipt would
    leak. It does not, because whenever the lazy register commits the
    greedy one agrees with it (`greedy_agrees_when_decided`), and the
    greedy tables absorb exactly where the label drops a branch.

    THE OVER-APPROXIMATION IS MUCH SMALLER THAN WE SAID (measured
    2026-08-20, `lab/label/`). The earlier figures — 16% of pending cells
    at depth 2, 35% at depth 6 — counted an atom as innocent when no
    change to it ALONE moved the answer. That probe is too weak: this
    corpus's own width measurement shows cells where no single ground
    moves the matter and a pair does. Against the right notion — the
    union of minimal JOINTLY moving sets — the label is EXACT in 93% of
    cells, and never once too small (14,530 cells, zero violations).

    The remaining 7% is a genuine over-approximation and it has one
    cause. `p ∧ (p ∨ q)` with both unverified names `q`, which cannot
    move anything: the analysis reads the two branches independently,
    sees the right one could reach F, and does not notice that it gets
    there only when `p` is F — at which point the left branch has already
    decided the matter. Occurrence-independence again, the same root as
    `¬¬Z = T` and as the lost tautologies.

    NOT CLOSABLE BY DEMAND PROPAGATION — tried and measured. A
    demand-driven label over reachable sibling values was built as a
    prototype and matched this one cell for cell: same 93%, not one cell
    narrower. The existing label already IS that analysis. Closing the 7%
    needs relational tracking of shared occurrences across branches,
    which is not cheap.
    The first draft of this docstring claimed "carriers for free in one
    pass", which the measurement refused. (Label propagation of this
    kind is old — de Kleer's ATMS, 1986 — and is named here rather than
    presented as new. A first draft also reported a `justified_by` field
    for decided values; it was always empty, because a label of holes
    cannot say who decided. The field was removed rather than renamed.)"""
    if isinstance(phi, str):
        v = m.get(phi, Z)
        return (v, {phi}) if v == Z else (v, set())
    op = phi[0]
    if op == "not":
        v, lab = _lazy(phi[1], m)
        return ({T: F, F: T, Z: Z}[v], lab)
    (a, la), (b, lb) = _lazy(phi[1], m), _lazy(phi[2], m)
    if op == "and":
        if a == F:
            return F, la
        if b == F:
            return F, lb
        return (T, set()) if a == b == T else (Z, la | lb)
    if op == "or":
        if a == T:
            return T, la
        if b == T:
            return T, lb
        return (F, set()) if a == b == F else (Z, la | lb)
    if op == "imp":
        return _lazy(("or", ("not", phi[1]), phi[2]), m)
    if op in ("xnor", "xor"):
        if Z in (a, b):
            return Z, la | lb
        same = (a == b)
        return (T if (same if op == "xnor" else not same) else F), set()
    raise ValueError(op)


def _happened(phi, m):
    """What the kernel did with one claim, as a dict."""
    k = _kernel(m)
    v = ev(phi, k)
    g = grade(phi, _grade_marking(m))
    unver = sorted(a for a in _atoms(phi) if m.get(a, Z) == Z)
    gone = sorted(a for a in _atoms(phi) if m.get(a) == E)
    lv, lab = _lazy(phi, k)
    return {"formula": _show(phi), "verdict": v, "grade": g,
            "marking": {a: m[a] for a in sorted(_atoms(phi))},
            "unverified": unver,
            # NOT a sub-list of `unverified`, and the separation is the whole
            # point: an unverified atom is an open question, an absent one is
            # no question at all. Nothing may be ASKED of the atoms named here.
            "absent": gone,
            # the second register, as a COLUMN beside the verdict and
            # never in place of it: greedy says whether to sign, lazy says
            # whether the matter is still running
            "lazy": lv,
            "pending": sorted(lab) if lv == Z else []}


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


def _moves(phi, m, a):
    """Would filling this one ground move the matter — verdict or grade?

    Deliberately NOT via `what_if`: that calls `judge`, and `judge` calls this,
    so the kernel is asked directly. Cheap, and no recursion."""
    v = ev(phi, _kernel(m))
    g = grade(phi, _grade_marking(m))
    for val in (T, F):
        m2 = dict(m); m2[a] = val
        if (ev(phi, _kernel(m2)) != v
                or grade(phi, _grade_marking(m2)) != g):
            return True
    return False


def _joint(phi, m, unv):
    """The grounds that must be filled TOGETHER, when no single one will do.

    Measured 2026-08-19 (`lab/width/`): for 91-93% of unsettled claims some
    single ground moves the matter, and inquiry is incremental. For the rest it
    is not — and the width goes as high as the number of unverified grounds, 4
    of 4 and 5 of 5 in the hunt. There a one-ground order is worse than none:
    it names a check that provably achieves nothing on its own.

    This does NOT compute the exact width. That search is exponential in the
    number of marks and buys little; what a reader needs is the difference
    between "go check this" and "no single check will move this", and that
    costs two kernel calls per ground.

    (The xor chain was my predicted witness and it was wrong: `p ⊕ q ⊕ r` has
    width 1, because the inner xor collapses to a definite value and the outer
    one is sensitive to the last ground alone. The wide cases are irregular.)"""
    if len(unv) < 2:
        return []
    return [] if any(_moves(phi, m, a) for a in unv) else list(unv)


def joint_grounds(phi, marking=None):
    """PUBLIC: the grounds that must be filled TOGETHER, for a kernel AST.

    Exists because the studio needs this and must not recompute it — the judge
    decides, the studio displays. Takes the AST rather than text, since a
    caller that has already parsed should not serialise back and re-parse.

    Returns `[]` when some single ground moves the matter, which is the
    ordinary case (91-93%, `lab/width/`)."""
    m = _full(phi, marking)
    unv = sorted(a for a, v in m.items() if v == Z)
    return _joint(phi, m, unv)


def _besides(unv, gone):
    """Name what did not matter — without pretending the two are one thing."""
    bits = []
    if unv:
        bits.append(f"the unverified {unv}")
    if gone:
        bits.append(f"the subjectless {gone}")
    return " nor ".join(bits)


def _forgone(text, marking, gone, disp):
    """What declaring a subject ABSENT cost — the audit line that keeps `E`
    from being a trapdoor.

    Asked by the curator 2026-08-19: is this Tarski's move, sending the bullet
    up a level where it cannot be stated? The declaration does come from
    outside the judge, exactly as a boundary does, so the danger is real in its
    practical form — declare `E` on the inconvenient atom and the judge stops
    asking. `zboundary` already answers that shape by printing which excluded
    readings would have CHANGED the verdict. This is the same receipt: restore
    the absent subjects, and report the settlement the declaration removed.

    An `E` that costs a settlement is a heavy claim about the world and should
    be contested on the world. One that costs nothing was never load-bearing.

    BILL ONLY WHAT WAS TAKEN. The first version of this reported the settlement
    a restored subject would reach, and the corpus's own regression refused it:
    on `present ∨ trace` the matter is EARNED already, so a check that "would
    have settled the claim" takes nothing away — the label was lying about
    arithmetic that was right. A claim already terminal without the subject has
    forgone nothing, whatever a restored probe could reach."""
    if disp in ("EARNED", "REFUTED"):
        return []
    restored = {a: (Z if v == E else v)
                for a, v in _full(formalize(text), marking).items()}
    out = []
    for o in what_if(text, restored):
        if o["atom"] in gone:
            out.append({"atom": o["atom"],
                        "would_have": ("settled the claim" if o["settles"] else
                                       "narrowed it")})
    return out


def _no_subject(gone):
    return (f"not established, and it cannot become established: {gone} has no "
            "subject, so there is nothing to verify. The cure is to repair the "
            "claim or withdraw it — and the silence must not be read as an "
            "answer in either direction")


def judge(text, marking=None):
    """Triage a claim by its WARRANT, not merely its truth. The verdict alone
    cannot tell 'earned' from 'true-on-credit', nor 'refuted' from 'not yet
    established' — the warranty GRADE does, and it names the weak link.

      EARNED    verdict T, hereditary — grounded; any marks are irrelevant.
      REFUTED   verdict F, hereditary — false regardless of the marks.
      ON CREDIT verdict T, but not hereditary — true only while an unverified
                link holds; if it flips, the claim can die.
      OPEN      not established — a mark actually matters; verify it.
      E         not established, and it CANNOT BE: what the claim rests on has
                no subject. Not a fifth kind of ignorance — the same fourth
                corner `znumjudge` has reported since 2026-08-12, arriving here
                by declaration instead of by an empty numeric domain.

    OPEN and E are the distinction the whole of `lab/desc/` was built to
    measure, and the curator's case states it in one line: "the weapon has not
    been identified" is OPEN — the object exists, the question stands, the
    matter proceeds. "No weapon was entered into the case" is E — there is
    nothing to judge on that point, and its silence is not an answer in either
    direction. Under one mark for both, the judge issues a verification order
    that can never be filled.

    This is the sort a plain truth-check and a proof kernel do NOT give: which
    conclusions ride on something unchecked, and exactly which link that is."""
    r = check(text, marking)
    v, g, unv, gone = (r["verdict"], r["grade"],
                       r["unverified"], r["absent"])
    if g == "hereditary":
        if v == T:
            disp = "EARNED"
            why = (f"grounded; {_besides(unv, gone)} do not matter"
                   if unv or gone else "grounded outright")
        elif v == F:
            disp = "REFUTED"
            why = (f"false regardless of {_besides(unv, gone)}"
                   if unv or gone else "grounded false")
        elif gone and not unv:
            disp, why = "E", _no_subject(gone)
        else:
            disp, why = "OPEN", "not established"
    elif v == T:
        # Still T, and still on credit: the verdict is not the judge's to
        # revise here. What changes is whether the credit can EVER be redeemed.
        disp = "ON CREDIT"
        why = (f"true only on credit — rides the unverified {unv}; "
               "if one flips, the claim can die" if unv else
               f"true only on credit, and the credit CANNOT BE REDEEMED — it "
               f"rides {gone}, which has no subject to verify")
        if unv and gone:
            why += f"; and {gone} cannot be verified at all — no subject"
    elif gone and not unv:
        disp, why = "E", _no_subject(gone)
    else:
        disp = "OPEN"
        why = f"not established — verify {unv} (it could still turn either way)"
        if gone:
            why += f"; {gone} is not on that list — it has no subject"
    # The declaration is billed, always — an absence that removes a settlement
    # is a claim about the world, and must be contestable as one.
    phi = formalize(text)
    joint = ([] if disp in ("EARNED", "REFUTED", "E")
             else _joint(phi, _full(phi, marking), unv))
    if joint:
        why += (f"; and NO SINGLE ground moves it — {joint} must be filled"
                f" together, so a one-at-a-time order would be empty work")
    return {**r, "disposition": disp, "why": why, "joint": joint,
            "forgone": _forgone(text, marking, gone, disp) if gone else []}


def absence_report(phi, marking=None):
    """PUBLIC: what a DECLARED absence costs, for a kernel AST.

    Same reason as `joint_grounds`: the studio must display this, not compute
    it. Goes through `judge` on the judge's own rendering of the AST, which
    round-trips exactly (`_show` and `formalize` are the same module's pair).

    Returns the absent grounds, the disposition, and the BILL — which
    settlement the declaration removed. The bill is the guard that keeps a
    declaration of absence from being a trapdoor."""
    r = judge(_show(phi), marking)
    return {"absent": r["absent"], "forgone": r["forgone"],
            "disposition": r["disposition"], "why": r["why"]}


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


DISPOSITIONS = ("EARNED", "ON CREDIT", "OPEN", "REFUTED", "E")


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
    checking that link resolves the claim whichever way it turns.

    An atom declared to have NO SUBJECT never appears here. Probing it would
    ask what happens 'if the weapon turns out to carry the trace' when no
    weapon was entered — a question with no procedure behind it. The list is
    an order to be filled, so an order that cannot be filled is not issued."""
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
    None if there is nothing left to verify.

    `None` now carries three different situations, and the caller must not read
    them alike: everything relevant is settled, OR what the claim rests on has
    no subject and no amount of checking will reach it, OR the matter is already
    decided hereditarily and further checking cannot move it. The disposition
    tells which — `E` for the second, `EARNED`/`REFUTED` for the third — and
    `judge(...)["why"]` names the cure, which for `E` is to REPAIR the claim
    rather than verify anything.

    THE THIRD CASE WAS A DEFECT UNTIL 2026-08-19, and Meno found it. This
    returned an order whenever an unverified atom EXISTED, not when one was
    worth checking, so `p ∧ q` with `p = F` — verdict F, grade hereditary,
    disposition REFUTED, the matter closed — still sent the reader off to
    verify `q`. Measured before it was fixed (`lab/meno/`): 27% of settled
    cells over the depth-2 pool, 30% over a random depth-4 sample. Meno's first
    horn says you cannot search for what you know; the judge was doing exactly
    that, and printing it as an instruction."""
    if judge(text, marking)["disposition"] in ("EARNED", "REFUTED"):
        return None
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
        print("      settled — nothing left to verify" if not r["absent"]
              else f"      NO ORDER ISSUED — {r['absent']} has no subject; "
                   f"there is nothing to go and check")
        _print_forgone(r)
        return
    for o in what_if(text, marking):
        star = " ⇐ check this next" if o["atom"] == nc["atom"] else ""
        tag = "settles" if o["settles"] else "narrows"
        print(f"      verify {o['atom']:12s} →  T: {o['if_T']:9s} "
              f"F: {o['if_F']:9s} ({tag}){star}")
    _print_forgone(r)


def _print_forgone(r):
    for f in r.get("forgone", []):
        print(f"      COST OF THE DECLARATION: had {f['atom']} had a subject, "
              f"checking it would have {f['would_have']}")


def _print_join(r):
    if r.get("status") == "REFUSED":
        print(f"    REFUSED — {r['reason']}"); return
    print(f"    left  {r['left']['formula']} → {r['left']['verdict']}")
    print(f"    right {r['right']['formula']} → {r['right']['verdict']}")
    print(f"    glue by {r['operator']}:  {r['joined_formula']} → "
          f"{r['verdict']}  ({r['grade']})")
    print(f"      {r['reading']}")


def _repl():
    print("ztljudge — check <formula> [| p=T q=F] · judge <formula> [| marks] "
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
    print("ztljudge — a closed tool over the ZTL core: check, check, join")
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
    # ---- the fourth corner, reached by declaration (2026-08-19)
    print("\n  NO SUBJECT vs NOT YET CHECKED — the two silences")
    _CASE = "weapon_carries_trace & suspect_was_present"
    for _label, _mk in (
            ("the weapon has not been identified",
             {"suspect_was_present": T}),
            ("no weapon was entered into the case",
             {"suspect_was_present": T, "weapon_carries_trace": E})):
        print(f"    {_label}")
        _print_whatif(_CASE, _mk)
    # the verdict is the SAME in both — E is not a value of the logic
    assert (judge(_CASE, {"suspect_was_present": T})["verdict"]
            == judge(_CASE, {"suspect_was_present": T,
                             "weapon_carries_trace": E})["verdict"] == F)
    # what differs is the disposition and the order
    assert judge(_CASE, {"suspect_was_present": T})["disposition"] == "OPEN"
    _r = judge(_CASE, {"suspect_was_present": T, "weapon_carries_trace": E})
    assert _r["disposition"] == "E" and _r["absent"] == ["weapon_carries_trace"]
    assert _r["unverified"] == []                # absent is NOT unverified
    # THE FIX ITSELF: no order is issued that could not be filled
    assert next_check(_CASE, {"suspect_was_present": T})["atom"] \
        == "weapon_carries_trace"
    assert next_check(_CASE, {"suspect_was_present": T,
                              "weapon_carries_trace": E}) is None
    # Meno's first horn: no order on a matter already decided (2026-08-19).
    assert judge("p & q", {"p": F})["disposition"] == "REFUTED"
    assert next_check("p & q", {"p": F}) is None       # q is unverified and moot
    assert next_check("p | q", {"p": T}) is None       # earned; nothing to seek
    # ...and Meno's residue: claims where NO single ground moves anything, so a
    # one-at-a-time order is empty work. Measured in lab/width/: 6-7% of
    # unsettled cells, and the width reaches the number of grounds.
    assert judge("p ^ q", {})["joint"] == ["p", "q"]
    assert judge("p = q", {})["joint"] == ["p", "q"]
    assert judge("p & q", {})["joint"] == []          # here one ground does move it
    print("\n  THE WIDTH OF AN INQUIRY — where step-by-step is not possible")
    for _t in ("p & q", "p ^ q"):
        _w = judge(_t, {})
        print(f"    {_t:8} {_w['disposition']:6} joint={_w['joint']}"
              + ("   one ground at a time works" if not _w["joint"]
                 else "   no single ground moves it"))
    # and a case that stands on OTHER grounds is untouched by the absence
    _stands = judge("suspect_was_present | weapon_carries_trace",
                    {"suspect_was_present": T, "weapon_carries_trace": E})
    assert _stands["disposition"] == "EARNED"
    print("    a missing subject halts its own predicate, never the matter:")
    print(f"    'present ∨ trace' with the weapon absent → "
          f"{_stands['disposition']}")
    # THE DECLARATION IS BILLED — the guard against E as a trapdoor. Asked by
    # the curator: is this Tarski, sending the bullet up a level? It is not,
    # while the level-shift prints what it took away.
    assert _r["forgone"] == [{"atom": "weapon_carries_trace",
                              "would_have": "settled the claim"}]
    # ...and takes NOTHING when the matter already stands: the first draft of
    # this receipt billed a settlement here too, and this line refused it.
    assert _stands["forgone"] == []
    print(f"    and the declaration is billed: {_r['forgone'][0]['would_have']}"
          f" — while on standing grounds it costs {_stands['forgone']}")
    # ---- the second register, measured against an honest probe
    print("\n  THE LAZY COLUMN — pause told from denial, and which holes "
          "matter")
    from ztime import depth2_pool
    cells = covered = extra = 0
    for phi in depth2_pool():
        for va in (T, F, Z):
            for vb in (T, F, Z):
                m = {"p": va, "q": vb}
                lv, lab = _lazy(phi, m)
                if lv != Z:
                    continue
                probe = set()
                for a in ("p", "q"):
                    if m[a] != Z:
                        continue
                    for val in (T, F):
                        m2 = dict(m)
                        m2[a] = val
                        if _lazy(phi, m2)[0] != lv:
                            probe.add(a)
                            break
                cells += 1
                covered += (probe <= lab)
                extra += bool(lab - probe)
    print(f"    pending cells checked: {cells}")
    print(f"    label covered every load-bearing hole: {covered}")
    print(f"    label also named an innocent one: {extra}")
    assert covered == cells and cells > 10000
    # ...and the same probe against the register that SIGNS. `pending` sits one
    # column from the greedy verdict, so it had better cover that too — proved
    # in `receipt_complete_greedy`, guarded here so the claim cannot rot.
    gcells = gmiss = 0
    for phi in depth2_pool():
        for va in (T, F, Z):
            for vb in (T, F, Z):
                m = {"p": va, "q": vb}
                if Z not in (va, vb):
                    continue
                gv = ev(phi, m)
                lab = _lazy(phi, m)[1]
                for a in ("p", "q"):
                    if m[a] != Z:
                        continue
                    for val in (T, F):
                        m2 = dict(m); m2[a] = val
                        if ev(phi, m2) != gv and a not in lab:
                            gmiss += 1
                gcells += 1
    print(f"    greedy cells with a hole: {gcells}   receipt missed: {gmiss}")
    assert gmiss == 0 and gcells > 5000
    for m in ({"paid": T, "delivered": Z, "refunded": T},
              {"paid": T, "delivered": Z, "refunded": F},
              {"paid": F, "delivered": Z, "refunded": F}):
        r = judge("(paid & delivered) | refunded", m)
        print(f"    {str(m):50} {r['disposition']:8} lazy={r['lazy']} "
              f"unverified={r['unverified']} pending={r['pending']}")
    assert judge("(paid & delivered) | refunded",
                 {"paid": T, "delivered": Z, "refunded": T})["pending"] == []
    assert judge("(paid & delivered) | refunded",
                 {"paid": T, "delivered": Z,
                  "refunded": F})["pending"] == ["delivered"]
    print("    the hole is in all three lines and worth filling in one.")
    print("    `unverified` lists every hole; `pending` lists the ones that")
    print("    still hold the answer up — a SAFE candidate list, never")
    print("    missing a load-bearing hole and sometimes naming an extra.")
    print("    (The draft that called this 'carriers for free in one pass'")
    print("    was corrected by the measurement above, not by argument.)")
    print("\n  ZTLJUDGE GREEN — formalize · check · check · join · judge · "
          "whatif, over an unchanged core; and a second register beside the "
          "verdict, telling a pause from a denial.")
