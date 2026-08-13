# -*- coding: utf-8 -*-
"""
zbook — the book of claims: what was asserted, what it rests on, and what
falls when a ground goes.

Stage 1 of the plan settled in words with the curator. The judge decides
one claim and forgets it; a mathematician uses proved theorems to prove
new ones. This is the first half of that: a ledger that KEEPS claims, so
that later stages can let one claim rest on another.

THE PRINCIPLE, and everything follows from it: the book does not store
verdicts as truth. It stores the claim and its grounds, and the verdict is
RECOMPUTED on every reading. A stored verdict would be exactly the sin
this corpus exists to refuse — a judgment taken on credit from a past
moment, when the ground may since have expired and the judge may since
have changed.

That last risk is not hypothetical here: the report shape changed six
times in two days of work. So the book carries a FINGERPRINT of the judge
— the verdicts it gives on a fixed battery of probe claims — and a
snapshot taken under a different fingerprint is flagged rather than
silently compared. The book can tell "the world changed" from "the judge
changed", which is the difference between a finding and an artefact.

Format: a claim is a sheet line, `id :: formula :: quantities`, so the
book is a claims sheet with a history. Witnesses live where they always
did, inside the quantities — and one may now name another claim,
`earned:claim/c1`, which is the single change that turns the book into a
graph. Three things follow, none of them needing a new rule:

  * warranty is INHERITED. A citation is honoured exactly as far as the
    cited claim currently stands; cite anything short of EARNED and the
    quantity drops to credit;
  * retraction TRAVELS. Withdraw one invoice and the whole subtree moves,
    including claims that never named it — the auditor's question, "what
    falls if this is a lie", answered by name instead of by memory;
  * a ground may be DECLARED rather than documented — several grounds
    asserted independent, or one asserted to take no inputs — and the
    verdict says so: EARNED with a `declared` warranty, inherited along
    citations so a declaration at the bottom cannot come out clean a
    storey up. Where the alternatives are claims the graph checks the
    independence outright and names the shared ancestor that refutes it;
    between documents it cannot, and that line is drawn rather than
    blurred;
  * and all of that is read through ONE frame with three axes — where a
    ground came from (`tested`), what is left to check (`under_learning`),
    what the calendar costs (`under_expiry`). Not a single merged grade:
    `epochs_matter` proves on an empty axiom list that invariance under
    learning and invariance under world-change are different properties;
  * a ground may carry a CLOCK. Retraction asks the adversarial question,
    what if this is a lie; a certificate can also simply run out, and
    nobody lied. That second move is E25's anti-tick `expire`, which this
    book's retraction has been at the ledger level all along. E25 also
    measured the discipline it needs — unrestricted expiry trivializes
    warranties — so the scope is DECLARED: `expiring/` must expire,
    `performed/` cannot, everything unmarked is an ordinary document;
  * a CIRCLE of support is classified, not rejected. Mutual citation
    without negation is the truth-teller's shape, and the passport calls
    it UNDERDETERMINED: ungrounded rather than refuted, curable only by
    stipulating a member. Agrippa's second horn, mechanically.

Run:  python3 zbook.py
"""
import hashlib
import json
import re
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z                                        # noqa: E402
from znumjudge import (judge_sheet_claim, parse_quantities,     # noqa: E402
                       load_sheet)

# A fixed battery. Its answers are the judge's signature: change how the
# floor decides anything here and the fingerprint moves, which is how a
# snapshot knows it is being compared against a different machine.
BATTERY = [
    ("b1", "a <= b", "a=1 earned:x, b=2 earned:y"),
    ("b2", "a <= b", "a=[0,10] credit, b=2 earned:y"),
    ("b3", "a == b", "a=1 earned:x, b=2 earned:y"),
    ("b4", "a == b", "a=8/3 earned:x, b=k, k=? int"),
    ("b5", "a == b", "a=1 earned:x m, b=1 earned:y RUB"),
    ("b6", "a <= b & ok", "a=1 earned:x, b=2 earned:y, ok=Z"),
]


def fingerprint():
    """A short hash of how the judge currently answers the battery."""
    parts = []
    for label, formula, data in BATTERY:
        try:
            q, m = parse_quantities(data)
            r = judge_sheet_claim(formula, q, m)
            parts.append(f"{label}:{r['disposition']}:{r.get('lazy')}")
        except Exception as exc:                    # a battery entry that
            parts.append(f"{label}:!{type(exc).__name__}")   # stops parsing
    return hashlib.sha256("|".join(parts).encode()).hexdigest()[:12]


CITE = "claim/"

# A ground that takes no inputs. Withdrawing a document is a move — it may
# be forged, expired, withdrawn. Withdrawing an operation with no arguments
# is not a move at all: there is nothing to fail to supply. The book must
# not model that as "protected"; it must REFUSE the move, which is what
# NotAMove is for. The book cannot verify that a witness really takes no
# inputs — nullarity is DECLARED here, and `declared_structural` lists
# every declaration so the claim of immunity is itemised and attributable
# rather than silent.
PERFORMED = "performed/"

# ALTERNATIVE grounds: `earned:inv-17|inv-18` — two independent invoices for
# the same sum, EITHER of which suffices. Until this existed the book knew
# only conjunctive support, every ground necessary, so a second ground was a
# second liability and `agrippa_book.py` had to score a web below a tower.
# That score belonged to the instrument, not to the world.
#
# The same honesty applies as to PERFORMED: the book cannot check that two
# grounds are INDEPENDENT. Two copies of one invoice are one witness under
# two names, and nothing here detects that. `declared_alternatives` lists
# every such claim so the independence is itemised rather than assumed.
# A ground that carries a CLOCK. `retract` asks the adversarial question —
# what if this is a lie — and a lie is not the only way to lose a ground: a
# certificate expires, a registry is re-pledged, a warranty runs out, and
# nobody lied. That second move is not new to this corpus; it is E25's
# anti-tick `expire(m, a)`, and this book's `retract` has been the same
# operation at the ledger level all along, built without noticing.
#
# E25 measured what makes it survivable: UNRESTRICTED EXPIRY TRIVIALIZES
# WARRANTIES — from any marking {expire, verify} reaches every marking, so a
# test invariant under both is a test that cannot fail; on the depth-2 pool
# only constant verdicts survive. The cure it names is a DECLARED SCOPE:
# say which grounds carry clocks. `performed/` was already half of that
# discipline — the class that cannot expire at all. This is the other half.
EXPIRING = "expiring/"

ALT = "|"
_WITNESS = re.compile(r"earned:([^\s,]+)")


def _alts(witness):
    return [a for a in (witness or "").split(ALT) if a]


def expiry_scope(book):
    """The grounds in this book that carry a declared clock."""
    out = set()
    for _cid, _f, data in book:
        q, _m = parse_quantities(data)
        for v in q.values():
            out |= {a for a in _alts(v.get("witness"))
                    if a.startswith(EXPIRING)}
    return sorted(out)


def expire_all(book):
    """Every clock runs out at once — the worst case the scope allows."""
    for w in expiry_scope(book):
        book = retract(book, w)
    return book


def scheduled_fallout(book):
    """What the CALENDAR costs, as against what a lie costs. Same shape as
    `fallout`, but the ground is not withdrawn by an adversary — it simply
    ran out, which is the ordinary way ledgers rot."""
    before, after = judge_book(book), judge_book(expire_all(book))
    return [(cid, before[cid]["disposition"], after[cid]["disposition"])
            for cid in before
            if before[cid]["disposition"] != after[cid]["disposition"]]


def declared_alternatives(book):
    """Every quantity in this book that claims two or more independent
    grounds — the claims of independence, by name."""
    out = []
    for cid, _f, data in book:
        q, _m = parse_quantities(data)
        for name, v in sorted(q.items()):
            alts = _alts(v.get("witness"))
            if len(alts) > 1:
                out.append((cid, name, alts))
    return out


class NotAMove(Exception):
    """Retraction was asked of a ground that has nothing to withdraw."""


def declared_structural(book):
    """Every ground in this book that claims to take no inputs."""
    out = set()
    for _cid, _f, data in book:
        q, _m = parse_quantities(data)
        out |= {v["witness"] for v in q.values()
                if (v.get("witness") or "").startswith(PERFORMED)}
    return sorted(out)


def _cited(quantities):
    """The claims this one leans on: witnesses of the form claim/<id>,
    including those offered as one alternative among several."""
    return sorted({a[len(CITE):] for v in quantities.values()
                   for a in _alts(v.get("witness")) if a.startswith(CITE)})


def _ancestors(node, deps, acc=None):
    """Every claim this one rests on, transitively."""
    acc = set() if acc is None else acc
    for d in deps.get(node, ()):
        if d not in acc:
            acc.add(d)
            _ancestors(d, deps, acc)
    return acc


def _false_independence(alts, deps):
    """Alternatives that are not alternatives. Declaring `a|b` asserts that
    the two grounds are independent; where both are CLAIMS the graph can
    check it, and a shared ancestor refutes it — one paper under two names.

    Note what this does NOT fix: the arithmetic was already right. Retract
    the common ancestor and both alternatives fall, so the blast radius has
    always been correct (measured). What was wrong is the DECLARATION, and
    an author who writes `a|b` is entitled to be told that this particular
    pair buys nothing. For grounds that are external documents the graph
    knows nothing and the declaration stands unchecked — which is exactly
    the boundary worth drawing."""
    named = [a[len(CITE):] for a in alts if a.startswith(CITE)]
    out = []
    for i, x in enumerate(named):
        for y in named[i + 1:]:
            common = ({x} | _ancestors(x, deps)) & ({y} | _ancestors(y, deps))
            if common:
                out.append((x, y, sorted(common)))
    return out


# ------------------------------------------------------- the assurance frame
#
# THREE AXES, NOT THREE NAMES FOR ONE THING. The book grew three separate
# words for "how well is this earned" — documented/declared, the clock, and
# the judge's own hereditary/sound/until-verification next door — and the
# obvious tidy-up is to fuse them. The corpus forbids it, and proves the
# ban: `epochs_matter` in lean/EpochBoundary.lean exhibits a formula that is
# Hereditary (invariant under EVERY epistemic refinement) and yet not
# epoch-blind. Invariance under learning and invariance under world-change
# are provably different notions, on an empty axiom list.
#
# So the fix is a FRAME rather than a merger: one record, three axes, each
# defined by what it is invariant under, in one place instead of scattered.
#
#   tested          — was any ground taken on the author's word?
#                     `documented` / `declared`. Not an invariance at all:
#                     this is about the ORIGIN of the ground.
#   under_learning  — does anything remain to be checked? `settled` /
#                     `pending`, read off the cures the judge still names.
#                     The book's analogue of the judge's grade axis.
#   under_expiry    — what does the calendar cost? `perpetual` (grounds that
#                     take no inputs and cannot be withdrawn), `exposed`
#                     (every standing ground carries a clock), `plain` (an
#                     ordinary document: losable to a lie, not to time).
#
# The judge's published vocabulary is deliberately NOT renamed — it is in
# the papers — and the correspondence is stated here instead.


def _perpetual_ground(alt, judged):
    """Can this ground be taken away at all?

    Two ways to answer, and they are worth a long way apart. `performed/`
    is DECLARED: the author says the ground takes no inputs and the machine
    believes them. A cited claim that is itself perpetual is CHECKED: the
    book descends into it and finds nothing that could be withdrawn. The
    descent bottoms out at a claim with NO QUANTITIES — `1 == 1` — which
    demanded nothing in the first place, so there is nothing to remove.

    That is the curator's question answered (2026-08-13): nullarity IS
    catchable by descent, and the declaration is only the fallback for
    grounds the book cannot see into. VR's `[]` is the same move at a
    bigger scale — the elaborator walks the whole construction and reports
    that it leans on nothing."""
    if alt.startswith(PERFORMED):
        return True
    if alt.startswith(CITE):
        return (judged.get(alt[len(CITE):], {})
                .get("assurance", {}).get("under_expiry") == "perpetual")
    return False


def _assurance(tested, pending, clocks, perpetual):
    return {"tested": "declared" if tested else "documented",
            "under_learning": "pending" if pending else "settled",
            "under_expiry": ("perpetual" if perpetual else
                             "exposed" if clocks else "plain")}


def _clocked(alt, judged):
    """Does this one ground live on a clock — directly, or by resting on a
    claim that does?"""
    if alt.startswith(EXPIRING):
        return True
    if alt.startswith(CITE):
        return bool(judged.get(alt[len(CITE):], {}).get("clock"))
    return False


def _stands(alt, judged):
    """Does this one ground currently hold? A document holds while it is in
    the book; a cited claim holds only while that claim is EARNED."""
    if alt.startswith(CITE):
        return judged.get(alt[len(CITE):], {}).get("disposition") == "EARNED"
    return True


def _order(book):
    """Dependency order, plus the cycles. A cycle is not an error here —
    it is a CIRCULAR JUSTIFICATION, which is a thing the corpus can
    classify rather than reject (Agrippa's second horn)."""
    deps, ids = {}, [c[0] for c in book]
    for cid, _f, data in book:
        q, _m = parse_quantities(data)
        deps[cid] = [d for d in _cited(q) if d in ids]
    order, seen, stack, cycles = [], set(), set(), []

    def visit(n, path):
        if n in seen:
            return
        if n in stack:                       # found a circle of support
            cycles.append(path[path.index(n):] + [n])
            return
        stack.add(n)
        for d in deps[n]:
            visit(d, path + [n])
        stack.discard(n)
        seen.add(n)
        order.append(n)

    for cid in ids:
        visit(cid, [])
    return order, deps, cycles


def judge_book(claims, strict=False):
    """Recompute the whole book, in dependency order, resolving citations.

    A witness of the form `claim/<id>` is honoured only as far as that
    claim currently stands: cite an EARNED claim and the citation carries
    its weight; cite anything else and the quantity drops to credit. The
    inheritance needs no special rule — it is the ordinary refusal to take
    a ground on somebody else's word, applied to our own book.

    The STRICT reading lives in `retract`, where the declarations are
    actually cashed: alternatives are treated as one paper under several
    names, and a `performed/` ground loses its immunity. The point is not
    pessimism but a BRACKET — the book's honest answer is the pair, and the
    truth is inside it. See `trust_interval`."""
    book = list(claims)
    order, deps, cycles = _order(book)
    by_id = {cid: (f, data) for cid, f, data in book}
    in_cycle = {n for cyc in cycles for n in cyc}
    out = {}
    for cid in order:
        formula, data = by_id[cid]
        q, m = parse_quantities(data)
        cites = _cited(q)
        # resolve each citation against the claim it names
        weakened, carried, declared = [], [], []
        unindependent, clocks, perpetual = [], [], []
        for name, qty_ in q.items():
            alts = _alts(qty_.get("witness"))
            if not alts:
                continue
            # WHAT THIS GROUND ASKS US TO TAKE ON TRUST. Naming several
            # grounds asserts they are independent; naming a `performed/`
            # one asserts it takes no inputs. Neither is checkable in
            # general, so neither may hide inside a bare "EARNED".
            if len(alts) > 1:
                declared.append((name, "independence", alts))
                unindependent.extend(_false_independence(alts, deps))
            standing = [a for a in alts if _stands(a, out)]
            if standing:
                if len(alts) > 1:
                    carried.append((name, standing[0]))
                # EXPOSURE, not presence. A quantity is on the calendar only
                # if EVERY ground still standing under it carries a clock —
                # one clock-free alternative is insurance, and E25 measured
                # that insurance as the thing that keeps a warranty alive.
                # (First written as "the carrying ground has a clock", which
                # was a label lying about arithmetic that was already right:
                # the insured claim survived expiry and the field said it
                # was exposed.)
                if all(_perpetual_ground(a, out) for a in standing):
                    perpetual.append(name)
                exposed = [a for a in standing if _clocked(a, out)]
                if len(exposed) == len(standing):
                    clocks.append((name, exposed[0] if len(exposed) == 1
                                   else exposed))
                if standing[0].startswith(PERFORMED):
                    declared.append((name, "nullarity", standing[0]))
                elif standing[0].startswith(CITE):
                    up = out.get(standing[0][len(CITE):], {})
                    if up.get("warranty") == "declared":
                        declared.append((name, "inherited",
                                         standing[0][len(CITE):]))
                continue
            # every ground it offered has failed
            qty_["prov"] = "credit"
            qty_["witness"] = None
            weakened.extend((name, a[len(CITE):]) for a in alts
                            if a.startswith(CITE))
        r = judge_sheet_claim(formula, q, m)
        out[cid] = {
            "formula": formula,
            "disposition": ("CIRCULAR" if cid in in_cycle
                            else r["disposition"]),
            "lazy": r.get("lazy"),
            "next_check": r.get("next_check", []),
            "why": r.get("why"),
            "cites": cites,
            "weakened_by": weakened,
            "carried_by": carried,
            "declared": declared,
            "assurance": _assurance(declared, r.get("next_check"), clocks,
                                    not q or (perpetual and
                                              len(perpetual) == len(q))),
            "warranty": "declared" if declared else "documented",
            "clock": clocks,
            "not_independent": unindependent,
            "witnesses": sorted({v["witness"] for v in q.values()
                                 if v.get("witness")}),
        }
    for cid, _f, _d in book:                 # cycles never reach `order`
        out.setdefault(cid, {"formula": by_id[cid][0],
                             "disposition": "CIRCULAR", "lazy": None,
                             "next_check": [], "why": "circular support",
                             "cites": deps[cid], "weakened_by": [],
                             "carried_by": [], "declared": [],
                             "assurance": _assurance(False, None, [], False),
                             "warranty": "documented", "clock": [],
                             "not_independent": [],
                             "witnesses": []})
    return out


def classify_cycles(book):
    """A circle of support, handed to the instrument that already knows
    what to do with self-reference. Mutual citation with no negation is
    the truth-teller's shape, and the passport calls it what it is:
    UNDERDETERMINED — not refuted, ungrounded, and curable only by
    stipulating one of its members. That is Agrippa's second horn,
    classified rather than deplored."""
    from zpassport import passports
    _order_, deps, cycles = _order(list(book))
    out = []
    for cyc in cycles:
        members = sorted(set(cyc))
        system = {m: (deps[m][0] if deps[m] else m) for m in members}
        reports = passports(system)[1]
        kinds = sorted({k for _c, k, _w in reports}) or ["GROUNDED"]
        out.append((members, kinds))
    return out


def retract(book, witness, strict=False):
    """A ground goes: the document is forged, or the certificate expired.
    Everything that named it drops to credit, and the book is recomputed —
    so the damage travels along citations by itself.

    A ground with no inputs is refused rather than survived (see PERFORMED)
    — except in STRICT mode, which refuses that immunity along with every
    other declaration the machine cannot check."""
    if witness.startswith(PERFORMED) and not strict:
        raise NotAMove(f"{witness} takes no inputs — "
                       f"withdrawing it is not a performable move")

    def drop(m):
        alts = m.group(1).split(ALT)
        if strict and witness in alts:
            return "credit"        # they were one paper under several names
        rest = [a for a in alts if a != witness]
        return f"earned:{ALT.join(rest)}" if rest else "credit"

    return [(cid, formula, _WITNESS.sub(drop, data))
            for cid, formula, data in book]


def fallout(book, witness, strict=False):
    """What a retraction costs, claim by claim: (id, before, after)."""
    before = judge_book(book, strict=strict)
    after = judge_book(retract(book, witness, strict=strict), strict=strict)
    return [(cid, before[cid]["disposition"], after[cid]["disposition"])
            for cid in before
            if before[cid]["disposition"] != after[cid]["disposition"]]


def all_grounds(book):
    """Every external ground named anywhere in the book."""
    out = set()
    for _cid, _f, data in book:
        for w in _WITNESS.findall(data):
            out |= set(w.split(ALT))
    return sorted(g for g in out if not g.startswith(CITE))


def trust_interval(book):
    """The book's honest answer to "what falls if this ground goes" is not a
    number but a BRACKET, and this returns it per ground.

    The low end reads the book AS DECLARED — every claim of independence
    and of nullarity believed. The high end reads it STRICT — every such
    claim assumed false, since the machine cannot check them and between
    external documents never will (KNOWN-LIMITS.md). The true cost lies
    between, and the WIDTH of the bracket is exactly the price of the
    author's unverifiable word.

    This is the corpus's own habit turned on itself. The numeric floor does
    not drop an unknown and does not guess it: it returns an interval and a
    theorem that the answer is inside. A ledger built on declarations owes
    the same, and a book whose brackets are all zero-width is one that took
    nothing on trust."""
    out = {}
    for g in all_grounds(book):
        try:
            low = len(fallout(book, g))
        except NotAMove:
            low = 0                    # withdrawal is not an available move
        out[g] = (low, len(fallout(book, g, strict=True)))
    return out


def snapshot(results):
    return {"judge": fingerprint(),
            "claims": {k: {"disposition": v["disposition"],
                           "lazy": v["lazy"]} for k, v in results.items()}}


def diff(old, new_results):
    """What moved since the snapshot — and whether the judge moved too."""
    new = snapshot(new_results)
    same_judge = old.get("judge") == new["judge"]
    changed, appeared, vanished = [], [], []
    for k, v in new["claims"].items():
        if k not in old.get("claims", {}):
            appeared.append(k)
        elif old["claims"][k] != v:
            changed.append((k, old["claims"][k], v))
    for k in old.get("claims", {}):
        if k not in new["claims"]:
            vanished.append(k)
    return {"same_judge": same_judge, "changed": changed,
            "appeared": appeared, "vanished": vanished,
            "old_judge": old.get("judge"), "new_judge": new["judge"]}


def trust_surface(book):
    """How much of what this book calls EARNED rests on something the
    machine did not check.

    `fallout` answers "what falls if this ground is a lie". This answers a
    different question — "how much of this is my own word" — and the two
    can disagree: a book can be robust to any single withdrawal and still be
    held up entirely by declarations, because a declaration is not a ground
    that might fail, it is a ground nobody ever tested.

    It reports only what the BOOK says. Whether a documented ground is one
    you could re-establish yourself is domain knowledge and belongs to
    whoever wrote the book — see `inventory/corpus_book.py`, where the
    corpus's own answer turns out to be the interesting one."""
    res = judge_book(book)
    earned = [v for v in res.values() if v["disposition"] == "EARNED"]
    declared = [v for v in earned if v["warranty"] == "declared"]
    clocked = [v for v in earned if v["clock"]]
    items = sorted({d[1] + ":" + str(d[2]) for v in res.values()
                    for d in v["declared"]})
    return {"claims": len(res), "earned": len(earned),
            "on_declarations": len(declared), "on_clocks": len(clocked),
            "share": (0 if not earned
                      else round(len(declared) / len(earned), 3)),
            "declarations": items,
            "refuted_independence": sorted({str(x) for v in res.values()
                                            for x in v["not_independent"]})}


def census(results):
    by = {}
    for v in results.values():
        by[v["disposition"]] = by.get(v["disposition"], 0) + 1
    return by


# ================================================================ the bench
BOOK = [
    ("c1", "sum(line1,line2,line3) <= budget",
     "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
     "line3=1500 earned:inv-19, budget=5000 earned:order-o4"),
    ("c2", "total == 4500",
     "total=4500 earned:contract"),
    ("c3", "vat == total / 5",
     "vat=900 earned:inv-20, total=4500 earned:contract"),
    ("c4", "headcount < cap",
     "headcount=? credit int, cap=75 earned:law"),
    ("c5", "fee == area",
     "fee=5 earned:reg-7 RUB, area=3 earned:plan m2"),
]


def sec1_the_book_reads_itself():
    print("-" * 72)
    print("1. THE BOOK, RECOMPUTED FROM ITS GROUNDS")
    results = judge_book(BOOK)
    for cid, v in results.items():
        cure = f"  cure {v['next_check']}" if v["next_check"] else ""
        print(f"   {cid}  {v['disposition']:9} lazy={v['lazy']}{cure}")
    print(f"   census: {census(results)}")
    assert census(results)["EARNED"] == 3
    assert results["c4"]["disposition"] == "OPEN"
    assert results["c5"]["disposition"] == "E"
    print("   nothing here was read from a cache: every verdict was")
    print("   recomputed from the grounds as they stand now, which is the")
    print("   only way a book can be trusted after its world has moved.")
    return results


def sec2_the_judge_has_a_fingerprint(results):
    print("-" * 72)
    print("2. THE FINGERPRINT: telling a changed world from a changed judge")
    snap = snapshot(results)
    print(f"   judge fingerprint now: {snap['judge']}")
    d = diff(snap, results)
    print(f"   same book, same judge: changed={len(d['changed'])} "
          f"same_judge={d['same_judge']}")
    assert d["same_judge"] and not d["changed"]
    # the world moves: a witness is withdrawn from line3
    moved = [(cid, f, data.replace("line3=1500 earned:inv-19",
                                   "line3=1500 credit"))
             for cid, f, data in BOOK]
    d2 = diff(snap, judge_book(moved))
    print(f"   after inv-19 is withdrawn: changed={[c[0] for c in d2['changed']]}"
          f"  same_judge={d2['same_judge']}")
    assert [c[0] for c in d2["changed"]] == ["c1"]
    assert d2["same_judge"]
    print("   c1 moved and the judge did not — so this is news about the")
    print("   WORLD. Had the fingerprint differed, the same movement would")
    print("   have been news about the machine, and the book says which.")


CHAIN = [
    ("c1", "line == amount",
     "line=1500 earned:inv-19, amount=1500 earned:inv-19"),
    ("c2", "total == sum(a,b)",
     "total=4500 earned:claim/c1, a=3000 earned:inv-17, b=1500 earned:inv-18"),
    ("c3", "total <= budget",
     "total=4500 earned:claim/c2, budget=5000 earned:order-o4"),
]

CIRCLE = [
    ("a1", "x == y", "x=1 earned:claim/a2, y=1 earned:doc"),
    ("a2", "y == x", "y=1 earned:claim/a1, x=1 earned:doc"),
]


def sec3_a_claim_may_rest_on_a_claim():
    print("-" * 72)
    print("3. STAGE TWO: A WITNESS MAY NAME ANOTHER CLAIM")
    res = judge_book(CHAIN)
    for cid in ("c1", "c2", "c3"):
        v = res[cid]
        print(f"   {cid}  {v['disposition']:9} cites={v['cites']} "
              f"weakened_by={v['weakened_by']}")
    assert all(res[c]["disposition"] == "EARNED" for c in ("c1", "c2", "c3"))
    print("   a chain three deep, every link earned. And the inheritance is")
    print("   not a special rule: a citation is honoured exactly as far as")
    print("   the cited claim currently stands.")


def sec4_retraction_travels_by_itself():
    print("-" * 72)
    print("4. STAGE THREE: WHAT FALLS WHEN A GROUND GOES")
    hits = fallout(CHAIN, "inv-19")
    for cid, before, after in hits:
        print(f"   {cid}: {before} -> {after}")
    assert [h[0] for h in hits] == ["c1", "c2", "c3"]
    assert all(b == "EARNED" and a == "ON CREDIT" for _c, b, a in hits)
    print("   one invoice withdrawn and three claims move, two of them")
    print("   never naming it: the damage travelled along the citations by")
    print("   itself. This is the auditor's question — WHAT FALLS IF THIS")
    print("   IS A LIE — answered by name instead of by memory, and it is")
    print("   the reason the book stores grounds rather than verdicts.")


def sec5_a_circle_is_classified_not_rejected():
    print("-" * 72)
    print("5. STAGE FOUR: A CIRCLE OF SUPPORT, CLASSIFIED")
    res = judge_book(CIRCLE)
    print(f"   a1 {res['a1']['disposition']}, a2 {res['a2']['disposition']}")
    assert all(v["disposition"] == "CIRCULAR" for v in res.values())
    for members, kinds in classify_cycles(CIRCLE):
        print(f"   the circle {members}: passport {kinds}")
        assert kinds == ["UNDERDETERMINED"]
    print("   UNDERDETERMINED — not refuted, UNGROUNDED, and curable only")
    print("   by stipulating one member. That is Agrippa's circle, and the")
    print("   book reaches the verdict with the instrument it already had:")
    print("   mutual citation without negation is the truth-teller's shape.")


ALTERNATIVES = [
    ("k1", "line == amount",
     "line=1500 earned:inv-19|inv-19-duplicate, amount=1500 earned:contract"),
    ("k2", "total == sum(a,b)",
     "total=4500 earned:claim/k1|ledger-page-7, a=3000 earned:inv-17, "
     "b=1500 earned:inv-18"),
]


def sec6_a_ground_may_have_an_alternative():
    print("-" * 72)
    print("6. STAGE FIVE: EITHER OF TWO GROUNDS")
    res = judge_book(ALTERNATIVES)
    for cid in ("k1", "k2"):
        print(f"   {cid}  {res[cid]['disposition']:9} "
              f"carried_by={res[cid]['carried_by']}")
    assert all(v["disposition"] == "EARNED" for v in res.values())
    for w in ("inv-19", "inv-19-duplicate", "claim/k1"):
        hits = fallout(ALTERNATIVES, w)
        print(f"   withdraw {w:18} -> "
              f"{[h[0] for h in hits] or 'nothing falls'}")
        assert not hits
    both = retract(retract(ALTERNATIVES, "inv-19"), "inv-19-duplicate")
    after = judge_book(both)
    print(f"   withdraw BOTH of k1's grounds -> k1 {after['k1']['disposition']}"
          f", k2 {after['k2']['disposition']}")
    assert after["k1"]["disposition"] == "ON CREDIT"
    assert after["k2"]["disposition"] == "EARNED"
    print("   Until this stage every ground was necessary, so a second one")
    print("   was a second liability and the book had to score a web below a")
    print("   tower. Now a quantity may name several and one suffices: the")
    print("   damage stops where an alternative holds — k2 keeps its ledger")
    print("   page and never learns that k1 fell.")
    print(f"   declared_alternatives: {declared_alternatives(ALTERNATIVES)}")
    assert len(declared_alternatives(ALTERNATIVES)) == 2
    print("   And the honest half: INDEPENDENCE IS DECLARED. `inv-19` and")
    print("   `inv-19-duplicate` may well be one paper photocopied, and")
    print("   nothing here can tell. The book itemises every such claim")
    print("   instead of detecting it — the same bargain as `performed/`.")


DECLARED = [
    ("h1", "x == 1", "x=1 earned:doc-c"),
    ("h2", "x == 1", "x=1 earned:claim/h1"),
    ("h3", "x == 1", "x=1 earned:claim/h1"),
    ("h4", "x == 1", "x=1 earned:claim/h2|claim/h3"),
    ("h5", "x == 1", "x=1 earned:performed/zero"),
    ("h6", "x == 1", "x=1 earned:claim/h5"),
]


def sec7_a_declaration_may_not_hide_inside_earned():
    print("-" * 72)
    print("7. STAGE SIX: WHAT THE VERDICT IS TAKING ON TRUST")
    res = judge_book(DECLARED)
    for cid, _f, _d in DECLARED:
        v = res[cid]
        print(f"   {cid}  {v['disposition']:7} {v['warranty']:10} "
              f"{v['declared']}")
    assert all(v["disposition"] == "EARNED" for v in res.values())
    assert [res[c]["warranty"] for c, _f, _d in DECLARED] == \
        ["documented", "documented", "documented",
         "declared", "declared", "declared"]
    print("   The two witness kinds added earlier are DECLARATIONS: naming")
    print("   several grounds asserts they are independent, naming a")
    print("   `performed/` one asserts it takes no inputs, and the machine")
    print("   verifies neither. Until now that hid inside a bare EARNED —")
    print("   the book cheerfully reporting the top disposition on the")
    print("   strength of something it never checked, which is the exact")
    print("   habit this corpus exists to refuse.")
    print("   So it is on the verdict now, where the corpus already puts")
    print("   the quality of an earning: not a new disposition and not a")
    print("   new value, a WARRANTY — earned, and here is what on.")
    print(f"   and it does not launder: h6 rests on h5 and reads "
          f"{res['h6']['declared']}")
    assert res["h6"]["declared"] == [("x", "inherited", "h5")]
    print("   One declaration at the bottom would otherwise come out clean")
    print("   one storey up, which is how such things always get lost.")


def sec8_where_the_graph_can_check_a_declaration():
    print("-" * 72)
    print("8. AND WHERE A DECLARATION CAN BE CHECKED, IT IS")
    res = judge_book(DECLARED)
    print(f"   h4 declared independence: {res['h4']['declared']}")
    print(f"   the graph on that pair   : {res['h4']['not_independent']}")
    assert res["h4"]["not_independent"] == [("h2", "h3", ["h1"])]
    hits = [h[0] for h in fallout(DECLARED, "doc-c")]
    print(f"   withdraw the common ancestor's document: {hits}")
    assert hits == ["h1", "h2", "h3", "h4"]
    print("   h2 and h3 are not alternatives: they are one paper under two")
    print("   names, and the graph says so by their shared ancestor h1.")
    print("   NOTE WHAT THIS DOES NOT FIX. The arithmetic was already")
    print("   right — h4 falls with h1 above, and always did, because a")
    print("   dead alternative does not stand. What was wrong was the")
    print("   DECLARATION, and an author who writes `a|b` is owed the news")
    print("   that this particular pair buys nothing. Where the grounds are")
    print("   external documents the graph knows nothing and the")
    print("   declaration stands unchecked — and drawing that line exactly")
    print("   is worth more than either half of it.")


CLOCKED = [
    ("p1", "x == 1", "x=1 earned:expiring/cert-7"),
    ("p2", "x == 1", "x=1 earned:claim/p1"),
    ("p3", "x == 1", "x=1 earned:deed-of-sale"),
    ("p4", "x == 1", "x=1 earned:expiring/warranty|deed-of-sale"),
]


def sec9_what_the_calendar_costs():
    print("-" * 72)
    print("9. STAGE SEVEN: A GROUND MAY RUN OUT WITHOUT ANYBODY LYING")
    print(f"   declared expiry scope: {expiry_scope(CLOCKED)}")
    res = judge_book(CLOCKED)
    for cid, _f, _d in CLOCKED:
        print(f"   {cid}  {res[cid]['disposition']:7} "
              f"clock={res[cid]['clock']}")
    assert res["p2"]["clock"] == [("x", "claim/p1")]
    assert res["p3"]["clock"] == [] and res["p4"]["clock"] == []
    hits = [(c, a) for c, _b, a in scheduled_fallout(CLOCKED)]
    print(f"   when every clock runs out: {hits}")
    assert hits == [("p1", "ON CREDIT"), ("p2", "ON CREDIT")]
    print("   `retract` asks the adversarial question — what if this is a")
    print("   lie. A lie is not the only way to lose a ground: certificates")
    print("   expire and nobody lied. That second move is E25's anti-tick")
    print("   `expire`, and this book's retraction has been the same")
    print("   operation at the ledger level all along, built without")
    print("   noticing. Naming the correspondence is most of the fix.")
    print("   The clock is inherited like every other property here, so p2")
    print("   knows it is living on p1's certificate without naming it. p3")
    print("   holds a deed and keeps standing; p4 is INSURED — its warranty")
    print("   expires and the deed carries it, which is exactly E25's")
    print("   expiry-insurance written as an alternative ground.")


def sec10_and_why_the_scope_must_be_declared():
    print("-" * 72)
    print("10. WHY THE SCOPE HAS TO BE DECLARED — E25's THEOREM, IN MINIATURE")
    everything = [
        ("q1", "x == 1", "x=1 earned:expiring/a"),
        ("q2", "x == 1", "x=1 earned:claim/q1"),
        ("q3", "x == 1", "x=1 earned:expiring/b"),
        ("q4", "x == 1", "x=1 earned:expiring/c|expiring/d"),
    ]
    res = judge_book(everything)
    print(f"   every ground on a clock, nothing off the calendar: "
          f"{census(res)}, scope {len(expiry_scope(everything))}")
    print(f"   after they all run out: "
          f"{census(judge_book(expire_all(everything)))}")
    hits = scheduled_fallout(everything)
    assert all(v["disposition"] == "EARNED" for v in res.values())
    assert len(hits) == len(everything)
    print("   Nothing survives — not even q4, which holds two grounds and")
    print("   was insured a section ago. Insurance is not redundancy; it is")
    print("   having something OFF the calendar, and two clocks are not one")
    print("   clock's cure.")
    print("   This is the ledger's copy of what E25 proved and measured:")
    print("   with {expire, verify} unrestricted every marking is reachable")
    print("   from every other, so a warranty required to hold under")
    print("   arbitrary expiry is a warranty on nothing — on the depth-2")
    print("   pool only the constant verdicts lived through it.")
    print("   Hence one discipline in both halves: say WHICH grounds carry")
    print("   clocks. `performed/` is the class that cannot expire,")
    print("   `expiring/` the class that must, and everything unmarked is an")
    print("   ordinary document — losable to a lie, not to the calendar.")
    t = trust_surface(DECLARED)
    print(f"   and the book-level number, for the declared book of §7: "
          f"{t['on_declarations']} of {t['earned']} earned claims stand on")
    print(f"   something nobody checked ({t['share']}), itemised: "
          f"{t['declarations']}")
    assert t["on_declarations"] == 3 and t["share"] == 0.5
    print("   `fallout` asks what falls if a ground is a LIE; this asks how")
    print("   much of the book is my own word. The two can disagree flatly:")
    print("   a book can be robust to every single withdrawal and still be")
    print("   held up entirely by declarations, because a declaration is")
    print("   not a ground that might fail — it is one nobody ever tested.")


FRAME = [
    ("f1", "x == 1", "x=1 earned:deed"),
    ("f2", "x == 1", "x=1 earned:performed/zero"),
    ("f3", "x == 1", "x=1 earned:expiring/cert-7"),
    ("f4", "x == y", "x=1 earned:deed, y=? credit int"),
    ("f5", "x == 1", "x=1 earned:deed|ledger-page"),
]


def sec11_one_frame_three_axes():
    print("-" * 72)
    print("11. STAGE EIGHT: ONE FRAME FOR 'HOW WELL IS THIS EARNED'")
    res = judge_book(FRAME)
    for cid, _f, _d in FRAME:
        a = res[cid]["assurance"]
        print(f"   {cid}  {res[cid]['disposition']:7} "
              f"tested={a['tested']:10} learning={a['under_learning']:7} "
              f"expiry={a['under_expiry']}")
    axes = {c: res[c]["assurance"] for c, _f, _d in FRAME}
    assert axes["f1"] == {"tested": "documented", "under_learning": "settled",
                          "under_expiry": "plain"}
    assert axes["f2"]["under_expiry"] == "perpetual"
    assert axes["f3"]["under_expiry"] == "exposed"
    assert axes["f4"]["under_learning"] == "pending"
    assert axes["f5"]["tested"] == "declared"
    print("   The book had grown three separate words for one question —")
    print("   documented/declared, the clock, and the judge's own")
    print("   hereditary/sound/until-verification next door — and the")
    print("   obvious tidy-up is to fuse them into a single grade.")
    print("   THE CORPUS FORBIDS IT, AND PROVES THE BAN. `epochs_matter`")
    print("   (lean/EpochBoundary.lean, empty axiom list) exhibits a formula")
    print("   invariant under EVERY epistemic refinement which is still not")
    print("   epoch-blind: surviving what you learn and surviving what")
    print("   changes are different properties, not two names for one.")
    print("   So this is a frame, not a merger. Three axes, each defined by")
    print("   what it is invariant under, in one place instead of scattered:")
    print("   where the ground CAME FROM, what is left to CHECK, and what")
    print("   the CALENDAR costs. The judge's published vocabulary is not")
    print("   renamed — it is in the papers — and the correspondence is")
    print("   written down here instead.")


BRACKETED = [
    ("g1", "x == 1", "x=1 earned:inv-17|inv-17-photocopy"),
    ("g2", "x == 1", "x=1 earned:claim/g1"),
    ("g3", "x == 1", "x=1 earned:performed/zero"),
    ("g4", "x == 1", "x=1 earned:plain-deed"),
]


def sec12_the_answer_is_a_bracket():
    print("-" * 72)
    print("12. STAGE NINE: THE HONEST ANSWER IS A BRACKET, NOT A NUMBER")
    iv = trust_interval(BRACKETED)
    for g, (lo, hi) in iv.items():
        width = hi - lo
        print(f"   {g:22} [{lo}, {hi}]"
              f"{'   <- zero width: nothing taken on trust' if not width else ''}")
    assert iv["inv-17"] == (0, 2) and iv["inv-17-photocopy"] == (0, 2)
    assert iv["performed/zero"] == (0, 1)
    assert iv["plain-deed"] == (1, 1)
    print("   The low end believes every declaration; the high end assumes")
    print("   each one false — alternatives are one paper under several")
    print("   names, and a `performed/` ground loses its immunity. The true")
    print("   cost is between, and the WIDTH is exactly the price of the")
    print("   author's unverifiable word.")
    print("   This is not new machinery, it is the corpus's own habit turned")
    print("   on itself: the numeric floor never drops an unknown and never")
    print("   guesses it — it returns an interval and a theorem that the")
    print("   answer is inside. A ledger built on declarations owes the same.")
    print("   And it repairs the thing that made the book worth distrusting.")
    print("   The judge's guarantee was always conditional AND total: given")
    print("   this marking, this verdict, and nothing claimed outside its")
    print("   jurisdiction. The book was the first component whose output")
    print("   could be wrong in a way its input did not show. Now it cannot:")
    print("   it no longer reports a number it might miss, it reports a")
    print("   range it cannot. Right in the small, and totally.")


DESCENT = [
    ("k0", "1 == 1", ""),
    ("k1", "x == 1", "x=1 earned:claim/k0"),
    ("k2", "x == 1", "x=1 earned:performed/zero"),
    ("k3", "x == 1", "x=1 earned:deed"),
]


def sec13_nullarity_is_catchable_by_descent():
    print("-" * 72)
    print("13. STAGE TEN: NULLARITY, CHECKED INSTEAD OF DECLARED")
    res = judge_book(DESCENT)
    for cid, _f, _d in DESCENT:
        a = res[cid]["assurance"]
        print(f"   {cid}  {res[cid]['disposition']:7} "
              f"tested={a['tested']:10} expiry={a['under_expiry']}")
    assert res["k0"]["assurance"] == {"tested": "documented",
                                      "under_learning": "settled",
                                      "under_expiry": "perpetual"}
    assert res["k1"]["assurance"]["under_expiry"] == "perpetual"
    assert res["k1"]["assurance"]["tested"] == "documented"
    assert res["k2"]["assurance"]["tested"] == "declared"
    iv = trust_interval(DESCENT)
    print(f"   trust brackets: {iv}")
    assert iv["deed"] == (1, 1) and iv["performed/zero"] == (0, 1)
    print("   `performed/` was a LABEL: the author says a ground takes no")
    print("   inputs and the machine believes them, which is why it costs a")
    print("   bracket at all — [0, 1] here, and as wide as the subtree that")
    print("   leans on it. k0 is not a label. It is a claim with NO")
    print("   QUANTITIES — `1 == 1` — which demanded nothing in the first")
    print("   place, so there is nothing anyone could withdraw. Its")
    print("   perpetuity is computed, not asserted, and it is `documented`")
    print("   rather than `declared`: it took nothing on trust at all.")
    print("   k1 shows the descent carrying: a claim resting on k0 inherits")
    print("   the perpetuity as a CHECKED property, because the book walked")
    print("   down into its ground and found the bottom.")
    print("   So nullarity is catchable after all, and the rule is exact:")
    print("   checkable exactly where the ground is TRANSPARENT, declared")
    print("   only where it is opaque. VR's `[]` is the same move at scale —")
    print("   the elaborator walks the whole construction and reports that")
    print("   it leans on nothing, which is why VR's zero is stronger than")
    print("   any `performed/` here could be.")


def sec14_what_is_still_missing():
    print("-" * 72)
    print("14. WHAT IS STILL MISSING")
    print("   Search. Nothing here finds the relevant stored claims for a")
    print("   new question — that is premise selection, a crowded field")
    print("   with strong tools (Sledgehammer and its kin), and this corpus")
    print("   would lose there. Citations are written by whoever writes the")
    print("   claim, and the machine only honours them honestly.")


if __name__ == "__main__":
    print("=" * 72)
    print("ZBOOK — the book of claims, stage one")
    print("=" * 72)
    res = sec1_the_book_reads_itself()
    sec2_the_judge_has_a_fingerprint(res)
    sec3_a_claim_may_rest_on_a_claim()
    sec4_retraction_travels_by_itself()
    sec5_a_circle_is_classified_not_rejected()
    sec6_a_ground_may_have_an_alternative()
    sec7_a_declaration_may_not_hide_inside_earned()
    sec8_where_the_graph_can_check_a_declaration()
    sec9_what_the_calendar_costs()
    sec10_and_why_the_scope_must_be_declared()
    sec11_one_frame_three_axes()
    sec12_the_answer_is_a_bracket()
    sec13_nullarity_is_catchable_by_descent()
    sec14_what_is_still_missing()
    print("=" * 72)
    print("ZBOOK GREEN — the book stores claims and grounds and never a")
    print("verdict: every reading recomputes. A snapshot carries the")
    print("judge's fingerprint, so a moved verdict can be told from a moved")
    print("machine — news about the world, or news about us. A witness may")
    print("name another claim, and then warranty is inherited without a")
    print("special rule; withdraw one invoice and three claims move, two of")
    print("them never naming it; and a circle of support is classified")
    print("UNDERDETERMINED by the passport — Agrippa's second horn, cured")
    print("only by stipulating a member. A ground may take no inputs at all,")
    print("and then its withdrawal is refused rather than survived; or it may")
    print("offer alternatives, and then the damage stops where one holds.")
    print("Both are DECLARATIONS, and neither may hide inside a bare EARNED:")
    print("the verdict now carries the warranty — earned, and here is what")
    print("on — and the declaration is inherited along citations, so one at")
    print("the bottom cannot come out clean a storey up. Where the grounds")
    print("are claims the graph checks the independence outright and names")
    print("the shared ancestor; where they are documents it cannot, and that")
    print("line is drawn rather than blurred. And a ground may run out")
    print("instead of being disputed — the calendar's fallout is computed")
    print("apart from the adversary's, over a declared scope, because E25")
    print("measured that unrestricted expiry leaves no warranty standing.")
