# -*- coding: utf-8 -*-
"""
The corpus as a book of claims: what rests on what, and what would fall.

`inventory/paper_claims.py` checks that a number printed in a paper is the
number the machine produces. `inventory/docket_claims.py` does the same for
the docket's table. Both are FLAT: they know that each claim is true, and
nothing about which claim holds up which.

This is the missing axis. Every headline result of the corpus is entered as
a claim in `zbook`, its value MEASURED live here rather than typed, and its
witness is either an instrument (`zsweep`, `zledger`, the Lean file) or —
where one result genuinely leans on another — the other claim. Then the
machine answers the auditor's question, per ground, by name:

    WHAT FALLS IF THIS TURNS OUT TO BE WRONG?

MEASURED HERE:

  1. the whole book stands: every headline number recomputes from the
     modules on this run, so nothing here is a remembered result;
  2. the blast radius of each ground, sorted. This is the number the
     project has never had: not "is the corpus green" but "which single
     mistake would cost the most", which is the only useful form of the
     Frege fear;
  3. the shape of the dependence — the corpus is not one tower. It is a
     few short stacks on separate instruments, which is why no single
     retraction takes everything, and also why the green run says less
     than it looks like it says.

The measurement corrected a prediction, which is the reason for running it.
Before the run the expected worst ground was `zsweep`, our own instrument,
at five or six claims. Measured: eight, and TIED WITH `tomova` — a pair of
numbers copied out of the literature. The most expensive single point of
failure in this corpus is not code we can test; it is a citation, and the
only cure for it is the ordinary one, reading the source. That is what a
blast-radius column is for.

CEILING, stated up front: this measures the numbers, not the prose. A claim
here can stand while the sentence that interprets it in a paper is wrong,
and the citations are written by hand — the machine honours them, it does
not discover them. The Lean ground is asked of the ELABORATOR (cached, a
fifth of a second), not read off the file; a cold build is `run_all.py`'s.

Run:  python3 inventory/corpus_book.py
"""
import os
import re
import subprocess
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z, IMP                                    # noqa: E402
from zbook import (judge_book, fallout, census, _order,          # noqa: E402
                   trust_surface, trust_interval, cost)
import zsweep as S                                              # noqa: E402
import zledger as L                                             # noqa: E402
import zclassify as C                                           # noqa: E402


# --------------------------------------------------------------- measuring
def measure_corpus():
    """Every number in the book below, computed on this run."""
    m = {}
    arrows = list(S.all_arrows())
    m["arrows"] = len(arrows)
    m["control_T"] = sum(1 for t in arrows
                         if S.c_extending(S.arrow(t))
                         and S.normal(S.arrow(t), (T,))
                         and S.order_condition(S.arrow(t), (T,)))
    m["control_TZ"] = sum(1 for t in arrows
                          if S.c_extending(S.arrow(t))
                          and S.normal(S.arrow(t), (T, Z))
                          and S.order_condition(S.arrow(t), (T, Z)))
    kin = [t for t in arrows
           if S.c_extending(S.arrow(t)) and S.normal(S.arrow(t), (T,))
           and S.no_credit(S.arrow(t), (T,))]
    m["kin"] = len(kin)
    m["with_id"] = len([t for t in kin if S.identity(S.arrow(t), (T,))])
    m["with_ord"] = len([t for t in kin
                         if S.order_condition(S.arrow(t), (T,))])

    pool = list(L.depth2_pool())
    m["pool"] = len(pool)
    m["cl_taut"] = len([p for p in pool if all(v == T for v in L.sig(p, L.CL))])
    m["ztl_taut"] = len([p for p in pool if all(v == T for v in L.sig(p, L.V))])
    m["new_laws"] = len([p for p in pool
                         if all(v == T for v in L.sig(p, L.V))
                         and not all(v == T for v in L.sig(p, L.CL))])

    m["docket"] = len(C.DOCKET)
    kinds = {}
    for _lab, system, _exp, _neg in C.DOCKET:
        kind, _models, _period, _comp = C.measure(system)
        kinds[kind] = kinds.get(kind, 0) + 1
    m["paradox"] = kinds.get("PARADOX", 0)
    m["underdetermined"] = kinds.get("UNDERDETERMINED", 0)
    m["classified"] = sum(kinds.values())

    # The Lean ground, asked of the ELABORATOR rather than of the file.
    # The file only contains `#print axioms`; the answer is the build's,
    # and it costs a fifth of a second from cache, so there is no excuse
    # for taking it on trust here. (A first, cold build is minutes; that
    # is `run_all.py`'s job, and this reads its cache.)
    out = subprocess.run(["lake", "env", "lean", "ClassicalAgreement.lean"],
                         cwd=os.path.join(_ROOT, "lean"),
                         capture_output=True, text=True, timeout=900).stdout
    clean = re.findall(r"'([\w.]+)' does not depend on any axioms", out)
    m["lean_clean"] = len(clean)
    m["lean_depending"] = len(re.findall(r"depends on axioms", out))
    m["lean_missing"] = 0 if any(c.endswith("ztl_taut_is_classical")
                                 for c in clean) else 1
    return m


# ------------------------------------------------------------------ the book
def build(m):
    """The corpus, as claims. A citation is written only where one result
    is worthless if another is wrong — not wherever two results are about
    the same subject. Getting that distinction right is the hand-work here,
    and it is where this file can be wrong."""
    return [
        # --- layer 0: is the instrument calibrated against the literature?
        ("control-T", "measured == published",
         f"measured={m['control_T']} earned:zsweep, published=6 earned:tomova"),
        ("control-TZ", "measured == published",
         f"measured={m['control_TZ']} earned:zsweep, published=24 "
         f"earned:tomova"),
        ("calibrated", "sum(check1,check2) == 2",
         "check1=1 earned:claim/control-T, check2=1 earned:claim/control-TZ"),

        # --- layer 1: the census of arrows. Worthless if uncalibrated.
        ("kin", "kin == 72",
         f"kin={m['kin']} earned:claim/calibrated"),
        ("no-identity", "with_id == 0",
         f"with_id={m['with_id']} earned:claim/kin"),
        ("no-order", "with_ord == 0",
         f"with_ord={m['with_ord']} earned:claim/kin"),
        ("price-forced", "sum(a,b) == 0",
         "a=0 earned:claim/no-identity, b=0 earned:claim/no-order"),

        # --- layer 1': agreement with classical logic
        ("lean-clean", "sum(depending,missing) == 0",
         f"depending={m['lean_depending']} earned:lake-build, "
         f"missing={m['lean_missing']} earned:lake-build"),
        ("no-new-laws", "sum(language,pool) == 0",
         f"language=0 earned:claim/lean-clean, "
         f"pool={m['new_laws']} earned:zledger"),
        ("strictly-fewer", "ztl < classical",
         f"ztl={m['ztl_taut']} earned:zledger, "
         f"classical={m['cl_taut']} earned:zledger"),

        # --- layer 2: the docket, which rests on the passport machinery
        ("docket-rows", "rows == 21",
         f"rows={m['docket']} earned:zclassify"),
        ("all-classified", "classified == rows",
         f"classified={m['classified']} earned:zpassport, "
         f"rows={m['docket']} earned:claim/docket-rows"),
        ("paradox-count", "n == 7",
         f"n={m['paradox']} earned:claim/all-classified"),
        ("underdetermined-count", "n == 8",
         f"n={m['underdetermined']} earned:claim/all-classified"),

        # --- layer 3: the headline reading, which needs both stacks
        ("the-thesis", "sum(forced,agrees,sorted_) == 3",
         "forced=1 earned:claim/price-forced, "
         "agrees=1 earned:claim/no-new-laws, "
         "sorted_=1 earned:claim/all-classified"),
    ]


# ------------------------------------------------------------------ sections
def sec1_the_corpus_recomputes(book):
    print("-" * 72)
    print("1. THE BOOK, RECOMPUTED FROM THE MODULES ON THIS RUN")
    res = judge_book(book)
    for cid, _f, _d in book:
        v = res[cid]
        cites = ",".join(v["cites"]) or "—"
        print(f"   {cid:24} {v['disposition']:9} on {cites}")
    print(f"   census: {census(res)}")
    bad = [c for c, v in res.items() if v["disposition"] != "EARNED"]
    assert not bad, bad
    print("   Every headline number of the corpus is EARNED, and not one of")
    print("   them was typed: they were measured here, this run, from the")
    print("   same modules the papers quote.")
    return res


def sec2_blast_radius(book):
    print("-" * 72)
    print("2. WHAT FALLS IF THIS IS WRONG — per ground, by name")
    grounds = sorted({w for _c, _f, d in book
                      for w in re.findall(r"earned:([^\s,]+)", d)
                      if not w.startswith("claim/")})
    rows = []
    for g in grounds:
        c = cost(book, g)
        rows.append((c["low"], g, [h[0] for h in c["as_declared"]],
                     c["high"], c["width"]))
    rows.sort(key=lambda r: (-r[0], r[1]))
    for n, g, who, high, width in rows:
        bracket = f"[{n}, {high}]" + ("" if not width else "  <- WIDE")
        print(f"   {g:32} {bracket:10}  {', '.join(who)}")
    print("   Every bracket above is a pair, never a single number: the low")
    print("   end believes the book's declarations and the high end assumes")
    print("   them false. Here the two coincide everywhere, because this")
    print("   book declares nothing — see §4.")
    worst = [r for r in rows if r[0] == rows[0][0]]
    names = ", ".join(r[1] for r in worst)
    print(f"   The most expensive single mistake would be in {names},")
    print(f"   at {rows[0][0]} of {len(book)} claims.")
    assert rows[0][0] >= 8 and "tomova" in names
    print("   And `tomova` is not one of our instruments. It is two numbers")
    print("   copied from the literature — the control that licenses reading")
    print("   the whole arrow census as measurement rather than as an")
    print("   artefact of our own encoding. So the corpus's dearest single")
    print("   point of failure is a CITATION, which no test here can check")
    print("   and only reading the source can. That was not the prediction")
    print("   before this ran (`zsweep`, five or six), and it is the reason")
    print("   a blast-radius column beats an intuition about one's own code.")
    return rows


def sec3_not_one_tower(book, rows):
    print("-" * 72)
    print("3. THE SHAPE: not one tower, a few short stacks")
    order, deps, cycles = _order(list(book))
    depth = {}
    for cid in order:
        depth[cid] = 1 + max([depth.get(d, 0) for d in deps[cid]] or [0])
    deepest = max(depth.values())
    roots = [c for c in depth if not deps[c]]
    print(f"   claims: {len(book)}, longest chain: {deepest}, "
          f"independent grounds: {len(rows)}, cycles: {len(cycles)}")
    print(f"   claims resting on nothing but an instrument: {len(roots)}")
    assert not cycles
    total = len(book)
    covered = max(r[0] for r in rows)
    print(f"   no single ground takes more than {covered} of {total} claims.")
    print("   That is worth reading in both directions. It means the corpus")
    print("   does not have one load-bearing wall — an error in the arrow")
    print("   census leaves the docket standing, and vice versa. It also")
    print("   means a green run is weaker evidence than it feels: separate")
    print("   stacks are separately checked, and agreement between them was")
    print("   never tested, because there is nothing to test — they do not")
    print("   talk to each other.")


# Which of our grounds we could re-establish ourselves, and which we could
# not. This is domain knowledge, not a graph property — the book cannot know
# it, so it is declared here, by hand, and it is the honest place for it.
RECOMPUTABLE = {"zsweep", "zledger", "zclassify", "zpassport", "lake-build"}


def sec4_the_trust_surface_of_our_own_corpus(book):
    print("-" * 72)
    print("4. HOW MUCH OF THIS IS OUR OWN WORD")
    t = trust_surface(book)
    print(f"   the machine's own trust surface: {t['on_declarations']} of "
          f"{t['earned']} earned claims rest on a declaration ({t['share']})")
    assert t["on_declarations"] == 0 and t["on_clocks"] == 0
    print("   Empty, and that is worth saying rather than assuming: this")
    print("   book contains no nullary grounds and no alternatives, so")
    print("   nothing here is earned on our unverifiable say-so.")
    grounds = sorted({w for _c, _f, d in book
                      for w in re.findall(r"earned:([^\s,]+)", d)
                      if not w.startswith("claim/")})
    outside = [g for g in grounds if g not in RECOMPUTABLE]
    hit = sorted({c for g in outside for c, _b, _a in fallout(book, g)})
    print(f"   grounds we re-establish on every run: "
          f"{sorted(set(grounds) & RECOMPUTABLE)}")
    print(f"   grounds we cannot re-establish at all: {outside}")
    print(f"   claims standing on those: {len(hit)} of {len(book)} — {hit}")
    assert outside == ["tomova"] and len(hit) == 8
    print("   So the real surface is not the machine's. Five of our six")
    print("   grounds are re-run from scratch every regression: if one had")
    print("   rotted we would know within the minute. The sixth is a pair of")
    print("   numbers read out of a paper, and no run of ours re-establishes")
    print("   it — only a person opening the source can. It carries 8 of 15")
    print("   claims, which is the same conclusion §2 reached from the other")
    print("   side, and the two roads meeting on it is the strongest thing")
    print("   this file says.")
    iv = trust_interval(book)
    widths = {g: hi - lo for g, (lo, hi) in iv.items()}
    print(f"   and the trust brackets, ground by ground: "
          f"{sorted(set(iv.values()))}")
    assert set(widths.values()) == {0}
    print("   Every bracket is zero-width. Read the book believing every")
    print("   declaration in it and read it assuming each one false, and")
    print("   the answer does not move — because there are no declarations")
    print("   to disbelieve. That is the strongest thing this book can say")
    print("   about itself, and unlike the sentence above it, it is checked")
    print("   rather than promised.")


def sec5_what_this_cannot_see():
    print("-" * 72)
    print("5. WHAT THIS CANNOT SEE")
    print("   The citations are hand-written. The machine honours them; it")
    print("   does not find them, and a dependence nobody wrote down is")
    print("   invisible here — so this file's own risk is an UNDERSTATED")
    print("   blast radius, never an overstated one.")
    print("   And it reads numbers, not prose: every claim above can stand")
    print("   while a sentence interpreting it in a paper is false. That")
    print("   gap is exactly where Frege's mistake lived, and nothing in")
    print("   this corpus closes it.")


def main():
    print("=" * 72)
    print("THE CORPUS AS A BOOK — what rests on what, and what would fall")
    print("=" * 72)
    m = measure_corpus()
    book = build(m)
    sec1_the_corpus_recomputes(book)
    rows = sec2_blast_radius(book)
    sec3_not_one_tower(book, rows)
    sec4_the_trust_surface_of_our_own_corpus(book)
    sec5_what_this_cannot_see()
    print("=" * 72)
    print("CORPUS BOOK GREEN — every headline result re-measured this run and")
    print("EARNED, with its grounds named. The blast radius is computed per")
    print("ground, so the question 'what falls if this is wrong' is answered")
    print("by name; and the answer's shape is that the corpus is a few short")
    print("stacks on separate instruments, not one tower — which limits both")
    print("the damage of any single error and the value of a green run.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
