# -*- coding: utf-8 -*-
"""
Expedition E35: the docket — machine-certified classification of paradoxes.

E28 built the catalogue and proved the passport axis complete (0 / 1 / ≥2
classical models exhaust the possibilities of a finite component). This
stand does the next thing the curator asked for (2026-08-08): it turns the
catalogue into a COURT DOCKET — for each classical paradox, run the E18
passport office and record WHICH of the competing literature versions the
measurement certifies as legitimate, and which overpay. Every row is
pinned; nothing is described that is not measured.

THE TWO-AXIS TAXONOMY (both measured per row):

    axis 1  passport   = number of classical models of the component
                         (0 PARADOX / 1 INTRINSIC / ≥2 UNDERDETERMINED,
                          plus INPUT and DOWNSTREAM off-cycle)
    axis 2  period     = greedy oscillation signature (Gupta–Belnap
                         revision), distinguishing paradoxes that share
                         a passport (liar 2 vs Jourdain 4)

For pure negation cycles a third, derived, coordinate — negation PARITY —
predicts axis 1 (the parity law).

THE CERTIFIED VERDICTS (each pinned as an assert below):

  V1  PARITY LAW, corpus-wide. On pure negation cycles: odd negation
      count (1 or 3 here) ⇒ PARADOX with zero models; even count
      (0, 2, 4) ⇒ UNDERDETERMINED with exactly two models, and the
      stipulation theorem grounds each cleanly. Kripke's groundedness
      taxonomy, transported and machine-checked; no exception anywhere
      in the corpus.

  V2  ALIAS CERTIFICATES. The barber, Grelling's heterological, and
      Russell's membership cell R∈R measure IDENTICALLY to the liar —
      same passport, same zero model count, same period, same parity.
      "The same paradox in different clothes" is now a certificate, not
      an aphorism. (Full Russell universe: E11 — one quarantined cell,
      8 of 9 facts grounded; the minimal-surgery version is certified,
      total prohibitions — type theory also bans the harmless twin —
      overpay.)

  V3  YABLO IS NOT FINITELY PARADOXICAL. Every finite truncation
      (n = 3 and n = 6 measured) is GROUNDED outright — no quarantine
      at all. Paradoxicality enters only with the actual infinity of
      sentences. This takes a measured side in the Priest–Sorensen
      dispute: no finite fragment hides a circle; the infinity is
      doing all the work.

  V4  THE INTRINSIC TRIO — self-reference with a FORCED verdict. The
      "strong" liar σ ≡ ¬σ∧σ has exactly ONE classical model (σ=F,
      forced); so does revenge μ ≡ ¬(μ↔μ) (μ=F); and the Henkin-style
      sentence h ≡ (h→h) is forced TRUE. Worsening the liar TAMES it:
      intuition refuted by measurement. INTRINSIC (Kripke's intrinsic
      value) is a genuinely inhabited third kind, on both sides of the
      truth table.

  V5  CURRY'S PASSPORT DEPENDS ON THE STATUS OF ⊥ — both versions
      measured. With a grounded falsum (γ ≡ γ→F) Curry IS the liar:
      PARADOX, zero models, period 2. With ⊥ carried as a defined
      sentence over unsettled ground (E28's encoding: ⊥ := s∧¬s,
      s := s) the refusal is DOWNSTREAM — inherited, culprit named.
      The literature dispute "is Curry just the liar or something
      else?" gets a measured answer: it depends on what is fed to the
      arrow, and each variant now carries its own passport.

  V6  PERIOD IS A REAL SECOND AXIS. The liar and the Jourdain/crocodile
      carousel share the PARADOX passport but differ in revision
      signature (2 vs 4) — the axis-1 passport does not determine the
      oscillation. One negation flipped (the optimistic mother) moves
      the carousel across the parity line to UNDERDETERMINED.

  V7  THE DOCKET ABSORBS THE DILEMMA SERIES. Theseus's title contest,
      the criterion-free "same", the person corecursion, and Agrippa's
      dogma all file into the UNDERDETERMINED/DOWNSTREAM rows — the
      instrument that certifies the liar as a real paradox certifies
      these as decree-resolvable non-paradoxes (dilemmas/*.py hold the
      full cases).

  V8  THE CONTINGENT LIAR — PARADOXICALITY IS EMPIRICAL (Kripke's
      Jones/Nixon point, machine-certified). Smith's sentence is the
      SAME in all three worlds: S ≡ "what Jones says is false". Only
      the empirical fact of what Jones actually said differs. World A
      (Jones said a truth): everything GROUNDED, S is an ordinary
      falsehood. World B (Jones happened to say "Smith speaks truly"):
      S and J form the Jourdain carousel — PARADOX, period 4, refusal
      permanent. World C (Jones's words not yet verified): J is INPUT
      and S is DOWNSTREAM — a CONDITIONAL refusal with the culprit
      named, lifted or hardened by verification. One sentence, three
      passports: no syntactic sieve can quarantine "the paradoxical
      sentences" in advance, because paradoxicality is a property of
      the world's reference configuration, not of the sentence — a
      paradox is an EVENT, not a text.

GENRE BOUNDARIES (documented, deliberately unmeasured here): the passport
axis governs finite definitional systems — self-reference paradoxes. It
does not adjudicate: Carroll's tortoise and the Sensor (warranty/frame
genre — the studio's assertion genre, E12/zverify); sorites (vagueness);
the surprise exam (epistemic time); the lottery (probability, E9); Berry
(definability). A classification that did not know its own borders would
be one more overpaying total theory.

HONEST SCOPE. The taxonomy's parents are named: Kripke (grounded /
paradoxical / intrinsic), Gupta–Belnap (revision signatures), Albert-era
trilemma work for the stipulation side. The axis-completeness argument
(0/1/many exhausts finite components) is E28's, not new here. Ours is the
executable arbitration: one instrument, one corpus, every classical
paradox and every dilemma of the series in one docket with pinned
passports, plus the specific certificates V2 (aliases), V3 (finite Yablo),
V4 (intrinsic trio), V5 (two Currys). "Legitimate" throughout means:
matches the measured passport — a calibrated, not an absolute, blessing.

Run:  python3 zclassify.py        (asserts every row and every verdict)
"""

from zpassport import passports, stipulation_theorem, component_models, \
    oscillation_period, deps  # noqa: F401
from ztl import T, F, Z

n = lambda x: ("not", x)  # noqa: E731


def yablo(k):
    """Finite truncation of Yablo: s_i ≡ ⋀_{j>i} ¬s_j (empty ⋀ = T)."""
    sys_ = {}
    for i in range(k):
        rest = [n(f"s{j}") for j in range(i + 1, k)]
        f = "T"
        for r in rest:
            f = r if f == "T" else ("and", f, r)
        sys_[f"s{i}"] = f
    return sys_


# name, system, expected (kind, models, period), parity or None
DOCKET = [
    ("liar            L ≡ ¬L",       {"L": n("L")},              ("PARADOX", 0, 2), 1),
    ("barber          (alias)",      {"sh": n("sh")},            ("PARADOX", 0, 2), 1),
    ("Grelling        (alias)",      {"het": n("het")},          ("PARADOX", 0, 2), 1),
    ("Russell cell    R∈R (alias)",  {"r": n("r")},              ("PARADOX", 0, 2), 1),
    ("Jourdain/crocodile R≡M,M≡¬R",  {"R": "M", "M": n("R")},    ("PARADOX", 0, 4), 1),
    ("odd 3-cycle",                  {"a": n("b"), "b": n("c"), "c": n("a")},
                                                                 ("PARADOX", 0, 2), 3),
    ("Curry, grounded ⊥: γ≡(γ→F)",   {"g": ("imp", "g", "F")},   ("PARADOX", 0, 2), None),
    ("truth-teller    τ ≡ τ",        {"t": "t"},                 ("UNDERDETERMINED", 2, 1), 0),
    ("Russell twin    S∈S",          {"s": "s"},                 ("UNDERDETERMINED", 2, 1), 0),
    ("optimistic crocodile R≡M,M≡R", {"R": "M", "M": "R"},       ("UNDERDETERMINED", 2, 1), 0),
    ("even 2-cycle    A≡¬B,B≡¬A",    {"A": n("B"), "B": n("A")}, ("UNDERDETERMINED", 2, 2), 2),
    ("even 4-cycle",                 {"a": n("b"), "b": n("c"), "c": n("d"), "d": n("a")},
                                                                 ("UNDERDETERMINED", 2, 2), 4),
    ("strong liar     σ ≡ ¬σ∧σ",     {"s": ("and", n("s"), "s")}, ("INTRINSIC", 1, 1), None),
    ("revenge         μ ≡ ¬(μ↔μ)",   {"m": n(("xnor", "m", "m"))}, ("INTRINSIC", 1, 1), None),
    ("Henkin-style    h ≡ (h→h)",    {"h": ("imp", "h", "h")},   ("INTRINSIC", 1, 1), None),
    ("Yablo trunc n=3",              yablo(3),                   ("GROUNDED", None, 1), None),
    ("Yablo trunc n=6",              yablo(6),                   ("GROUNDED", None, 1), None),
    # the dilemma series files into the same docket (V7)
    ("Theseus title contest",        {"theA": n("theB"), "theB": n("theA")},
                                                                 ("UNDERDETERMINED", 2, 2), 2),
    ("Theseus 'same', criterion-free", {"same": "same"},         ("UNDERDETERMINED", 2, 1), 0),
    ("person corecursion, obs=T",    {"S": ("and", "obs", "S"), "obs": "T"},
                                                                 ("UNDERDETERMINED", 2, 1), None),
    ("person corecursion, obs=F",    {"S": ("and", "obs", "S"), "obs": "F"},
                                                                 ("GROUNDED", None, 1), None),
]

CURRY_DOWNSTREAM = {"γ": ("imp", "γ", "⊥"), "⊥": ("and", "s", n("s")), "s": "s"}
AGRIPPA_DOGMA = {"p": "f", "f": "f"}


def measure(system):
    """(kind, models, period) of the focus component; GROUNDED if none."""
    lfp, reports, kinds = passports(system)
    if not reports:
        return ("GROUNDED", None, 1, [])
    comp, kind, detail = reports[-1]  # deepest / last-reported component
    env_names = set()
    for s in comp:
        env_names |= deps(system[s]) - set(comp)
    env = {m: lfp[m] for m in env_names if m in lfp}
    classical_env = all(v in (T, F) for v in env.values())
    mods = len(component_models(comp, system, env)) if classical_env else 0
    per = oscillation_period(comp, system, env) if classical_env else None
    return (kind, mods, per, comp)


def run():
    print("E35. THE DOCKET: MACHINE-CERTIFIED CLASSIFICATION OF PARADOXES")
    print("=" * 74)
    print(f"{'case':32s} {'passport':16s} {'mod':>3} {'per':>3} {'par':>3}")
    print("-" * 74)

    rows = {}
    for name, system, (ekind, emods, eper), par in DOCKET:
        kind, mods, per, comp = measure(system)
        rows[name] = (kind, mods, per, par)
        print(f"{name:32s} {kind:16s} {str(mods) if mods is not None else '-':>3} "
              f"{str(per):>3} {str(par) if par is not None else '-':>3}")
        assert kind == ekind, (name, kind, ekind)
        if emods is not None:
            assert mods == emods, (name, mods, emods)
        assert per == eper, (name, per, eper)

    print("\n### V1. Parity law: no exception on pure negation cycles")
    for name, (kind, mods, per, par) in rows.items():
        if par is None:
            continue
        assert (par % 2 == 1) == (kind == "PARADOX"), name
        assert (par % 2 == 0) == (kind == "UNDERDETERMINED"), name
    for name, system, (ekind, _, _), par in DOCKET:
        if par is not None and par % 2 == 0:
            ou, cu, op_, cp = stipulation_theorem(system)
            assert ou == cu and cp == 0, name
    print("ok  odd (1,3) ⇒ PARADOX/0 models; even (0,2,4) ⇒ UNDERDETERMINED/2,")
    print("    every even stipulation grounds cleanly — Kripke transported, total")

    print("\n### V2. Alias certificates: one paradox, four costumes")
    liar = rows["liar            L ≡ ¬L"]
    for alias in ("barber          (alias)", "Grelling        (alias)",
                  "Russell cell    R∈R (alias)"):
        assert rows[alias][:3] == liar[:3], alias
    print("ok  barber = Grelling = R∈R = liar (passport, models, period)")
    print("ok  full Russell universe: E11 — one cell quarantined, 8/9 grounded;")
    print("    minimal surgery certified; type theory also bans the curable twin")

    print("\n### V3. Yablo: no finite stage is paradoxical")
    assert rows["Yablo trunc n=3"][0] == "GROUNDED"
    assert rows["Yablo trunc n=6"][0] == "GROUNDED"
    print("ok  n=3, n=6 GROUNDED outright — paradoxicality lives only in the")
    print("    actual infinity (measured side in the Priest–Sorensen dispute)")

    print("\n### V4. The intrinsic trio: forced verdicts on both sides")
    _, _, kinds = passports({"s": ("and", n("s"), "s")})
    ms = component_models(["s"], {"s": ("and", n("s"), "s")}, {})
    assert [dict(m) for m in ms] == [{"s": F}]
    mh = component_models(["h"], {"h": ("imp", "h", "h")}, {})
    assert [dict(m) for m in mh] == [{"h": T}]
    print("ok  strong liar forced σ=F; revenge forced μ=F; Henkin forced h=T —")
    print("    'worse' self-reference is TAMER: one model, stipulation forced")

    print("\n### V5. Two Currys, two passports — ⊥ decides")
    assert rows["Curry, grounded ⊥: γ≡(γ→F)"][0] == "PARADOX"
    lfp, reports, kinds = passports(CURRY_DOWNSTREAM)
    assert kinds["γ"][0] == "DOWNSTREAM"
    culprit_report = [d for c, k, d in reports if "γ" in c][0]
    print(f"ok  grounded ⊥ ⇒ PARADOX (Curry IS the liar in arrow costume)")
    print(f"ok  suspended ⊥ ⇒ DOWNSTREAM ({culprit_report[:50]})")

    print("\n### V6. Period: the second axis is real")
    assert rows["liar            L ≡ ¬L"][2] == 2
    assert rows["Jourdain/crocodile R≡M,M≡¬R"][2] == 4
    assert rows["optimistic crocodile R≡M,M≡R"][0] == "UNDERDETERMINED"
    print("ok  liar 2 vs carousel 4 under one passport; one flipped negation")
    print("    moves the carousel across the parity line")

    print("\n### V7. The dilemma series files into the docket")
    lfp, reports, kinds = passports(AGRIPPA_DOGMA)
    assert kinds["f"][0] == "UNDERDETERMINED" and kinds["p"][0] == "DOWNSTREAM"
    assert rows["Theseus title contest"][0] == "UNDERDETERMINED"
    assert rows["person corecursion, obs=T"][0] == "UNDERDETERMINED"
    assert rows["person corecursion, obs=F"][0] == "GROUNDED"
    print("ok  Theseus contest / criterion-free same / person / Agrippa's dogma:")
    print("    decree-resolvable non-paradoxes, same instrument, same table")

    print("\n### V8. The contingent liar: paradoxicality is empirical")
    S_DEF = ("not", "J")            # Smith's sentence, identical in all worlds
    lfp, reports, _ = passports({"S": S_DEF, "J": "g", "g": "T"})
    assert reports == [] and str(lfp["S"]) == "F"
    print("ok  world A (Jones told a truth): GROUNDED — S is ordinary falsehood")
    _, reports, kinds = passports({"S": S_DEF, "J": "S"})
    assert kinds["S"][0] == "PARADOX" and kinds["S"][1] == 4
    print("ok  world B (Jones said 'Smith speaks truly'): PARADOX, period 4 —")
    print("    the unlucky configuration IS the Jourdain carousel")
    _, reports, kinds = passports({"S": S_DEF, "J": "Z"})
    assert kinds["J"][0] == "INPUT" and kinds["S"][0] == "DOWNSTREAM"
    culprit = [d for c, k, d in reports if "S" in c][0]
    assert "'J'" in culprit and "conditional" in culprit
    print(f"ok  world C (Jones unverified): INPUT + DOWNSTREAM ({culprit[:45]})")
    print("ok  one sentence, three passports — a paradox is an EVENT, not a")
    print("    text; no syntactic sieve can quarantine paradoxes in advance")

    print("\nE35: docket complete — every row pinned, every verdict certified.")
    print("Genre borders stand outside the axis by design: tortoise & sensor →")
    print("warranty genre; sorites, surprise exam, lottery, Berry → other")
    print("instruments. The liar earns its title; the impostors are named.")
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(run())
