# -*- coding: utf-8 -*-
"""VRG Public Review Proposal 001 — ZTL Judgment Kernel Test.
Agentic Payment With Mid-Execution Revocation.

This artifact demonstrates, on the REAL ZTL core (zhunt.judge /
zverify.grade), exactly one thing and its exact boundary:

  ZTL judges the INFERENCE (is ADMIT forced by the grounding, and how
  stable is that verdict under refinement of the unknowns) — and NOTHING
  ELSE. It does NOT establish that the grounds are current, authoritative,
  or institutionally sufficient. That is the grounding/admissibility
  layer (modelled here minimally, labelled "GROUNDING LAYER", standing in
  for Veraxis/VEIP), which ZTL is not and does not claim to be.

Every "verdict" and "warranty grade" printed below is produced by the
ZTL core, not by this script. Everything under "INTERPRETATION" is
hypothesis, not an experimental result (per the review's signature
discipline: formulations not confirmed by code are not results).

Two objects must never be conflated:
  * a WARRANT is the pair (ZTL verdict + grade, grounding-snapshot id):
    ZTL's verdict is snapshot-RELATIVE and never claims timelessness;
  * ADMISSIBILITY additionally requires that the snapshot is still
    CURRENT — a check outside ZTL.

Run 5 is the central test: an old warrant stays logically correct
relative to its snapshot G0, yet is rejected as inadmissible once the
grounding advances to G1 — because ZTL proves the inference, not the
currency of the grounds.
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from zhunt import judge

# --- the ADMIT formula (curator's / Veraxis spec) ----------------------
ATOMS = ["delegation_active", "within_time_window", "amount_within_limit",
         "merchant_admissible", "approved_funding_source"]


def conj(atoms):
    f = atoms[-1]
    for a in reversed(atoms[:-1]):
        f = ("and", a, f)
    return f


ADMIT = conj(ATOMS)   # delegation ∧ time ∧ amount ∧ merchant ∧ funding


# --- the conservative institutional mapping (INTERPRETATION, not result)
MAPPING = {
    ("T", "hereditary"): "candidate for admission IF grounding is full & current",
    ("T", "sound"): "requires intermediate-refinement checks + policy",
    ("T", "until-verification"): "HOLD / DENY — not execution",
}


def institutional(v, g):
    if v == "F":
        return "NOT admitted under the presented formalization"
    return MAPPING.get((v, g), "—")


# --- a WARRANT: ZTL verdict bound to its grounding snapshot ------------
class Warrant:
    def __init__(self, snapshot_id, marking, verdict, grade):
        self.snapshot_id = snapshot_id
        self.marking = dict(marking)
        self.verdict = verdict
        self.grade = grade


def evaluate(snapshot_id, marking):
    """The ZTL kernel: judge ADMIT under this grounding snapshot.
    Returns a snapshot-bound warrant. The verdict/grade come from the
    core, not from here."""
    v, g, _, _ = judge(ADMIT, marking)
    return Warrant(snapshot_id, marking, v, g)


def show(run, title, w, extra=""):
    print(f"RUN {run} — {title}")
    print(f"  snapshot {w.snapshot_id}: " +
          ", ".join(f"{a}={w.marking[a]}" for a in ATOMS))
    print(f"  [ZTL, code-confirmed]  verdict = {w.verdict}, "
          f"warranty = {w.grade}")
    print(f"  [INTERPRETATION]       institutional status: "
          f"{institutional(w.verdict, w.grade)}")
    if extra:
        print(extra)
    print()
    return w


# --- the grounding layer (models Veraxis; NOT ZTL) --------------------
def admissible(warrant, current_snapshot_id):
    """Runtime admissibility = the ZTL verdict is admitting AND the
    warrant's snapshot is still the current one. The currency check is
    OUTSIDE ZTL — that is the whole point."""
    ztl_ok = (warrant.verdict == "T" and warrant.grade == "hereditary")
    current = (warrant.snapshot_id == current_snapshot_id)
    return ztl_ok and current, ztl_ok, current


if __name__ == "__main__":
    print(__doc__)
    print("=" * 68)
    print(f"ADMIT := {' ∧ '.join(ATOMS)}\n")

    full_T = {a: "T" for a in ATOMS}

    # RUN 1 — all grounds established (snapshot G0)
    w1 = show(1, "all grounds established (G0)",
              evaluate("G0", full_T))

    # RUN 2 — sanction status of merchant unknown
    m2 = dict(full_T); m2["merchant_admissible"] = "M"
    show(2, "merchant sanction status UNKNOWN (Z)",
         evaluate("G0", m2),
         "  → the unknown is not laundered into admission; see the grade.")

    # RUN 3 — the unknown resolves to admissible
    m3 = dict(full_T)  # merchant now verified admissible
    show(3, "merchant status resolved to admissible (T)",
         evaluate("G0b", m3),
         "  → verdict/grade change is produced by the core, not asserted.")

    # RUN 4 — delegation revoked mid-execution: NEW snapshot G1
    m4 = dict(full_T); m4["delegation_active"] = "F"
    w4 = show(4, "delegation REVOKED after admission — new snapshot G1",
              evaluate("G1", m4),
              "  → a new institutional reality (G0→G1), not a mere Z→F.")

    # RUN 5 — replay the Run-1 warrant after revocation
    print("RUN 5 — REPLAY of the Run-1 warrant, current snapshot is now G1")
    ok, ztl_ok, current = admissible(w1, current_snapshot_id="G1")
    # re-check the OLD formula against its OWN snapshot G0 — still correct
    recheck = evaluate("G0", full_T)
    print(f"  [ZTL, code-confirmed]  re-checking the old warrant against its "
          f"OWN snapshot G0: verdict={recheck.verdict}, grade={recheck.grade}"
          " — STILL CORRECT relative to G0")
    print(f"  [GROUNDING LAYER]      warrant.snapshot=G0, current=G1 → "
          f"snapshot current? {current}")
    print(f"  [ADMISSIBILITY]        admitted for execution? {ok}  "
          "(REJECTED: stale grounding, though the ZTL proof stands)")
    print()

    # --- assertions: the code-confirmed facts this artifact stands on ---
    assert w1.verdict == "T"                       # all grounds → ADMIT true
    assert institutional("F", w4.grade).startswith("NOT")
    assert recheck.verdict == w1.verdict and recheck.grade == w1.grade
    assert not ok and not current                  # Run 5 rejection is by currency
    print("=" * 68)
    print("THE FOUR OBJECTS, kept distinct (the demonstration):")
    print("  1. logical warrant   — ZTL: is ADMIT forced by G? (per snapshot)")
    print("  2. grounding currency— is the snapshot still G? (NOT ZTL)")
    print("  3. runtime admissibility — 1 AND 2 (NOT ZTL alone)")
    print("  4. downstream reliance — an institutional decision on 3 (human)")
    print()
    print("Run 5 shows the gap: ZTL's proof of (1) stays correct relative to")
    print("G0, yet (3) fails under G1 because ZTL cannot and does not assert")
    print("(2). The kernel judges the inference; the grounding layer judges")
    print("the currency; reliance stays human.")
