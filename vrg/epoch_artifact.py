# -*- coding: utf-8 -*-
"""
The FROZEN ARTIFACT — Institutional Computation worked example on the ZTL core.

Agreed with A. (Veraxis) 2026-07-18/19; implements the reviewed spec verbatim:

  * three-coordinate cell per state:  (epistemic_status, decision, warrant)
    — epistemic_status: supervaluation over the unknowns (Z = not established;
      never conflated with F);
    — decision: the POLICY layer (ALLOW_EXECUTION / DENY_EXECUTION) — the
      greedy operational verdict; Z at the epistemic layer maps to DENY here;
    — warrant: the grade ladder (until-verification / sound / hereditary),
      hereditary being machine-licensed (Lean, empty axiom list) AGAINST
      FURTHER VERIFICATION WITHIN THE SAME EPOCH — never against world change.
  * event taxonomy:
      verify           — knowledge refines, same world state; keeps the epoch;
      evidence_expire  — a confirmation lapses, the atom returns to Z;
                         OPENS A NEW EPOCH;
      revoke           — DERIVED: composed_of [evidence_expire, verify(new)],
                         each component carrying its own source_reference;
                         opens a new epoch and grounds the new fact in it.
  * every event carries source_reference; an event WITHOUT a source is an
    UNGROUNDED VERIFICATION EVENT and is REJECTED — the closed-world loan
    ("no proof of revocation, hence not revoked") cannot enter as a tick;
    the core itself refuses the argument from absence. The check is stated
    on the atom it is ABOUT: with R = `revoked` unverified (R = Z), the
    proposition ¬R ("not revoked") evaluates F/until-verification — never
    T. (`fresh` is NOT that atom: it already MEANS "not revoked", the
    opposite polarity; the earlier draft computed ¬fresh under the ¬revoked
    label — corrected on review, A., 2026-07-19.)
  * rejected events are part of the FROZEN RECORD, not merely printed:
    the JSON carries `rejected_events` with source_reference: null,
    decision: "REJECT_EVENT", a stable `reason_code`
    (E_UNGROUNDED_VERIFICATION), `state_unchanged: true` and the untouched
    three-coordinate cell nested under `state_after` (so the event's own
    disposition is never shadowed by the state's decision).

Scenario = the two reviewed formulations:
  F1  admission = power ∧ confirmed ∧ jurisdiction ∧ fresh (iff; power alone
      insufficient), all atoms starting Z;
  F2  admissible at t0, then before execution at t1 EITHER the confirmation
      lapses (branch A: evidence_expire) OR the ground is authoritatively
      revoked (branch B: revoke) — the reviewed target cells:
        evidence_expire(fresh)  ⟹  (Z, DENY_EXECUTION, until-verification)
        revoke ⟹ fresh = F      ⟹  (F, DENY_EXECUTION, hereditary)   [new epoch]

Reproduce:  python3 vrg/epoch_artifact.py
Output:     the ledger below + vrg/epoch_artifact.json (deterministic).
Both target cells are asserted; the run fails loudly if the core drifts.
"""
import json
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F                                     # noqa: E402
from zmodal import ztl_eval, global_super                # noqa: E402
from zverify import grade, verify                        # noqa: E402

ADMIT = ("and", "power", ("and", "confirmed",
         ("and", "jurisdiction", "fresh")))
ATOMS = ("power", "confirmed", "jurisdiction", "fresh")


class UngroundedVerificationEvent(Exception):
    """A verification tick with no source: the CWA loan, made visible."""


def cell(marking):
    """The three-coordinate cell of the current state."""
    epi = global_super(ADMIT, marking)
    op = ztl_eval(ADMIT, marking)
    return {"epistemic_status": epi,
            "decision": ("ALLOW_EXECUTION" if op == T else "DENY_EXECUTION"),
            "warrant": grade(ADMIT, marking)}


class Ledger:
    def __init__(self):
        self.epoch = 0
        self.marking = {a: "M" for a in ATOMS}
        self.rows = []
        self.rejected = []          # ungrounded events, kept in the ledger

    def _row(self, event_type, atom, source, composed=None):
        r = {"epoch_id": self.epoch, "event_type": event_type, "atom": atom,
             "source_reference": source, **cell(self.marking)}
        if composed:
            r["composed_of"] = composed
        self.rows.append(r)
        return r

    def verify(self, atom, value, source):
        if not source:
            # An ungrounded verification event: recorded, never applied.
            # The state is left untouched; the ledger keeps the attempt so
            # that the refusal is auditable, not merely printed.
            self.rejected.append(
                {"epoch_id": self.epoch, "event_type": "verify",
                 "atom": f"{atom} := {value}", "source_reference": None,
                 "decision": "REJECT_EVENT",
                 "reason_code": "E_UNGROUNDED_VERIFICATION",
                 "reason": "a verification tick without a source_reference; "
                           "the closed-world assumption (no proof of "
                           "revocation, hence not revoked) is not admissible "
                           "as ground",
                 "state_unchanged": True,
                 # the state cell is nested, so the event's own disposition
                 # (REJECT_EVENT) is never shadowed by the state's decision
                 "state_after": cell(self.marking)})
            raise UngroundedVerificationEvent(
                f"verify({atom}:={value}) carries no source_reference — "
                "the closed-world loan is not admissible as a tick")
        self.marking = verify(self.marking, atom, value)
        return self._row("verify", f"{atom} := {value}", source)

    def evidence_expire(self, atom, source):
        self.epoch += 1                       # validity chronology: new epoch
        m = dict(self.marking)
        m[atom] = "M"
        self.marking = m
        return self._row("evidence_expire", f"{atom} -> Z", source)

    def revoke(self, atom, new_value, src_expire, src_verify):
        """Derived event: composed_of [evidence_expire, verify(new)]."""
        self.epoch += 1
        m = dict(self.marking)
        m[atom] = "M"
        self.marking = verify(m, atom, new_value)
        composed = [{"component": "evidence_expire",
                     "atom": f"{atom} -> Z", "source_reference": src_expire},
                    {"component": "verify",
                     "atom": f"{atom} := {new_value}",
                     "source_reference": src_verify}]
        return self._row("revoke", f"{atom} := {new_value}", None,
                         composed=composed)


def show(row):
    c = (f"  [{'|'.join(x['component'] for x in row['composed_of'])}]"
         if "composed_of" in row else "")
    src = row["source_reference"] or "(per component)"
    print(f"  E{row['epoch_id']}  {row['event_type']:16s} "
          f"{row['atom']:22s} ({row['epistemic_status']}, "
          f"{row['decision']:15s}, {row['warrant']}){c}")
    print(f"      source: {src}")


if __name__ == "__main__":
    print("=" * 76)
    print("THE FROZEN ARTIFACT — Institutional Computation on the ZTL core")
    print("  admission = power AND confirmed AND jurisdiction AND fresh")
    print("  cell = (epistemic_status, decision, warrant); epochs split")
    print("  knowledge chronology (verify) from validity chronology (expire)")
    print("=" * 76)

    # ---- t0, epoch 0: the four checks arrive -----------------------------
    print("\n### t0 — epoch E0: verification chronology (the world unchanged)")
    L = Ledger()
    start = cell(L.marking)
    print(f"  E0  start            all atoms Z          "
          f"({start['epistemic_status']}, {start['decision']}, "
          f"{start['warrant']})")
    assert start == {"epistemic_status": "Z", "decision": "DENY_EXECUTION",
                     "warrant": "until-verification"}
    show(L.verify("power", T, "mandate-registry:2026-07-19:rec-4411"))
    show(L.verify("confirmed", T, "source-attestation:notary:file-88K"))
    show(L.verify("jurisdiction", T, "legal-desk:jurisdiction-memo-17"))
    t0 = L.verify("fresh", T, "revocation-registry:negative-clearance-901")
    show(t0)
    assert (t0["epistemic_status"], t0["decision"], t0["warrant"]) == \
        (T, "ALLOW_EXECUTION", "hereditary")
    print("  -> admissible at t0: (T, ALLOW_EXECUTION, hereditary) — the")
    print("     hereditary license is intra-epoch: further VERIFICATION")
    print("     cannot revoke it (Lean, empty axiom list); world change can.")

    # ---- branch A: the confirmation lapses (no new fact) -----------------
    print("\n### t1, branch A — evidence_expire: the clearance window lapses")
    A = Ledger()
    A.marking = dict(L.marking)
    A.rows = []
    a1 = A.evidence_expire("fresh",
                           "clearance-901:validity-window-elapsed")
    show(a1)
    assert (a1["epistemic_status"], a1["decision"], a1["warrant"]) == \
        ("Z", "DENY_EXECUTION", "until-verification")
    print("  -> the reviewed cell: evidence_expire => (Z, DENY, until-")
    print("     verification): NOT established, blocked until a NEW positive")
    print("     check; Z is never conflated with F.")

    # the ungrounded verification event is REJECTED
    print("\n  the closed-world loan, attempted and refused:")
    try:
        A.verify("fresh", T, source=None)
        raise AssertionError("an ungrounded tick was accepted")
    except UngroundedVerificationEvent as e:
        print(f"    REJECTED: {e}")
    # The CWA loan is about the atom `revoked` itself (R), NOT about
    # `fresh` (which already MEANS "not revoked" — the opposite polarity).
    # With R unverified, the core is asked whether "not revoked" holds.
    R_UNKNOWN = {"revoked": "M"}
    NOT_R = ("not", "revoked")
    nr, nrg = ztl_eval(NOT_R, R_UNKNOWN), grade(NOT_R, R_UNKNOWN)
    print(f"    and inside the core: '\u00acrevoked' at revoked=Z evaluates "
          f"{nr}/{nrg} — the argument")
    print("    from absence never yields T; absence of proof of revocation")
    print("    is not proof of absence.")

    # ---- branch B: authoritative revocation (a new fact) -----------------
    print("\n### t1, branch B — revoke: the ground is authoritatively changed")
    B = Ledger()
    B.marking = dict(L.marking)
    B.rows = []
    b1 = B.revoke("fresh", F,
                  src_expire="revocation-notice:authority:2026-1907",
                  src_verify="revocation-notice:authority:2026-1907")
    show(b1)
    assert (b1["epistemic_status"], b1["decision"], b1["warrant"]) == \
        (F, "DENY_EXECUTION", "hereditary")
    print("  -> the reviewed cell: revoke => fresh=F => (F, DENY, hereditary)")
    print("     in the NEW epoch E1 — an EARNED refusal, distinct by type")
    print("     from branch A's (Z, DENY, until-verification).")

    # ---- the t0 -> t1 carry, refused ------------------------------------
    print("\n### the transfer admit(t0) -> admit(t1) without a new check")
    print("  DOES NOT FOLLOW (counterexample {admit_t0=T, fresh_t1=F}, see")
    print("  the reviewed run): the t0 warrant explains the t0 decision; it")
    print("  does not legitimize reliance across an epoch boundary.")

    # ---- freeze the ledger ----------------------------------------------
    out = {"artifact": "IC worked example on the ZTL core",
           "admission_formula":
               "and(power, and(confirmed, and(jurisdiction, fresh)))",
           "epoch_rule": "verify keeps the epoch; evidence_expire and "
                         "revoke open a new one",
           "t0_epoch0": L.rows,
           "t1_branch_A_evidence_expire": A.rows,
           "t1_branch_B_revoke": B.rows,
           "rejected_events": L.rejected + A.rejected + B.rejected}
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "epoch_artifact.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)
    print(f"\n  ledger frozen: vrg/epoch_artifact.json "
          f"({sum(len(r) for r in (L.rows, A.rows, B.rows))} events)")
    print("\n  == the frozen cells ==")
    print("  t0  verify x4        -> (T, ALLOW_EXECUTION,  hereditary)   E0")
    print("  t1A evidence_expire  -> (Z, DENY_EXECUTION,   until-verif.) E1")
    print("  t1B revoke [composed]-> (F, DENY_EXECUTION,   hereditary)   E1")
    print("  ungrounded verify    -> REJECTED (the CWA loan, visible)")
