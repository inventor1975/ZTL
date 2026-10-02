# -*- coding: utf-8 -*-
"""firewall — the AMPS black-hole firewall through the ZTL lens: the debate reduced to one question.

Second modern target (the curator's line of 2026-10-02). The prediction was written BEFORE this file ran
(ztl-private/notes/FIREWALL-PREDICTION-2026-10-02.md, 12:02).

  THE ARGUMENT (Almheiri, Marolf, Polchinski, Sully 2012). An old black hole; B a late outgoing mode.
      BR  unitarity: B is maximally entangled with the early radiation R;
      BA  no drama: an infaller sees vacuum, so B is maximally entangled with its interior partner A;
      monogamy (a theorem): not both. AMPS: drop BA — a firewall at the horizon.

  F1  EACH PREMISE HAS ITS OWN WITNESS. BR is redeemable by the outside decoder (who collects and
      decodes R); BA by the infaller. Each alone has a future that earns it.

  F2  THE CONJUNCTION IS THE QUESTION. Under Harlow-Hayden (2013: decoding R takes longer than the hole
      lives, so the decoder cannot then jump in and check B-A), for EITHER observer the other premise is
      Z_PERMANENT and "BR & BA" has a frozen ceiling: monogamy refutes a conjunction nobody can earn, and
      no firewall follows from earned premises. Under Oppenheim-Unruh (2014: a protocol claimed to evade
      Harlow-Hayden, one observer able to check both), the conjunction is redeemable, monogamy's
      refutation is real, and ZTL cannot dismiss AMPS.

  So ZTL does NOT settle the firewall. It reduces the debate to the repertoire question — "is there an
  act that witnesses both entanglements?" — which is exactly what Harlow-Hayden and Oppenheim-Unruh argue
  about. As predicted. The same criterion as wigner_friends.py with a new nuance: there the records were
  ERASED; here two facts are each witnessable but not JOINTLY (complementarity, as bell.py's unmade
  readings).

  PRIOR ART, plainly: AMPS 2012; Susskind's black-hole complementarity (1993); Harlow & Hayden 2013;
  Oppenheim & Unruh 2014; ER=EPR (Maldacena & Susskind 2013). The physics input — who can witness what —
  is theirs; ZTL only keeps the books. Not new physics.

Run:  python3 dilemmas/firewall.py        (asserts every measurement)
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from zredeem import ceiling, stamp  # noqa: E402

M = {"BR": "Z", "BA": "Z", "mono": "T"}
SCENARIOS = {
    "Harlow-Hayden, outside decoder": {"BR", "mono"},
    "Harlow-Hayden, infaller": {"BA", "mono"},
    "Oppenheim-Unruh, one observer": {"BR", "BA", "mono"},
}


def run():
    print("FIREWALL — AMPS through the ZTL lens")
    print("=" * 72)

    print("\n### F1. Each premise has its own witness")
    br = ceiling("BR", M, {"BR"})["earned_futures"]
    ba = ceiling("BA", M, {"BA"})["earned_futures"]
    print(f"ok  BR for the outside decoder: {br} earned future; BA for the infaller: {ba} earned future")
    assert br == 1 and ba == 1

    print("\n### F2. The conjunction is the question")
    for label, rep in SCENARIOS.items():
        c = ceiling("BR & BA", M, rep)
        st = {a: stamp(a, M, rep) for a in ("BR", "BA")}
        print(f"ok  {label:32s} 'BR & BA' frozen={c['ceiling_frozen']}, earned futures "
              f"{c['earned_futures']}/{c['futures']}, stamps {st}")
        if label.startswith("Harlow"):
            assert c["ceiling_frozen"] and "Z_PERMANENT" in st.values()
        else:
            assert not c["ceiling_frozen"] and set(st.values()) == {"Z_REDEEMABLE_STABLE"}

    print("\nFIREWALL: all measurements hold.")
    print("ZTL does not settle the firewall; it reduces it to one question: can one act witness both?")


if __name__ == "__main__":
    run()
