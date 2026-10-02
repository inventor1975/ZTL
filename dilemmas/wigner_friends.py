# -*- coding: utf-8 -*-
"""wigner_friends — Frauchiger-Renner (2018) through the ZTL lens: which step of the chain fails.

The curator's line of 2026-10-02: "go to the present; there will be the same dilemmas." The first modern
target: FR's no-go, "quantum theory cannot consistently describe the use of itself". The prediction was
written BEFORE this file ran (ztl-private/notes/FR-PREDICTION-2026-10-02.md, 11:54).

  THE SETUP. F-bar tosses a quantum coin (heads 1/3, tails 2/3) and prepares a spin (heads: down;
  tails: (up+down)/sqrt2); F measures the spin. W-bar measures F-bar's whole lab in {ok-bar, fail-bar},
  then W measures F's whole lab in {ok, fail}. Three statements, each certain when made:
      F-bar, on tails:      "W will see fail";
      F,     on up:         "F-bar saw tails";
      W-bar, on ok-bar:     "F saw up".
  Chained: W-bar sees ok-bar => F saw up => F-bar saw tails => W sees fail. Yet in 1/12 of runs both
  Wigners see ok. FR: drop Q (QM applies to agents), C (agents' conclusions combine) or S (one outcome).

  W1  THE PHYSICS, from amplitudes (asserted): P(ok-bar, ok) = 1/12; each statement's exception has
      probability 0; and "F-bar saw tails" does not commute with "W-bar saw ok-bar", nor "F saw up" with
      "W saw ok" — the records the chain needs cannot be witnessed together with the Wigners' outcomes.

  W2  THE LENS, at W's time in the contested run. "W saw ok" is EARNED. FR's chain, ending in "W will see
      fail", is REFUTED by the observation — and its weak links are exactly "F saw up" and "F-bar saw
      tails", both Z_PERMANENT (erased, no act can witness them now), the chain's ceiling frozen: it could
      never have been earned at W's time. The contradiction refutes nothing that was earned; it lands on
      records that no longer exist. So the failing assumption is C, in a narrow form: conclusions combine
      only while their grounds are held — facts are not absent, they EXPIRE with their record.
      As predicted. A side measurement: even at F's own time "F-bar saw tails" is an INFERENCE (from the
      QM rule), not a witnessing — OPEN in ZTL — while F-bar, who saw it, had it earned.

  PRIOR ART, plainly: Frauchiger & Renner (Nat. Commun. 2018); Brukner ("no observer-independent facts",
  2018); Bong et al. (Nat. Phys. 2020, local friendliness); Di Biagio & Rovelli ("stable facts, relative
  facts", 2021) — the nearest: facts are stable only while decoherence holds them. ZTL takes the same side
  of the live debate (against dropping Q or S), for an operational reason it shares with the rest of the
  series: the classical step that fails is the one that leans on an atom no act can witness —
  identity (indistinguishable.py, ZQuasi), routes (Hong-Ou-Mandel), unmade readings (bell.py), erased
  records (here). Not new physics; one criterion, four places.

Run:  python3 dilemmas/wigner_friends.py        (asserts every measurement)
"""

import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import ceiling, stamp  # noqa: E402

S3, R2 = 1 / math.sqrt(3), 1 / math.sqrt(2)
PSI = {("h", "dn"): S3, ("t", "up"): S3, ("t", "dn"): S3}
OKBAR = {"h": R2, "t": -R2}
OK = {"dn": R2, "up": -R2}
COIN = {"h": {"h": 1, "t": 0}, "t": {"h": 0, "t": 1}}
SPIN = {"up": {"up": 1, "dn": 0}, "dn": {"up": 0, "dn": 1}}


def prob(br, bz):
    a = sum(PSI.get((r, z), 0) * br[r] * bz[z] for r in "ht" for z in ("up", "dn"))
    return a * a


def commutator(u, v):
    P = [[u[a] * u[b] for b in u] for a in u]
    Q = [[v[a] * v[b] for b in v] for a in v]
    PQ = [[sum(P[i][k] * Q[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    QP = [[sum(Q[i][k] * P[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    return max(abs(PQ[i][j] - QP[i][j]) for i in range(2) for j in range(2))


def run():
    print("WIGNER'S FRIENDS — Frauchiger-Renner through the ZTL lens")
    print("=" * 72)

    print("\n### W1. The physics, from amplitudes")
    both = prob(OKBAR, OK)
    s1, s2, s3 = prob(COIN["t"], OK), prob(COIN["h"], SPIN["up"]), prob(OKBAR, SPIN["dn"])
    c1 = commutator(COIN["t"], OKBAR)
    c2 = commutator({"up": 1, "dn": 0}, {"up": OK["up"], "dn": OK["dn"]})
    print(f"ok  P(ok-bar, ok) = {both:.4f} (1/12); exceptions to the three statements: {s1:.4f} {s2:.4f} {s3:.4f}")
    print(f"ok  [tails, ok-bar] = {c1:.3f}, [up, ok] = {c2:.3f}: not jointly witnessable")
    assert abs(both - 1 / 12) < 1e-12 and max(s1, s2, s3) < 1e-12 and c1 > 0.1 and c2 > 0.1

    print("\n### W2. The lens, at W's time in the contested run")
    m = {"wbar_ok": "T", "w_ok": "T", "r_t": "Z", "z_up": "Z"}
    rep = {"wbar_ok", "w_ok"}
    seen = judge("w_ok", m)["disposition"]
    chain = "wbar_ok & (wbar_ok -> z_up) & (z_up -> r_t) & (r_t -> ~w_ok) & ~w_ok"
    r = judge(chain, m)
    c = ceiling(chain, m, rep)
    st = {a: stamp(a, m, rep) for a in ("r_t", "z_up")}
    print(f"ok  'W saw ok': {seen}; FR's chain to 'W will see fail': {r['disposition']}, weak links "
          f"{sorted(r['unverified'])}, ceiling frozen = {c['ceiling_frozen']}; stamps {sorted(set(st.values()))}")
    assert seen == "EARNED" and r["disposition"] == "REFUTED"
    assert sorted(r["unverified"]) == ["r_t", "z_up"] and c["ceiling_frozen"]
    assert set(st.values()) == {"Z_PERMANENT"}
    inferred = judge("z_up & (z_up -> r_t)", {"z_up": "T", "r_t": "Z"})["disposition"]
    print(f"ok  at F's own time, 'F-bar saw tails' from 'F saw up' and the rule: {inferred} (an inference, not a witnessing)")
    assert inferred == "OPEN"

    print("\nWIGNER'S FRIENDS: all measurements hold.")
    print("The contradiction lands on erased records, never on an earned fact: conclusions combine only while their grounds are held.")


if __name__ == "__main__":
    run()
