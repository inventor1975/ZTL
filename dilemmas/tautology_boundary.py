# -*- coding: utf-8 -*-
"""
tautology_boundary — calibrating the operational/material boundary with
an answer known in advance.

The curator's move, 2026-07-20: we sit on the seam between the
operational and the material, and even a careful reasoner glitches there
(nine times in one day, this file's author included). So do not send the
machine a question whose answer we want. Send it one that **cannot come
back false**, and measure whether it does.

That is the cheapest probe of any instrument, and it is the discipline
this repository already keeps in software: `kripke.py` refuses to judge
anything until it has calibrated itself on eight known facts;
`pssl/grounds.py` aborts if its Python MO2 disagrees with the Lean one.
Here the same discipline is carried to the MATERIAL boundary.

THE TAUTOLOGY IS OURS, not physics'. A physical certainty (prepare |0⟩,
measure Z) would calibrate IBM. We want to calibrate the round trip
    operational verdict → material device → operational verdict
so the invariant has to be a theorem of our own kernel:

    `ZTime.hereditary_absorbing` (lean/ZTime.lean, EMPTY axiom list):
    once a verdict is hereditary at a marking, verifying any marked atom
    to ANY value leaves the verdict unchanged — and hereditary.

So: let the device's measured bits BE the verifications. The verdict is
forbidden by theorem to move, whatever the hardware says. Every observed
move is therefore pipeline error — encoding, transport, decoding, or the
author — and never physics. **That count is the number this stand
exists to produce: the noise floor of the boundary itself.** Below it a
σ (the world answering against) is indistinguishable from noise; above
it, an objection is real.

THE CONTROL, because a probe that cannot fail proves nothing about
liveness: the same device bits are also fed to an `until-verification`
verdict, which the same theory says MUST move, at a rate computable in
advance from the completion table. A dead pipeline returning constants
would pass the tautology and fail this.

  probe    (¬p∧p) — hereditary, value F: must never move
  controls (p∧q), ¬p, (p∨q) — until-verification, with predicted move
           rates 1/4, 1/2, 3/4 fixed before a shot is fired. Three
           different rates, so the pipeline must reproduce a
           DISTRIBUTION, which a broken decoder cannot fake by luck.

Circuit: H on each of two qubits — uniform independent bits, so every
completion of the marking is exercised. (The singlet of
`quantum_junction_hw.py` would give CORRELATED verifications; that is a
worthwhile second experiment and is deliberately not this one.)

MEASURED (simulator, 4096 shots, 2026-07-20):
  ideal            probe moved 0, grade lost 0; controls 0.2529 / 0.4944
                   / 0.7456 against 0.25 / 0.50 / 0.75
  2% depolarizing  probe moved 0, grade lost 0; controls 0.2490 / 0.4951
                   / 0.7524 — the probe is INDIFFERENT to device noise,
                   which is the point: it isolates pipeline error from
                   device error. Noise moves the controls' inputs and
                   still cannot move a hereditary verdict.

Run:
  python3 dilemmas/tautology_boundary.py --sim         # ideal simulator
  python3 dilemmas/tautology_boundary.py --sim --noisy # with a noise model
  python3 dilemmas/tautology_boundary.py --ibm         # real hardware
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(_HERE))

from zmodal import ztl_eval                                   # noqa: E402
from zverify import grade, refinements                        # noqa: E402

ATOMS = ("p", "q")
MARKING = {a: "M" for a in ATOMS}

PROBE = ("and", ("not", "p"), "p")     # hereditary, F — must not move

# Three controls with DIFFERENT predicted rates, computed from the
# completion table before a shot is fired. A single control that moves
# on every outcome (like the bare atom p, rate 1.0) only shows the
# pipeline is not a constant. Three rates — 1/4, 1/2, 3/4 — require it to
# reproduce a specific distribution, which a broken decoder cannot fake.
CONTROLS = [("and", "p", "q"),         # rate 0.25
            ("not", "p"),              # rate 0.50
            ("or", "p", "q")]          # rate 0.75

SHOTS = 4096


def show(x):
    if isinstance(x, str):
        return x
    if x[0] == "not":
        return f"¬{show(x[1])}"
    return f"({show(x[1])}{ {'and': '∧', 'or': '∨', 'imp': '→'}[x[0]] }"\
           f"{show(x[2])})"


def predicted_move_rate(phi):
    """Under uniform independent bits every full completion is equally
    likely, so the predicted fraction of moves is computed from the
    completion table — before a single shot is fired."""
    base = ztl_eval(phi, MARKING)
    full = [m for m in refinements(MARKING)
            if all(v != "M" for v in m.values())]
    moved = sum(1 for m in full if ztl_eval(phi, m) != base)
    return moved / len(full), base


def circuit():
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(len(ATOMS), len(ATOMS))
    for i in range(len(ATOMS)):
        qc.h(i)
    qc.measure(range(len(ATOMS)), range(len(ATOMS)))
    return qc


def judge(counts):
    """Feed every shot's bits through the kernel as verifications."""
    stats = {"shots": 0, "probe_moved": 0, "grade_lost": 0,
             "control_moved": [0] * len(CONTROLS), "ones": [0] * len(ATOMS)}
    pb = ztl_eval(PROBE, MARKING)
    cb = [ztl_eval(c, MARKING) for c in CONTROLS]
    for bitstring, n in counts.items():
        bits = bitstring.replace(" ", "")[::-1]          # qiskit is little-endian
        m = {a: ("T" if bits[i] == "1" else "F")
             for i, a in enumerate(ATOMS)}
        stats["shots"] += n
        for i in range(len(ATOMS)):
            stats["ones"][i] += n * (bits[i] == "1")
        if ztl_eval(PROBE, m) != pb:
            stats["probe_moved"] += n
        if grade(PROBE, m) != "hereditary":
            stats["grade_lost"] += n
        for j, c in enumerate(CONTROLS):
            if ztl_eval(c, m) != cb[j]:
                stats["control_moved"][j] += n
    return stats


def report(stats, tag):
    n = stats["shots"]
    pred_p, base_p = predicted_move_rate(PROBE)
    print(f"\n{'=' * 74}\n{tag} — {n} shots\n{'=' * 74}")
    print(f"  device bias: " + ", ".join(
        f"{a}→1 in {stats['ones'][i] / n:.4f}" for i, a in enumerate(ATOMS)))

    print(f"\n  PROBE   {show(PROBE):14s} = {base_p}, hereditary")
    print(f"    theorem says it can never move (hereditary_absorbing)")
    print(f"    predicted move rate : {pred_p:.4f}")
    print(f"    OBSERVED moves      : {stats['probe_moved']} of {n}"
          f"   = {stats['probe_moved'] / n:.6f}")
    print(f"    OBSERVED grade loss : {stats['grade_lost']} of {n}")
    print(f"    → BOUNDARY NOISE FLOOR: {stats['probe_moved'] / n:.6f}")

    print(f"\n  CONTROLS — must move, at rates fixed before any shot")
    live = True
    for j, c in enumerate(CONTROLS):
        pred, base = predicted_move_rate(c)
        obs = stats["control_moved"][j] / n
        ok = abs(obs - pred) < 0.05
        live = live and ok
        print(f"    {show(c):10s} = {base}   predicted {pred:.4f}"
              f"   observed {obs:.4f}   {'ok' if ok else 'OFF'}")
    print(f"    → pipeline is {'LIVE' if live else 'NOT LIVE'}"
          f" (a dead pipeline passes the probe and fails here)")
    return stats["probe_moved"], stats["grade_lost"], live


def run_sim(noisy):
    from qiskit_aer import AerSimulator
    if noisy:
        from qiskit_aer.noise import NoiseModel, depolarizing_error
        nm = NoiseModel()
        nm.add_all_qubit_quantum_error(depolarizing_error(0.02, 1), ["h"])
        sim = AerSimulator(noise_model=nm)
        tag = "SIMULATOR (2% depolarizing on H)"
    else:
        sim = AerSimulator()
        tag = "SIMULATOR (ideal)"
    res = sim.run(circuit(), shots=SHOTS).result()
    return report(judge(res.get_counts()), tag)


def run_ibm(token=None):
    from qiskit import transpile
    from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
    service = (QiskitRuntimeService(channel="ibm_quantum_platform",
                                    token=token)
               if token else QiskitRuntimeService())
    backend = service.least_busy(operational=True, simulator=False)
    print(f"REAL HARDWARE — backend {backend.name}")
    qc = transpile(circuit(), backend=backend)
    job = SamplerV2(mode=backend).run([qc], shots=SHOTS)
    print(f"  job {job.job_id()} submitted; waiting…")
    r = job.result()[0]
    counts = r.data[list(r.data.keys())[0]].get_counts()
    return report(judge(counts), f"REAL ({backend.name})")


if __name__ == "__main__":
    print("=" * 74)
    print("TAUTOLOGY AT THE BOUNDARY — an answer known in advance,")
    print("sent through the material to see whether it returns")
    print("=" * 74)
    print("  The probe is OUR theorem, not physics: a hereditary verdict")
    print("  cannot move under any verification (lean/ZTime.lean, empty")
    print("  axiom list). Whatever the device says, the verdict is")
    print("  forbidden to change — so every change measures the boundary.")

    if "--ibm" in sys.argv:
        i = sys.argv.index("--ibm")
        tok = sys.argv[i + 1] if len(sys.argv) > i + 1 else None
        moved, lost, live = run_ibm(tok)
    else:
        moved, lost, live = run_sim("--noisy" in sys.argv)

    print()
    if moved == 0 and lost == 0:
        print("  TAUTOLOGY HELD — the boundary returned what could not come")
        print("  back false. Noise floor 0 at this shot count: below it a σ")
        print("  is indistinguishable from noise, and there is no floor to")
        print("  hide one in.")
    else:
        print(f"  σ AT THE BOUNDARY — {moved} moves, {lost} grade losses on")
        print("  a verdict a machine-checked theorem forbids to move. This")
        print("  is NOT physics: it is the pipeline, and the culprit is one")
        print("  of three doors — encoding, transport, or the author.")
    assert live, "the control did not move: the pipeline is dead, probe void"
    assert moved == 0 and lost == 0, \
        f"hereditary verdict moved {moved} times — boundary error"
    print("\n  BOUNDARY GREEN — tautology held, control live.")
