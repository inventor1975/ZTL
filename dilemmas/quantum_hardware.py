# -*- coding: utf-8 -*-
"""quantum_hardware — the ZTL stones on REAL quantum hardware.

Our emulator (qemu.py) is honest theatre: its randomness is a
pseudo-random generator, i.e. determinism in costume. On real quantum
hardware the same two circuits become the THING, not the theatre — the
vacancy of will produces genuinely fresh bits, and the singlet realizes
the first-night axiom on actually entangled qubits.

Two circuits, each one stone of the arc:

  1. ¬N=N — the negation fixed point.  X|+> = |+> (the plus state is
     invariant under the quantum NOT), and measuring |+> mints a fresh
     bit from a state no Boolean pressure can move.  On hardware these
     bits are REAL — the brick of randomness, the vacancy of will, made
     physical (not simulated).

  2. Z↔Z=F — the singlet.  The entangled pair (|01>-|10>)/√2: each side
     measures random (¬N=N), yet the two are perfectly anti-correlated —
     "two unverified are not equal even to each other" (Z↔Z=F, the
     quarantine axiom of the very first evening) realized as the law of
     entanglement.

Honest scope: this demonstrates the PHYSICS of our arc on real hardware;
it does not accelerate ZTL (ZTL needs no quantum) and proves nothing new
about quantum mechanics (both circuits are textbook).  The point is that
the "theatre" of qemu.py becomes real: genuine fresh bits, genuine
entanglement.

MEASURED on real hardware (IBM ibm_fez, 156-qubit superconducting
processor, 2026-07-17, 4096 shots each):
  ¬N=N fresh bits:  0 -> 0.504, 1 -> 0.496 — a fair coin, GENUINE quantum
    randomness (bits that did not exist before measurement).
  Z↔Z=F singlet:    01 -> 0.475, 10 -> 0.476 (anti-correlated 95.1%);
    00 -> 0.032, 11 -> 0.017 (same-outcome 4.9% = hardware noise:
    decoherence + readout error). The ideal law is exact (simulator:
    0.000 same-outcome); the physical realization carries ~5% noise.
    "Two unverified are not equal even to each other" (Z↔Z=F, the axiom
    of the first evening) holds at 95% on real entangled qubits — and
    even the processor's verdict comes with a warranty grade, not
    certainty: the 4.9% is the Z of measurement itself.

USAGE
  Dry run on the local simulator (still pseudo-random — a correctness
  check of the circuits, not the real vacancy):
      python3 dilemmas/quantum_hardware.py --sim
  Real hardware (genuine fresh bits) needs a free account on the new IBM
  Quantum Platform (quantum.cloud.ibm.com): an API key and an instance
  CRN. Either save the account once —
      python3 dilemmas/quantum_hardware.py --save API_KEY "INSTANCE_CRN"
  then just:
      python3 dilemmas/quantum_hardware.py --ibm
  or pass inline:
      python3 dilemmas/quantum_hardware.py --ibm API_KEY "INSTANCE_CRN"
"""
import sys

from qiskit import QuantumCircuit


def circuit_fixed_point(shots_note=""):
    """¬N=N: prepare |+>, verify X|+>=|+> is implicit, measure fresh bits."""
    qc = QuantumCircuit(1, 1)
    qc.h(0)            # |0> -> |+>  (the ¬N=N cell)
    qc.x(0)            # X|+> = |+>  — negation does not move it
    qc.measure(0, 0)   # collapse: a fresh bit from the invariant cell
    return qc


def circuit_singlet():
    """Z↔Z=F: the entangled anti-correlated pair (Bell singlet)."""
    qc = QuantumCircuit(2, 2)
    qc.h(0)
    qc.x(1)
    qc.cx(0, 1)        # -> (|01> - |10>)/√2 up to phase: anti-correlated
    qc.z(0)
    qc.measure([0, 1], [0, 1])
    return qc


def summarize(counts, name):
    total = sum(counts.values())
    print(f"\n  {name}: {total} shots")
    for outcome in sorted(counts):
        p = counts[outcome] / total
        print(f"    {outcome}: {counts[outcome]:5d}  ({p:.3f})")
    return counts


def run_sim(shots=4096):
    from qiskit_aer import AerSimulator
    sim = AerSimulator()
    print("DRY RUN — local Aer simulator (pseudo-random; correctness check "
          "only)\n" + "=" * 60)
    fp = circuit_fixed_point()
    r = sim.run(fp, shots=shots).result()
    c = summarize(r.get_counts(), "¬N=N fresh bits (|+> measured)")
    ones = c.get("1", 0)
    print(f"    → ones fraction {ones/shots:.3f} (fair coin ⟺ the vacancy)")

    sg = circuit_singlet()
    r2 = sim.run(sg, shots=shots).result()
    c2 = summarize(r2.get_counts(), "Z↔Z=F singlet (anti-correlated)")
    agree = c2.get("00", 0) + c2.get("11", 0)
    print(f"    → same-outcome fraction {agree/shots:.3f} "
          "(0 ⟺ Z↔Z=F: never equal)")
    print("\n  Circuits correct. For the REAL vacancy (genuine fresh bits), "
          "run --ibm.")


def save_account(api_key, instance):
    from qiskit_ibm_runtime import QiskitRuntimeService
    QiskitRuntimeService.save_account(
        channel="ibm_quantum_platform", token=api_key, instance=instance,
        overwrite=True, set_as_default=True)
    print("account saved — now run with --ibm (no args needed)")


def run_ibm(api_key=None, instance=None, shots=4096):
    from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
    from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
    if api_key:
        service = QiskitRuntimeService(channel="ibm_quantum_platform",
                                       token=api_key, instance=instance)
    else:
        service = QiskitRuntimeService()   # uses the saved account
    backend = service.least_busy(operational=True, simulator=False)
    print(f"REAL HARDWARE — backend {backend.name}\n" + "=" * 60)
    for name, qc, tag in [
            ("¬N=N fresh bits", circuit_fixed_point(), "fp"),
            ("Z↔Z=F singlet", circuit_singlet(), "sg")]:
        pm = generate_preset_pass_manager(optimization_level=1, backend=backend)
        isa = pm.run(qc)
        sampler = SamplerV2(mode=backend)
        job = sampler.run([isa], shots=shots)
        print(f"  submitted {name}: job {job.job_id()} (queue...)")
        res = job.result()
        counts = res[0].data.c.get_counts()
        summarize(counts, name + " [REAL QUANTUM]")
    print("\n  These bits were minted by physics, not a PRNG — the vacancy, "
          "for real.")


if __name__ == "__main__":
    if "--save" in sys.argv:
        i = sys.argv.index("--save")
        save_account(sys.argv[i + 1], sys.argv[i + 2])
    elif "--ibm" in sys.argv:
        i = sys.argv.index("--ibm")
        rest = sys.argv[i + 1:]
        if len(rest) >= 2:
            run_ibm(rest[0], rest[1])   # inline key + instance
        else:
            run_ibm()                   # saved account
    else:
        run_sim()
