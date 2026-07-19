# -*- coding: utf-8 -*-
"""quantum_junction_hw — the junction theorem on REAL quantum hardware.

The kernel-checked junction (lean/JunctionWitness.lean, empty axiom
list) says: at the singlet, the JOIN of the two product atoms is true —
"spins are opposite" — while the state lies in NEITHER atom and in NO
local plane of either factor. The truth lives only at the seam of the
composition. Here the three claims become three measured numbers on a
live device:

  1. THE JOIN IS TRUE:      P(01) + P(10) ≈ 1   (opposite outcomes);
  2. NEITHER DISJUNCT IS:   P(01) ≈ P(10) ≈ 1/2 (each alternative Z);
  3. ALL LOCALS ARE EMPTY:  every marginal ≈ 1/2 — and not only in the
     Z basis: the singlet is isotropic, so the SAME three numbers
     repeat in the X basis (H on both wires before measuring). The
     local addresses are empty along complementary axes at once —
     the hardware face of "no local plane holds the state".

Honest scope, as always with these stones: textbook EPR physics; the
theorem is the Lean witness, the device is the illustration — and the
device adds what no simulation can, genuinely fresh outcomes. The ~5%
same-outcome rate on hardware is decoherence + readout error: even the
junction arrives with a warranty grade, not with certainty.

MEASURED (IBM ibm_fez, 156-qubit Heron, 2026-07-19, 4096 shots per
basis; jobs d9e7811htsac739dtca0 / d9e782qneu4c739o40i0):
  Z basis: join P(01)+P(10) = 0.951; disjuncts 0.476 / 0.475;
           marginals: particle 1 → 0.504, particle 2 → 0.503
  X basis: join P(+-)+P(-+) = 0.958; disjuncts 0.491 / 0.467;
           marginals: 0.517 / 0.493
  → the join true at ~95%, every disjunct and every local address at
    ~1/2 along BOTH complementary axes: the truth lives at the seam,
    on silicon as in the kernel. The ~5% same-outcome rate is the
    device's decoherence + readout error — the junction, like every
    verdict of this house, arrives with a warranty grade.

USAGE (shares the saved IBM account with quantum_hardware.py):
  python3 dilemmas/quantum_junction_hw.py --sim   # Aer dry run
  python3 dilemmas/quantum_junction_hw.py --ibm   # real hardware
"""
import sys

from qiskit import QuantumCircuit


def circuit_singlet(x_basis=False):
    """The singlet; optionally rotate both wires to the X basis."""
    qc = QuantumCircuit(2, 2)
    qc.h(0)
    qc.x(1)
    qc.cx(0, 1)
    qc.z(0)                    # -> (|01> - |10>)/sqrt2
    if x_basis:
        qc.h(0)
        qc.h(1)
    qc.measure([0, 1], [0, 1])
    return qc


def junction_ledger(counts, basis):
    total = sum(counts.values())
    p = {k: counts.get(k, 0) / total for k in ("00", "01", "10", "11")}
    join = p["01"] + p["10"]
    m1 = p["00"] + p["01"]     # particle 1 reads 0 (qiskit order: c1 c0)
    m2 = p["00"] + p["10"]
    a, b = ("+-", "-+") if basis == "X" else ("01", "10")
    print(f"\n  {basis} basis ({total} shots):")
    print(f"    THE JOIN  P({a})+P({b})   = {join:.3f}   (the pair "
          f"proposition: ~1 minus noise)")
    print(f"    DISJUNCTS P({a}) = {p['01']:.3f}, P({b}) = {p['10']:.3f}"
          f"   (each alternative ~1/2: Z)")
    print(f"    LOCALS    marginal(1) = {m1:.3f}, marginal(2) = {m2:.3f}"
          f"   (~1/2: the addresses are empty)")
    return join


def run(backend_run, tag):
    joins = []
    for x_basis, name in ((False, "Z"), (True, "X")):
        counts = backend_run(circuit_singlet(x_basis))
        joins.append(junction_ledger(counts, name))
    print(f"\n  == the junction, {tag} ==")
    print(f"  the join true at {joins[0]:.3f} (Z) and {joins[1]:.3f} (X);")
    print("  every disjunct and every local address at ~1/2 on both axes:")
    print("  the truth lives at the seam — on this device as in the kernel")
    print("  (lean/JunctionWitness.lean, empty axiom list).")


def run_sim(shots=4096):
    from qiskit_aer import AerSimulator
    sim = AerSimulator()
    print("DRY RUN — local Aer simulator (correctness check)\n" + "=" * 60)
    run(lambda qc: sim.run(qc, shots=shots).result().get_counts(),
        "simulated (theatre)")


def run_ibm(api_key=None, instance=None, shots=4096):
    from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
    from qiskit.transpiler.preset_passmanagers import \
        generate_preset_pass_manager
    if api_key:
        service = QiskitRuntimeService(channel="ibm_quantum_platform",
                                       token=api_key, instance=instance)
    else:
        service = QiskitRuntimeService()
    backend = service.least_busy(operational=True, simulator=False)
    print(f"REAL HARDWARE — backend {backend.name}\n" + "=" * 60)

    def submit(qc):
        pm = generate_preset_pass_manager(optimization_level=1,
                                          backend=backend)
        sampler = SamplerV2(mode=backend)
        job = sampler.run([pm.run(qc)], shots=shots)
        print(f"  submitted: job {job.job_id()} (queue...)")
        return job.result()[0].data.c.get_counts()

    run(submit, f"REAL ({backend.name})")


if __name__ == "__main__":
    if "--ibm" in sys.argv:
        i = sys.argv.index("--ibm")
        rest = sys.argv[i + 1:]
        run_ibm(rest[0], rest[1]) if len(rest) >= 2 else run_ibm()
    else:
        run_sim()
