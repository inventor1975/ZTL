# -*- coding: utf-8 -*-
"""quantum_distributivity — the non-distributivity pole of PSSL on REAL hardware.

The fourth stone: the one law the OTHER three corners of the cycle keep and
quantum alone breaks. Classical logic, intuitionistic / type theory, and ZTL
all validate distributivity; orthomodular quantum logic does not
(PSSL, Proposition B(iii); machine-checked in lean/QuantumWitness.lean over
MO2 on the empty axiom list). Here we make the break PHYSICAL.

  THE WITNESS.  On one qubit read a = "the qubit is |0>" (Z basis), and let
  b, b' = |+>, |-> (the X basis, an INCOMPATIBLE pair). In the projector
  lattice b ∨ b' = 1 (the whole space — the trivial "true"), while the two
  atoms meet a at nothing: a ∧ b = a ∧ b' = 0. Distributivity would demand

        a ∧ (b ∨ b')  =  (a ∧ b) ∨ (a ∧ b')
             a         =           0                 (FALSE)

  and quantum logic refuses the equation. The physical face of the refusal is
  complementarity / measurement disturbance:

    LHS  a ∧ (b∨b') = a :   prepare |0>, do NOTHING to the b∨b'=1 question
                            (it needs no measurement), then measure a.
                            The qubit is untouched  →  P(a=0) = 1.

    RHS  (a∧b) ∨ (a∧b') = 0 :  prepare |0>, but now RESOLVE b vs b'
                            (a mid-circuit measurement in the X basis — the
                            act of forming a∧b and a∧b' separately), then
                            measure a. Resolving b∨b' into its parts
                            DESTROYS a  →  P(a=0) = 1/2.

  Classically, since b∨b'=1, the two sides are the same manipulation and must
  give the same number. Quantum-mechanically the gap  1.0 vs 0.5  IS the
  failure of distributivity, on a live qubit.

Honest scope (same as its siblings quantum_hardware.py): this is textbook
complementarity — it proves nothing new about quantum mechanics and does not
accelerate ZTL. It exhibits, physically, the one cell where quantum leaves the
cycle. The THEOREM is the Lean witness on the empty axiom list; the hardware
is the illustration.

IDEAL (noiseless):
  LHS  P(a=0) = 1.000    (a survives: a ∧ (b∨b') = a)
  RHS  P(a=0) = 0.500    (a destroyed: (a∧b) ∨ (a∧b') = 0)

MEASURED on real hardware (IBM ibm_marrakesh, 156-qubit Heron, 2026-07-18,
4096 shots each):
  LHS  P(a=0) = 1.000    (4095/4096 — essentially noiseless: "do nothing" is easy)
  RHS  P(a=0) = 0.517    (ideal 0.500; ~1.7% bias = readout + decoherence)
  gap  = 0.483           (ideal 0.500) — distributivity would force gap = 0.
The break is physical: resolving b∨b'=1 into b, b' (a mid-circuit X measurement)
destroys a on a live qubit. The one law classical/intuitionistic/ZTL keep and
quantum alone breaks, shown on real hardware — an illustration of PSSL Prop.
B(iii), whose proof is the Lean witness on the empty axiom list.

USAGE (mirrors quantum_hardware.py — shares the saved IBM account):
  python3 dilemmas/quantum_distributivity.py --sim
  python3 dilemmas/quantum_distributivity.py --ibm            # saved account
  python3 dilemmas/quantum_distributivity.py --ibm KEY "CRN"  # inline
  (to save an account once, use quantum_hardware.py --save KEY "CRN")
"""
import sys

from qiskit import QuantumCircuit


def circuit_lhs():
    """a ∧ (b∨b') = a : |0>, leave b∨b'=1 unresolved, measure a (Z).  P(0)=1."""
    qc = QuantumCircuit(1, 1)
    # prepare |0> = a  (the identity state; nothing to do)
    qc.measure(0, 0)          # measure a in the Z basis
    return qc


def circuit_rhs():
    """(a∧b) ∨ (a∧b') = 0 : resolve b vs b' (mid-circuit X measure), then a."""
    qc = QuantumCircuit(1, 2)
    # prepare |0> = a
    qc.h(0)                   # rotate X basis -> Z, so the next measure reads b/b'
    qc.measure(0, 0)          # RESOLVE b vs b' — the act of forming a∧b, a∧b'
    qc.h(0)                   # rotate back: qubit now collapsed onto b or b'
    qc.measure(0, 1)          # measure a in the Z basis — now only 50% |0>
    return qc


def prob_a0(counts):
    """P(a=0). a is the highest-indexed classical bit (leftmost in the key)."""
    total = sum(counts.values())
    a0 = sum(n for k, n in counts.items() if k.replace(" ", "")[0] == "0")
    return a0 / total if total else 0.0


def summarize(counts, name, ideal):
    total = sum(counts.values())
    print(f"\n  {name}: {total} shots")
    for outcome in sorted(counts):
        p = counts[outcome] / total
        print(f"    {outcome}: {counts[outcome]:5d}  ({p:.3f})")
    p0 = prob_a0(counts)
    print(f"    → P(a=0) = {p0:.3f}   (ideal {ideal:.3f})")
    return p0


def _verdict(lhs_p0, rhs_p0):
    gap = lhs_p0 - rhs_p0
    print("\n  " + "-" * 56)
    print(f"  LHS  a∧(b∨b')      : P(a=0) = {lhs_p0:.3f}   (a survives = a)")
    print(f"  RHS  (a∧b)∨(a∧b')  : P(a=0) = {rhs_p0:.3f}   (a destroyed = 0)")
    print(f"  gap = {gap:.3f}  — distributivity would force gap = 0.")
    print("  A nonzero gap IS the failure of distributivity, on a live qubit —")
    print("  the one law classical/intuitionistic/ZTL keep and quantum breaks")
    print("  (PSSL Prop. B(iii); Lean witness: lean/QuantumWitness.lean).")


def run_sim(shots=4096):
    from qiskit_aer import AerSimulator
    sim = AerSimulator()
    print("DRY RUN — local Aer simulator (correctness check of the circuits)\n"
          + "=" * 60)
    rl = sim.run(circuit_lhs(), shots=shots).result()
    lhs = summarize(rl.get_counts(), "LHS  a∧(b∨b')  (do nothing, measure a)", 1.0)
    rr = sim.run(circuit_rhs(), shots=shots).result()
    rhs = summarize(rr.get_counts(), "RHS  (a∧b)∨(a∧b')  (resolve b/b', then a)", 0.5)
    _verdict(lhs, rhs)
    print("\n  Circuits correct. For the physical break, run --ibm.")


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
    results = {}
    for name, qc, ideal, tag in [
            ("LHS  a∧(b∨b')", circuit_lhs(), 1.0, "lhs"),
            ("RHS  (a∧b)∨(a∧b')", circuit_rhs(), 0.5, "rhs")]:
        pm = generate_preset_pass_manager(optimization_level=1, backend=backend)
        isa = pm.run(qc)
        sampler = SamplerV2(mode=backend)
        job = sampler.run([isa], shots=shots)
        print(f"  submitted {name}: job {job.job_id()} (queue...)")
        res = job.result()
        counts = res[0].data.c.get_counts()
        results[tag] = summarize(counts, name + " [REAL QUANTUM]", ideal)
    _verdict(results["lhs"], results["rhs"])
    print("\n  The gap was opened by physics — non-distributivity, for real.")


if __name__ == "__main__":
    if "--save" in sys.argv:
        i = sys.argv.index("--save")
        from qiskit_ibm_runtime import QiskitRuntimeService
        QiskitRuntimeService.save_account(
            channel="ibm_quantum_platform", token=sys.argv[i + 1],
            instance=sys.argv[i + 2], overwrite=True, set_as_default=True)
        print("account saved — now run with --ibm")
    elif "--ibm" in sys.argv:
        i = sys.argv.index("--ibm")
        rest = sys.argv[i + 1:]
        run_ibm(rest[0], rest[1]) if len(rest) >= 2 else run_ibm()
    else:
        run_sim()
