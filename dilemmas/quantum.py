# -*- coding: utf-8 -*-
"""quantum — the quantum stones, made runnable (emulator: qemu.py).

Three demos, each a stone from the 2026-07-16/17 arc executed in gates:
  1. ¬N=N has a physical carrier: X|+> = |+> — the negation fixed point,
     and measuring it births the fresh bit.
  2. The quantum tax paid in our own hands: distributivity fails in the
     projection lattice of one qubit (the spin cell, Birkhoff–von
     Neumann) — the join MINTS, the meet is thrifty.
  3. The socks with a quantum coin (EXP 5): symmetric agents break
     symmetry by measuring |+> — the vacancy at work.

Honest note (from qemu.py): the emulator is a classical simulation —
the grammar of the vacancy, not the vacancy.
"""
import os
import random
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from qemu import zero, apply1, X, H, measure, close, line, meet, join, dim


def fixed_point():
    print("DEMO 1 — ¬N=N in gates: the plus state is the fixed point of NOT\n")
    plus = apply1(H, 0, zero(1))                   # |+> = H|0>
    x_plus = apply1(X, 0, plus)
    x_zero = apply1(X, 0, zero(1))
    print(f"  X|+> = |+>  : {close(x_plus, plus)}   (the phase itself is "
          "invariant under negation)")
    print(f"  X|0> = |0>  : {close(x_zero, zero(1))}   (the gods swap: "
          "X|0>=|1>)")
    assert close(x_plus, plus) and not close(x_zero, zero(1))
    rnd = random.Random(7)
    bits = [measure(plus, 0, rnd)[0] for _ in range(10000)]
    ones = sum(bits)
    print(f"  measuring |+> 10000 times: {ones} ones — fresh bits from the")
    print("  state no Boolean pressure can move; the coin in the air is")
    print("  'not heads = spinning = not tails', and only landing breaks it")
    assert 4800 < ones < 5200


def quantum_tax():
    print("DEMO 2 — the quantum tax, paid in our hands\n")
    p = line(1, 1)                                  # S_x = +   (|+>)
    q = line(1, 0)                                  # S_z = +   (|0>)
    r = line(0, 1)                                  # S_z = -   (|1>)
    left = meet(p, join(q, r))
    right = join(meet(p, q), meet(p, r))
    print(f"  p∧(q∨r): dim {dim(left)}   — q∨r spans EVERYTHING, p survives")
    print(f"  (p∧q)∨(p∧r): dim {dim(right)}   — two honest zeros: no state is")
    print("  definite in x AND z (complementarity)")
    assert dim(left) == 1 and dim(right) == 0
    print("\n  distributivity falls exactly as the map of falls says: the")
    print("  join is a MINT (it holds states neither disjunct has — the")
    print("  superposition), the meet is thrifty; and there is no classical")
    print("  substrate to distribute over. Our lift keeps distributivity")
    print("  (27/27) because our Z is ignorance OF a world; here there is")
    print("  no world underneath — nothing to be ignorant of.")


def quantum_socks():
    print("DEMO 3 — the socks with a quantum coin (EXP 5)\n")
    rnd = random.Random(7)
    trials = []
    for _ in range(10000):
        rounds = 0
        while True:
            rounds += 1
            a = measure(apply1(H, 0, zero(1)), 0, rnd)[0]
            b = measure(apply1(H, 0, zero(1)), 0, rnd)[0]
            if a != b:
                break
        trials.append(rounds)
    avg = sum(trials) / len(trials)
    print(f"  two symmetric agents, each measuring its own |+>: symmetry")
    print(f"  breaks in {avg:.2f} rounds on average (max {max(trials)}) —")
    print("  deterministic twins never break (measured in chaos.py EXP 4);")
    print("  the ¬N=N cell is what the classical twins lacked")
    assert 1.8 < avg < 2.2


if __name__ == "__main__":
    print("THE QUANTUM STONES — run, not quoted\n")
    fixed_point()
    print()
    quantum_tax()
    print()
    quantum_socks()
    print()
    print("The arc closes: the brick of randomness (¬N=N) is a state you can")
    print("prepare with one gate; the tax of the top system is payable at a")
    print("desk of subspaces; and the vacancy of will is a coin any pair of")
    print("socks can flip — in the emulator, as theatre; in the world, as")
    print("the real thing.")
