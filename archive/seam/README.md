# archive/seam — the decentralised-seam apparatus (institutional track)

This folder holds the seam / federation experiments — kernel A ⊗ kernel B →
kernel C, the rubber operator engine, and the responses to A. Miteiko's
seam reviews (composition, direction, the verdict-equality attack). It is
**archived, not part of the fundamental ZTL work**: the seam is an
*application* — joining warranted claims across parties, the institutional
/ Veraxis layer that sits ON TOP of the published logic, not inside it.

It is kept here so that a fork built for the institutional track inherits
it directly. It is deliberately OUT of `run_all.py` (the fundamental
regression) and out of the preprint. The files import from the repository
root; move them back to the root, or add the root to `sys.path`, to run
them.

- `zsew.py` — E29, the original seam (the curator's design).
- `zsew_compose.py`, `zsew_direction.py`, `zsew_attack.py` — the review
  responses (composition properties, entailment direction, the attacks).
- `zrubber.py` — E35, the rubber operator engine (one mechanism, sixteen
  seams, typed by operator).

The fundamental repository keeps the ZTL core unchanged; the universal tool
that reads, verifies, and reports "what happened" is built OVER that core,
not here.
