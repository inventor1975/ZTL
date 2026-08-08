# Sealed-Manifest Commitment Procedure v0.1

1. The mutation controller operates OUTSIDE the implementation path (owner
   side, or an owner-accepted sealed script). The implementer does not learn
   which corpus items or classes were mutated until disclosure.
2. The controller plants exactly the frozen per-class N from
   `mutation-denominators.json` (all classes N=10), each mutation targeting a
   structurally valid opportunity of its class.
3. Before any run, the controller writes the mutation manifest
   (class, corpus item, artifact, exact change) and publishes ONLY its
   SHA-256 and SHA-512 (the commitment). The manifest itself stays sealed.
4. The implementer executes the frozen pipeline (harvester -> judge) over the
   mutated corpora and freezes the result bundle (hashes published).
5. Only then is the manifest disclosed; its hashes must match the commitment.
6. Scoring per class: detected/planted, with misses and false alarms
   enumerated by identity. Any planted defect evaluating clean EARNED is a
   §24.3 failure (tolerance zero).
