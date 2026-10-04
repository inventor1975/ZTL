# runtime_gate — latency of the ZRuntimeGate gate

The gate of `lean/ZRuntimeGate.lean`: one pass over the formula in the lazy (strong Kleene) register, pass iff T.
`gate_sound` proves a pass is EARNED; `gateC_steps` proves the cost is one step per node, independent of the
marking; `reval_correct`/`reval_cost` prove the incremental re-check touches only the nodes mentioning the changed
atom. This directory MEASURES what the theorems cannot: wall-clock time.

    cc -O2 -o gate_bench gate_bench.c && ./gate_bench

`RESULTS-x86-i9-14900F-loaded.txt` (2026-10-05 00:17): Intel i9-14900F, ONE thread, machine under load
(load average ~33 on 32 cores — other jobs running at nice 19). Random formulas over 64 atoms, ~20% of atoms
unverified (Z). Every incremental result is checked against a full pass (a mismatch aborts the run); built
and run once under AddressSanitizer, clean.

| formula size | full check p50 / p99 | incremental re-check p50 / p99 | 10 000 checks, one thread |
|---|---|---|---|
| 31 nodes   | 0.5 / 0.7 µs  | 0.1 / 0.4 µs | 5.3 ms  |
| 255 nodes  | 3.8 / 4.3 µs  | 0.3 / 0.9 µs | 39 ms   |
| 1023 nodes | 15 / 21 µs    | 0.4 / 2.0 µs | 155 ms  |

Read honestly: per-check latency does not grow with the number of simultaneous checks (it is a per-formula
pass); time grows linearly with formula size, as the theorem says. NOT measured: ARM edge CPUs (no hardware
here), multi-threading, real formula distributions from a deployed system, an unloaded machine. The gate is
SOUND and INCOMPLETE: what it does not pass goes to a hold, not to a false pass (`gate_incomplete`).
