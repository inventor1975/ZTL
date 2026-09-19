# Reproduce ZTL

Paste this whole block into a terminal (Mac/Linux; on Windows use WSL). It runs everything itself:

```bash
git clone https://github.com/inventor1975/ZTL &&
cd ZTL &&
git checkout v2.0.0 &&
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y &&
source "$HOME/.elan/env" &&
(cd lean && lake build) &&
python3 run_all.py &&
python3 inventory/axiom_audit.py &&
python3 inventory/paper_claims.py &&
echo "
============================================================
  ✅ REPRODUCED — everything matched.  Copy the counts printed above.
  Copy THIS line into your report — you are done.
============================================================"
```

Installing Lean takes a few minutes — that is normal. A `N/M stands finished…` counter shows it is working, not stuck.

You only need the **last line**:
- **✅ REPRODUCED** → it matched, you are done. The counts (stands / theorems /
  modules) are printed by the run itself and GROW as the corpus grows — a
  number different from any figure quoted elsewhere is **not** a failure;
- no `✅` line (or a `FAIL` / red message) → copy the last lines of the terminal.

## Fill in and send back

| Question | Your answer |
|---|---|
| My connection to ZTL / a downstream consumer | none / acquaintance / relative / colleague |
| Date | |
| OS | e.g. Ubuntu 24.04 / Windows 11 + WSL / macOS |
| Saw the "✅ REPRODUCED" line? Which three counts did it print? | yes + the numbers / no (then: what you saw) |
| Anything different from the instructions? | no / describe |
| Where was it hard or confusing? | no / describe |
| Name or handle (a real name gives more weight) | |
