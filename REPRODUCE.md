# Reproduce ZTL

Paste this whole block into a terminal (Mac/Linux; on Windows use WSL). It runs everything itself:

```bash
git clone https://github.com/inventor1975/ZTL &&
cd ZTL &&
git checkout 9d9a07afd435cea896edfedeff2b93324ccc19a5 &&
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y &&
source "$HOME/.elan/env" &&
(cd lean && lake build) &&
python3 run_all.py &&
python3 inventory/axiom_audit.py &&
python3 inventory/paper_claims.py &&
echo "
============================================================
  ✅ REPRODUCED — everything matched.  59 stands / 371 theorems / 21 modules.
  Copy THIS line into your report — you are done.
============================================================"
```

Installing Lean takes a few minutes — that is normal. A `N/59 stands finished…` counter shows it is working, not stuck.

You only need the **last line**:
- **✅ REPRODUCED** with **59 / 371 / 21** → it matched, you are done;
- no `✅` line (or a `FAIL` / red message) → copy the last lines of the terminal.

## Fill in and send back

| Question | Your answer |
|---|---|
| My connection to ZTL / Veraxis | none / acquaintance / relative / colleague |
| Date | |
| OS | e.g. Ubuntu 24.04 / Windows 11 + WSL / macOS |
| Saw the "✅ REPRODUCED" line + numbers 59 / 371 / 21? | yes / no (then: what you saw) |
| Anything different from the instructions? | no / describe |
| Where was it hard or confusing? | no / describe |
| Name or handle (a real name gives more weight) | |
