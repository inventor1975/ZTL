#!/usr/bin/env bash
# What CI actually sees, imitated honestly: a FRESH CLONE of HEAD with a
# COLD Lean cache. Two bug classes hide from the local suite and only
# these two conditions expose them —
#   * a file that exists on disk and was never `git add`ed (the lakefile
#     asked for lean/Cogito_Conservativity.lean for a day while CI died);
#   * stands racing over the same `lake build` on a cold cache (bridge.py
#     and inventory/paper_claims.py, both green alone, both red together).
# Both cost a red workflow on 2026-08-11 and neither was visible here.
#
# Usage:  ./ci-sim.sh            (about the cost of one cold Lean build)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

echo "clean clone of HEAD -> $WORK"
git -C "$ROOT" clone -q --no-hardlinks . "$WORK/ztl"
cd "$WORK/ztl"
git log --oneline -1

# uncommitted work is exactly what this check must NOT see
if ! git -C "$ROOT" diff --quiet || ! git -C "$ROOT" diff --cached --quiet; then
  echo "note: the working tree has uncommitted changes — they are NOT in"
  echo "      this run, which is the point. CI sees committed history only."
fi

rm -rf lean/.lake/build          # cold cache, as on a fresh runner
python3 run_all.py
