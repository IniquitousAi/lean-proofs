#!/usr/bin/env bash
# Re-run every claim in RERUN-RECEIPT.md on this machine (Mac, Linux, or Git Bash on Windows). About 20 to 40 minutes the
# first time (Lean fetches Mathlib's prebuilt files), then a PASS/FAIL table, one line per claim.
set -uo pipefail
cd "$(dirname "$0")"
echo "Humanities Helping Hands engine, built by Daniel Steadham"
# (a name that runs a real Python 3.11+: on Windows "python3" can be the Microsoft Store stub, which only opens the Store)
py=""
for p in python3 python py; do
  if command -v "$p" >/dev/null 2>&1 && "$p" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' >/dev/null 2>&1; then py=$p; break; fi
done
if [ -z "$py" ]; then echo "RERUN: Python 3.11 or newer is needed (https://www.python.org/downloads/), then run RERUN again."; exit 1; fi
if ! command -v lake >/dev/null 2>&1; then
  if [ "${1:-}" = "--install" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
    export PATH="$HOME/.elan/bin:$PATH"
  else
    echo "RERUN: Lean's installer (elan) is missing. Run ./RERUN.sh --install to install it, or see https://github.com/leanprover/elan"
    exit 1
  fi
fi
exec "$py" scripts/rerun.py "$@"
