#!/usr/bin/env bash
# Re-run every claim in RERUN-RECEIPT.md on this machine (Mac, Linux, or Git Bash on Windows). About 20 to 40 minutes the
# first time (Lean fetches Mathlib's prebuilt files), then a PASS/FAIL table, one line per claim.
set -uo pipefail
cd "$(dirname "$0")"
echo "Humanities Helping Hands engine, built by Daniel Steadham"
# What it found (Python, Lean's lake) is appended to runs/steps.jsonl (append only) before it stops or hands over to
# scripts/rerun.py, which logs each claim itself. Program names only, never paths.
ran=$(echo "RERUN.sh $*" | tr -d '"\134'); ran=${ran% }
note() { mkdir -p runs; printf '{"at":"%s","script":"RERUN.sh","ran":"%s","found":"%s","result":"%s","exit":%d}\n' \
  "$(date +%Y-%m-%dT%H:%M:%S%z)" "$ran" "$1" "$2" "$3" >> runs/steps.jsonl; }
# (a name that runs a real Python 3.11+: on Windows "python3" can be the Microsoft Store stub, which only opens the Store)
# (and never one from WindowsApps: a Python started through the Store's alias leaves the job a guard puts the run in, so a stop
#  could not end it; measured 2026-10-28)
py=""
for p in python3 python py; do
  case "$(command -v "$p" 2>/dev/null)" in *WindowsApps*) continue;; esac
  if command -v "$p" >/dev/null 2>&1 && "$p" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' >/dev/null 2>&1; then py=$p; break; fi
done
if [ -z "$py" ]; then
  echo "RERUN: Python 3.11 or newer is needed (https://www.python.org/downloads/), then run RERUN again."
  note "no Python 3.11 or newer (tried python3, python, py; Store aliases skipped)" FAIL 1; exit 1
fi
if ! command -v lake >/dev/null 2>&1; then
  if [ "${1:-}" = "--install" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
    export PATH="$HOME/.elan/bin:$PATH"
  else
    echo "RERUN: Lean's installer (elan) is missing. Run ./RERUN.sh --install to install it, or see https://github.com/leanprover/elan"
    note "no lake (elan not installed; --install not given)" FAIL 1; exit 1
  fi
fi
note "Python $("$py" -c 'import sys; print("%d.%d.%d" % sys.version_info[:3])') ($py), lake found; handed over to scripts/rerun.py" PASS 0
exec "$py" scripts/rerun.py "$@"
