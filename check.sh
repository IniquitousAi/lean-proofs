#!/usr/bin/env bash
# One command an outside reader runs to check this whole repository:
#   1. fetch Mathlib's prebuilt files      (lake exe cache get)
#   2. source and text audit                (scripts/audit_source.sh: no sorry, admit, unsafe, extern, implemented_by,
#                                            native_decide or axiom declarations in LeanProofs/*.lean;
#                                            scripts/test_name.sh: public name spelled Humanities Helping Hands,
#                                            every text file valid UTF-8 with no mojibake)
#   3. build every proof                    (lake build)
#   4. restate the headline statements      (lake env lean VerifyAll.lean, then every #print axioms list must be a
#                                            subset of propext, Quot.sound, Classical.choice)
#   5. kernel replay                        (leanchecker replays every declaration of the LeanProofs modules
#                                            through Lean's kernel again, from the compiled .olean files)
# Full output and the real wall-clock time go to AUDIT.log. Exit 0 only when every step passes.
# Every Lean command goes through `lake`, so elan picks the version pinned in lean-toolchain; no default toolchain
# (`elan default`) is needed, and `leanchecker` is the one bundled with that toolchain (nothing else to install).
set -euo pipefail
cd "$(dirname "$0")"

if [ -z "${CHECK_INNER:-}" ]; then
  start=$(date +%s)
  set +e
  CHECK_INNER=1 bash "$0" "$@" 2>&1 | tee AUDIT.log
  status=${PIPESTATUS[0]}
  set -e
  end=$(date +%s)
  {
    echo "== Wall-clock time: $((end - start)) s (real, measured by check.sh from start to finish)"
    if [ "$status" -eq 0 ]; then echo "== RESULT: PASS (exit 0)"; else echo "== RESULT: FAIL (exit $status)"; fi
  } | tee -a AUDIT.log
  exit "$status"
fi

step() { echo; echo "== $(date -u +%H:%M:%S) UTC  $*"; }

if ! command -v lake >/dev/null 2>&1; then
  echo "check.sh: 'lake' not found. Install elan (https://github.com/leanprover/elan), open a new shell, run ./check.sh again."
  exit 1
fi

echo "== check.sh started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "== commit: $(git rev-parse HEAD 2>/dev/null || echo unknown)$(git diff --quiet 2>/dev/null || echo ' (with uncommitted changes)')"
echo "== toolchain: $(cat lean-toolchain)"
echo "== mathlib (lake-manifest.json): $(grep -B6 '"name": "mathlib"' lake-manifest.json | grep '"rev"' | tr -d ' ,')"
echo "== lean: $(lake env lean --version)"

step "1/5 lake exe cache get"
# Skipped when the last fetch succeeded for this exact manifest and toolchain and Mathlib's build folder is still there
# (it took 188 s on 2026-10-28 with nothing to fetch). Delete .lake/cache-stamp to force a fetch.
want=$(cat lake-manifest.json lean-toolchain | git hash-object --stdin)
if [ -d .lake/packages/mathlib/.lake/build/lib ] && [ "$(cat .lake/cache-stamp 2>/dev/null)" = "$want" ]; then
  echo "cache: same manifest and toolchain as the last successful fetch ($want), Mathlib build present: skipped"
else
  lake exe cache get
  echo "$want" > .lake/cache-stamp
fi

step "2/5 source and text audit"
bash scripts/audit_source.sh
bash scripts/test_name.sh

step "3/5 lake build"
lake build

step "4/5 lake env lean VerifyAll.lean"
out=$(lake env lean VerifyAll.lean 2>&1)
echo "$out"
flat=$(echo "$out" | tr '\n' ' ' | tr -s ' ')
if echo "$flat" | grep -qE '(^| )error:'; then echo "VerifyAll: Lean reported an error"; exit 1; fi
expected=$(grep -c '^#print axioms' VerifyAll.lean)
lists=$(echo "$flat" | grep -oE "depends on axioms: \[[^]]*\]" || true)
none=$( (echo "$flat" | grep -oE "does not depend on any axioms" || true) | grep -c . || true)
got=$(( $( (echo "$lists" | grep -c .) || true) + none ))
bad=$(echo "$lists" | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' | grep -vE '^(propext|Quot\.sound|Classical\.choice)?$' || true)
problems=$(grep -oE '^-- p[0-9]+_[A-Za-z0-9_]+' VerifyAll.lean | sort -u | grep -c . || true)
echo "VerifyAll: $problems Proven problems; $expected headline statements restated; $got axiom reports; axioms outside propext, Quot.sound, Classical.choice: ${bad:-none}"
if [ "$got" -ne "$expected" ] || [ -n "$bad" ]; then echo "VerifyAll: FAIL"; exit 1; fi

step "5/5 leanchecker: kernel replay of the LeanProofs modules"
# One module at a time (all at once peaked above 14 GB of memory), named from the source files so a stale .olean
# left in .lake/build by a deleted file is not mistaken for part of the project. LeanProofs.lean itself only imports.
mods=()
for f in LeanProofs/*.lean; do m="${f%.lean}"; mods+=("${m//\//.}"); done
# (Tried 2026-10-28, ORD-1028-BZ: one leanchecker call for all 16 with LEAN_NUM_THREADS=2 still reached 90% of 32 GB in
#  under 5 minutes and was stopped; 4.35 starts one task per module at once and has no worker flag. The loop stays.)
for m in "${mods[@]}"; do
  t0=$(date +%s)
  lake env leanchecker -v "$m"
  echo "leanchecker: $m replayed with no error ($(( $(date +%s) - t0 )) s)"
done
echo "leanchecker: all ${#mods[@]} LeanProofs modules (${mods[*]}) replayed through the kernel with no error"
