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

step "0/6 stamps: every stamps/**/*.ots is committed and pushed (nothing proven is ever lost)"
# An OpenTimestamps proof that exists only on this PC is a proof that can be lost. Untracked or modified .ots files, or a
# commit touching stamps/ that origin does not have yet, fail the run before the long steps start.
if git rev-parse --git-dir >/dev/null 2>&1 && [ -d stamps ]; then
  bad=$(git status --porcelain -uall -- stamps | grep '\.ots$' || true)
  if [ -n "$bad" ]; then echo "stamps: FAIL, .ots files not committed:"; echo "$bad"; exit 1; fi
  if git rev-parse '@{u}' >/dev/null 2>&1; then
    unpushed=$(git log '@{u}..HEAD' --name-only --pretty=format: -- stamps | grep '\.ots$' || true)
    if [ -n "$unpushed" ]; then echo "stamps: FAIL, .ots files committed but not pushed:"; echo "$unpushed"; exit 1; fi
  fi
  echo "stamps: every .ots under stamps/ is committed and pushed"
fi

step "1/6 lake exe cache get"
# Skipped when the last fetch succeeded for this exact manifest and toolchain and Mathlib's build folder is still there
# (it took 188 s on 2026-10-28 with nothing to fetch). Delete .lake/cache-stamp to force a fetch.
want=$(cat lake-manifest.json lean-toolchain | git hash-object --stdin)
if [ -d .lake/packages/mathlib/.lake/build/lib ] && [ "$(cat .lake/cache-stamp 2>/dev/null)" = "$want" ]; then
  echo "cache: same manifest and toolchain as the last successful fetch ($want), Mathlib build present: skipped"
else
  lake exe cache get
  echo "$want" > .lake/cache-stamp
fi

step "2/6 source and text audit"
bash scripts/audit_source.sh
bash scripts/test_name.sh

step "3/6 lake build"
lake build

step "4/6 lake env lean VerifyAll.lean"
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

step "5/6 leanchecker: kernel replay of the LeanProofs modules"
# One module at a time (all at once peaked above 14 GB of memory), named from the source files so a stale .olean
# left in .lake/build by a deleted file is not mistaken for part of the project. LeanProofs.lean itself only imports.
mods=()
for f in LeanProofs/*.lean; do m="${f%.lean}"; mods+=("${m//\//.}"); done
# (Tried 2026-10-28, ORD-1028-BZ: one leanchecker call for all 16 with LEAN_NUM_THREADS=2 still reached 90% of 32 GB in
#  under 5 minutes and was stopped; 4.35 starts one task per module at once and has no worker flag. The loop stays.
#  2026-10-29 04:5x: a group of only 5 small modules in one call also reached 90% and was stopped by safe_run, with the PC at
#  about 56% before Lean started: each module still loads its own Mathlib. Grouping does not fit on this PC.)
# (2026-10-29, ORD-1029-HUNT2: replay took 77% of the 31 minutes. A module whose compiled file is byte for byte the one that
#  already passed this replay, on the same toolchain and Mathlib, and whose LeanProofs imports are also unchanged, is skipped
#  with its stamp printed: the same trust as step 1's cache skip, since the kernel replays exactly those bytes. FULL=1 replays
#  every module; a fresh checkout (the GitHub Action, any outside reader) has no stamps, so it always replays all of them.)
mkdir -p .lake/replay-stamps
base=$(cat lake-manifest.json lean-toolchain | git hash-object --stdin)
olean() { echo ".lake/build/lib/lean/${1//.//}.olean"; }
imports() { (grep -oE '^import LeanProofs\.[A-Za-z0-9_.]+' "${1//.//}.lean" || true) | sed 's/^import //'; }   # (no match is fine: set -e)
# (ORD-1029-HUNT2V item 3: the key covers the whole LeanProofs import chain, not only direct imports, so a change two imports
#  down still forces a replay)
chain() { local seen=" " todo; todo=$(imports "$1"); while [ -n "$todo" ]; do local next=""; for d in $todo; do
  case "$seen" in *" $d "*) ;; *) seen="$seen$d "; next="$next $(imports "$d")";; esac; done; todo=$next; done
  echo $seen | tr ' ' '\n' | sort; }
for m in "${mods[@]}"; do
  t0=$(date +%s)
  deps=$(chain "$m")
  key=$( { echo "$base"; for d in $m $deps; do git hash-object "$(olean "$d")"; done; } | git hash-object --stdin)
  if [ "${FULL:-0}" != 1 ] && [ "$(cat ".lake/replay-stamps/$m" 2>/dev/null)" = "$key" ]; then
    echo "leanchecker: $m skipped: same .olean, imports and toolchain as its last kernel pass (stamp $key)"
    continue
  fi
  lake env leanchecker -v "$m"
  echo "$key" > ".lake/replay-stamps/$m"
  echo "leanchecker: $m replayed with no error ($(( $(date +%s) - t0 )) s)"
done
echo "leanchecker: all ${#mods[@]} LeanProofs modules (${mods[*]}) replayed through the kernel with no error, now or at their stamped pass"

step "6/6 nanoda: a second, independent kernel (Rust) checks every headline theorem"
# A proof stays Proven only when both kernels accept it: Lean's own (step 5) and nanoda, written separately in Rust
# (github.com/ammkrn/nanoda_lib), reading what lean4export writes. Only the headline theorems and everything they rest on are
# exported (a whole-Mathlib export is huge). Tools: ../external/nanoda_lib (cargo build --release) and ../external/lean4export
# (tag v4.35.0, lake build); the GitHub Action builds both the same way. A planted change to a proven number is refused (vibe-lab tests/test_nanoda_planted.py).
NANODA=../external/nanoda_lib/target/release/nanoda_bin; [ -x "$NANODA.exe" ] && NANODA=$NANODA.exe   # (pinned: nanoda d0a02cc)
EXPORT=../external/lean4export/.lake/build/bin/lean4export; [ -x "$EXPORT.exe" ] && EXPORT=$EXPORT.exe
[ -x "$NANODA" ] && [ -x "$EXPORT" ] || { echo "nanoda: not installed (see the comment above step 6)"; exit 1; }
names=$(grep '^#print axioms' VerifyAll.lean | awk '{print $3}' | tr '\n' ' ')
mkdir -p .lake/nanoda
t0=$(date +%s)
lake env "$EXPORT" LeanProofs -- $names HHHStampRule > .lake/nanoda/headlines.ndjson
nout=$("$NANODA" scripts/nanoda.json < .lake/nanoda/headlines.ndjson 2>&1); ns=$?
echo "$nout" | head -3
if [ $ns -ne 0 ] || ! echo "$nout" | grep -q 'with no typechecker errors'; then echo "nanoda: FAIL (exit $ns)"; exit 1; fi
echo "nanoda: $(echo $names | wc -w) headline theorems and the stamp rule re-checked by a second kernel with no error ($(( $(date +%s) - t0 )) s)"
