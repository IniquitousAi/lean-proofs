#!/usr/bin/env bash
# Step 5 of check.sh (kernel replay), kept in its own file so it can be tested with a fake `lake` (scripts/test_replay.sh).
# Run from the repository root, or sourced by check.sh. LANES=1 (the default) is the old one-module-at-a-time loop, unchanged.
# LANES=N (ORD-1030-LANE1) runs up to N separate leanchecker processes at once, one module each, biggest .olean first. Each process
# replays only its own module on top of its imports, the same trust as the loop. A new lane starts only while memory in use is
# under LANE_MEM % (default 70), and 20 s after the last start so that start shows in the reading. A module's stamp is written only
# after its own exit 0; the step fails if any lane fails.
set -euo pipefail
mods=()
for f in LeanProofs/*.lean; do m="${f%.lean}"; mods+=("${m//\//.}"); done
mkdir -p .lake/replay-stamps .lake/lanes
base=$(cat lake-manifest.json lean-toolchain | git hash-object --stdin)
olean() { echo ".lake/build/lib/lean/${1//.//}.olean"; }
imports() { (grep -oE '^import LeanProofs\.[A-Za-z0-9_.]+' "${1//.//}.lean" || true) | sed 's/^import //'; }   # (no match is fine: set -e)
# (ORD-1029-HUNT2V item 3: the key covers the whole LeanProofs import chain, not only direct imports, so a change two imports
#  down still forces a replay)
chain() { local seen=" " todo; todo=$(imports "$1"); while [ -n "$todo" ]; do local next=""; for d in $todo; do
  case "$seen" in *" $d "*) ;; *) seen="$seen$d "; next="$next $(imports "$d")";; esac; done; todo=$next; done
  echo $seen | tr ' ' '\n' | sort; }
replay_one() {
  local m=$1 t0 deps key
  t0=$(date +%s)
  deps=$(chain "$m")
  key=$( { echo "$base"; for d in $m $deps; do git hash-object "$(olean "$d")"; done; } | git hash-object --stdin)
  if [ "${FULL:-0}" != 1 ] && [ "$(cat ".lake/replay-stamps/$m" 2>/dev/null)" = "$key" ]; then
    echo "leanchecker: $m skipped: same .olean, imports and toolchain as its last kernel pass (stamp $key)"
    return 0
  fi
  lake env leanchecker -v "$m" || { echo "leanchecker: $m FAILED"; return 1; }
  echo "$key" > ".lake/replay-stamps/$m"
  echo "leanchecker: $m replayed with no error ($(( $(date +%s) - t0 )) s)"
}
mem_used() { awk '/^MemTotal/{t=$2} /^MemAvailable/{a=$2} /^MemFree/{f=$2} END{if(!a)a=f; print int(100*(t-a)/t)}' /proc/meminfo; }
LANES=${LANES:-1}
if [ "$LANES" -le 1 ]; then
  for m in "${mods[@]}"; do replay_one "$m"; done
else
  order=$(for m in "${mods[@]}"; do echo "$(stat -c %s "$(olean "$m")" 2>/dev/null || echo 0) $m"; done | sort -rn | awk '{print $2}')
  pids=(); names=(); last=0
  for m in $order; do
    while :; do
      running=$(jobs -rp | wc -l)
      if [ "$running" -eq 0 ]; then break; fi
      if [ "$running" -lt "$LANES" ] && [ $(( $(date +%s) - last )) -ge "${LANE_GAP:-20}" ] && [ "$(mem_used)" -lt "${LANE_MEM:-70}" ]; then break; fi
      sleep 1
    done
    ( replay_one "$m" ) > ".lake/lanes/$m.log" 2>&1 &
    pids+=($!); names+=("$m"); last=$(date +%s)
    echo "leanchecker: lane started for $m (memory in use $(mem_used)%)"
  done
  fail=0
  for i in "${!pids[@]}"; do
    if wait "${pids[$i]}"; then cat ".lake/lanes/${names[$i]}.log"; else cat ".lake/lanes/${names[$i]}.log"; echo "leanchecker: ${names[$i]} lane FAILED"; fail=1; fi
  done
  [ "$fail" -eq 0 ] || { echo "leanchecker: FAIL (a lane failed; no stamp was written for it)"; exit 1; }
fi
echo "leanchecker: all ${#mods[@]} LeanProofs modules (${mods[*]}) replayed through the kernel with no error, now or at their stamped pass"
