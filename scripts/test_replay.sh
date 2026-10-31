#!/usr/bin/env bash
# ORD-1030-LANE1: scripts/replay.sh with a fake `lake` (no Lean, a few seconds). Checks: LANES=3 replays every module, runs lanes at
# the same time, writes a stamp per passing module; a planted failing module fails the step and gets no stamp; LANES=1 still works.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd); t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
mkdir -p "$t/LeanProofs" "$t/.lake/build/lib/lean/LeanProofs" "$t/bin"
for m in A B C D; do echo "theorem t$m : True := trivial" > "$t/LeanProofs/$m.lean"; head -c $((RANDOM % 900 + 100)) /dev/zero > "$t/.lake/build/lib/lean/LeanProofs/$m.olean"; done
echo '{}' > "$t/lake-manifest.json"; echo 'leanprover/lean4:fake' > "$t/lean-toolchain"
cat > "$t/bin/lake" <<'EOF'
#!/usr/bin/env bash
m=${@: -1}; echo "start $m $(date +%s)" >> "$T/ran"; sleep 3; echo "end $m" >> "$T/ran"
[ "$m" != "${FAIL_MOD:-none}" ]
EOF
chmod +x "$t/bin/lake"; export T=$t PATH="$t/bin:$PATH"
cd "$t"; ok=1
LANES=3 LANE_GAP=0 LANE_MEM=101 FULL=1 bash "$here/scripts/replay.sh" > out1 2>&1; rc=$?
[ $rc -eq 0 ] && [ "$(ls .lake/replay-stamps | wc -l)" -eq 4 ] || { echo "FAIL 3 lanes: rc $rc"; cat out1; ok=0; }
starts=$(grep -c '^start' ran); first_end=$(grep -n '^end' ran | head -1 | cut -d: -f1)
[ "$starts" -eq 4 ] && [ "$first_end" -ge 4 ] || { echo "FAIL lanes did not overlap"; cat ran; ok=0; }
rm -rf .lake/replay-stamps ran
LANES=3 LANE_GAP=0 LANE_MEM=101 FULL=1 FAIL_MOD=LeanProofs.B bash "$here/scripts/replay.sh" > out2 2>&1; rc=$?
[ $rc -ne 0 ] && [ ! -f .lake/replay-stamps/LeanProofs.B ] && grep -q 'B lane FAILED' out2 || { echo "FAIL planted failure not caught: rc $rc"; cat out2; ok=0; }
rm -rf .lake/replay-stamps ran
LANES=1 FULL=1 bash "$here/scripts/replay.sh" > out3 2>&1; rc=$?
[ $rc -eq 0 ] && [ "$(ls .lake/replay-stamps | wc -l)" -eq 4 ] && [ "$(grep -n '^end LeanProofs.A' ran | cut -d: -f1)" -lt "$(grep -n '^start LeanProofs.B' ran | cut -d: -f1)" ] || { echo "FAIL LANES=1"; cat out3; ok=0; }
LANES=1 FULL=1 FAIL_MOD=LeanProofs.C bash "$here/scripts/replay.sh" > out4 2>&1 && { echo "FAIL LANES=1 planted"; ok=0; }
[ $ok -eq 1 ] && echo "test_replay: PASS (3 lanes overlap, planted failure caught with no stamp, LANES=1 unchanged)" || { echo "test_replay: FAIL"; exit 1; }
