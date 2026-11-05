#!/bin/bash
# check.sh step 0 passes on committed-but-unpushed stamps unless STAMP_PUSH=1; uncommitted always fails.
set -u
here=$(cd "$(dirname "$0")/.." && pwd); t=$(mktemp -d); fail=0
sed -n '/^step "0\/6/,/^fi$/p' "$here/check.sh" > "$t/step0.sh"
run() { (cd "$t/r" && step(){ :; }; export -f step; STAMP_PUSH="$1" bash -c "step(){ :; }; set -e; . $t/step0.sh" 2>&1); }
git init -q --bare "$t/o.git"; git clone -q "$t/o.git" "$t/r" 2>/dev/null; cd "$t/r"
git config user.email t@t; git config user.name t; mkdir stamps; echo a > stamps/a.ots; git add .; git commit -qm i; git push -q -u origin HEAD 2>/dev/null
echo b > stamps/b.ots; git add .; git commit -qm b
out=$(run 0); [ $? -eq 0 ] && echo "$out" | grep -q 'push off until Daniel' || { echo "FAIL off: $out"; fail=1; }
out=$(run 1); [ $? -ne 0 ] && echo "$out" | grep -q 'not pushed' || { echo "FAIL strict: $out"; fail=1; }
echo c > stamps/c.ots   # (planted: uncommitted must fail either way)
out=$(run 0); [ $? -ne 0 ] && echo "$out" | grep -q 'not committed' || { echo "FAIL uncommitted: $out"; fail=1; }
rm stamps/c.ots; git push -q 2>/dev/null
out=$(run 1); [ $? -eq 0 ] && echo "$out" | grep -q 'committed and pushed' || { echo "FAIL pushed: $out"; fail=1; }
[ $fail -eq 0 ] && echo "test_step0: PASS" || { echo "test_step0: FAIL"; exit 1; }
