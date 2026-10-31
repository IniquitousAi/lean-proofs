#!/usr/bin/env bash
# Builds the HHH files against the pinned upstream and prints axioms.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${WORK:-$HERE/_build}"
COMMIT=fbb5be4875dd86fd0e180b97e359a6cece930cbd
SUB="AC0[2] Circuit Lower Bounds-Yichuan Wang"
command -v lake >/dev/null || source "$HOME/.elan/env"
if [ ! -d "$WORK/up" ]; then
  git clone --filter=blob:none --no-checkout https://github.com/ucb-lean-course-sp26/final-projects "$WORK/up"
  git -C "$WORK/up" sparse-checkout set --skip-checks "$SUB"
  git -C "$WORK/up" checkout "$COMMIT"
fi
P="$WORK/up/$SUB"
cp "$HERE"/Project/HHH_*.lean "$P/Project/"
cp "$HERE/lakefile.toml" "$HERE/lake-manifest.json" "$HERE/lean-toolchain" "$HERE/Axioms.lean" "$P/"
cd "$P"
# Reuse an existing package checkout (no new Mathlib copy) if PKGS is set,
# e.g. PKGS="/path/to/upstream/.lake/packages". Otherwise fetch the cache.
if [ -n "${PKGS:-}" ] && [ ! -e .lake/packages ]; then
  mkdir -p .lake && ln -s "$PKGS" .lake/packages
else
  lake exe cache get
fi
time lake build Project.HHH_Vacuity Project.HHH_Repair Project.HHH_Asymptotic \
  Project.HHH_Final Project.HHH_Real Project.HHH_Sanity
echo "sorry count:"; grep -c sorry Project/HHH_*.lean || true
lake env lean Axioms.lean
