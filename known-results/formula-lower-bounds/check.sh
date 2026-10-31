#!/usr/bin/env bash
# Rebuilds the circuit-lane files (lib PvNP, Mathlib pinned in lake-manifest.json) and prints axioms.
# Options: PKGS=<existing .lake/packages with this Mathlib rev>: symlinked, no new Mathlib download.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${WORK:-$HERE/_build}"
command -v lake >/dev/null || source "$HOME/.elan/env"
mkdir -p "$WORK"
cp -r "$HERE/src/PvNP" "$HERE/Axioms.lean" "$HERE/lakefile.toml" "$HERE/lake-manifest.json" "$HERE/lean-toolchain" "$WORK/"
cd "$WORK"
if [ -n "${PKGS:-}" ]; then
  [ -e .lake/packages ] || { mkdir -p .lake && ln -s "$PKGS" .lake/packages; }
else
  lake exe cache get
fi
MODS="PvNP.Subbotovskaya PvNP.SubbotovskayaRandom PvNP.SubbotovskayaRp PvNP.Andreev PvNP.AndreevFinal PvNP.RpTrue PvNP.Khrapchenko PvNP.Decomp PvNP.ParityUpper"
time lake build $MODS
echo "sorry count:"; cat PvNP/*.lean | grep -c sorry || true
lake env lean Axioms.lean
