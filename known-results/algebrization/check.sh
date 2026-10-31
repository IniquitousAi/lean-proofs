#!/usr/bin/env bash
# Rebuilds HHHAlg.lean against the BGS relativization repo at commit 2d9d847 (Mathlib pinned
# in its lake-manifest.json, rev fabf563a) and prints axioms.
# Options: UP=<git url or local path of the BGS repo> (default GitHub)
#          PKGS=<existing .lake/packages of a BGS checkout>: symlinked, no new Mathlib download.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${WORK:-$HERE/_build}"
COMMIT=2d9d84792344a53422e03b888aaa708b7d6d47f6
UP="${UP:-https://github.com/JoshuaTan42/lean-relativization-bgs}"
command -v lake >/dev/null || source "$HOME/.elan/env"
if [ ! -d "$WORK/up" ]; then
  git clone --no-checkout "$UP" "$WORK/up"
  git -C "$WORK/up" checkout -q "$COMMIT"
fi
P="$WORK/up"
cp "$HERE/HHHAlg.lean" "$HERE/Axioms.lean" "$HERE/lakefile.toml" "$HERE/lake-manifest.json" "$HERE/lean-toolchain" "$P/"
cd "$P"
if [ -n "${PKGS:-}" ]; then
  [ -e .lake/packages ] || { mkdir -p .lake && ln -s "$PKGS" .lake/packages; }
else
  lake exe cache get
fi
time lake build HHHAlg
echo "sorry count:"; grep -c sorry HHHAlg.lean || true
lake env lean Axioms.lean
