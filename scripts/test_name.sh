#!/usr/bin/env bash
# Text check over every text file git tracks or would add (.lake and binaries skipped):
#   1. the public name is spelled "Humanities Helping Hands" (the old "Humanity's" spelling fails, straight or curly ')
#   2. every file is valid UTF-8, with no replacement character (U+FFFD) and no mojibake of the trademark,
#      copyright or quote signs (UTF-8 bytes read as Windows-1252).
# Exit 0 and "0 problems" when clean; exit 1 and each problem (file: what) otherwise.
set -euo pipefail
cd "$(dirname "$0")/.."

problems=0
report() { echo "test_name: $1"; problems=$((problems + 1)); }

# The patterns are built from escapes, so this file does not match itself.
old_name="Humanity(?:'|\xe2\x80\x99)s Helping Hands"
bad_bytes=$(printf '\xef\xbf\xbd|\xc3\xa2\xe2\x80\x9e\xc2\xa2|\xc3\x82\xc2\xa9|\xc3\xa2\xe2\x82\xac')

checked=0
while IFS= read -r -d '' f; do
  [ -f "$f" ] || continue
  grep -Iq . "$f" 2>/dev/null || continue            # binary or empty: skip
  checked=$((checked + 1))
  if ! perl -MEncode -e 'local $/; my $s = <>; Encode::decode("UTF-8", $s, Encode::FB_CROAK); 1' "$f" 2>/dev/null; then
    report "$f: not valid UTF-8"
  fi
  if perl -ne "exit 1 if /$old_name/" "$f"; then :; else report "$f: old spelling of the public name (use Humanities Helping Hands)"; fi
  if LC_ALL=C grep -qE "$bad_bytes" "$f"; then report "$f: replacement character or mojibake (a sign saved in the wrong encoding)"; fi
done < <(git ls-files -z --cached --others --exclude-standard -- . ':!:.lake')

echo "test_name: checked $checked text files; $problems problems"
[ "$problems" -eq 0 ]
