#!/usr/bin/env bash
# Source audit: scans LeanProofs/*.lean with comments removed for anything that would let a proof skip the kernel
# or add an assumption: sorry, admit, unsafe, extern, implemented_by, native_decide, and `axiom` declarations.
# Exit 0 and "0 matches" when clean; exit 1 and every match (file:line: text) otherwise.
set -euo pipefail
cd "$(dirname "$0")/.."

shopt -s nullglob
files=(LeanProofs/*.lean)
if [ ${#files[@]} -eq 0 ]; then echo "audit_source: no LeanProofs/*.lean files found"; exit 1; fi

# Removes -- line comments and /- ... -/ block comments (nested, doc comments included), keeps line numbers.
strip_comments() {
  perl -0777 -ne '
    my ($s, $out, $depth, $i, $n) = ($_, "", 0, 0, length $_);
    while ($i < $n) {
      my $two = substr($s, $i, 2);
      my $c = substr($s, $i, 1);
      if ($depth == 0 && $c eq "\"") {                      # string literal: copy as is
        my $j = $i + 1;
        while ($j < $n && substr($s, $j, 1) ne "\"") { $j += (substr($s, $j, 1) eq "\\") ? 2 : 1; }
        $out .= substr($s, $i, $j - $i + 1); $i = $j + 1; next;
      }
      if ($two eq "/-") { $depth++; $i += 2; next; }
      if ($depth > 0 && $two eq "-/") { $depth--; $i += 2; next; }
      if ($depth > 0) { $out .= "\n" if $c eq "\n"; $i++; next; }
      if ($two eq "--") { while ($i < $n && substr($s, $i, 1) ne "\n") { $i++; } next; }
      $out .= $c; $i++;
    }
    print $out;' "$1"
}

pattern='\b(sorry|admit|unsafe|extern|implemented_by|native_decide)\b|^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|partial)[[:space:]]+)*axiom\b'

matches=0
for f in "${files[@]}"; do
  hits=$(strip_comments "$f" | grep -nE "$pattern" || true)
  if [ -n "$hits" ]; then
    while IFS= read -r line; do echo "$f:$line"; matches=$((matches + 1)); done <<< "$hits"
  fi
done

echo "audit_source: scanned ${#files[@]} files (${files[*]}), comments removed"
echo "audit_source: looked for sorry, admit, unsafe, extern, implemented_by, native_decide, axiom declarations"
echo "audit_source: $matches matches"
[ "$matches" -eq 0 ]
