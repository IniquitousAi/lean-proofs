#!/usr/bin/env sh
# Lean 4 + Mathlib test project for the engine's checker #6. Makes projects/lean-proofs (Mathlib's own recommended way:
# lake new with the math template on Mathlib's toolchain, then the prebuilt cache). About 10 to 25 minutes, mostly downloads.
export PATH="$USERPROFILE/.elan/bin:$PATH"
RUN="lean-setup-$(date +%s)"
tell() { curl -s -m 3 -X POST http://127.0.0.1:8050/event -H "Content-Type: application/json" -d "{\"kind\":\"task\",\"id\":\"$RUN\",\"name\":\"Installing Lean 4 and Mathlib\",\"step\":$1,\"of\":3,\"about\":1200,\"note\":\"$2\",\"done\":$3}" >/dev/null; }
cd /c/Users/danie/Desktop/projects || exit 1
tell 1 "Lean and a new Mathlib project" false
[ -d lean-proofs ] || lake +leanprover-community/mathlib4:lean-toolchain new lean-proofs math || { tell 3 "making the project failed" true; exit 1; }
cd lean-proofs
tell 2 "downloading Mathlib's prebuilt files (several GB)" false
lake exe cache get || { tell 3 "the Mathlib cache download failed" true; exit 1; }
tell 3 "Lean and Mathlib are in" true
lean --version
