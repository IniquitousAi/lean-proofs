# lean-proofs

*Part of Humanity's Helping Hands™. © 2026 Daniel Steadham.*

Checker 6 of the engine's checker loop (`simulator-engine-claude/checkers`): answer-bank results stated as Lean 4 theorems,
checked by Lean's kernel with Mathlib. Set up on 2026-10-14 at Daniel's ask (elan, Lean 4.35.0, Mathlib's prebuilt cache:
about 7 GB in `.lake`, which is not committed). `SETUP.sh` makes it again from nothing; its install log is in
`../lean-proofs-setup/setup.log`.

- `LeanProofs/Bank.lean`: p01 (two dice sum to 7 with chance 1/6, counted over all 36 rolls) and p06 (a 20 step walk returns
  with chance 46189/262144). Compiles in about 23 s. A wrong version (1/5 for 1/6) is refused.
- Check: `lake env lean LeanProofs/Bank.lean` here, or `python checkers/loop.py run lean` in the engine.
