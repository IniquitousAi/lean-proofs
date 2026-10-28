# Re-run receipt

Humanities Helping Hands engine, built by Daniel Steadham.

One line per claim. `RERUN.cmd` (Windows) or `./RERUN.sh` (Mac, Linux) re-runs every one on your own machine and prints
the same lines in the same order, each with PASS or FAIL and why. `scripts/test_rerun.py` fails if a claim here has no
re-run step, or a step has no claim.

| id | claim |
| --- | --- |
| toolchain | Lean is the version pinned in `lean-toolchain` (leanprover/lean4:v4.35.0), installed by elan |
| source-audit | No proof file uses sorry, admit, unsafe, extern, implemented_by, native_decide or a new axiom |
| build | Every proof in `LeanProofs/` builds (`lake build`) |
| headline | Every headline statement in `VerifyAll.lean` is restated word for word and rests only on propext, Quot.sound and Classical.choice |
| root | Daniel's Root Theorem (`LeanProofs/Root.lean`, `DanielRootTheorem`) is one of them |
| kernel | leanchecker replays every `LeanProofs` module through Lean's kernel again, `LeanProofs.Root` included |
| answer-bank | The answer bank's hand-checked tests pass (`answer-bank`, `python -m pytest`) |
| stamps | Every OpenTimestamps proof in `stamps/` names the fingerprint recorded for its file in `stamps/STAMPS.md` (and, where the file is on this machine, the file's own fingerprint) |
| anchor-20261022-manifest | The 2026-10-22 drive manifest matches its anchor |

The last line is a known FAIL and stays in on purpose: the 2026-10-22 manifest was lost, a search of 9,096 files on the
key and the full Desktop did not find it, and the attempt is logged. It is shown, never hidden, because the aim is to be
perfect and this is where we are not yet.
