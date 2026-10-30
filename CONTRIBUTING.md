# Help build the floor

This library holds facts that a machine has checked. You can add one. You do not need permission, and nobody has to trust you:
the automatic check decides.

## Pick a task

Go to https://humanitieshelpinghands.com/help/ and press **Give me a task**. You get one of three kinds:

- **Prove one fact in Lean.** Write a Lean theorem that states the fact and prove it.
- **Check a source.** Read one fact's English sentence and its Lean statement. Do they say the same thing? Say so in an issue.
- **Flag a gap.** Something people ask that the library cannot answer. Open an issue that says what is missing.

Each task has a button that opens it as a GitHub issue, already filled in. Issues marked **good first issue** are good places to start.

## Send a proof

1. Fork this repository and make a branch.
2. Put your theorem in a new file under `LeanProofs/` (a subfolder is fine), and add an `import` line for it to `LeanProofs.lean`.
3. Run `./check.sh` on your machine if you can. It is the same check the pull request runs.
4. Open a pull request. The template asks for your GitHub name and your theorem's full name.

## When it counts

It counts when the **Verify** check on your pull request passes. That check builds every file with Lean, replays the proofs in a
second kernel, and scans the source for anything that skips the proof: `sorry`, `admit`, `native_decide`, `axiom` and a few
others. One `sorry` anywhere and the check fails. Nothing else counts: not a review, not a promise.

## Credit

When your pull request is merged, your GitHub name is added to `CONTRIBUTORS.json` next to your theorem. From then on the fact's
receipt on the website shows **Proved by @your-name**, and you are listed on the contributors page. It stays there.

## Rules

- Be kind. Questions are welcome.
- Your proof is published under this repository's license (see `LICENSE`).
- No proofs that only work by adding an assumption. If the check rejects it, it does not go in.
