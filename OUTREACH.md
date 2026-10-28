# Outreach plan (drafts only, nothing sent)

*Part of Humanities Helping Hands™. © 2026 Daniel Steadham.*

A plan for asking outside Lean users to check or break this repository: the links that must work first, who to
contact and in what order, and two drafts. Nothing here has been sent. The repository is private by design until every
internal check is perfected; the browser example works either way.

Counts (Measured, 2026-10-27: `runs/lean_gate.json` of the answer-bank engine and `./check.sh`, see `AUDIT.log`):
34 problems are Proven: 31 of the answer bank's 100, plus 3 problems the simulator engine adds (p48, p65 bridge hand,
p69 twenty dice). `VerifyAll.lean` restates 35 headline statements for them, because p32 has two (its equation, the
limit equals 4/7, and the convergence statement it comes from). 69 bank problems have no Lean proof yet. Re-read these from the README scoreboard right before sending.

## 1. Links that must work first

1. `<LIVE_LINK>` (the contents of `FLAGSHIP_URL.txt`): opens the flagship proof on live.lean-lang.org in the
   "Stable Release (v4.35.0 with mathlib)" project and ends with the `#print axioms` line. Open it once in a fresh
   browser and wait for the check to finish before sending anything.
2. `<REPO_URL>`: the repository, for readers who have been given access. `./check.sh` passes on a clean clone.
3. The GitHub Action "Verify (check.sh)" shows a green run on the commit being shared.

## 2. Who to contact, in order

1. The Lean Zulip stream "Machine Learning for Theorem Proving" (draft A): one public post, so any reader can try to
   break it.
2. One Lean contributor who works on autoformalization (draft B), chosen by Daniel: a direct message, only after the
   Zulip post has been up for a few days, so they can see any replies.
3. Anyone who answers with a break or a clean re-run: their result goes in the README's Expert Vouch Log, with credit
   if they want it.

## 3. Draft A: Lean Zulip post

**Topic:** Please try to break: 34 exact probability answers as Lean 4 theorems, one-command check

Hi all. I'm Daniel Steadham (Humanities Helping Hands). I have a small benchmark of 100 probability and counting
problems with exact answers. 31 of them, plus 3 related problems, are now stated and proven in Lean 4.35.0 with
Mathlib v4.35.0 (34 problems, 35 headline statements: one problem has two).

Each headline theorem states, about the problem's own objects, that a count or chance equals one exact number. For
example, the average number of cycles of a uniformly random permutation of 20 cards is exactly 55835135/15519504,
proven by grouping all 20! permutations by cycle type (Mathlib's `Equiv.Perm.card_of_cycleType`) and letting the
kernel add up the 627 groups. It runs in the browser: <LIVE_LINK>

`./check.sh` (<REPO_URL>) does: `lake exe cache get`, a comment-stripped source scan (no `sorry`, `admit`, `axiom`,
`unsafe`, `extern`, `implemented_by`, `native_decide`), `lake build`, a file that restates each headline statement
verbatim as `example : <statement> := <theorem>` and prints its axioms (only `propext`, `Quot.sound`,
`Classical.choice`), and the toolchain's bundled `leanchecker` replaying each project module through the kernel.

What I'm asking for is falsification, not praise:

1. Find a mismatch between a plain-English claim in the README table and its formal statement: a definition that does
   not mean what its name or docstring says, a statement weaker than the claim, a wrong probability space.
2. Or make `./check.sh` pass on something false, or fail on a clean checkout.

The other 69 bank problems have no Lean proof yet; they are listed in the README too. Any break you find gets logged in the
README's Expert Vouch Log with credit, and so does a clean re-run if you are willing to vouch for one.

Thanks for reading.

## 4. Draft B: short DM to a Lean contributor working on autoformalization

Hi <NAME>, I'm Daniel Steadham. I read your work on <THEIR_PROJECT> and have a small request that I think fits it.

I have 34 exact probability answers (31 from a 100-problem bank, plus 3 related ones) formalized in Lean 4.35.0 + Mathlib, with a one-command
check (`./check.sh`: source audit, build, verbatim restatement of the 35 headline statements with `#print axioms`,
`leanchecker` kernel replay). The weak point I worry about is the step you know best: whether each formal statement
really says what its plain-English claim says.

Would you spend 15 minutes trying to find one statement that does not match its claim, or a way to make `./check.sh`
pass on something false? Flagship in the browser: <LIVE_LINK>. Repository: <REPO_URL>.

If you find nothing, a one-line "re-ran it, it passed" would go in the README's vouch log with your name, only if you
want that. Thank you either way.
