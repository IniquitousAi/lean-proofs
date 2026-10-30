# lean-proofs

**Prove it once. Keep it forever. Move on.**

*Part of Humanities Helping Hands™. © 2026 Daniel Steadham.*

Exact answers to small probability and counting problems, stated as Lean 4 theorems and checked by Lean's kernel with
Mathlib. Each theorem says, about the problem's own objects (every roll, hand, walk or shuffle), that a count or
chance equals one exact number, for example that a random shuffle of 20 cards has exactly 55835135/15519504 cycles on
average. One command, `./check.sh`, re-checks everything from scratch and writes what it saw to `AUDIT.log`.

Private by design until every internal check is perfected; the browser example works either way.

The problems come from the answer bank (100 problems with known exact answers) and from the simulator engine that
checks it. 48 problems are Proven here: 45 of the bank's 100, plus 3 the engine adds
(p48_third_success_by_twelve, p65_trap_bridge_aces_kings, p69_trap_twenty_dice_low_tail). No problem with a Lean theorem is held back: all of them are Proven. The other 55 bank problems have no Lean proof yet and are listed at
the end.

**Every claim on this page carries one of four labels:**

| Label | Meaning |
|---|---|
| **Proven** | A Lean theorem states it; `leanchecker` replays the proof through Lean's kernel; nanoda, a second kernel written separately in Rust, accepts it too; `#print axioms` shows only `propext`, `Quot.sound`, `Classical.choice`; zero `sorry`; the formal statement is paired with a plain-English claim in the table below. |
| **Measured** | Counted or timed by a script, with a receipt (a log file or a command you can rerun). |
| **Reasoned** | Deduced by hand, not machine-checked. |
| **Guess** | Not tested. |

## Starting rules

Every proof starts somewhere that no check can check: the bottom has to be taken as given. Each Proven row says where it
starts, strongest first:

1. **Lean's logic only.** Nothing assumed beyond Lean's own rules for a valid step. Example: the HHH stamp rule
   (`LeanProofs/Stamp.lean`: a claim carries the stamp only if the checker passed it), `#print axioms` says it depends on no axioms.
2. **Lean's logic + the standard 3.** The three assumptions nearly all of modern mathematics rests on: `propext` (two
   statements that each imply the other are the same statement), `Quot.sound` (things declared equal can be swapped), and
   `Classical.choice` (if something exists, one may be picked; this is where "true or false" comes from). All 48 problems.

And the machine: two kernels written separately (Lean's own, and nanoda in Rust) must both accept every headline proof, so
trusting one program is not enough to fool it. A planted change to a proven number is refused (vibe-lab
`tests/test_nanoda_planted.py`). Lean 4.35.0 is past the 4.32.2 fix for a kernel bug that let a crafted proof of False through.

## Scoreboard (Measured: `runs/lean_gate.json` of the answer-bank engine, 2026-10-27T21:12:21, and `./check.sh` on 2026-10-28)

| | Count |
|---|---:|
| Problems in the answer bank | 100 |
| Problems with a Lean theorem stating the exact answer | 48 |
| Proven | 48 |
| Proven, from the bank's 100 | 45 |
| Proven, engine problems beyond the bank | 3 |
| Headline statements restated in `VerifyAll.lean`: 49 for the 48 Proven problems (p32 has two: its equation, the limit equals 4/7, and the convergence statement it comes from), plus Daniel's Root Theorem | 50 |
| Pass Lean but held at Guess | 0 |
| Bank problems with no Lean proof yet | 69 |
| `sorry`, `admit`, `axiom`, `unsafe`, `extern`, `implemented_by`, `native_decide` in `LeanProofs/` (comments removed) | 0 |
| Axioms used by the headline theorems | `propext`, `Quot.sound`, `Classical.choice` only |

## Verify it yourself

1. **In the browser, nothing to install** (the flagship proof below, one file): [open it on live.lean-lang.org](https://live.lean-lang.org/#project=mathlib-stable&codez=JYWwDg9gTgLgBAWQIYwBYBtgCMBQOD0AtAIQ4DEcAYukgOYDOqwYAXHEnFEgHYAmEIOIwCuAM1HoApnAii4AJgAMcAMZIovenFRItkgB5IVMdAE84AVgsAOAMwWAjPfwOrDgJwXFAFlWmVUloQ3OwAbpJctJJ4AMqS6KKEKsEwSMDckryqEGDmsnBo0mDe8nBgUBD5ohWCAAYAMpI8AAoVsvT4AMKoTWAAdFI8tXAAFPSSxsDBcLWd%2FoG1ADTZYMCZcMLcKjrcUbwAlHDpOLTAaMJYfckg%2BACS3MAAjsJnEML0AILA%2BIPchOWVUT0PpwTpQJowdZYcwAER4a3QcBikKQvB0IGWAAlhCB4TA1lpMfFVrs4JieJo%2BnhmjR0oQAKK7TCMVS0kBsVYqADWMgyMjkhQUimIcAAvApFt5bPJFu5FDLFIprIsHAB2ABsi3V3kUi0VymgvAi6QYozAERAwlS%2BOC9EO%2BSUqnUmmWSHQiMkzzdZhwmC58VMIMoEHdEAA7nAmtsnRoChACj0yjQVNIznAQBBwlkYBBXXwhPHgstNvjEaY3tkQNIsEYuWw0Cg4OhKmAjloOCp5tIRh3nQmUDh6KlTFowFa2%2Bw%2FAFpPkpLs0HAHPsQQAVRNIcKRaTcHFYCL8qeBCcGIwmcxWOyOZyuRyeHyjJBYN7wWx9Czuaz7ZZhpjR4D0HBBSUBcdCgDMHhUOAdxAPcoEXOAAGpF3wUokL6dDEOQpQqRwTFwyOeB%2FzKCpwm4esenBdhKNEdQ43jXFuHMc0wKtFApm4LQcybf8YGWeh40FAF8loCphDATiekEaFD2kRgkHNEFak7acYh0c16FqX0eIk6R1XkVUyggeh6GwKQhDUyR6AAbhmZSpBXUxzQAfSrEAnLk804hgYYAXCPRNyYi1WJtEIHWUNQNC0HQgj5fJChAKycGQNBMCwAByLRanpZ5gFCPpmgtK5nSc2QnLsyQHPNYZkhLHSyiC612KCOQo1Qcz5MkGzBX9KAMkRVFNA2VtBT0gyRLecScBGWojRUYAjUQnq%2BqWKD4wMGAuHYfQphAZc8AAdR0eBamguZpw07JarYZKMGwDLbK7ShT2gehKHScZvNGQVyuaptJHnNrSmgdNoEkQ4wHQd4E2kURgH0dZIHSGBgTwNdpBoIduL5cokbqpBtoEOqelRTA%2BXBIcYrYAxzWMYicnW5ZOgxky1HQK5UAgYAU2WABFYQIBgPp%2BM2XgqUIfA8G4JAq3oMAjGkbpenqHhokHCYQtBLsAJwemQmyl5Qiod7JBgPAiEIOA0Zk36OGYy1GumMKY00Ngzi0H6DznWgFyBuCM0okYbtS%2B6lMe56oFe43vPByGtDdnBYfhrJEe4ZGvsTD3Z3%2B722qXEFxZwI05FOrW4AAbxCNhAFRCABfUZAGHgOA2AKsDRjekJuH2Q5q6b8UyHrq4w%2BMF724%2BzCyDL%2FQ4AAHzgRup%2FFfQa7NwgLat5lkeWGgoCiTG5dgOBYYj3i4DDM42skAKynUeBqgEBQ40QZZ97TgaTSGx%2FGwzTGADk8yyL%2BRlb7X1gPQFgOBL4RCYkZEyWAzIbwPOVP6AMtAjF9iDcE9o5C2wamxYI%2BcJZFxkqpDqWge6ACTCOAVc4CUOoZQ%2BoPFRgMMxlXfYOA4AzzgLqOATllhOTFAAPjgAAbWEQAXTEewzhcgkIOGWH%2FRAgiRFiKbmwEYzDBZcF2JINKD9A5wAtkuZcEgUDIDAFIjhHCRiiE2JOUUQjgDYLgIAEyI4A%2F2hiEEY5USHqUPqMdxFskCHCCX0XErYeyqLgAAdsOPEcYyi2GAR6KDQQrkypdh8ZZJucBAAARKMOQ7iEDZNYaMREbANFUK%2FE2fKaQoBn3iSMKJcBACmRNEw45CLGjDyVPQAEERNmWKUVxU9ADkRHAKeriEDtOqfQHELi3E0OqV7Bcri5CUMRH07xFktAFMQFI2e3DeE8OWOIvhpyjk8KUdJEy4ARGbNIZIjhs9%2BGyLOYck55zDmfMueYa5rZhF3PUg8zhBzXmRM%2Ba85YbV7FwCuaAVsjZUB7L8S8txywECukiSfVAYBIX6EhfQSFiJoXQk6XUkRGi%2Bhy2AHU%2F8kgyq2hUQi8xljtAbmkDoXu2gp4cApWk5IHF3LxFEJ035vIzDkp4kLHE9KOLLApUs1AMr6CMvgKgKK6ARVwrFeYf5GStlyslXy20BqhyhMkG5ExMAzEmsFmkrRUQ0pOQcECjhUBgC0FQKbFl4JYZ8kABfkSBlh%2BukgISQtBA0wryFWcNgBL8mWAAficjGkVEMzhOUcVoM%2BIEkA%2F06U0k8tNeXmpcvJPopQ%2FUnz5Xq0hfiRgBPYMEgo2h%2BjyE6Sy6xtip6oH0Lo6FfqRjdrGUww1xb%2BX0BKqIFy5qLndrSl3Pocjm0LqHbOmNhwRghujUE0Ym6w1BOWFACQyaWVNNDeGvAhQUl%2FXctK0qrldFsDySMMpcAKklJGFPauVTelNgWeM6ZOIkXvMOVCoRsKbkIqRRwFg9Zlh4u0N80lahxhaCLW5Mdy62pZraoexEs9EUnqEHCvNrLwicqkDetyd7zW6PgF2ttRGbnBHFcIilMz0MMpsmepAF7kngkEDAMMEAXLCHQE5BV4npCPtKdkt9VSRjdLgH09AAy5n6CmaUAAVIs7OyyAMgCA2Ivh3zGPMs4dB2DCHiWmE6ToMjLBxSCeE5aMTEmzLwA7SELtC8hFtSnuokdHGBXUcEPw7tXdbNss5W1HlgWlWCoSJqpj3AWNselWOm1AxdOKrHWIrjW6V4W3pFfDe6wPKpi0PxWAmQt7qF3vAF%2Bh9qVDm%2FOfVaID4CPkzNIBABCkmSCvQCyy7loCQiyNJ6x8yilfuWHk9ZxCtl%2BMKVvGp1L6ndiaa0mJcBRmKeU3BuZCAkUgvOSpqzYGbMstFcxnVQ2CWvriyZJkJtggqu0CKi4mNUA2V%2BUimRi55Foq3pCxDV2tU3dudW9SmWjWyoe6atJlrrXw9tcW%2B1OinVvYI5YqAyGslYba7hzhAag06BlKyhAcbtDHssU037hHZaYBgOmoE7BVWnzazoXNLKOGnqwKkdIcAK2QpPrhmNnK0Mlv6A4d7PPLF2dTG1BzC3SEjeq1kOQdaDENsnKqr1cvOCSF9dIP1FKqU0vGEqstQubFea5Uo4AqBrfeeWI7hdVPbcrp83ARNNO5e490FkyXGGZeDuw5wCQnDu0Md5zIArBvomkak%2BKN3pRvP5b3QxunWrIMEFXm4%2BM5WJylezGfFMfXL38ZV%2BpJy3AIC8DEtkp9OzpuVOWF4qHWSW%2FLh%2FvXsSx3QXWdM5DlSWygWz3%2B4uhRRTrOkojLq0fpDMt14b2AJVLrsgcQ2sIYeUASPXZSzqyXSP5LLDr8zgw2kz8CychSDfHCkYVEnGFhjjO00ZrZ7Lnn2eIOqqz8PyDQjMlVjSVFfMSJyE%2FMAe%2FTfIcKAHfHMPfOXJpR%2FeMDgJyGPIQVNZnDNDA%2FNQwWmDvRfGvMA1sTXetbdEJMJfJWxfhMLJRClMddNbgAAK3VlynZTYQTzwNPBRz6BINr2AA1SQMN2N14N71X0pVqXWwnQgOgG9Fr2kApX4PR10U9zQJhRnUfCUUTQwOAMoE2EmHwWCH0O4Ey14H%2FGYM5lTkk1EBgGgIf1Tif0RAwA4AwFwATzf2wNZwRRoG0HQCwDgAAB4rIhED9Us4swll8b80kHh0AsdfC3CMCIB%2Bc0gQhhdzkxdosaAkiUjBc%2FVhAzlUBhBxdldEiE8C1VUtCAtTVGDPQrdQ9hBlwHAhZTAQADM8815ExRoZJ2pfF8g7ZgomoDxHQIpKQDFCEjdejLJHRylGFqj4ASllc7tFxlBHQlBCtLZExyt2wtAXN8QPpUEg47pMpypKpJBhgiIOA9jaUYB9gbI68CghMqJpBBR6BpZJA%2BJ0gUxIwjA2oEEiIqsxs%2BsiFysvJslR4TZRgEBRN9jITFjRQpE%2FVABEwjGC2WwioM81%2FVmJYSUWfWyWhPQFhIWK7iqQJKJKuAgDpRIOt0COnk6UIKkEyXHRIJWKFCFGXDCRKhCE928zgHMFQH5MEQYwpRbhAD6DqNKnN3W10RGDgmV0aRaTaXXTuzVzG1ZLWOUG8yaIwIZMkCZNVPWAcFWONL5O0FMCaKhJhJuIpLpTqOSEkEw32GTQ6LgGKygXqhYgdlCjkBGOdCil0F5BnAFETBLymOBHGP60Gy7DOKnTclBMhJGEbmbgtDbkFyUC7myQHlOMcmkD6XjPgGVxJQ4THjKXFCzOjJzKFlG1GE2zaSkQVz8OyTxOuitLHhKTLMHmnDOM5TJOtMBKck9AuXQI4QbLVVmTYDZnYzmRmPFCLPlyi2V1FKlXQwrOcjMnrjnxEUAATCPwtFVsk2Zc%2BlD4o2VOSs0YiA9IN7NAf8TpCohMG8kcqLVAUoaTH9M7QZIdZXHk%2B3exTpJcpzSTGQqtLsnM0YQOfc1HOM6shUrbedUPdTesp81ybJebbYmczpYCxkxbI0tkx0REcCwk60qU2lVUoczgnnTE3kvtZ8r3dvCjdjICmjX9LUvoDaHgKKdjNdbQdjBjDdfkhcxzITETVzbLSTX9Z8jPcNcixgfCcskC80JTUYFEtCxQUJeSagkIF9N9XEl9Xstskk%2FEiCy0wi%2FS8i4AvSg8o1Y8yXMJIFO8v1M7VAVyQlZ0yvadEuc6Acx4BubJUU1MkIdM7uTpDyo8RucUCywWUYueTs%2ByUCpCNBZQC2OS2KhSdjbuWcy7JPbQGXFskyg8qK5KiqUCvuQqp6XfSODiSEwszK11efJc7M5yIuPcvKyK4qWymyXDRCsjGi5XCE1qjQC8wkiIW%2FXgXgMqYqWGIaqAWvAWUYMhcUEYTYXKcEqOfy9kjMyipReeMUMZci0c2wbJfuKVMASAA%2BPuRah4PKSayEOCb86FAAGrniHUXnSsjU6X5REkXCkTCNu2KiWtCGWHbhgDPImsvM%2F2fKkWAKXIYoauPNQEXRCssiBW4w2OKHkDYG6zgm9CFBFAGK9N%2Bl9MimWG%2BlLgGg%2Fi4mVFVAsBlHcG8GVEUFsE1A1DkXVEVD1EVB2qUBFG00xASv2HImiDxrwQ4meLgHGjEihHMCQXK3%2FkQBQFunShOOKlKlhuqjeFTj0F%2BLFtEn6AjLcsEDRqchzFSBfUAEQiJ65M1uEYdudks%2FHEM6UKna6wKm%2BQWm6wBm9UZm1m%2FUZQaq768HQ%2FERRG8dT0IFYAncvqw82GWCaQu9eScdLiMYTlf69dAs8UfM9dWgTleq1csGekz3RufhaFWG2M9yCyME%2BufYIFUc6OpvdMRS%2FMxYXi82xuPpf6voa6%2FcTEpMuAPy62tMxQQ4aFQq7s8UXaJuhPAi8kgqmKoqhS%2BKx0JK2es45ckkjAvuMuHuvum29MzhEe4q9MOubTKe60qKwQBexK9MVe16uchwjaeiHhTc4RSOmG4IT6onEYLOr8mgpRCKoqWMc%2B0YReq%2BtK8i9tAu7QMKi7TgeffuyqyCwam6zDSustMRKpF%2B9LW0E%2BegFzLy4SsO%2BfDBoLd%2ByPVAaOoFH6kRfWXKfKQqc8lW3OwGpGEGga31IFWaeaaQBCJaeIVGkoNgfiScJa0QaAEAcVLRfgA23BDWJ2UY%2F0rQC8ewJwCwFwNwO8XwTOEINlLcUYcUXm9M5YROBGKw5GHAGqVOdYAMzOOQBVRcZcPWvjadQ2kQcQCjamdWTIdJc6JuekkYFu3ylMuB22qCe20uHuxYuAQALEJDh8B%2FLgaFIoqRht6B6My2BomGNxRFGrwLA4BYmbwPAvBfA%2FbHzuq5A1EZjKkO7w5gA3ROapRXb5RFRrA1R1RtQfbOVpIOGFpuGIg%2BpIb59Dbja3QmHTyEnio7YRn4mHTzzfVIVRAgU68wJa9AMIF8wHbLI8AyAcZU4todpRwSgy6xAJBbT9AaYxsvHAg8B%2FoshFZ5JlYMgcAgA).
   It loads in the site's "Stable Release (v4.35.0 with mathlib)" project, the same Lean version as this repository
   (Reasoned: the site's Mathlib build may differ slightly from the pinned one here). The kernel check takes a while;
   wait for the `#print axioms` line at the end.
2. **In a GitHub Codespace:** open this repository in a Codespace (Code, Codespaces, Create). The dev container installs
   elan and downloads Mathlib's prebuilt files on creation. Then run `./check.sh`.
3. **On your own machine** (needs git, bash, perl, curl and [elan](https://github.com/leanprover/elan); no default
   toolchain is needed: `./check.sh` runs every Lean command through `lake`, so elan installs and uses the version
   pinned in `lean-toolchain`, and `leanchecker` comes bundled with that toolchain, nothing extra to install):

   ```bash
   git clone https://github.com/IniquitousAi/lean-proofs && cd lean-proofs && ./check.sh
   ```

   Measured: `./check.sh` took 1071 s of wall-clock time on Daniel's PC (Windows 11, Git Bash, Mathlib cache already
   downloaded and the proofs already built once; commit 4996b70; see `AUDIT.log`). A cold machine also downloads
   Lean (about 200 MB) and Mathlib's cache (several GB) and builds `LeanProofs` from scratch, so expect longer.

What `./check.sh` does, in order, stopping at the first failure:

1. `lake exe cache get`: Mathlib's prebuilt files, at the commit pinned in `lake-manifest.json`.
2. `scripts/audit_source.sh`: scans `LeanProofs/*.lean` with comments removed for `sorry`, `admit`, `unsafe`,
   `extern`, `implemented_by`, `native_decide` and `axiom` declarations. Must find 0. Then `scripts/test_name.sh`:
   every text file is valid UTF-8 with no garbled signs, and the public name is spelled Humanities Helping Hands.
3. `lake build`: builds every proof.
4. `lake env lean VerifyAll.lean`: restates each headline statement word for word as
   `example : <statement> := <theorem>`. The proof term of each `example` is the original theorem constant itself
   (for example `CheapLane.p42_shuffle_expected_cycles`), so each restated statement is bound to that exact theorem,
   and a theorem that states something else fails to compile. Then it checks that every `#print axioms` list uses only
   `propext`, `Quot.sound`, `Classical.choice`.
5. `lake env leanchecker -v LeanProofs.<Module>`, one module at a time for each file in `LeanProofs/`: replays every
   declaration through Lean's kernel again from the compiled files.
6. nanoda, a second kernel written separately in Rust (`github.com/ammkrn/nanoda_lib`, pinned commit `d0a02cc`), re-checks
   every headline theorem and everything it rests on, read from `lean4export` (tag `v4.35.0`). Both tools sit in
   `../external`; the GitHub Action builds them the same way.

The GitHub Action `.github/workflows/verify.yml` runs the same `./check.sh` on every push and pull request.

Pinned versions: Lean `leanprover/lean4:v4.35.0` (`lean-toolchain`), Mathlib `v4.35.0` (`lakefile.toml`; commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`).

## Flagship: p42, the average number of cycles of a random shuffle of 20 cards (Proven)

**Plain English:** pick one of the 20! = 2,432,902,008,176,640,000 orderings of 20 cards, every one equally likely.
Follow each card to where it moved, then that card, and so on, until you are back where you started: that loop is a
cycle (a card that stays put is a cycle of length 1). On average there are exactly 55835135/15519504 cycles (about
3.598). That number is 1 + 1/2 + ... + 1/20 (Measured: Python's `fractions` gives the same value).

There are far too many orderings to list one by one, so the proof groups them by cycle shape: it lists the 627 possible
shapes, proves every permutation of 20 cards has one of them, counts each group with Mathlib's
`Equiv.Perm.card_of_cycleType`, and lets the kernel add the groups up.

The one definition the statement uses (`Perm`, `cycleFactorsFinset`, `Fintype.card` and `#` (Finset card) are Mathlib's):

```lean
open Equiv Finset

/-- The cycles of a permutation of 20 cards: its cycles of length 2 or more (Mathlib's `cycleFactorsFinset`) plus its
fixed points (the cycles of length 1). -/
def numCycles {n : ℕ} (σ : Perm (Fin n)) : ℕ := #σ.cycleFactorsFinset + #{x | σ x = x}
```

The exact theorem ([`LeanProofs/Cheap.lean` line 458](LeanProofs/Cheap.lean#L458)):

```lean
theorem p42_shuffle_expected_cycles :
    ((∑ σ : Perm (Fin 20), numCycles σ : ℕ) : ℚ) / (Fintype.card (Perm (Fin 20)) : ℚ)
      = 55835135 / 15519504
```

`flagship_playground.lean` is the same proof as one self-contained file (`import Mathlib` plus its own definitions).
Measured: `lake env lean flagship_playground.lean` exits 0 in 29 s on Daniel's PC.

Runners-up: p43 (Proven: the kernel counts the shuffles of 10 cards, all 3,628,800 of them, that keep some card i
directly before card i + 1) and p32 (Proven: a Markov token's chance of winning within n moves tends to exactly 4/7, a
limit rather than a finite count).

## The 48 problems with a Lean proof

Plain claim and exact answer from the answer bank's `answers.json` (for the 3 engine problems, our own plain reading of
the engine's spec in `problems.txt`, Reasoned); the theorem states that exact value about the
problem's own cases. "Starts from" is read from `#print axioms` (Measured: `runs/lean_gate.json`, and step 4 of `./check.sh`).

| Problem | Plain claim: exact answer | Headline theorem | Starts from | Label |
|---|---|---|---|---|
| p01 | Dice odds: sum of two dice is 7: `1/6` | [`p01_dice_sum_seven`](LeanProofs/Bank.lean#L16) | Lean's logic + the standard 3 | Proven |
| p02 | Coin streaks: a run of 5 heads in 20 flips: `32751/131072` | [`p02_coin_streaks`](LeanProofs/Walks.lean#L289) | Lean's logic + the standard 3 | Proven |
| p04 | Card draws: exactly two aces in five cards: `2162/54145` | [`CheapLane.p04_two_aces_in_five`](LeanProofs/Cheap.lean#L136) | Lean's logic + the standard 3 | Proven |
| p05 | Birthday problem: a shared birthday among 23 people: `1 - (365*364*363*...*343)/365^23` | [`TowerBatch.p05_birthday_problem`](LeanProofs/Tower.lean#L916) | Lean's logic + the standard 3 | Proven |
| p06 | Random walk: return to origin after 20 steps: `46189/262144` | [`p06_random_walk`](LeanProofs/Bank.lean#L31) | Lean's logic + the standard 3 | Proven |
| p07 | Monty Hall: win probability when switching: `2/3` | [`p07_monty_hall`](LeanProofs/Bank.lean#L93) | Lean's logic + the standard 3 | Proven |
| p09 | Waiting for a six: expected rolls to first 6: `6 rolls` | [`WaitingLane.p09_rolls_to_first_six`](LeanProofs/Waiting.lean#L14) | Lean's logic + the standard 3 | Proven |
| p10 | Maximum of two dice: expected larger face: `161/36` | [`p10_max_of_two_dice`](LeanProofs/Bank.lean#L62) | Lean's logic + the standard 3 | Proven |
| p12 | Three or more sixes in ten rolls: `566299/2519424` | [`CheapLane.p12_three_plus_sixes`](LeanProofs/Cheap.lean#L155) | Lean's logic + the standard 3 | Proven |
| p13 | Expected cards to the first ace: `53/5 cards` | [`TowerBatch.p13_cards_to_first_ace`](LeanProofs/Tower.lean#L929) | Lean's logic + the standard 3 | Proven |
| p17 | Three-of-five vote: chance of passing at 60% yes: `2133/3125` | [`TowerBatch.p17_three_of_five_vote`](LeanProofs/Tower.lean#L947) | Lean's logic + the standard 3 | Proven |
| p21 | Trap: one specified outcome in 1,000: `1/1000` | [`TowerBatch.p21_rare_one_in_1000`](LeanProofs/Tower.lean#L958) | Lean's logic + the standard 3 | Proven |
| p22 | Trap: St. Petersburg payout capped at 2^20: `21 dollars` | [`TowerBatch.p22_st_petersburg_capped`](LeanProofs/Tower.lean#L970) | Lean's logic + the standard 3 | Proven |
| p30 | Area under a curve: y = x^2 from 0 to 3: `9` | [`CalculusLane.p30_area_under_square`](LeanProofs/Calculus.lean#L15) | Lean's logic + the standard 3 | Proven |
| p31 | Markov weather: rain exactly four steps after a sunny start: `2137/10000` | [`p31_markov_weather_four_steps`](LeanProofs/Bank.lean#L104) | Lean's logic + the standard 3 | Proven |
| p32 | Markov token: reaching the win square before the lose square: `4/7` | [`CheapLane.p32_markov_token_absorption_limit`](LeanProofs/Cheap.lean#L912) | Lean's logic + the standard 3 | Proven |
| p36 | Birthdays: expected number of different days among 30 people: `5840637997733944304472717260382885356354745452713098221901782271034552207449/202531728519726872798204574491055504334773427222006304748356342315673828125` | [`CheapLane.p36_birthday_expected_distinct`](LeanProofs/Cheap.lean#L1002) | Lean's logic + the standard 3 | Proven |
| p37 | Random walk: reaching +3 within 12 steps: `397/1024` | [`p37_random_walk_hits_three`](LeanProofs/Walks.lean#L259) | Lean's logic + the standard 3 | Proven |
| p38 | Two-dimensional walk: back at the start after 6 steps: `25/256` | [`CheapLane.p38_random_walk_2d`](LeanProofs/Cheap.lean#L84) | Lean's logic + the standard 3 | Proven |
| p39 | Random walk: expected highest point in 10 steps: `251/128` | [`CheapLane.p39_expected_max`](LeanProofs/Cheap.lean#L62) | Lean's logic + the standard 3 | Proven |
| p40 | Random walk: first return to the start exactly at step 10: `7/256` | [`CheapLane.p40_first_return_10`](LeanProofs/Cheap.lean#L45) | Lean's logic + the standard 3 | Proven |
| p41 | Shuffle: no card back in its place among 10 cards: `16481/44800` | [`p41_shuffle_derangement_ten`](LeanProofs/Bank.lean#L73) | Lean's logic + the standard 3 | Proven |
| p42 | Shuffle: expected number of cycles in a shuffled pack of 20: `55835135/15519504` | [`CheapLane.p42_shuffle_expected_cycles`](LeanProofs/Cheap.lean#L458) | Lean's logic + the standard 3 | Proven |
| p43 | Shuffle: some originally neighbouring pair stays together in order: `2160343/3628800` | [`CheapLane.p43_shuffle_kept_neighbours`](LeanProofs/Cheap.lean#L806) | Lean's logic + the standard 3 | Proven |
| p44 | Cards: a 13-card hand with no spades but every other suit present: `8091223647/635013559600` | [`CheapLane.p44_bridge_hand_no_spades`](LeanProofs/Cheap.lean#L303) | Lean's logic + the standard 3 | Proven |
| p45 | Cards: all four aces appear before any king in a shuffled deck: `1/70` | [`CheapLane.p45_aces_before_kings`](LeanProofs/Cheap.lean#L27) | Lean's logic + the standard 3 | Proven |
| p48 | At least 3 successes in 12 trials, each a success with chance 1/3: `435185/531441` | [`TowerBatch.p48_third_success_by_twelve`](LeanProofs/Tower.lean#L992) | Lean's logic + the standard 3 | Proven |
| p49 | Polya urn: exactly three reds in five draws: `4/21` | [`CheapLane.p49_polya_three_reds`](LeanProofs/Cheap.lean#L110) | Lean's logic + the standard 3 | Proven |
| p52 | Random walk: never below the start and back at it after 12 steps: `33/1024` | [`p52_random_walk_never_negative`](LeanProofs/Walks.lean#L272) | Lean's logic + the standard 3 | Proven |
| p53 | Birthdays: expected number of same-birthday pairs among 28 people: `378/365 pairs` | [`CheapLane.p53_birthday_expected_pairs`](LeanProofs/Cheap.lean#L937) | Lean's logic + the standard 3 | Proven |
| p56 | Trap: expected value of a wide lognormal payout: `exp(2)` | [`WaitingLane.p56_lognormal_mean`](LeanProofs/Lognormal.lean#L15) | Lean's logic + the standard 3 | Proven |
| p63 | Trap: two numbers up to 1,000 share no common factor: `608383/1000000` | [`CheapLane.p63_trap_coprime_pair_finite`](LeanProofs/Cheap.lean#L197) | Lean's logic + the standard 3 | Proven |
| p65 | A 13-card hand from a shuffled deck holds all four aces and all four kings: `11/6431950` | [`TowerBatch.p65_trap_bridge_aces_kings`](LeanProofs/Tower.lean#L1003) | Lean's logic + the standard 3 | Proven |
| p65 | Trap: chance of disease after a positive 99%-sensitive test: `11/122` | [`TowerBatch.p65_trap_medical_test_positive`](LeanProofs/Tower.lean#L1051) | Lean's logic + the standard 3 | Proven |
| p68 | Trap: all five backup units fail, with a rare common shock: `10000000999/10000000000000` | [`TowerBatch.p68_trap_common_shock_failure`](LeanProofs/Tower.lean#L1059) | Lean's logic + the standard 3 | Proven |
| p69 | Twenty fair dice total 30 or less: `9944165/1218719480020992` | [`TowerBatch.p69_trap_twenty_dice_low_tail`](LeanProofs/Tower.lean#L1077) | Lean's logic + the standard 3 | Proven |
| p69 | Trap: days 100 and 101 are both rainfall records: `1/10100` | [`TowerBatch.p69_trap_two_records_in_row`](LeanProofs/Tower.lean#L1089) | Lean's logic + the standard 3 | Proven |
| p83 | Floating block: submerged depth of a wooden block: `3/10 m` | [`PhysicsLane.p83_floating_block_depth`](LeanProofs/Physics.lean#L29) | Lean's logic + the standard 3 | Proven |
| p88 | Elastic collision: speed of the 2 kg cart after a head-on hit: `1 m/s` | [`PhysicsLane.p88_elastic_two_kg_cart`](LeanProofs/Physics.lean#L16) | Lean's logic + the standard 3 | Proven |
| p91 | Integral: area under exp(x) from 0 to 1: `e-1` | [`CalculusLane.p91_exp_area`](LeanProofs/Calculus.lean#L23) | Lean's logic + the standard 3 | Proven |
| p92 | Integral: area under one arch of the sine curve: `2` | [`CalculusLane.p92_sine_arch`](LeanProofs/Calculus.lean#L19) | Lean's logic + the standard 3 | Proven |
| p93 | Series: the sum of 1/k^2 over all positive integers: `pi^2/6` | [`SeriesLane.p93_basel`](LeanProofs/Basel.lean#L15) | Lean's logic + the standard 3 | Proven |
| p94 | Series: the sum of k/2^k over all positive integers: `2` | [`SeriesLane.p94_k_over_two_pow`](LeanProofs/Series.lean#L34) | Lean's logic + the standard 3 | Proven |
| p95 | Root finding: the positive root of x^2 = 2: `sqrt(2)` | [`RootsLane.p95_positive_root_of_two`](LeanProofs/Roots.lean#L15) | Lean's logic + the standard 3 | Proven |
| p97 | ODE: logistic growth from 10 toward a cap of 100 after 2 days: `50` | [`CalculusLane.p97_logistic`](LeanProofs/Logistic.lean#L17) | Lean's logic + the standard 3 | Proven |
| p98 | ODE: value of the oscillator y'' + 4y = 0 at t = pi/6: `1/2` | [`CalculusLane.p98_oscillator`](LeanProofs/Oscillator.lean#L17) | Lean's logic + the standard 3 | Proven |
| p99 | Series: the sum of 1/(k(k+1)) over all positive integers: `1` | [`SeriesLane.p99_telescoping`](LeanProofs/Series.lean#L26) | Lean's logic + the standard 3 | Proven |
| p100 | Integral: area under log(x)/x from 1 to e: `1/2` | [`CalculusLane.p100_log_over_x`](LeanProofs/CalculusLog.lean#L21) | Lean's logic + the standard 3 | Proven |

<details>
<summary>The 55 problems with no Lean proof yet (label: Reasoned, the exact answer is derived by hand)</summary>

| Problem | Claim | Exact answer | Label |
|---|---|---|---|
| p03 | Falling object: time to fall 100 m | `sqrt(200/9.80665) seconds` | Reasoned |
| p08 | Buffon's needle: pi from crossing probability 2/pi | `pi` | Reasoned |
| p11 | Falling object plus measurement noise: estimate within 1% | `1559861/1599960` | Reasoned |
| p14 | Gambler's ruin: reach 20 before 0 from 10 | `79792266297612001/198834690125225002` | Reasoned |
| p15 | Coupon collector: expected rolls to see all six faces | `147/10 rolls` | Reasoned |
| p16 | Compound interest: expected balance after 10 years | `10000*(241/240)^120 dollars` | Reasoned |
| p18 | Queue at one cashier: expected wait before service | `16 minutes` | Reasoned |
| p19 | Half-life decay: grams left after 12 years | `80*2^(-12/5) grams` | Reasoned |
| p20 | Loaded die: expected gross payout | `183/20 dollars` | Reasoned |
| p23 | Trap: at least one head in 100 flips at p=0.01 | `1-(99/100)^100` | Reasoned |
| p24 | Trap: stable early average, rare $10,000 regime | `10999/1000 dollars` | Reasoned |
| p25 | Trap: 100 dice sum to at least 400 | `397005243855922678844356646275759075181938765156403148806158361930231905795/217772874500023635365563422386019273512381236824318290514357322123165713825792` | Reasoned |
| p26 | Projectile: range at 20 m/s and 30 degrees | `400*sin(60 deg)/9.80665 m` | Reasoned |
| p27 | Pendulum: period of a 1 m pendulum, small swing | `2*pi*sqrt(1/9.80665) s` | Reasoned |
| p28 | Orbit: period of a circular orbit 7,000 km from Earth's centre | `2*pi*sqrt(7000000^3/3.986004418e14) s` | Reasoned |
| p29 | Cooling: coffee temperature after 10 minutes | `20+70/e deg C` | Reasoned |
| p33 | Birthday triple: some day shared by at least three of 20 people | `318216859291500848355491224812734106060376537/38605964915937015670485458180605550689697265625` | Reasoned |
| p34 | Birthday near-match: two of 12 birthdays equal or one day apart | `52320594080314323068895673/122549486550140511084765625` | Reasoned |
| p35 | Birthday cross-match: a day shared between two groups of 15 and 20 | `147141185471117953786100199811792158919834035766785934516561730075538112528019110234401/262414233172146075072926452987537249139191971290746359275449091685004532337188720703125` | Reasoned |
| p46 | Waiting: expected flips to see heads-tails-heads | `10 flips` | Reasoned |
| p47 | Waiting: expected rolls to roll two sixes in a row | `42 rolls` | Reasoned |
| p48 | Random chord: longer than the inscribed equilateral triangle side | `1/3` | Reasoned |
| p50 | Polya urn with double additions: expected reds in ten draws | `6 reds` | Reasoned |
| p51 | Markov machine: expected worn days in the next eight days | `149797/65536 days` | Reasoned |
| p54 | Cards: expected cards to reveal to see all four suits | `4829/630 cards` | Reasoned |
| p55 | Waiting: the first event is type A and comes within half an hour | `(2/5)*(1-exp(-5/2))` | Reasoned |
| p57 | Trap: expected capped Pareto payout with tail index 3/2 | `3-2/sqrt(1000000) dollars` | Reasoned |
| p58 | Trap: at least three events in a half-rate Poisson hour | `1-exp(-1/2)*(1+1/2+1/8)` | Reasoned |
| p59 | Trap: a 100-step walk spends over 90% of its steps above zero | `53590814556005219805049997187/316912650057057350374175801344` | Reasoned |
| p60 | Trap: expected largest of 1,000 geometric waiting times | `sum_{k>=0} (1-(1-(99/100)^k)^1000)` | Reasoned |
| p61 | Trap: a Cauchy draw lands more than 100 from zero | `1-(2/pi)*arctan(100)` | Reasoned |
| p62 | Trap: expected wait for a bus alternating 1- and 19-minute gaps | `181/20 minutes` | Reasoned |
| p64 | Trap: expected people to arrive before the first shared birthday | `sum_{t=0}^{365} (365)_t/365^t people` | Reasoned |
| p66 | Trap: expected wait when one machine in a hundred is slow | `599/50 trials` | Reasoned |
| p67 | Trap: expected reciprocal of a uniform draw from 0.001 to 1 | `log(1000)/(999/1000)` | Reasoned |
| p70 | Trap: a payout equal to the square of a slow geometric wait | `4950 dollars` | Reasoned |
| p71 | Doppler: frequency heard from an approaching sound source | `500*340/(340-30) Hz` | Reasoned |
| p72 | Spring: fastest speed of a mass released 3 cm from balance | `0.03*sqrt(200/0.5) m/s` | Reasoned |
| p73 | Damped spring: position after 2 seconds | `exp(-1)*(cos(sqrt(99))+sin(sqrt(99))/sqrt(99)) m` | Reasoned |
| p74 | Linear drag: fall speed after 3 seconds | `(2*9.80665/0.5)*(1-exp(-3/4)) m/s` | Reasoned |
| p75 | Quadratic drag: fall speed after 2 seconds | `20*tanh(9.80665*2/20) m/s` | Reasoned |
| p76 | Charged particle: circle radius of a proton in a magnetic field | `(1.67e-27*2.0e6)/(1.602e-19*0.25) m` | Reasoned |
| p77 | Charged particle: electron deflection between charged plates | `(1/2)*(1.758820088e11*1000)*(0.10/1.0e7)^2 m` | Reasoned |
| p78 | Rocket: speed gain burning from 10,000 kg down to 4,000 kg | `3000*log(10000/4000) m/s` | Reasoned |
| p79 | Rocket: escape speed from Earth's surface | `sqrt(2*3.986004418e14/6371000) m/s` | Reasoned |
| p80 | Heat equation: temperature 1 m from a heat spike after 25 seconds | `10/sqrt(pi)*exp(-1) K` | Reasoned |
| p81 | Heat equation: warmth 2 m into cold ground after 100 seconds | `100*erfc(1) deg C` | Reasoned |
| p82 | RC circuit: capacitor voltage after 2 seconds of charging | `12*(1-exp(-2)) V` | Reasoned |
| p84 | LC circuit: resonant frequency of a 10 mH coil and 1 microfarad capacitor | `1/(2*pi*sqrt(0.01*1e-6)) Hz` | Reasoned |
| p85 | RLC circuit: series impedance at 1000 radians per second | `sqrt(30^2+(1000*0.2-1/(1000*6.25e-6))^2) ohm` | Reasoned |
| p86 | Atwood machine: acceleration of 5 kg against 3 kg | `(5-3)*9.80665/(5+3) m/s^2` | Reasoned |
| p87 | Incline: acceleration down a 30-degree slope with friction 0.2 | `9.80665*(sin(30 deg)-0.2*cos(30 deg)) m/s^2` | Reasoned |
| p89 | Gas: work in a slow isothermal expansion from 0.03 to 0.09 cubic metres | `6000*log(3) J` | Reasoned |
| p90 | Dam: total water force on a 20 m wide, 5 m deep wall | `1000*9.80665*20*5^2/2 N` | Reasoned |
| p96 | Root finding: the positive root of x^2 - x - 1 = 0 | `(1+sqrt(5))/2` | Reasoned |

</details>

## Expert Vouch Log

0 outside expert re-runs logged yet. See below to attack or verify this build.

| Date | Who | What they ran | Result | Link |
|---|---|---|---|---|

**How to attack it:** find a row in the table above where the plain-English claim and the formal statement disagree
(a definition that does not mean what its name says, a statement that is weaker than the claim, a wrong number), or
make `./check.sh` pass on something false, or fail on a clean checkout. Open an issue with what you found; a confirmed
break is logged here with credit.

**How to vouch:** run `./check.sh` on your own machine and send the last lines of `AUDIT.log` (the `RESULT` and
wall-clock lines) with the commit hash.

## Files

- `LeanProofs/Bank.lean`, `Walks.lean`, `Cheap.lean`, `Tower.lean`: the proofs. `LeanProofs/Root.lean`: Daniel's Root
  Theorem (`DANIELS-ROOT-THEOREM.md`), not an answer-bank problem; its headline `DanielRootTheorem` is restated in
  `VerifyAll.lean` too (Proven: axioms `propext`, `Quot.sound` only; replayed by `leanchecker`).
- `VerifyAll.lean`: the headline statements restated, plus `#print axioms`.
- `check.sh`, `scripts/audit_source.sh`: the one-command check. `AUDIT.log`: its last full output.
- `flagship_playground.lean`, `FLAGSHIP_URL.txt`: the flagship proof as one file, and its browser link.
- `OUTREACH.md`: drafts for asking outside Lean users to check or break this.
- `SETUP.sh`: how this project was first made (2026-10-14).

## License

Code: Apache License 2.0 (`LICENSE`). Documentation: CC BY 4.0 (`LICENSE-DOCS.md`). See `NOTICE`.
Credit: Daniel Steadham, Humanities Helping Hands™.
