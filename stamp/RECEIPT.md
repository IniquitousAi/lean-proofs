# Receipt: Daniel's HHH stamp rule

Checked 2026-10-28 01:4x CT on this PC by `lean stamp/StampRule.lean` (Lean 4.35.0, commit eb6cafb7290e), plain Lean with no
libraries, under 1 second. File fingerprint: sha256 `cf70a80b1184...` of `stamp/StampRule.lean`.

| Theorem | What it says | Rests on |
| --- | --- | --- |
| `stamp_means_proven` | anything carrying the stamp passed all five checks | propext |
| `no_stamp_without_pass` | a claim the checker does not pass can never carry the stamp | nothing |
| `planted_is_refused` | the planted claim (a `sorry` left in) gets no stamp | nothing |
| `honest_is_stamped` | a claim that passes everything does get one | nothing |

The forgery test: adding `def forged : Stamp := ⟨planted, by decide⟩` makes Lean stop with "decide proved that the proposition
`passes planted = true` is false" (exit 1). Both checks run in `scripts/test_stamp_rule.py`.

What this proves and what it does not: it proves the rule (a stamp can only exist with a pass). Whether each of the five checks
is answered truthfully for a real claim is the stamp tool's job (vibe-lab `tools/hhh_stamp.py`), and RERUN re-checks that.

Check it yourself: `lean stamp/StampRule.lean`
