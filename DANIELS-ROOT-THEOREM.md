# Daniel's Root Theorem

**Credit:** Daniel Steadham, 2026-10-27.

> "I'm solving for diminishing returns from the lowest root possible." (Daniel)

## In plain words

Fixing a mistake at the root, once, always costs no more than fixing its copies in every layer built on top of it. Once the mistake has spread to two or more layers, fixing the root costs strictly less.

## What exactly is proven

- A mistake sits at the root (layer 0) and gets copied into `n` layers above it.
- One fix costs `c`, wherever it is made.
- Fix it at the root: you pay `c`, once.
- Fix it downstream: you pay `c` in each of the `n` layers, so `n × c` in total.

Two claims, both checked by Lean:

1. **Never more:** if the mistake reached at least one layer (`n ≥ 1`), then `c ≤ n × c`.
2. **Strictly less:** if it spread to two or more layers (`n ≥ 2`) and a fix costs anything at all (`c > 0`), then `c < n × c`.

The second claim needs "a fix costs anything at all". If fixing were free, both ways would cost the same, zero.

## What it does not say

It only covers the model above: one mistake, one fix price, copies in layers. It does not say how much a real fix costs, or that every real mistake spreads this way. That is a question about the real world, not about the math.

## The proof

`LeanProofs/Root.lean`, theorem `DanielRootTheorem` (with its two parts `DanielRootTheorem.root_never_costs_more` and `DanielRootTheorem.root_costs_strictly_less`).

- `lake build`: 9,054 jobs, no errors (lean-proofs 2255785).
- `#print axioms`: only `propext` and `Quot.sound`; the first part uses none. No `sorry`, `admit` or `native_decide`.
- A planted wrong version, "fixing downstream costs less than the root" (`n × c < c`), is refused by Lean (vibe-lab `tests/test_verify_proofs.py`).
- Seen live in the **VERIFY MY PROOFS** window (Desktop, APPROVE AND SAFETY), marked as yours.

## Honest note

The idea is known in engineering. This framing, statement and proof are Daniel's.
