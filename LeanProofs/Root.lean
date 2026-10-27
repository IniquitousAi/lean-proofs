import Mathlib

/-!
# Daniel's Root Theorem

Credit: Daniel Steadham, 2026-10-27. His words: "I'm solving for diminishing returns from the lowest root possible."

A mistake made at the root (layer 0) is copied into every one of the `n` layers built on top of it. Fixing it at the root
costs `c`, once. Fixing it downstream instead costs `c` in each of the `n` layers, `n * c` in all.

* `DanielRootTheorem.root_never_costs_more`: once the mistake has reached at least one layer (`1 ≤ n`), the root fix never
  costs more: `c ≤ n * c`.
* `DanielRootTheorem.root_costs_strictly_less`: once it has spread to two or more layers (`2 ≤ n`) and a fix costs anything at
  all (`0 < c`), the root fix costs strictly less: `c < n * c`.

The idea is known in engineering; this framing, statement and proof are Daniel's.
-/

namespace DanielRootTheorem

/-- Fixing the root once never costs more than fixing its copies in every layer above it. -/
theorem root_never_costs_more (c n : ℕ) (spread : 1 ≤ n) : c ≤ n * c :=
  Nat.le_mul_of_pos_left c spread

/-- Once the mistake has spread to two or more layers, fixing the root costs strictly less (any fix that costs something). -/
theorem root_costs_strictly_less (c n : ℕ) (spread : 2 ≤ n) (costs : 0 < c) : c < n * c := by
  calc c = 1 * c := (one_mul c).symm
    _ < n * c := Nat.mul_lt_mul_of_pos_right (by omega) costs

end DanielRootTheorem

/-- Daniel's Root Theorem, both parts together. -/
theorem DanielRootTheorem (c n : ℕ) :
    (1 ≤ n → c ≤ n * c) ∧ (2 ≤ n → 0 < c → c < n * c) :=
  ⟨DanielRootTheorem.root_never_costs_more c n, DanielRootTheorem.root_costs_strictly_less c n⟩
