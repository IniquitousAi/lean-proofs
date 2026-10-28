import Mathlib

/-!
# p93, the Basel problem (ORD-1028-BQ)

The sum of 1/k^2 over all positive integers is pi^2/6. Mathlib already proves it (`hasSum_zeta_two`, sums from 0, where
Lean reads 1/0 as 0); this restates it from k = 1, the way the bank asks, so no 1/0 convention is needed to read it.
-/

open Real

namespace SeriesLane

/-- p93: the sum of 1/k^2 over all positive integers k is exactly pi^2/6. Term k here is 1/(k+1)^2. -/
theorem p93_basel : HasSum (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

end SeriesLane
