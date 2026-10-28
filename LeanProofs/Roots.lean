import Mathlib

/-!
# The roots lane (ORD-1028-BQ)

Bank problems that ask for a root. Each proof shows both halves: the answer works, and it is the only one that does.
-/

open Real

namespace RootsLane

/-- p95: the positive root of x^2 = 2 is exactly the square root of 2: it is positive, it squares to 2, and every
positive x with x^2 = 2 is that number. -/
theorem p95_positive_root_of_two :
    (0 < √2 ∧ √2 ^ 2 = 2) ∧ ∀ x : ℝ, 0 < x → x ^ 2 = 2 → x = √2 := by
  refine ⟨⟨by positivity, sq_sqrt (by norm_num)⟩, fun x hx h => ?_⟩
  rw [← h, sqrt_sq hx.le]

end RootsLane
