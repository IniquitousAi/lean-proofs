import Mathlib

/-!
# The calculus lane (ORD-1028-BQ)

Bank problems whose answer is a definite integral. Mathlib's interval-integral rules (the fundamental theorem of
calculus, already proven there) give each exact value; nothing is estimated or rounded.
-/

open Real intervalIntegral

namespace CalculusLane

/-- p30: the area under y = x^2 from 0 to 3 is exactly 9. -/
theorem p30_area_under_square : ∫ x in (0:ℝ)..3, x ^ 2 = 9 := by
  rw [integral_pow]; norm_num

/-- p92: the area under one arch of the sine curve, from 0 to pi, is exactly 2. -/
theorem p92_sine_arch : ∫ x in (0:ℝ)..π, sin x = 2 := by
  rw [integral_sin]; simp; norm_num

/-- p91: the area under exp(x) from 0 to 1 is exactly e - 1. -/
theorem p91_exp_area : ∫ x in (0:ℝ)..1, exp x = exp 1 - 1 := by
  rw [integral_exp]; simp

end CalculusLane
