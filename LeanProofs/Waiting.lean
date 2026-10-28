import Mathlib

/-!
# The waiting lane (ORD-1028-BQ)

Bank problems that ask how long you wait on average. Each is the full expected value, written out as a sum over every
possible wait with its exact chance, proven equal to the bank's answer. Nothing is simulated or rounded.
-/

namespace WaitingLane

/-- p09: the expected number of rolls of a fair die until the first 6 is exactly 6. Roll k+1 is the first six with
chance (5/6)^k * (1/6), so the expected value is the sum of (k+1) times that chance over every k. -/
theorem p09_rolls_to_first_six :
    HasSum (fun k : ℕ => ((k:ℝ) + 1) * ((5/6) ^ k * (1/6))) 6 := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (r := (5/6:ℝ)) (by norm_num)
  have h2 := hasSum_geometric_of_lt_one (r := (5/6:ℝ)) (by norm_num) (by norm_num)
  have h := (h1.add h2).mul_right (1/6)
  convert h using 1
  · funext k; ring
  · norm_num

end WaitingLane
