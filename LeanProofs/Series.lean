import Mathlib

/-!
# The series lane (ORD-1028-BQ)

Bank problems whose answer is an infinite sum. Each is proven the long way round: the exact partial sum after n terms,
then the limit of those partial sums as n grows. Nothing is estimated or rounded.
-/

open Filter Topology

namespace SeriesLane

/-- The first n terms of 1/(k(k+1)), for k = 1, 2, ..., n, add up to exactly 1 - 1/(n+1) (each term is 1/k - 1/(k+1),
so all the middle pieces cancel). Indexed from 0 here: term k is 1/((k+1)(k+2)). -/
theorem p99_partial (n : ℕ) : ∑ k ∈ Finset.range n, (1:ℝ) / ((k + 1) * (k + 2)) = 1 - 1 / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- p99: the sum of 1/(k(k+1)) over all positive integers k is exactly 1. -/
theorem p99_telescoping : HasSum (fun k : ℕ => (1:ℝ) / ((k + 1) * (k + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  simp_rw [p99_partial]
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  rwa [sub_zero] at h

/-- p94: the sum of k/2^k over all positive integers k is exactly 2 (the k = 0 term is 0, so starting at 0 changes
nothing). Mathlib's sum of k r^k = r/(1-r)^2, at r = 1/2. -/
theorem p94_k_over_two_pow : HasSum (fun k : ℕ => (k:ℝ) / 2 ^ k) 2 := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)
  convert h using 1
  · funext k; rw [one_div, inv_pow, div_eq_mul_inv]
  · norm_num

end SeriesLane
