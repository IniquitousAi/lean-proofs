import Mathlib

/-!
# p56, the wide lognormal payout (ORD-1028-BQ)

The payout is exp(2Z) for a standard normal Z. Its expected value is the average of exp(2x) over the bell curve, which
is the normal moment formula (proven in Mathlib: `mgf_fun_id_gaussianReal`) at t = 2: exp(0 * 2 + 1 * 2^2 / 2) = exp 2.
-/

open ProbabilityTheory MeasureTheory

namespace WaitingLane

/-- p56: the expected payout exp(2Z), Z a standard normal draw (mean 0, spread 1), is exactly e^2 dollars. -/
theorem p56_lognormal_mean : ∫ x, Real.exp (2 * x) ∂(gaussianReal 0 1) = Real.exp 2 := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) 2
  simp only [mgf] at h
  rw [h]
  norm_num

end WaitingLane
