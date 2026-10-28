import Mathlib

/-!
# The calculus lane, part 2 (ORD-1028-BQ)

p100 needs more than a stock rule: the area comes from an antiderivative found by hand, (log x)^2 / 2, whose slope is
log(x)/x everywhere on the interval, and the fundamental theorem of calculus (proven in Mathlib) turns that into the area.
-/

open Real

namespace CalculusLane

/-- Every point between 1 and e is above 0, so log and division by x behave there. -/
lemma pos_of_mem_one_e {x : ℝ} (hx : x ∈ Set.uIcc 1 (exp 1)) : 0 < x := by
  rcases Set.mem_uIcc.1 hx with h | h
  · linarith [h.1]
  · linarith [h.1, exp_pos 1]

/-- p100: the area under log(x)/x from 1 to e is exactly 1/2. -/
theorem p100_log_over_x : ∫ x in (1:ℝ)..exp 1, log x / x = 1 / 2 := by
  have hd : ∀ x ∈ Set.uIcc (1:ℝ) (exp 1), HasDerivAt (fun x => log x ^ 2 / 2) (log x / x) x := by
    intro x hx
    have h0 := pos_of_mem_one_e hx
    convert ((hasDerivAt_log h0.ne').pow 2).div_const 2 using 1
    field_simp
    norm_num
    try ring
  have hint : IntervalIntegrable (fun x => log x / x) MeasureTheory.volume 1 (exp 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_log.mono (fun x hx => (pos_of_mem_one_e hx).ne')
    · exact continuousOn_id
    · intro x hx; exact (pos_of_mem_one_e hx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  norm_num [log_exp]

end CalculusLane
