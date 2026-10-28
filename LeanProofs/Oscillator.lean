import Mathlib

/-!
# p98, the oscillator (ORD-1028-BQ)

The claim is about every function that obeys y'' + 4y = 0 with y(0) = 1 and y'(0) = 0, not only the one we can write
down. The proof: take the gap z = y - cos(2t) and its slope z' = y' + 2 sin(2t). The energy z'^2 + 4 z^2 has slope 0
everywhere, so it keeps its starting value, which is 0. A sum of squares that is 0 makes the gap 0, so every solution is
cos(2t), and at t = pi/6 that is cos(pi/3) = 1/2.
-/

open Real

namespace CalculusLane

/-- p98: any y with slope y' and second slope y'' obeying y'' + 4y = 0, y(0) = 1, y'(0) = 0 has y(pi/6) = 1/2 exactly. -/
theorem p98_oscillator (y y' y'' : ℝ → ℝ)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hy' : ∀ t, HasDerivAt y' (y'' t) t)
    (ode : ∀ t, y'' t + 4 * y t = 0) (h0 : y 0 = 1) (h0' : y' 0 = 0) :
    y (π / 6) = 1 / 2 := by
  -- the gap and its slope
  have hz : ∀ t, HasDerivAt (fun t => y t - cos (2 * t)) (y' t + 2 * sin (2 * t)) t := by
    intro t
    have hc : HasDerivAt (fun t => cos (2 * t)) (-sin (2 * t) * 2) t := by
      simpa using ((hasDerivAt_id t).const_mul 2).cos
    convert (hy t).sub hc using 1
    ring
  have hz' : ∀ t, HasDerivAt (fun t => y' t + 2 * sin (2 * t)) (-4 * (y t - cos (2 * t))) t := by
    intro t
    have hs : HasDerivAt (fun t => sin (2 * t)) (cos (2 * t) * 2) t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sin
    convert (hy' t).add (hs.const_mul 2) using 1
    linarith [ode t]
  -- the energy has slope 0 everywhere
  have hE : ∀ t, HasDerivAt (fun t => (y' t + 2 * sin (2 * t)) ^ 2 + 4 * (y t - cos (2 * t)) ^ 2) 0 t := by
    intro t
    convert ((hz' t).pow 2).add (((hz t).pow 2).const_mul 4) using 1
    simp
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hE t).differentiableAt) (fun t => (hE t).deriv) (π / 6) 0
  simp only [h0, h0', mul_zero, sin_zero, cos_zero] at hconst
  -- a sum of squares that is 0: the gap is 0 at pi/6
  have gap : y (π / 6) - cos (2 * (π / 6)) = 0 := by
    nlinarith [sq_nonneg (y' (π / 6) + 2 * sin (2 * (π / 6))), sq_nonneg (y (π / 6) - cos (2 * (π / 6)))]
  rw [show 2 * (π / 6) = π / 3 by ring, cos_pi_div_three] at gap
  linarith

end CalculusLane
