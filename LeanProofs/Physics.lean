import Mathlib

/-!
# The physics lane (ORD-1028-BQ)

Bank problems whose physics is one stated law; what Lean proves is the algebra from that law to the answer. The law itself
(momentum and energy conserved; a floating body displaces its own weight of water) is the bank's assumption, written into
each statement so a reader sees exactly what is assumed and what is proven.
-/

namespace PhysicsLane

/-- p88: a 2 kg cart at +5 m/s meets a 1 kg cart at -1 m/s, elastically. If the after-speeds u (2 kg) and w (1 kg) keep
both momentum and kinetic energy, and the carts really collided (u is not still 5, the only other solution: passing through
untouched), then the 2 kg cart moves at exactly 1 m/s. -/
theorem p88_elastic_two_kg_cart (u w : ℝ)
    (momentum : 2 * u + 1 * w = 2 * 5 + 1 * (-1))
    (energy : 2 * u ^ 2 / 2 + 1 * w ^ 2 / 2 = 2 * 5 ^ 2 / 2 + 1 * (-1) ^ 2 / 2)
    (collided : u ≠ 5) : u = 1 := by
  have hw : w = 9 - 2 * u := by linarith
  subst hw
  have h : (u - 1) * (u - 5) = 0 := by nlinarith
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · exact absurd (by linarith) collided

/-- p83: a block of density 600 kg/m^3 and height 1/2 m floats in water of density 1000 kg/m^3. With top face area A > 0
and gravity g > 0, if its weight equals the weight of the water it displaces at depth d, then d is exactly 3/10 m. -/
theorem p83_floating_block_depth (A g d : ℝ) (hA : 0 < A) (hg : 0 < g)
    (floats : 600 * (A * (1/2)) * g = 1000 * (A * d) * g) : d = 3/10 := by
  have hAg : A * g ≠ 0 := by positivity
  have key : A * g * d = A * g * (3/10) := by linear_combination (-1/1000 : ℝ) * floats
  exact mul_left_cancel₀ hAg key

end PhysicsLane
