import Mathlib

/-!
# p97, logistic growth (ORD-1028-BQ)

The claim is about every population that obeys P' = r P (1 - P/100) with r = log 3 and P(0) = 10, not only the curve we
can write down, f(t) = 100 / (1 + 9 e^(-rt)). The proof: the gap g = P - f obeys g' = c g with c = r (1 - (P + f)/100),
a continuous rate. Let A be the area under c from 0. Then g e^(-A) has slope 0 and starts at 0, so it is 0 everywhere,
and since e^(-A) is never 0 the gap is 0: every solution is f. At t = 2, e^(-2 log 3) = 1/9, so P(2) = 100 / 2 = 50.
-/

open Real

namespace CalculusLane

/-- p97: any P with slope P' obeying P' = log 3 * P * (1 - P / 100) and P(0) = 10 has P(2) = 50 exactly. -/
theorem p97_logistic (P P' : ℝ → ℝ) (hP : ∀ t, HasDerivAt P (P' t) t)
    (ode : ∀ t, P' t = log 3 * P t * (1 - P t / 100)) (h0 : P 0 = 10) :
    P 2 = 50 := by
  set r := log 3 with hr
  -- the known curve f and its slope
  have hDpos : ∀ t, 0 < 1 + 9 * exp (-(r * t)) := fun t => by positivity
  have hf : ∀ t, HasDerivAt (fun t => 100 / (1 + 9 * exp (-(r * t))))
      (r * (100 / (1 + 9 * exp (-(r * t)))) * (1 - 100 / (1 + 9 * exp (-(r * t))) / 100)) t := by
    intro t
    have he : HasDerivAt (fun t => exp (-(r * t))) (exp (-(r * t)) * (-(r * 1))) t :=
      (((hasDerivAt_id t).const_mul r).neg).exp
    have hD : HasDerivAt (fun t => 1 + 9 * exp (-(r * t))) (9 * (exp (-(r * t)) * (-(r * 1)))) t :=
      (he.const_mul 9).const_add 1
    convert (hasDerivAt_const t (100 : ℝ)).div hD (hDpos t).ne' using 1
    have := (hDpos t).ne'
    field_simp
    ring
  set f := fun t => 100 / (1 + 9 * exp (-(r * t))) with hfdef
  -- the rate c is continuous, so its area A has slope c
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  set c := fun s => r * (1 - (P s + f s) / 100) with hcdef
  have hcc : Continuous c := by
    simp only [hcdef]; fun_prop
  have hA : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, c s) (c t) t :=
    fun t => (hcc.integral_hasStrictDerivAt 0 t).hasDerivAt
  -- g e^(-A) has slope 0
  have hw : ∀ t, HasDerivAt (fun t => (P t - f t) * exp (-(∫ s in (0 : ℝ)..t, c s))) 0 t := by
    intro t
    convert ((hP t).sub (hf t)).mul ((hA t).neg.exp) using 1
    rw [ode t]
    simp only [Pi.sub_apply, Pi.neg_apply, hcdef, hfdef]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hw t).differentiableAt) (fun t => (hw t).deriv) 2 0
  have hf0 : f 0 = 10 := by simp only [hfdef]; norm_num
  simp only [intervalIntegral.integral_same, neg_zero, exp_zero, mul_one, h0, hf0, sub_self] at hconst
  -- e^(-A) is never 0, so the gap is 0 at 2
  have gap : P 2 = f 2 := by
    have := (mul_eq_zero.1 hconst).resolve_right (exp_ne_zero _)
    linarith
  have h9 : exp (r * 2) = 9 := by
    rw [show r * 2 = log 3 + log 3 by rw [hr]; ring, exp_add, exp_log (by norm_num)]
    norm_num
  rw [gap]
  simp only [hfdef]
  rw [exp_neg, h9]
  norm_num

end CalculusLane
