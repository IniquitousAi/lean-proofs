import PvNP.SubbotovskayaRandom

/-! Round 11 (1): Subbotovskaya under R_p-style restrictions. The number of free variables
k is Binomial(m, p); given k, the restriction is produced by the uniform sequential process
(which yields a uniform k-star restriction). -/

namespace Subb
open Finset

variable {n : ℕ}

/-- Binomial weight. -/
def bw (m k : ℕ) (p : ℝ) : ℝ := (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)

theorem bw_nonneg (m k : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bw m k p := by
  unfold bw; have : 0 ≤ 1 - p := by linarith
  positivity

theorem bw_sum (m : ℕ) (p : ℝ) : ∑ k ∈ range (m + 1), bw m k p = 1 := by
  have := add_pow p (1 - p) m
  rw [show p + (1 - p) = 1 by ring, one_pow] at this
  rw [this]; exact sum_congr rfl fun k _ => by unfold bw; ring

theorem bw_shift (M : ℕ) (p : ℝ) (h : ℕ → ℝ) :
    ∑ k ∈ range (M + 2), bw (M + 1) k p * ((k : ℝ) * h k)
      = (M + 1) * p * ∑ k ∈ range (M + 1), bw M k p * h (k + 1) := by
  rw [sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hc : ((M + 1 : ℕ) : ℝ) * (M.choose k : ℝ) = ((M + 1).choose (k + 1) : ℝ) * (k + 1 : ℕ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq M k
  have hk' : M + 1 - (k + 1) = M - k := by omega
  unfold bw; rw [hk']; push_cast at hc ⊢
  linear_combination (-(p ^ (k + 1) * (1 - p) ^ (M - k) * h (k + 1))) * hc

theorem bw_mom1 (m : ℕ) (p : ℝ) : ∑ k ∈ range (m + 1), bw m k p * k = m * p := by
  rcases m with _ | M
  · simp [bw]
  · have := bw_shift M p (fun _ => 1)
    simp only [mul_one] at this
    rw [this, bw_sum]; push_cast; ring

theorem bw_mom2 (m : ℕ) (p : ℝ) :
    ∑ k ∈ range (m + 1), bw m k p * (k : ℝ) ^ 2 = m * p * ((m - 1) * p + 1) := by
  rcases m with _ | M
  · simp [bw]
  · have := bw_shift M p (fun k => (k : ℝ))
    simp only [← sq] at this
    have e : ∑ k ∈ range (M + 1), bw M k p * ((k + 1 : ℕ) : ℝ)
        = ∑ k ∈ range (M + 1), bw M k p * k + ∑ k ∈ range (M + 1), bw M k p := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun k _ => by push_cast; ring
    rw [this, e, bw_mom1, bw_sum]; push_cast; ring

/-- Expected complexity under the R_p-style restriction on W (|W| = m): k ~ Bin(m, p) free
variables, the other m - k fixed by the uniform sequential process. -/
noncomputable def Ep (p : ℝ) (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ k ∈ range (W.card + 1), bw W.card k p * Eres (W.card - k) W f

theorem rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  rcases hx.lt_or_eq with h | h
  · rw [Real.rpow_add h, Real.rpow_one]
  · subst h; rw [zero_mul]; exact Real.zero_rpow (show (1 + 1 / 2 : ℝ) ≠ 0 by norm_num)

/-- SUBBOTOVSKAYA, R_p FORM. For 0 ≤ p ≤ 1, |W| = m ≥ 1, f representable on W:
  E_p[L(f_ρ)] ≤ p · √(p + (1-p)/m) · L_W(f) + 1. -/
theorem subbotovskaya_Rp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset (Fin n)) (f)
    (hm : 1 ≤ W.card) (hf : ∃ r, Rep W f r) :
    Ep p W f ≤ p * Real.sqrt (p + (1 - p) / W.card) * LW W f + 1 := by
  set m := W.card
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set L := (LW W f : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  set X : ℕ → ℝ := fun k => (k : ℝ) / m
  have hX : ∀ k, 0 ≤ X k := fun k => by positivity
  -- step 1: termwise bound
  have h1 : Ep p W f ≤ ∑ k ∈ range (m + 1), bw m k p * (X k ^ (3 / 2 : ℝ) * L + 1) := by
    apply sum_le_sum; intro k hk
    have hk : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have := subbotovskaya_random (m - k) m W f rfl hm (Nat.sub_le _ _) hf
    rw [Nat.sub_sub_self hk] at this
    exact mul_le_mul_of_nonneg_left this (bw_nonneg _ _ hp0 hp1)
  have h2 : ∑ k ∈ range (m + 1), bw m k p * (X k ^ (3 / 2 : ℝ) * L + 1)
      = (∑ k ∈ range (m + 1), bw m k p * X k ^ (3 / 2 : ℝ)) * L + 1 := by
    rw [show ∑ k ∈ range (m + 1), bw m k p * (X k ^ (3 / 2 : ℝ) * L + 1)
        = ∑ k ∈ range (m + 1), bw m k p * X k ^ (3 / 2 : ℝ) * L + ∑ k ∈ range (m + 1), bw m k p by
          rw [← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring, bw_sum, sum_mul]
  -- step 2: Cauchy-Schwarz
  set S := ∑ k ∈ range (m + 1), bw m k p * X k ^ (3 / 2 : ℝ)
  have hCS : S ^ 2 ≤ (∑ k ∈ range (m + 1), bw m k p * X k ^ 2) *
      ∑ k ∈ range (m + 1), bw m k p * X k := by
    have := sum_mul_sq_le_sq_mul_sq (range (m + 1))
      (fun k => Real.sqrt (bw m k p) * X k) (fun k => Real.sqrt (bw m k p) * Real.sqrt (X k))
    convert this using 2
    · exact sum_congr rfl fun k _ => by
        rw [rpow_three_halves _ (hX k), show Real.sqrt (bw m k p) * X k * (Real.sqrt (bw m k p) *
          Real.sqrt (X k)) = (Real.sqrt (bw m k p) * Real.sqrt (bw m k p)) * (X k * Real.sqrt (X k))
          by ring, Real.mul_self_sqrt (bw_nonneg m k hp0 hp1)]
    · exact sum_congr rfl fun k _ => by
        rw [mul_pow, Real.sq_sqrt (bw_nonneg m k hp0 hp1)]
    · exact sum_congr rfl fun k _ => by
        rw [mul_pow, Real.sq_sqrt (bw_nonneg m k hp0 hp1), Real.sq_sqrt (hX k)]
  have hE1 : ∑ k ∈ range (m + 1), bw m k p * X k = p := by
    have := bw_mom1 m p
    simp only [X, div_eq_mul_inv, ← mul_assoc, ← sum_mul, this]; field_simp
  have hE2 : ∑ k ∈ range (m + 1), bw m k p * X k ^ 2 = p * (p + (1 - p) / m) := by
    have := bw_mom2 m p
    have e : ∑ k ∈ range (m + 1), bw m k p * X k ^ 2
        = (∑ k ∈ range (m + 1), bw m k p * (k : ℝ) ^ 2) / (m : ℝ) ^ 2 := by
      rw [sum_div]; exact sum_congr rfl fun k _ => by simp only [X, div_pow]; ring
    rw [e, this]; field_simp; ring
  rw [hE1, hE2] at hCS
  have hS0 : 0 ≤ S := sum_nonneg fun k _ =>
    mul_nonneg (bw_nonneg m k hp0 hp1) (Real.rpow_nonneg (hX k) _)
  have hq : 0 ≤ p + (1 - p) / m := by have : 0 ≤ 1 - p := by linarith
                                      positivity
  have hS : S ≤ p * Real.sqrt (p + (1 - p) / m) := by
    rw [show p * Real.sqrt (p + (1 - p) / m) = Real.sqrt (p ^ 2 * (p + (1 - p) / m)) by
      rw [Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp0]]
    calc S = Real.sqrt (S ^ 2) := (Real.sqrt_sq hS0).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_right hS hL]

/-- Corollary: if p·m ≥ 1 then E_p[L(f_ρ)] ≤ √2 · p^(3/2) · L + 1. -/
theorem subbotovskaya_Rp_simple (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset (Fin n)) (f)
    (hm : 1 ≤ W.card) (hpm : 1 ≤ p * W.card) (hf : ∃ r, Rep W f r) :
    Ep p W f ≤ Real.sqrt 2 * p ^ (3 / 2 : ℝ) * LW W f + 1 := by
  have h := subbotovskaya_Rp p hp0 hp1 W f hm hf
  have hmR : (0 : ℝ) < W.card := by exact_mod_cast hm
  have hq : p + (1 - p) / W.card ≤ 2 * p := by
    have : (1 - p) / W.card ≤ p := by rw [div_le_iff₀ hmR]; nlinarith
    linarith
  have hs : Real.sqrt (p + (1 - p) / W.card) ≤ Real.sqrt 2 * Real.sqrt p := by
    rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hq
  rw [rpow_three_halves p hp0] at *
  have hL : (0 : ℝ) ≤ LW W f := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hs hp0
  nlinarith [mul_le_mul_of_nonneg_right this hL]

end Subb
