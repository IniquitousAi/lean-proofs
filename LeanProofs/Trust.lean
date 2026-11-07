import Mathlib

/-!
# The Daniel trust theorem

Credit: Daniel Steadham, 2026-11-07 (his pick: "prove the fairness in Lean"). The checker gives every source a trust score
earned only by its claims we checked: the Wilson score lower bound (Wilson 1927) for `t` true out of `c` checked, at the normal
quantile `z` (95%: `z = 1.959963984540054`). `wilson` below is written the way `vibe-lab/atoms/trust.py` computes it.

* `DanielTrust.same_record_same_score`: the score depends on the record and nothing else.
* `DanielTrust.true_check_never_lowers`: one more check that came out true never lowers the score.
* `DanielTrust.false_check_never_raises`: one more check that came out false never raises it.
* `DanielTrust.score_bounds`: the score is between 0 and 1 (so the clamp in `trust.py` never changes it), and below 1.

Assumptions, stated plainly: real numbers, not the computer's floating point (the Python tests check the floats on every
record up to 2,000 checks); any `z > 0`.

The proof: a candidate rate `p` passes the score test when `t - c p ≤ 0` or `(t - c p)^2 ≤ z^2 c p (1 - p)` (`accept`).
The score is exactly the smallest rate that passes (`le_iff_accept`). A true check only makes the test harder to pass for every
`p`, a false check only easier, so the smallest passing rate moves the right way.
-/

namespace DanielTrust

/-- The trust score of `trust.py` (the Wilson score lower bound), 0 with no record. -/
noncomputable def wilson (z : ℝ) (t c : ℕ) : ℝ :=
  if c = 0 then 0 else
    ((t / c : ℝ) + z ^ 2 / (2 * c) - z * Real.sqrt ((t / c : ℝ) * (1 - t / c) / c + z ^ 2 / (4 * (c : ℝ) ^ 2)))
      / (1 + z ^ 2 / c)

/-- The score test at level `z` does not reject the rate `p` for `t` true out of `c` checked. -/
def accept (z : ℝ) (t c : ℕ) (p : ℝ) : Prop :=
  (t : ℝ) - c * p ≤ 0 ∨ ((t : ℝ) - c * p) ^ 2 ≤ z ^ 2 * c * (p * (1 - p))

/-- The same record always gives the same score. -/
theorem same_record_same_score (z : ℝ) {t₁ c₁ t₂ c₂ : ℕ} (h₁ : t₁ = t₂) (h₂ : c₁ = c₂) :
    wilson z t₁ c₁ = wilson z t₂ c₂ := by
  subst h₁; subst h₂; rfl

section core

variable {z : ℝ} {t c : ℕ}

/-- The score as the lower root of a quadratic. -/
lemma wilson_root (hc : 0 < c) (htc : t ≤ c) :
    wilson z t c = (2 * t + z ^ 2 - z * Real.sqrt (z ^ 2 + 4 * t * (c - t) / c)) / (2 * (c + z ^ 2)) := by
  have hn : (0 : ℝ) < c := by exact_mod_cast hc
  have hT : (t : ℝ) ≤ c := by exact_mod_cast htc
  have harg : (0 : ℝ) ≤ z ^ 2 + 4 * t * (c - t) / c := by
    have : (0 : ℝ) ≤ 4 * t * (c - t) / c := by
      apply div_nonneg _ hn.le
      have : (0 : ℝ) ≤ c - t := by linarith
      positivity
    positivity
  have hS : Real.sqrt ((t / c : ℝ) * (1 - t / c) / c + z ^ 2 / (4 * (c : ℝ) ^ 2))
      = Real.sqrt (z ^ 2 + 4 * t * (c - t) / c) / (2 * c) := by
    rw [show (t / c : ℝ) * (1 - t / c) / c + z ^ 2 / (4 * (c : ℝ) ^ 2)
        = (z ^ 2 + 4 * t * (c - t) / c) / (2 * c) ^ 2 by field_simp; ring]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  unfold wilson
  rw [if_neg (by omega), hS]
  field_simp

/-- The score is exactly the smallest rate the test does not reject. -/
theorem le_iff_accept (hz : 0 < z) (hc : 0 < c) (htc : t ≤ c) (p : ℝ) :
    wilson z t c ≤ p ↔ accept z t c p := by
  have hn : (0 : ℝ) < c := by exact_mod_cast hc
  have hT0 : (0 : ℝ) ≤ t := by positivity
  have hT : (t : ℝ) ≤ c := by exact_mod_cast htc
  set n : ℝ := (c : ℝ) with hn_def
  set T : ℝ := (t : ℝ) with hT_def
  have harg : (0 : ℝ) ≤ z ^ 2 + 4 * T * (n - T) / n := by
    have : (0 : ℝ) ≤ 4 * T * (n - T) / n := by
      apply div_nonneg _ hn.le
      have : (0 : ℝ) ≤ n - T := by linarith
      positivity
    positivity
  set S := Real.sqrt (z ^ 2 + 4 * T * (n - T) / n) with hS_def
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = z ^ 2 + 4 * T * (n - T) / n := Real.sq_sqrt harg
  have hB : 0 < n + z ^ 2 := by positivity
  set L := (2 * T + z ^ 2 - z * S) / (2 * (n + z ^ 2)) with hL_def
  set U := (2 * T + z ^ 2 + z * S) / (2 * (n + z ^ 2)) with hU_def
  have hW : wilson z t c = L := wilson_root hc htc
  have hLU : L ≤ U := by
    rw [hL_def, hU_def]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg hz.le hS0]
  -- the test's quadratic factors through the two roots
  have hg : ∀ x : ℝ, (T - n * x) ^ 2 - z ^ 2 * n * (x * (1 - x)) = n * (n + z ^ 2) * ((x - L) * (x - U)) := by
    intro x
    have e : (x - L) * (x - U) = ((2 * (n + z ^ 2) * x - (2 * T + z ^ 2)) ^ 2 - z ^ 2 * S ^ 2) / (4 * (n + z ^ 2) ^ 2) := by
      rw [hL_def, hU_def]
      field_simp
      ring
    rw [e, hS2]
    field_simp
    ring
  -- the observed rate T / n lies between the roots
  have hph : L ≤ T / n ∧ T / n ≤ U := by
    have h := hg (T / n)
    have h1 : T - n * (T / n) = 0 := by field_simp; ring
    have hp0 : 0 ≤ T / n := div_nonneg hT0 hn.le
    have hp1 : T / n ≤ 1 := (div_le_one hn).mpr hT
    have hneg : (T - n * (T / n)) ^ 2 - z ^ 2 * n * (T / n * (1 - T / n)) ≤ 0 := by
      rw [h1]
      have : 0 ≤ z ^ 2 * n * (T / n * (1 - T / n)) := by
        have : 0 ≤ 1 - T / n := by linarith
        positivity
      linarith
    rw [h] at hneg
    have hprod : (T / n - L) * (T / n - U) ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      have : 0 < n * (n + z ^ 2) * ((T / n - L) * (T / n - U)) := by positivity
      linarith
    constructor
    · by_contra hlt; push_neg at hlt; nlinarith
    · by_contra hlt; push_neg at hlt; nlinarith
  rw [hW]
  unfold accept
  rw [← hn_def, ← hT_def]
  constructor
  · intro hp
    by_cases hN : T - n * p ≤ 0
    · exact Or.inl hN
    · right
      push_neg at hN
      have hpU : p ≤ U := by
        have : p < T / n := by rw [lt_div_iff₀ hn]; linarith
        linarith [hph.2]
      have hprod : (p - L) * (p - U) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have := hg p
      have : n * (n + z ^ 2) * ((p - L) * (p - U)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hprod
      linarith
  · rintro (hN | hq)
    · have : T / n ≤ p := by rw [div_le_iff₀ hn]; linarith
      linarith [hph.1]
    · by_contra hlt
      push_neg at hlt
      have hpos : 0 < (p - L) * (p - U) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have : 0 < n * (n + z ^ 2) * ((p - L) * (p - U)) := by positivity
      have := hg p
      linarith

/-- The score is between 0 and 1. -/
theorem score_bounds (hz : 0 < z) (htc : t ≤ c) : 0 ≤ wilson z t c ∧ wilson z t c ≤ 1 := by
  rcases Nat.eq_zero_or_pos c with h0 | hc
  · simp [wilson, h0]
  have hn : (0 : ℝ) < c := by exact_mod_cast hc
  have hT : (t : ℝ) ≤ c := by exact_mod_cast htc
  constructor
  · -- every negative rate is rejected, so the smallest accepted one is not negative
    by_contra hneg
    push_neg at hneg
    have hacc := (le_iff_accept hz hc htc (wilson z t c)).mp le_rfl
    set w := wilson z t c
    rcases hacc with h | h
    · have : (0 : ℝ) ≤ t := by positivity
      nlinarith
    · have h1 : 0 < (t : ℝ) - c * w := by
        have : (0 : ℝ) ≤ t := by positivity
        nlinarith
      have h2 : z ^ 2 * c * (w * (1 - w)) < 0 := by
        have : 0 < z ^ 2 * c := by positivity
        have : w * (1 - w) < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
        nlinarith
      nlinarith [sq_nonneg ((t : ℝ) - c * w)]
  · -- the rate 1 is accepted
    apply (le_iff_accept hz hc htc 1).mpr
    left
    linarith

/-- One more check that came out true never lowers the score. -/
theorem true_check_never_lowers (hz : 0 < z) (htc : t ≤ c) : wilson z t c ≤ wilson z (t + 1) (c + 1) := by
  have hb := score_bounds hz (Nat.succ_le_succ htc)
  rcases Nat.eq_zero_or_pos c with h0 | hc
  · rw [show wilson z t c = 0 by simp [wilson, h0]]
    exact hb.1
  set w := wilson z (t + 1) (c + 1)
  have hacc : accept z (t + 1) (c + 1) w :=
    (le_iff_accept hz (Nat.succ_pos c) (Nat.succ_le_succ htc) w).mp le_rfl
  apply (le_iff_accept hz hc htc w).mpr
  have hn : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hT : (t : ℝ) ≤ c := by exact_mod_cast htc
  have hw0 := hb.1
  have hw1 := hb.2
  unfold accept at hacc ⊢
  push_cast at hacc
  -- with N = t - c w, the new record's gap is N + (1 - w)
  rcases hacc with h | h
  · left; nlinarith
  · by_cases hN : (t : ℝ) - c * w ≤ 0
    · exact Or.inl hN
    right
    push_neg at hN
    set N := (t : ℝ) - c * w with hN_def
    have hNle : N ≤ c * (1 - w) := by rw [hN_def]; nlinarith
    have hstep : N ^ 2 * (c + 1) ≤ (N + (1 - w)) ^ 2 * c := by
      nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hw1), mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hw1)]
    have hgap : (t : ℝ) + 1 - (c + 1) * w = N + (1 - w) := by rw [hN_def]; ring
    rw [hgap] at h
    have hc0 : (0 : ℝ) < c := by linarith
    have key : N ^ 2 * (c + 1) ≤ z ^ 2 * c * (w * (1 - w)) * (c + 1) := by
      calc N ^ 2 * (c + 1) ≤ (N + (1 - w)) ^ 2 * c := hstep
        _ ≤ z ^ 2 * (c + 1) * (w * (1 - w)) * c := by nlinarith
        _ = z ^ 2 * c * (w * (1 - w)) * (c + 1) := by ring
    exact le_of_mul_le_mul_right key (by linarith)

/-- One more check that came out false never raises the score. -/
theorem false_check_never_raises (hz : 0 < z) (htc : t ≤ c) : wilson z t (c + 1) ≤ wilson z t c := by
  have hb := score_bounds hz htc
  set w := wilson z t c
  have hacc : accept z t c w := by
    rcases Nat.eq_zero_or_pos c with h0 | hc
    · left
      have : t = 0 := by omega
      simp [this, h0]
    · exact (le_iff_accept hz hc htc w).mp le_rfl
  apply (le_iff_accept hz (Nat.succ_pos c) (Nat.le_succ_of_le htc) w).mpr
  have hw0 := hb.1
  have hw1 := hb.2
  unfold accept at hacc ⊢
  push_cast
  rcases hacc with h | h
  · left; nlinarith
  · by_cases hM : (t : ℝ) - (c + 1) * w ≤ 0
    · exact Or.inl hM
    right
    push_neg at hM
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have hww : 0 ≤ w * (1 - w) := mul_nonneg hw0 (by linarith)
    have hsq : ((t : ℝ) - (c + 1) * w) ^ 2 ≤ ((t : ℝ) - c * w) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg z) hww]

end core

/-- The checker's own setting, 95%. -/
theorem fair_at_95 {t c : ℕ} (htc : t ≤ c) :
    wilson 1.959963984540054 t c ≤ wilson 1.959963984540054 (t + 1) (c + 1) ∧
    wilson 1.959963984540054 t (c + 1) ≤ wilson 1.959963984540054 t c :=
  ⟨true_check_never_lowers (by norm_num) htc, false_check_never_raises (by norm_num) htc⟩

end DanielTrust
