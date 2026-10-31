import Project.RazborovSmolenskyModqBooleanTransfer_v21

/-! HHH audit: the counting hypotheses of `ACP.MODq_notin_AC0p_quantitative`
cannot all hold when `δ ≥ 1` (δ is a natural number). So the theorem only ever
fires with δ = 0, where its conclusion `0 ≤ F.size` is trivial. -/

open Finset

namespace HHH

/-- V1 (pure counting): if N ≤ e, the ball sum up to e is at least (K+1)^N ≥ K^N,
so K^N > C * B with C ≥ 1 is impossible. -/
theorem ball_contradiction (N e B K C : ℕ) (he : N ≤ e) (hC : 1 ≤ C)
    (hB : (range (e + 1)).sum (fun t => N.choose t * K ^ t) ≤ B)
    (hs : K ^ N > C * B) : False := by
  have h1 : (K + 1) ^ N = (range (N + 1)).sum (fun t => N.choose t * K ^ t) := by
    rw [add_pow]; refine sum_congr rfl (fun t _ => by simp only [one_pow, mul_one, Nat.cast_id]; ring)
  have h2 : (range (N + 1)).sum (fun t => N.choose t * K ^ t)
      ≤ (range (e + 1)).sum (fun t => N.choose t * K ^ t) :=
    sum_le_sum_of_subset (range_subset_range.mpr (by omega))
  have h3 : K ^ N ≤ (K + 1) ^ N := Nat.pow_le_pow_left (by omega) N
  have h4 : B ≤ C * B := Nat.le_mul_of_pos_left B hC
  omega

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- V2: the exact hypotheses `herror`, `hballB`, `hstrict` of
`ACP.MODq_notin_AC0p_quantitative` force δ = 0. -/
theorem quantitative_hyps_force_delta_zero
    {q n δ e B D : ℕ} [Fact (Nat.Prime q)]
    (herror : q * (δ * 2 ^ (n + (q - 1))) ≤ e)
    (hballB :
      (Finset.range (e + 1)).sum
        (fun t : ℕ =>
          Nat.choose (2 ^ n) t *
            Fintype.card (ACP.ModqField (p := p) q) ^ t) ≤ B)
    (hstrict :
      Fintype.card (ACP.ModqField (p := p) q) ^ (2 ^ n) >
        Fintype.card (ACP.LowDegreeSupport n D → ACP.ModqField (p := p) q) * B) :
    δ = 0 := by
  by_contra hδ
  have hq : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  have hN : 2 ^ n ≤ e := by
    have : 2 ^ n ≤ 2 ^ (n + (q - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ (n + (q - 1)) ≤ δ * 2 ^ (n + (q - 1)) := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : δ * 2 ^ (n + (q - 1)) ≤ q * (δ * 2 ^ (n + (q - 1))) := Nat.le_mul_of_pos_left _ hq
    omega
  exact ball_contradiction _ _ _ _ _ hN Fintype.card_pos hballB hstrict

end HHH
