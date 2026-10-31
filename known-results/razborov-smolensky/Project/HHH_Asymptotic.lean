import Project.HHH_Repair

/-! HHH Round 6: unconditional explicit MOD_q lower bound for AC0[p] (even input
length 2m + (q-1)), via the plan in HHH_Repair.lean. -/

open Finset

namespace HHH

/-- Step 1a: binomial ratio away from the center. -/
theorem choose_ratio (m : ℕ) : ∀ k, k ≤ m →
    (2 * m).choose m * (m - k) ^ k ≤ (2 * m).choose (m + k) * (m + k) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hs := Nat.choose_succ_right_eq (2 * m) (m + k)
    have h1 : 2 * m - (m + k) = m - k := by omega
    rw [h1] at hs
    have e1 : m + (k + 1) = m + k + 1 := by omega
    rw [e1]
    calc (2 * m).choose m * (m - (k + 1)) ^ (k + 1)
        = (2 * m).choose m * (m - (k + 1)) ^ k * (m - (k + 1)) := by ring
      _ ≤ (2 * m).choose m * (m - k) ^ k * (m - k) := by
          gcongr <;> omega
      _ ≤ (2 * m).choose (m + k) * (m + k) ^ k * (m - k) := by gcongr
      _ = (2 * m).choose (m + k + 1) * (m + k + 1) * (m + k) ^ k := by
          rw [show (2 * m).choose (m + k) * (m + k) ^ k * (m - k)
              = (2 * m).choose (m + k) * (m - k) * (m + k) ^ k by ring, ← hs]
      _ ≤ (2 * m).choose (m + k + 1) * (m + k + 1) ^ (k + 1) := by
          rw [pow_succ]
          have : (m + k) ^ k ≤ (m + k + 1) ^ k := Nat.pow_le_pow_left (by omega) k
          calc (2 * m).choose (m + k + 1) * (m + k + 1) * (m + k) ^ k
              ≤ (2 * m).choose (m + k + 1) * (m + k + 1) * (m + k + 1) ^ k := by gcongr
            _ = _ := by ring

/-- Step 1b: Bernoulli-type estimate in ℕ. -/
theorem bern_aux (m k : ℕ) (hk : k ≤ m) : ∀ j,
    (m + k) ^ (j + 1) ≤ (m - k) ^ (j + 1) + 2 * k * (j + 1) * (m + k) ^ j := by
  intro j
  induction j with
  | zero => simp; omega
  | succ j ih =>
    have hmk : m + k = (m - k) + 2 * k := by omega
    have hle : (m - k) ^ (j + 1) ≤ (m + k) ^ (j + 1) := Nat.pow_le_pow_left (by omega) _
    calc (m + k) ^ (j + 1 + 1) = (m + k) ^ (j + 1) * (m + k) := pow_succ _ _
      _ ≤ ((m - k) ^ (j + 1) + 2 * k * (j + 1) * (m + k) ^ j) * (m + k) := by gcongr
      _ = (m - k) ^ (j + 1) * (m - k) + (m - k) ^ (j + 1) * (2 * k)
            + 2 * k * (j + 1) * ((m + k) ^ j * (m + k)) := by
          rw [hmk]; ring
      _ ≤ (m - k) ^ (j + 1) * (m - k) + (m + k) ^ (j + 1) * (2 * k)
            + 2 * k * (j + 1) * ((m + k) ^ j * (m + k)) := by gcongr
      _ = (m - k) ^ (j + 1 + 1) + 2 * k * (j + 1 + 1) * (m + k) ^ (j + 1) := by ring

theorem bern (m k : ℕ) (hk : 1 ≤ k) (h4 : 4 * k ^ 2 ≤ m + k) (hkm : k ≤ m) :
    (m + k) ^ k ≤ 2 * (m - k) ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hb := bern_aux m (j + 1) hkm j
  set X := (m + (j + 1)) ^ j
  have hX : (m + (j + 1)) ^ (j + 1) = X * (m + (j + 1)) := pow_succ _ _
  have h4X : 4 * (j + 1) ^ 2 * X ≤ (m + (j + 1)) * X := Nat.mul_le_mul_right _ h4
  rw [hX] at hb ⊢
  nlinarith

/-- Step 1: the mass beyond m + k is at least 4^m / (2(2m+1)). -/
theorem tail_choose_lb (m k : ℕ) (hk : 1 ≤ k) (h4 : 4 * k ^ 2 ≤ m) :
    4 ^ m ≤ 2 * (2 * m + 1) * (2 * m).choose (m + k) := by
  have hkm : k < m := by nlinarith
  have hr := choose_ratio m k hkm.le
  have hb := bern m k hk (by omega) hkm.le
  have hc := Nat.four_pow_le_two_mul_add_one_mul_central_binom m
  have hpos : 0 < (m - k) ^ k := pow_pos (by omega) _
  have : 4 ^ m * (m - k) ^ k ≤ 2 * (2 * m + 1) * (2 * m).choose (m + k) * (m - k) ^ k :=
    calc 4 ^ m * (m - k) ^ k ≤ (2 * m + 1) * (2 * m).choose m * (m - k) ^ k := by gcongr
      _ = (2 * m + 1) * ((2 * m).choose m * (m - k) ^ k) := by ring
      _ ≤ (2 * m + 1) * ((2 * m).choose (m + k) * (m + k) ^ k) := by gcongr
      _ ≤ (2 * m + 1) * ((2 * m).choose (m + k) * (2 * (m - k) ^ k)) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

/-- Step 1c: low-degree support plus one tail binomial fits inside 4^m. -/
theorem support_add_tail_le (m D : ℕ) (hD : D + 1 ≤ m) :
    Fintype.card (ACP.LowDegreeSupport (2 * m) (2 * m / 2 + D)) +
      (2 * m).choose (m + (D + 1)) ≤ 4 ^ m := by
  rw [show 2 * m / 2 = m by omega, card_lowDegreeSupport_eq_sum]
  rw [show m + (D + 1) = m + D + 1 by omega, ← Finset.sum_range_succ]
  calc (range (m + D + 1 + 1)).sum (fun i => (2 * m).choose i)
      ≤ (range (2 * m + 1)).sum (fun i => (2 * m).choose i) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = 4 ^ m := by rw [Nat.sum_range_choose, pow_mul]; norm_num

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Steps 2+3: the explicit unconditional bound. For any AC0[p] circuit `F` on
`2m + (q-1)` inputs computing MOD_q, and any ℓ with 4(((p-1)ℓ)^depth + 1)^2 ≤ m:
  (4^m / (4 q (2m+1)(2m+2))) * 2^ℓ ≤ size * 2^(2m + (q-1)). -/
theorem MODq_AC0p_explicit
    {q m ℓ : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : ACP.FeedForward (Fin 2) (Fin (2 * m + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACP.ACp_GateOps p))
    (hCompute : ∀ x : Fin (2 * m + (q - 1)) → Fin 2,
      F.eval₁ x = (ACP.modGateOp q (2 * m + (q - 1))).func x)
    (hm : 4 * (ACP.circuitDegreeBound p ℓ F.depth + 1) ^ 2 ≤ m) :
    (4 ^ m / (4 * q * (2 * m + 1) * (2 * m + 2))) * 2 ^ ℓ ≤ F.size * 2 ^ (2 * m + (q - 1)) := by
  classical
  set D := ACP.circuitDegreeBound p ℓ F.depth
  set k := D + 1 with hkdef
  set K := Fintype.card (ACP.ModqField (p := p) q)
  set E := 4 ^ m / (4 * q * (2 * m + 1) * (2 * m + 2))
  set e := q * E
  set G := (2 * m).choose (m + k)
  set S := Fintype.card (ACP.LowDegreeSupport (2 * m) (2 * m / 2 + D))
  have hK : 1 < K := Fintype.one_lt_card
  have hk1 : 1 ≤ k := by omega
  have hkm : k ≤ m := by nlinarith
  have hG := tail_choose_lb m k hk1 hm
  have hSG : S + G ≤ 4 ^ m := support_add_tail_le m D (by omega)
  have hGpos : 0 < G := Nat.choose_pos (by omega)
  have hE : E * (4 * q * (2 * m + 1) * (2 * m + 2)) ≤ 4 ^ m := Nat.div_mul_le_self _ _
  have he : 2 * (e * (2 * m + 2)) ≤ G := by
    have : 2 * (e * (2 * m + 2)) * (2 * (2 * m + 1)) ≤ G * (2 * (2 * m + 1)) := by
      calc 2 * (e * (2 * m + 2)) * (2 * (2 * m + 1))
          = E * (4 * q * (2 * m + 1) * (2 * m + 2)) := by simp only [e]; ring
        _ ≤ 4 ^ m := hE
        _ ≤ _ := by linarith
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have hball := ball_sum_le (2 ^ (2 * m)) K e (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by positivity) (by omega)))
  have hB : (e + 1) * (2 ^ (2 * m) * K) ^ e ≤ K ^ (e * (2 * m + 2)) := by
    have h1 : e + 1 ≤ K ^ e :=
      (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hK e)
    have h2 : 2 ^ (2 * m) ≤ K ^ (2 * m) := Nat.pow_le_pow_left hK _
    calc (e + 1) * (2 ^ (2 * m) * K) ^ e ≤ K ^ e * (K ^ (2 * m) * K) ^ e := by gcongr
      _ = K ^ (e * (2 * m + 2)) := by ring
  have hstrict : K ^ (2 ^ (2 * m)) >
      Fintype.card (ACP.LowDegreeSupport (2 * m) (2 * m / 2 + D) → ACP.ModqField (p := p) q) *
        (range (e + 1)).sum (fun t => (2 ^ (2 * m)).choose t * K ^ t) := by
    rw [Fintype.card_fun]
    calc K ^ S * (range (e + 1)).sum (fun t => (2 ^ (2 * m)).choose t * K ^ t)
        ≤ K ^ S * K ^ (e * (2 * m + 2)) := by gcongr; exact hball.trans hB
      _ < K ^ S * K ^ G := by
          apply Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hK (by omega))
          positivity
      _ = K ^ (S + G) := (pow_add _ _ _).symm
      _ ≤ K ^ (4 ^ m) := Nat.pow_le_pow_right (by omega) hSG
      _ = K ^ (2 ^ (2 * m)) := by rw [pow_mul]; norm_num
  exact MODq_notin_AC0p_fractional (p := p) (n := 2 * m) (e := e) hpq F hUses hCompute
    le_rfl le_rfl hstrict

/-- The growing parameter: largest ℓ ≤ m allowed by the hypothesis at depth d. -/
noncomputable def ellStar (p d m : ℕ) : ℕ :=
  Nat.findGreatest (fun ℓ => 4 * (ACP.circuitDegreeBound p ℓ d + 1) ^ 2 ≤ m) m

/-- ellStar is unbounded: it is ≥ L once m ≥ max L (4(((p-1)L)^d+1)^2). -/
theorem le_ellStar (p d m L : ℕ) (hL : L ≤ m)
    (hm : 4 * (ACP.circuitDegreeBound p L d + 1) ^ 2 ≤ m) : L ≤ ellStar p d m :=
  Nat.le_findGreatest hL hm

/-- Unconditional asymptotic form: for depth-d AC0[p] circuits computing MOD_q on
2m+(q-1) inputs, with m ≥ 4 (so ℓ = 0 qualifies at depth d ≥ 1 or any d),
  (4^m / (4q(2m+1)(2m+2))) * 2^(ellStar p d m) ≤ size * 2^(2m+q-1),
and ellStar p d m → ∞ (le_ellStar). -/
theorem MODq_AC0p_asymptotic
    {q m d : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : ACP.FeedForward (Fin 2) (Fin (2 * m + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACP.ACp_GateOps p))
    (hCompute : ∀ x : Fin (2 * m + (q - 1)) → Fin 2,
      F.eval₁ x = (ACP.modGateOp q (2 * m + (q - 1))).func x)
    (hd : F.depth = d)
    (hm0 : 4 * (ACP.circuitDegreeBound p 0 d + 1) ^ 2 ≤ m) :
    (4 ^ m / (4 * q * (2 * m + 1) * (2 * m + 2))) * 2 ^ ellStar p d m
      ≤ F.size * 2 ^ (2 * m + (q - 1)) := by
  apply MODq_AC0p_explicit hpq F hUses hCompute
  rw [hd]
  exact Nat.findGreatest_spec (P := fun ℓ => 4 * (ACP.circuitDegreeBound p ℓ d + 1) ^ 2 ≤ m)
    (Nat.zero_le m) hm0

end HHH
