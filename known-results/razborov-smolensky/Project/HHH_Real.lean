import Project.HHH_Final

/-! HHH Round 8: real-number form. For d ≥ 1, primes p ≠ q, n ≥ 16q+32:
  2^(c · n^(1/(2d))) ≤ 2 · (2^q · 8q(n+1)(n+2)) · size,  c = 1 / ((p-1) · 64^(1/(2d))). -/

namespace HHH

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The floor of x = (n/64)^(1/(2d)) / (p-1) is at most ellStarN p d n. -/
theorem floor_le_ellStarN (d n : ℕ) (hd : 1 ≤ d) (hn : 4 ≤ n) :
    ⌊((n : ℝ) / 64) ^ ((1 : ℝ) / (2 * d)) / (p - 1)⌋₊ ≤ ellStarN p d n := by
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  set y : ℝ := (n : ℝ) / 64
  have hy0 : 0 ≤ y := by positivity
  set t : ℝ := (1 : ℝ) / (2 * d)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set x := y ^ t / (p - 1)
  set L := ⌊x⌋₊
  rcases Nat.eq_zero_or_pos L with h0 | hL1
  · rw [h0]; exact Nat.zero_le _
  have hLx : (L : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hyt : y ^ t ≤ (n : ℝ) := by
    rcases le_or_gt 1 y with h1 | h1
    · calc y ^ t ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 ht1
        _ = y := Real.rpow_one y
        _ ≤ n := by simp only [y]; have : (0:ℝ) ≤ n := by positivity
                    linarith [div_le_self this (by norm_num : (1:ℝ) ≤ 64)]
    · calc y ^ t ≤ 1 := Real.rpow_le_one hy0 h1.le ht0
        _ ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hxn : x ≤ n := by
    calc x ≤ y ^ t := div_le_self (by positivity) hp1
      _ ≤ n := hyt
  have hLn : L ≤ n := by exact_mod_cast hLx.trans hxn
  apply ellStarN_closed_form d n L hL1 hLn
  -- 32((p-1)L)^(2d) + 2 ≤ n, via reals
  have hpow : (((p : ℝ) - 1) * L) ^ (2 * d) ≤ y := by
    have h1 : ((p : ℝ) - 1) * L ≤ y ^ t := by
      calc ((p : ℝ) - 1) * L ≤ ((p : ℝ) - 1) * x := by gcongr
        _ = y ^ t := by simp only [x]; field_simp
    calc (((p : ℝ) - 1) * L) ^ (2 * d) ≤ (y ^ t) ^ (2 * d) := by
          gcongr
      _ = y := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]
          have : t * ((2 * d : ℕ) : ℝ) = 1 := by
            simp only [t]; push_cast; field_simp
          rw [this, Real.rpow_one]
  have hcast : ((((p - 1) * L) ^ (2 * d) : ℕ) : ℝ) = (((p : ℝ) - 1) * L) ^ (2 * d) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hreal : ((32 * ((p - 1) * L) ^ (2 * d) + 2 : ℕ) : ℝ) ≤ n := by
    rw [Nat.cast_add, Nat.cast_mul, hcast]
    simp only [y] at hpow
    push_cast
    linarith
  exact_mod_cast hreal

/-- MAIN REAL COROLLARY. -/
theorem MODq_AC0p_rpow
    {q n d : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : ACP.FeedForward (Fin 2) (Fin (n + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACP.ACp_GateOps p))
    (hCompute : ∀ x : Fin (n + (q - 1)) → Fin 2,
      F.eval₁ x = (ACP.modGateOp q (n + (q - 1))).func x)
    (hdep : F.depth = d) (hd : 1 ≤ d)
    (hn : 16 * q + 32 ≤ n) :
    (2 : ℝ) ^ ((1 / (((p : ℝ) - 1) * (64 : ℝ) ^ ((1 : ℝ) / (2 * d)))) *
        (n : ℝ) ^ ((1 : ℝ) / (2 * d)))
      ≤ 2 * ((2 ^ q * (8 * q * (n + 1) * (n + 2)) : ℕ) : ℝ) * (F.size : ℝ) := by
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  set t : ℝ := (1 : ℝ) / (2 * d)
  set x := ((n : ℝ) / 64) ^ t / (p - 1)
  have hx : (1 / (((p : ℝ) - 1) * (64 : ℝ) ^ t)) * (n : ℝ) ^ t = x := by
    simp only [x]
    rw [Real.div_rpow (by positivity) (by norm_num)]
    have : (0:ℝ) < (64:ℝ) ^ t := by positivity
    field_simp
  rw [hx]
  set L := ⌊x⌋₊
  have hL := floor_le_ellStarN (p := p) d n hd (by omega)
  have hfin := MODq_AC0p_final hpq F hUses hCompute hdep hn
  have hxL : x ≤ (L : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  calc (2 : ℝ) ^ x ≤ (2 : ℝ) ^ ((L : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hxL
    _ = 2 * (2 : ℝ) ^ L := by
        rw [show ((L : ℝ) + 1) = ((L + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
          pow_succ]; ring
    _ ≤ 2 * (2 : ℝ) ^ ellStarN p d n := by
        gcongr; norm_num
    _ ≤ 2 * ((F.size * (2 ^ q * (8 * q * (n + 1) * (n + 2)) : ℕ) : ℝ)) := by
        gcongr; exact_mod_cast hfin
    _ = _ := by push_cast; ring

end HHH
