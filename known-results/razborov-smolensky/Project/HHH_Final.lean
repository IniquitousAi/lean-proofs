import Project.HHH_Asymptotic

/-! HHH Round 7: every input length, divided form size ≥ f(n), closed-form ellStar. -/

open Finset

namespace HHH

/-- Tail bound for any n: with m = n/2 and 4k² ≤ m, 2^n ≤ 4(n+1)·C(n, n/2+k). -/
theorem tail_choose_lb_any (n k : ℕ) (hk : 1 ≤ k) (h4 : 4 * k ^ 2 ≤ n / 2) :
    2 ^ n ≤ 4 * (n + 1) * n.choose (n / 2 + k) := by
  have h1 := tail_choose_lb (n / 2) k hk h4
  have h2 : (2 * (n / 2)).choose (n / 2 + k) ≤ n.choose (n / 2 + k) :=
    Nat.choose_le_choose _ (by omega)
  have h3 : 2 ^ n ≤ 2 * 4 ^ (n / 2) := by
    rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
    · subst hr; rw [show (r + r) / 2 = r by omega, show r + r = 2 * r by omega, pow_mul]
      norm_num
    · subst hr; rw [show (2 * r + 1) / 2 = r by omega, pow_succ, pow_mul]; norm_num; ring_nf; omega
  calc 2 ^ n ≤ 2 * 4 ^ (n / 2) := h3
    _ ≤ 2 * (2 * (2 * (n / 2) + 1) * (2 * (n / 2)).choose (n / 2 + k)) := by gcongr
    _ ≤ 2 * (2 * (n + 1) * n.choose (n / 2 + k)) := by gcongr; omega
    _ = 4 * (n + 1) * n.choose (n / 2 + k) := by ring

theorem support_add_tail_le_any (n D : ℕ) (hD : n / 2 + D + 1 ≤ n) :
    Fintype.card (ACP.LowDegreeSupport n (n / 2 + D)) + n.choose (n / 2 + (D + 1)) ≤ 2 ^ n := by
  rw [card_lowDegreeSupport_eq_sum, show n / 2 + (D + 1) = n / 2 + D + 1 by omega,
    ← Finset.sum_range_succ]
  calc (range (n / 2 + D + 1 + 1)).sum (fun i => n.choose i)
      ≤ (range (n + 1)).sum (fun i => n.choose i) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = 2 ^ n := Nat.sum_range_choose n

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Explicit bound for EVERY input length n + (q-1). -/
theorem MODq_AC0p_explicit_any
    {q n ℓ : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : ACP.FeedForward (Fin 2) (Fin (n + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACP.ACp_GateOps p))
    (hCompute : ∀ x : Fin (n + (q - 1)) → Fin 2,
      F.eval₁ x = (ACP.modGateOp q (n + (q - 1))).func x)
    (hm : 4 * (ACP.circuitDegreeBound p ℓ F.depth + 1) ^ 2 ≤ n / 2) :
    (2 ^ n / (8 * q * (n + 1) * (n + 2))) * 2 ^ ℓ ≤ F.size * 2 ^ (n + (q - 1)) := by
  classical
  set D := ACP.circuitDegreeBound p ℓ F.depth
  set k := D + 1 with hkdef
  set K := Fintype.card (ACP.ModqField (p := p) q)
  set E := 2 ^ n / (8 * q * (n + 1) * (n + 2))
  set e := q * E
  set G := n.choose (n / 2 + k)
  set S := Fintype.card (ACP.LowDegreeSupport n (n / 2 + D))
  have hK : 1 < K := Fintype.one_lt_card
  have hk1 : 1 ≤ k := by omega
  have hkm : k ≤ n / 2 := by nlinarith
  have hG := tail_choose_lb_any n k hk1 hm
  have hSG : S + G ≤ 2 ^ n := support_add_tail_le_any n D (by omega)
  have hGpos : 0 < G := Nat.choose_pos (by omega)
  have hE : E * (8 * q * (n + 1) * (n + 2)) ≤ 2 ^ n := Nat.div_mul_le_self _ _
  have he : 2 * (e * (n + 2)) ≤ G := by
    have : 2 * (e * (n + 2)) * (4 * (n + 1)) ≤ G * (4 * (n + 1)) := by
      calc 2 * (e * (n + 2)) * (4 * (n + 1))
          = E * (8 * q * (n + 1) * (n + 2)) := by simp only [e]; ring
        _ ≤ 2 ^ n := hE
        _ ≤ _ := by linarith
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have hball := ball_sum_le (2 ^ n) K e (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by positivity) (by omega)))
  have hB : (e + 1) * (2 ^ n * K) ^ e ≤ K ^ (e * (n + 2)) := by
    have h1 : e + 1 ≤ K ^ e :=
      (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hK e)
    have h2 : 2 ^ n ≤ K ^ n := Nat.pow_le_pow_left hK _
    calc (e + 1) * (2 ^ n * K) ^ e ≤ K ^ e * (K ^ n * K) ^ e := by gcongr
      _ = K ^ (e * (n + 2)) := by ring
  have hstrict : K ^ (2 ^ n) >
      Fintype.card (ACP.LowDegreeSupport n (n / 2 + D) → ACP.ModqField (p := p) q) *
        (range (e + 1)).sum (fun t => (2 ^ n).choose t * K ^ t) := by
    rw [Fintype.card_fun]
    calc K ^ S * (range (e + 1)).sum (fun t => (2 ^ n).choose t * K ^ t)
        ≤ K ^ S * K ^ (e * (n + 2)) := by gcongr; exact hball.trans hB
      _ < K ^ S * K ^ G := by
          apply Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hK (by omega))
          positivity
      _ = K ^ (S + G) := (pow_add _ _ _).symm
      _ ≤ K ^ (2 ^ n) := Nat.pow_le_pow_right (by omega) hSG
  exact MODq_notin_AC0p_fractional (p := p) (n := n) (e := e) hpq F hUses hCompute
    le_rfl le_rfl hstrict

/-- Largest admissible ℓ for input parameter n at depth d. -/
noncomputable def ellStarN (p d n : ℕ) : ℕ :=
  Nat.findGreatest (fun ℓ => 4 * (ACP.circuitDegreeBound p ℓ d + 1) ^ 2 ≤ n / 2) n

/-- Closed form: for L ≥ 1, n ≥ 32((p-1)L)^(2d) + 2 and L ≤ n give L ≤ ellStarN p d n.
Equivalently ellStarN p d n ≥ ⌊(n/32)^(1/(2d))⌋ / (p-1) (up to the +2, L ≤ n side conditions). -/
theorem ellStarN_closed_form (d n L : ℕ) (hL1 : 1 ≤ L) (hLn : L ≤ n)
    (hn : 32 * ((p - 1) * L) ^ (2 * d) + 2 ≤ n) : L ≤ ellStarN p d n := by
  apply Nat.le_findGreatest hLn
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hx : 1 ≤ ((p - 1) * L) ^ d := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) hL1)
  set x := ((p - 1) * L) ^ d
  show 4 * (x + 1) ^ 2 ≤ n / 2
  have hsq : ((p - 1) * L) ^ (2 * d) = x ^ 2 := by rw [mul_comm 2 d, pow_mul]
  rw [hsq] at hn
  have : 4 * (x + 1) ^ 2 ≤ 16 * x ^ 2 := by nlinarith
  omega

/-- Cubic beats the constant: 8q(n+1)(n+2) ≤ 2^n for n ≥ 16q + 32. -/
theorem poly_le_two_pow (q n : ℕ) (hn : 16 * q + 32 ≤ n) :
    8 * q * (n + 1) * (n + 2) ≤ 2 ^ n := by
  have cube : ∀ j, (j + 10) ^ 3 ≤ 2 ^ (j + 10) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ 2 (j + 10)]
      have : (j + 1 + 10) ^ 3 ≤ 2 * (j + 10) ^ 3 := by
        ring_nf; nlinarith [Nat.zero_le (j ^ 3), Nat.zero_le (j ^ 2), Nat.zero_le j]
      linarith
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
  have h3 := cube j
  have : 8 * q * (j + 10 + 1) * (j + 10 + 2) ≤ (j + 10) ^ 3 := by
    have a : (j + 10 + 1) * (j + 10 + 2) ≤ 2 * (j + 10) ^ 2 := by nlinarith
    have b : 16 * q * (j + 10) ^ 2 ≤ (j + 10) * (j + 10) ^ 2 :=
      Nat.mul_le_mul_right _ (by omega)
    calc 8 * q * (j + 10 + 1) * (j + 10 + 2) = 8 * q * ((j + 10 + 1) * (j + 10 + 2)) := by ring
      _ ≤ 8 * q * (2 * (j + 10) ^ 2) := by gcongr
      _ = 16 * q * (j + 10) ^ 2 := by ring
      _ ≤ (j + 10) * (j + 10) ^ 2 := b
      _ = (j + 10) ^ 3 := by ring
  linarith

/-- FINAL (unconditional, every n): for primes p ≠ q, depth d, and every n ≥ 16q + 32,
every depth-d AC0[p] circuit on n + (q-1) inputs computing MOD_q satisfies
  2^(ellStarN p d n) ≤ size · (2^q · 8q(n+1)(n+2)). -/
theorem MODq_AC0p_final
    {q n d : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : ACP.FeedForward (Fin 2) (Fin (n + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACP.ACp_GateOps p))
    (hCompute : ∀ x : Fin (n + (q - 1)) → Fin 2,
      F.eval₁ x = (ACP.modGateOp q (n + (q - 1))).func x)
    (hd : F.depth = d)
    (hn : 16 * q + 32 ≤ n) :
    2 ^ ellStarN p d n ≤ F.size * (2 ^ q * (8 * q * (n + 1) * (n + 2))) := by
  have hq2 : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
  have h0 : 4 * (ACP.circuitDegreeBound p 0 d + 1) ^ 2 ≤ n / 2 := by
    have : ACP.circuitDegreeBound p 0 d ≤ 1 := by
      unfold ACP.circuitDegreeBound; simp only [mul_zero]
      rcases d with _ | d <;> simp
    have : (ACP.circuitDegreeBound p 0 d + 1) ^ 2 ≤ 4 := by nlinarith
    omega
  have hspec := Nat.findGreatest_spec
    (P := fun ℓ => 4 * (ACP.circuitDegreeBound p ℓ d + 1) ^ 2 ≤ n / 2) (Nat.zero_le n) h0
  have hx := MODq_AC0p_explicit_any (ℓ := ellStarN p d n) hpq F hUses hCompute (by rw [hd]; exact hspec)
  set c := 8 * q * (n + 1) * (n + 2)
  set E := 2 ^ n / c
  set L := ellStarN p d n
  have hc : c ≤ 2 ^ n := poly_le_two_pow q n hn
  have hcpos : 0 < c := by positivity
  have hlt : 2 ^ n < c * (E + 1) := Nat.lt_mul_div_succ _ hcpos
  have hE1 : 1 ≤ E := (Nat.le_div_iff_mul_le hcpos).mpr (by linarith)
  have h2 : 2 ^ n ≤ 2 * E * c := by nlinarith
  have hpow : 2 ^ (n + (q - 1)) * 2 = 2 ^ n * 2 ^ q := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have key : 2 ^ L * 2 ^ n ≤ (F.size * (2 ^ q * c)) * 2 ^ n := by
    calc 2 ^ L * 2 ^ n ≤ 2 ^ L * (2 * E * c) := by gcongr
      _ = 2 * c * (E * 2 ^ L) := by ring
      _ ≤ 2 * c * (F.size * 2 ^ (n + (q - 1))) := by gcongr
      _ = c * F.size * (2 ^ (n + (q - 1)) * 2) := by ring
      _ = (F.size * (2 ^ q * c)) * 2 ^ n := by rw [hpow]; ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- Divided form: size ≥ f(n) := 2^(ellStarN p d n) / (2^q · 8q(n+1)(n+2)) for all n ≥ 16q+32. -/
theorem MODq_AC0p_size_ge
    {q n d : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : ACP.FeedForward (Fin 2) (Fin (n + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACP.ACp_GateOps p))
    (hCompute : ∀ x : Fin (n + (q - 1)) → Fin 2,
      F.eval₁ x = (ACP.modGateOp q (n + (q - 1))).func x)
    (hd : F.depth = d)
    (hn : 16 * q + 32 ≤ n) :
    2 ^ ellStarN p d n / (2 ^ q * (8 * q * (n + 1) * (n + 2))) ≤ F.size :=
  Nat.div_le_of_le_mul (by
    have := MODq_AC0p_final hpq F hUses hCompute hd hn
    linarith [mul_comm F.size (2 ^ q * (8 * q * (n + 1) * (n + 2)))])

end HHH
