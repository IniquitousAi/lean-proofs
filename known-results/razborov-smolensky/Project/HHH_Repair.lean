import Project.RazborovSmolenskyModqBooleanTransfer_v21

/-! HHH repair of `ACP.MODq_notin_AC0p_quantitative`. The bad-input count `E` is kept
absolute, so the error FRACTION is δ = E / 2^(n+q-1) (a rational number), and the
conclusion is `E * 2^ℓ ≤ size * 2^(n+q-1)`, i.e. size ≥ δ · 2^ℓ. -/

open Finset

namespace HHH

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- R1: the repaired quantitative theorem, proved from upstream lemmas only. -/
theorem MODq_notin_AC0p_fractional
    {q n ℓ E e B : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : ACP.FeedForward (Fin 2) (Fin (n + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACP.ACp_GateOps p))
    (hCompute : ∀ x : Fin (n + (q - 1)) → Fin 2,
      F.eval₁ x = (ACP.modGateOp q (n + (q - 1))).func x)
    (herror : q * E ≤ e)
    (hballB :
      (Finset.range (e + 1)).sum
        (fun t : ℕ => Nat.choose (2 ^ n) t * Fintype.card (ACP.ModqField (p := p) q) ^ t) ≤ B)
    (hstrict :
      Fintype.card (ACP.ModqField (p := p) q) ^ (2 ^ n) >
        Fintype.card
          (ACP.LowDegreeSupport n (n / 2 + ACP.circuitDegreeBound p ℓ F.depth) →
            ACP.ModqField (p := p) q) * B) :
    E * 2 ^ ℓ ≤ F.size * 2 ^ (n + (q - 1)) := by
  have hLB := ACP.smolensky_modQ_lowDegreeBadCountLB (p := p) (q := q) (n := n)
    (d := ACP.circuitDegreeBound p ℓ F.depth) (E := E) (e := e) (B := B)
    hpq herror hballB hstrict
  exact ACP.size_lower_bound_from_badCountLB (p := p) F hUses hCompute ℓ E hLB

/-- L1: count of the low-degree support type, as a filter count. -/
theorem card_lowDegreeSupport (n D : ℕ) :
    Fintype.card (ACP.LowDegreeSupport n D) =
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card ≤ D)).card := by
  classical
  exact (Fintype.card_congr (Equiv.refl _ :
      ACP.LowDegreeSupport n D ≃ {s : Finset (Fin n) // s.card ≤ D})).trans
    (Fintype.card_subtype _)

/-- L2: card of the field GF(p^(q-1)). -/
theorem card_modqField (q : ℕ) [Fact (Nat.Prime q)] :
    Fintype.card (ACP.ModqField (p := p) q) = p ^ (q - 1) := by
  have hq := (Fact.out : q.Prime).two_le
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card p (q - 1) (by omega)

/-- L3 (Hamming-ball bound): Σ_{t≤e} C(N,t) K^t ≤ (e+1) (N K)^e when N K ≥ 1. -/
theorem ball_sum_le (N K e : ℕ) (hNK : 1 ≤ N * K) :
    (range (e + 1)).sum (fun t => N.choose t * K ^ t) ≤ (e + 1) * (N * K) ^ e := by
  have h : ∀ t ∈ range (e + 1), N.choose t * K ^ t ≤ (N * K) ^ e := by
    intro t ht
    have hte : t ≤ e := Nat.lt_succ_iff.mp (mem_range.mp ht)
    calc N.choose t * K ^ t ≤ N ^ t * K ^ t :=
          Nat.mul_le_mul_right _ (Nat.choose_le_pow N t)
      _ = (N * K) ^ t := (mul_pow N K t).symm
      _ ≤ (N * K) ^ e := Nat.pow_le_pow_right hNK hte
  simpa using Finset.sum_le_card_nsmul _ _ _ h

/-- L4: concrete count, 42 subsets of Fin 6 with at most 3 elements. -/
theorem card_lowDegreeSupport_6_3 : Fintype.card (ACP.LowDegreeSupport 6 3) = 42 := by
  rw [card_lowDegreeSupport]; decide

/-- S1 (NOT vacuous): the hypotheses of `MODq_notin_AC0p_fractional` hold for a real
instance with E = 1 > 0: p = 2, q = 3, n = 6, degree budget d = 0, e = 3. -/
theorem fractional_hyps_satisfiable :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    ∃ E e B : ℕ, 0 < E ∧ 3 * E ≤ e ∧
      (Finset.range (e + 1)).sum
        (fun t : ℕ => Nat.choose (2 ^ 6) t * Fintype.card (ACP.ModqField (p := 2) 3) ^ t) ≤ B ∧
      Fintype.card (ACP.ModqField (p := 2) 3) ^ (2 ^ 6) >
        Fintype.card (ACP.LowDegreeSupport 6 (6 / 2 + 0) → ACP.ModqField (p := 2) 3) * B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨1, 3, 2699009, by norm_num, by norm_num, ?_, ?_⟩
  · rw [card_modqField (p := 2) 3]
    simp [Finset.sum_range_succ, Nat.choose]
  · rw [Fintype.card_fun, card_modqField (p := 2) 3, card_lowDegreeSupport_6_3]
    norm_num

/-- L5 (low-degree count, general): subsets of Fin n of size ≤ D number Σ_{i≤D} C(n,i). -/
theorem card_lowDegreeSupport_eq_sum (n D : ℕ) :
    Fintype.card (ACP.LowDegreeSupport n D) = (range (D + 1)).sum (fun i => n.choose i) := by
  classical
  rw [card_lowDegreeSupport]
  have hset : (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card ≤ D)
      = (range (D + 1)).biUnion (fun i => powersetCard i (Finset.univ : Finset (Fin n))) := by
    ext s; simp [mem_powersetCard, Nat.lt_succ_iff]
  rw [hset, card_biUnion]
  · simp [card_powersetCard]
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr (fun s h1 h2 =>
      hij ((mem_powersetCard.1 h1).2.symm.trans (mem_powersetCard.1 h2).2))

/-! PLAN (not yet proved, no placeholder used):
1. Asymptotic hstrict: for d fixed and n large, with D = n/2 + d,
   |LDS n D| ≤ 2^n - c*2^n/sqrt n (central binomial bound, Mathlib Nat.choose_le_centralBinom
   plus a Stirling-type estimate) so K^(2^n) / K^|LDS| ≥ K^(c*2^n/sqrt n).
2. Ball side: ball_sum_le gives ≤ (e+1)(2^n K)^e; take e = q*E with E = eps*2^n/sqrt n,
   eps small, so log_K of the ball is < c*2^n/sqrt n. That yields hstrict.
3. Plug into MODq_notin_AC0p_fractional to get size ≥ eps*2^(n-ℓ)/sqrt n with
   ℓ ~ n^(1/(2d)), the classical exp(n^(1/2d)) bound.
-/
end HHH
