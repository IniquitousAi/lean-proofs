import PvNP.SubbotovskayaRp

/-! Round 12 (1): Ep equals the expectation under the TRUE independent R_p distribution:
each variable of W is kept (star) independently with probability p, otherwise fixed to a
uniform random bit. -/

namespace Subb
open Finset

variable {n : ℕ}

/-- f with the variables in T fixed according to a. -/
def fixSet (f : (Fin n → Bool) → Bool) (T : Finset (Fin n)) (a : Fin n → Bool) :
    (Fin n → Bool) → Bool := fun x => f (fun i => if i ∈ T then a i else x i)

/-- TRUE R_p expectation on W: kept set S ⊆ W has probability p^|S| (1-p)^(|W|-|S|), and the
fixed variables W \ S get a uniform assignment a (coordinates of a outside W \ S are unused,
so averaging over all a : Fin n → Bool is the uniform distribution on W \ S). -/
noncomputable def Ptrue (p : ℝ) (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S ∈ W.powerset, p ^ S.card * (1 - p) ^ (W.card - S.card) *
    ((∑ a : Fin n → Bool, (LW S (fixSet f (W \ S) a) : ℝ)) / 2 ^ n)

/-- Uniform j-subset form of the sequential process. -/
noncomputable def U (j : ℕ) (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : ℝ :=
  (∑ T ∈ powersetCard j W, ∑ a : Fin n → Bool, (LW (W \ T) (fixSet f T a) : ℝ)) /
    ((W.card.choose j : ℝ) * 2 ^ n)

theorem fixSet_fix (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool) (T : Finset (Fin n))
    (hi : i ∉ T) (a : Fin n → Bool) :
    fixSet (fix f i b) T a = fixSet f (insert i T) (Function.update a i b) := by
  funext x; simp only [fixSet, fix]; congr 1; funext j
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Function.update_of_ne h]

theorem sum_update (G : (Fin n → Bool) → ℝ) (i : Fin n) :
    ∑ a, G (Function.update a i false) + ∑ a, G (Function.update a i true) = 2 * ∑ a, G a := by
  let e := Equiv.piSplitAt i (fun _ : Fin n => Bool)
  have hu : ∀ (c b : Bool) (r : {j // j ≠ i} → Bool),
      Function.update (e.symm (c, r)) i b = e.symm (b, r) := by
    intro c b r; funext j
    by_cases h : j = i
    · subst h; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, h, Function.update_of_ne h]
  have hs : ∀ H : (Fin n → Bool) → ℝ, ∑ a, H a = ∑ c : Bool, ∑ r, H (e.symm (c, r)) := by
    intro H; rw [← Fintype.sum_prod_type', ← e.symm.sum_comp]
  rw [hs (fun a => G (Function.update a i false)), hs (fun a => G (Function.update a i true)), hs G]
  simp only [hu, Fintype.sum_bool]; ring

theorem sum_reindex (W : Finset (Fin n)) (i : Fin n) (hi : i ∈ W) (j : ℕ)
    (K : Finset (Fin n) → ℝ) :
    ∑ T ∈ powersetCard j (W.erase i), K (insert i T)
      = ∑ T ∈ (powersetCard (j + 1) W).filter (fun T => i ∈ T), K T := by
  apply sum_nbij' (insert i) (fun T => T.erase i)
  · intro T hT
    obtain ⟨h1, h2⟩ := mem_powersetCard.mp hT
    have hiT : i ∉ T := fun h => by simpa using h1 h
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨insert_subset hi (h1.trans (erase_subset _ _)), by rw [card_insert_of_notMem hiT, h2]⟩,
      mem_insert_self _ _⟩
  · intro T hT
    rw [mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨h1, h2⟩, h3⟩ := hT
    rw [mem_powersetCard]
    exact ⟨erase_subset_erase _ h1, by rw [card_erase_of_mem h3, h2]; rfl⟩
  · intro T hT
    rw [mem_powersetCard] at hT
    have hiT : i ∉ T := fun h => by simpa using hT.1 h
    exact erase_insert hiT
  · intro T hT
    exact insert_erase (mem_filter.mp hT).2
  · intro T _; rfl

theorem double_count (W : Finset (Fin n)) (j : ℕ) (g : Finset (Fin n) → ℝ) :
    ∑ i ∈ W, ∑ T ∈ (powersetCard (j + 1) W).filter (fun T => i ∈ T), g T
      = (j + 1) * ∑ T ∈ powersetCard (j + 1) W, g T := by
  rw [sum_comm' (t' := powersetCard (j + 1) W) (s' := fun T => T)]
  · rw [mul_sum]; refine sum_congr rfl fun T hT => ?_
    rw [sum_const, (mem_powersetCard.mp hT).2, nsmul_eq_mul]; push_cast; ring
  · intro i T
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩, h3⟩; exact ⟨h3, h1, h2⟩
    · rintro ⟨h3, h1, h2⟩; exact ⟨h1 h3, ⟨h1, h2⟩, h3⟩

theorem Eres_eq_U : ∀ j (W : Finset (Fin n)) f, j ≤ W.card → Eres j W f = U j W f := by
  intro j
  induction j with
  | zero =>
    intro W f _
    simp only [Eres, U, powersetCard_zero, sum_singleton, sdiff_empty, Nat.choose_zero_right]
    have : ∀ a, fixSet f ∅ a = f := fun a => by funext x; simp [fixSet]
    simp only [this, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; field_simp
  | succ j ih =>
    intro W f hj
    have hm : W.card ≠ 0 := by omega
    obtain ⟨M, hM⟩ : ∃ M, W.card = M + 1 := ⟨W.card - 1, by omega⟩
    rw [Eres, if_neg hm]
    have hci : ∀ i ∈ W, (W.erase i).card = M := fun i hi => by rw [card_erase_of_mem hi, hM]; rfl
    have key : ∀ i ∈ W, Eres j (W.erase i) (fix f i false) + Eres j (W.erase i) (fix f i true)
        = 2 * (∑ T ∈ (powersetCard (j + 1) W).filter (fun T => i ∈ T),
            ∑ a : Fin n → Bool, (LW (W \ T) (fixSet f T a) : ℝ)) / ((M.choose j : ℝ) * 2 ^ n) := by
      intro i hi
      rw [ih _ _ (by rw [hci i hi]; omega), ih _ _ (by rw [hci i hi]; omega), U, U, hci i hi,
        ← add_div, ← sum_add_distrib, ← sum_reindex W i hi j, mul_sum]
      congr 1; refine sum_congr rfl fun T hT => ?_
      have hiT : i ∉ T := fun h => by simpa using (mem_powersetCard.mp hT).1 h
      have hsd : W.erase i \ T = W \ insert i T := by ext v; simp; tauto
      simp only [fixSet_fix f i _ T hiT, hsd]
      exact sum_update (fun a => (LW (W \ insert i T) (fixSet f (insert i T) a) : ℝ)) i
    rw [sum_congr rfl key, ← sum_div, ← mul_sum, double_count, U, hM]
    have hc : ((M + 1 : ℕ) : ℝ) * (M.choose j : ℝ) = ((M + 1).choose (j + 1) : ℝ) * (j + 1 : ℕ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq M j
    have hp : (0 : ℝ) < (M.choose j : ℝ) := by
      have : j ≤ M := by omega
      exact_mod_cast Nat.choose_pos this
    have hp' : (0 : ℝ) < ((M + 1).choose (j + 1) : ℝ) := by
      have : j + 1 ≤ M + 1 := by omega
      exact_mod_cast Nat.choose_pos this
    push_cast at hc ⊢
    rw [div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-(2 * (∑ T ∈ powersetCard (j + 1) W, ∑ a : Fin n → Bool,
      (LW (W \ T) (fixSet f T a) : ℝ)) * 2 ^ n)) * hc

/-- Round 12 (1): the binomial-mixture expectation Ep IS the true independent R_p expectation. -/
theorem Ep_eq_Ptrue (p : ℝ) (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    Ep p W f = Ptrue p W f := by
  rw [Ptrue, ← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (W.card + 1))
    (fun S hS => mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp hS)))), Ep]
  refine sum_congr rfl fun k hk => ?_
  rw [← powersetCard_eq_filter]
  have hk' : k ≤ W.card := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [Eres_eq_U _ _ _ (Nat.sub_le _ _), U, Nat.choose_symm hk']
  have hre : ∑ T ∈ powersetCard (W.card - k) W, ∑ a : Fin n → Bool, (LW (W \ T) (fixSet f T a) : ℝ)
      = ∑ S ∈ powersetCard k W, ∑ a : Fin n → Bool, (LW S (fixSet f (W \ S) a) : ℝ) := by
    apply sum_nbij' (W \ ·) (W \ ·)
    · intro T hT
      rw [mem_powersetCard] at hT ⊢
      exact ⟨sdiff_subset, by rw [card_sdiff_of_subset hT.1, hT.2]; omega⟩
    · intro S hS
      rw [mem_powersetCard] at hS ⊢
      exact ⟨sdiff_subset, by rw [card_sdiff_of_subset hS.1, hS.2]⟩
    · intro T hT
      rw [mem_powersetCard] at hT
      exact Finset.sdiff_sdiff_eq_self hT.1
    · intro S hS
      rw [mem_powersetCard] at hS
      exact Finset.sdiff_sdiff_eq_self hS.1
    · intro T hT
      simp only [mem_powersetCard] at hT
      rw [Finset.sdiff_sdiff_eq_self hT.1]
  have hcp : (0 : ℝ) < (W.card.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk'
  rw [hre, bw]
  rw [show ∑ S ∈ powersetCard k W, p ^ S.card * (1 - p) ^ (W.card - S.card) *
      ((∑ a : Fin n → Bool, (LW S (fixSet f (W \ S) a) : ℝ)) / 2 ^ n)
      = ∑ S ∈ powersetCard k W, p ^ k * (1 - p) ^ (W.card - k) *
      ((∑ a : Fin n → Bool, (LW S (fixSet f (W \ S) a) : ℝ)) / 2 ^ n) from
    sum_congr rfl fun S hS => by rw [(mem_powersetCard.mp hS).2], ← mul_sum, ← sum_div]
  field_simp

/-- SUBBOTOVSKAYA under the TRUE R_p distribution (independent stars with prob p). -/
theorem subbotovskaya_Rp_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset (Fin n)) (f)
    (hm : 1 ≤ W.card) (hf : ∃ r, Rep W f r) :
    Ptrue p W f ≤ p * Real.sqrt (p + (1 - p) / W.card) * LW W f + 1 := by
  rw [← Ep_eq_Ptrue]; exact subbotovskaya_Rp p hp0 hp1 W f hm hf

end Subb
