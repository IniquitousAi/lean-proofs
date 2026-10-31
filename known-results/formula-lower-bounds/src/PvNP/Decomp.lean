import PvNP.RpTrue

/-! Round 13: Håstad/Tal plan, step 1 (decomposition) and step 2 (per-piece bound). -/

namespace Subb
open Finset

variable {n : ℕ}

/-! ## Step 1: greedy bottom-up decomposition. A node's accumulated leaf mass is cut off as a
piece once it reaches l. Output: (residual mass at the root, list of piece sizes). -/

def dstep (l : ℕ) (a b : ℕ × List ℕ) : ℕ × List ℕ :=
  if l ≤ a.1 + b.1 then (0, (a.1 + b.1) :: (a.2 ++ b.2)) else (a.1 + b.1, a.2 ++ b.2)

def decomp (l : ℕ) : Fm n → ℕ × List ℕ
  | Fm.lit _ _ => (1, [])
  | Fm.and A B => dstep l (decomp l A) (decomp l B)
  | Fm.or A B => dstep l (decomp l A) (decomp l B)

def Good (l : ℕ) (L : ℕ) (p : ℕ × List ℕ) : Prop :=
  p.1 < l ∧ p.1 + p.2.sum = L ∧ ∀ s ∈ p.2, l ≤ s ∧ s < 2 * l

theorem good_dstep (l L1 L2 : ℕ) (a b) (ha : Good l L1 a) (hb : Good l L2 b) :
    Good l (L1 + L2) (dstep l a b) := by
  obtain ⟨a1, a2, a3⟩ := ha; obtain ⟨b1, b2, b3⟩ := hb
  unfold dstep; split_ifs with h
  · refine ⟨by omega, by simp [List.sum_append]; omega, ?_⟩
    intro s hs
    simp only [List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · omega
    · exact a3 s hs
    · exact b3 s hs
  · refine ⟨by omega, by simp [List.sum_append]; omega, ?_⟩
    intro s hs; rcases List.mem_append.mp hs with hs | hs
    · exact a3 s hs
    · exact b3 s hs

theorem decomp_good (l : ℕ) (hl : 2 ≤ l) : ∀ F : Fm n, Good l F.size (decomp l F) := by
  intro F
  induction F with
  | lit => exact ⟨by simp [decomp]; omega, by simp [decomp, Fm.size], by simp [decomp]⟩
  | and A B iA iB => exact good_dstep l _ _ _ _ iA iB
  | or A B iA iB => exact good_dstep l _ _ _ _ iA iB

/-- DECOMPOSITION LEMMA (counting form). For l ≥ 2 the leaves of any De Morgan formula of
size L split into a root residue of size < l plus pieces, each of size in [l, 2l), and the
number of pieces is at most L / l. -/
theorem decomposition (l : ℕ) (hl : 2 ≤ l) (F : Fm n) :
    (decomp l F).1 < l ∧ (decomp l F).1 + (decomp l F).2.sum = F.size ∧
    (∀ s ∈ (decomp l F).2, l ≤ s ∧ s < 2 * l) ∧ (decomp l F).2.length * l ≤ F.size := by
  obtain ⟨h1, h2, h3⟩ := decomp_good l hl F
  refine ⟨h1, h2, h3, ?_⟩
  have : (decomp l F).2.length * l ≤ (decomp l F).2.sum := by
    have key : ∀ P : List ℕ, (∀ s ∈ P, l ≤ s) → P.length * l ≤ P.sum := by
      intro P; induction P with
      | nil => simp
      | cons a t ih =>
        intro h; simp only [List.length_cons, List.sum_cons]
        have := ih (fun s hs => h s (List.mem_cons_of_mem _ hs)); have := h a (by simp)
        nlinarith
    exact key _ (fun s hs => (h3 s hs).1)
  omega

/-! ## Step 2: per-piece bound under the TRUE R_p. -/

theorem cnt_exists : ∀ F : Fm n, ∃ j, 0 < F.cnt j := by
  intro F; induction F with
  | lit j _ => exact ⟨j, by simp [Fm.cnt]⟩
  | and A B iA _ => obtain ⟨j, h⟩ := iA; exact ⟨j, by simp [Fm.cnt]; omega⟩
  | or A B iA _ => obtain ⟨j, h⟩ := iA; exact ⟨j, by simp [Fm.cnt]; omega⟩

theorem eval_congr : ∀ (F : Fm n) (x y : Fin n → Bool), (∀ j, 0 < F.cnt j → x j = y j) →
    F.eval x = F.eval y := by
  intro F; induction F with
  | lit j t => intro x y h; simp [Fm.eval, h j (by simp [Fm.cnt])]
  | and A B iA iB =>
    intro x y h; simp only [Fm.eval]
    rw [iA x y (fun j hj => h j (by simp [Fm.cnt]; omega)), iB x y (fun j hj => h j (by simp [Fm.cnt]; omega))]
  | or A B iA iB =>
    intro x y h; simp only [Fm.eval]
    rw [iA x y (fun j hj => h j (by simp [Fm.cnt]; omega)), iB x y (fun j hj => h j (by simp [Fm.cnt]; omega))]

open Classical in
/-- A function on at most one variable has formula complexity at most that many leaves. -/
theorem LW_small (S : Finset (Fin n)) (g : (Fin n → Bool) → Bool) (hS : S.card ≤ 1) :
    LW S g ≤ S.card := by
  by_cases hex : ∃ r, Rep S g r
  · obtain ⟨r, hr⟩ := hex
    rcases r with c | F
    · have := LW_le hr; simp [rsize] at this; omega
    · obtain ⟨j, hj⟩ := cnt_exists F
      have hjS : j ∈ S := hr.1 j (by simpa [rcnt] using hj)
      have hS1 : S = {j} := by
        rw [card_le_one] at hS; ext v; simp; constructor
        · intro hv; exact hS v hv j hjS
        · rintro rfl; exact hjS
      have hg : ∀ x, g x = g (fun _ => x j) := by
        intro x
        have e := fun y => (hr.2 y).symm
        rw [e x, e (fun _ => x j)]
        simp only [reval]
        apply eval_congr; intro v hv
        have : v ∈ S := hr.1 v (by simpa [rcnt] using hv)
        rw [hS1, mem_singleton] at this; subst this; rfl
      rw [hS1, card_singleton]
      by_cases hc : g (fun _ => false) = g (fun _ => true)
      · have : Rep S g (.inl (g (fun _ => false))) := ⟨fun v hv => by simp [rcnt] at hv, fun x => by
          simp only [reval]; rw [hg x]; cases x j
          · rfl
          · exact hc⟩
        have := LW_le this; rw [hS1] at this; simp [rsize] at this; omega
      · have : Rep S g (.inr (Fm.lit j (g (fun _ => true)))) := ⟨fun v hv => by
            simp only [rcnt, Fm.cnt] at hv; split_ifs at hv with h
            · rw [hS1, mem_singleton]; exact h.symm
            · omega, fun x => by
          simp only [reval, Fm.eval]; rw [hg x]
          cases hx : x j <;> cases h0 : g (fun _ => false) <;> cases h1 : g (fun _ => true) <;>
            simp_all⟩
        have := LW_le this; rw [hS1] at this; simp [rsize, Fm.size] at this; omega
  · simp [LW, hex]

theorem Eres_small (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ 1)
    (hkm : k ≤ W.card) : Eres (W.card - k) W f ≤ k := by
  rw [Eres_eq_U _ _ _ (Nat.sub_le _ _), U]
  have hc : (0 : ℝ) < (W.card.choose (W.card - k) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.sub_le _ _)
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ ∑ T ∈ powersetCard (W.card - k) W, ∑ _a : Fin n → Bool, (k : ℝ) := by
        apply sum_le_sum; intro T hT; apply sum_le_sum; intro a _
        obtain ⟨h1, h2⟩ := mem_powersetCard.mp hT
        have hc : (W \ T).card = k := by rw [card_sdiff_of_subset h1, h2]; omega
        have := LW_small (W \ T) (fixSet f T a) (by omega)
        rw [hc] at this; exact_mod_cast this
    _ = _ := by
        rw [sum_const, sum_const, card_powersetCard, card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin]; simp [nsmul_eq_mul]; ring

/-- PER-PIECE BOUND (no key lemma needed). Under the true R_p on a piece's m variables:
  E[L(f|ρ)] ≤ m·p + (m(m-1)/2)·p²·L_W(f).
Reason: ≤ 1 surviving variable leaves size ≤ 1; ≥ 2 survive with probability ≤ C(m,2)p². -/
theorem piece_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset (Fin n)) (f)
    (hf : ∃ r, Rep W f r) :
    Ptrue p W f ≤ W.card * p + W.card * (W.card - 1) / 2 * p ^ 2 * LW W f := by
  rw [← Ep_eq_Ptrue, Ep]
  set m := W.card
  set L := (LW W f : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hterm : ∀ k ∈ range (m + 1), bw m k p * Eres (m - k) W f ≤
      bw m k p * k + bw m k p * (k : ℝ) ^ 2 / 2 * L - bw m k p * k / 2 * L := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hb := bw_nonneg m k hp0 hp1
    have hE : Eres (m - k) W f ≤ k + ((k : ℝ) ^ 2 - k) / 2 * L := by
      rcases Nat.lt_or_ge k 2 with h | h
      · have := Eres_small W f k (by omega) hkm
        have : (0 : ℝ) ≤ ((k : ℝ) ^ 2 - k) / 2 * L := by
          interval_cases k <;> norm_num
        linarith
      · have h1 := Eres_le_LW (m - k) W f hf
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast h
        have : L ≤ ((k : ℝ) ^ 2 - k) / 2 * L := by
          have : (1 : ℝ) ≤ ((k : ℝ) ^ 2 - k) / 2 := by nlinarith
          nlinarith
        have : (0 : ℝ) ≤ k := by positivity
        linarith
    have := mul_le_mul_of_nonneg_left hE hb
    linarith [show bw m k p * (k + ((k : ℝ) ^ 2 - k) / 2 * L)
      = bw m k p * k + bw m k p * (k : ℝ) ^ 2 / 2 * L - bw m k p * k / 2 * L by ring]
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [sum_sub_distrib, sum_add_distrib]
  have e1 := bw_mom1 m p; have e2 := bw_mom2 m p
  have s2 : ∑ k ∈ range (m + 1), bw m k p * (k : ℝ) ^ 2 / 2 * L
      = (∑ k ∈ range (m + 1), bw m k p * (k : ℝ) ^ 2) / 2 * L := by
    rw [sum_div, sum_mul]
  have s3 : ∑ k ∈ range (m + 1), bw m k p * k / 2 * L
      = (∑ k ∈ range (m + 1), bw m k p * k) / 2 * L := by
    rw [sum_div, sum_mul]
  rw [s2, s3, e1, e2]; ring

end Subb
