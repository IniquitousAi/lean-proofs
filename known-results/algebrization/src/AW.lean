import Mathlib
/-!
HHH: Aaronson-Wigderson 2009, "Algebrization", Section 4.2.1 (deterministic lower bounds).
Lemma 4.2, Lemma 4.3, Theorem 4.4 (adversary form), plus the general-n center-average formula
showing multilinear extensions are not enough for the 0/1 oracle form.
Polynomials are `MvPolynomial (Fin n) F`; multiquadratic means `degreeOf i p ≤ 2` for all i.
-/
namespace HHH.AW
open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Linear algebra core: a solution with many coordinates equal to 1. -/
theorem many_ones {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (col : ι → V) :
    ∃ x : ι → F, ∑ i, x i • col i = 0 ∧
      Fintype.card ι ≤ (univ.filter (fun i => x i = 1)).card + Module.finrank F V := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F col
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ ≤ Module.finrank F V := hli.fintype_card_le_finrank
  let w : V := ∑ i ∈ univ.filter (fun i => i ∉ Set.range a), col i
  have hw : w ∈ Submodule.span F (Set.range (col ∘ a)) := by
    rw [hsp]
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hw
  let x : ι → F := fun i => (if i ∈ Set.range a then 0 else 1) - ∑ k, c k * (Pi.single (a k) (1:F) : ι → F) i
  refine ⟨x, ?_, ?_⟩
  · simp only [x, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
    have h1 : ∑ i, (if i ∈ Set.range a then (0:F) else 1) • col i = w := by
      simp only [w, ite_smul, zero_smul, one_smul]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    have h2 : ∑ i, ∑ k, (c k * (Pi.single (a k) (1:F) : ι → F) i) • col i = ∑ k, c k • col (a k) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [mul_smul]
      rw [← Finset.smul_sum]
      congr 1
      rw [Finset.sum_eq_single (a k)]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    rw [h1, h2, ← hc]; simp
  · have hsub : univ.filter (fun i => x i ≠ 1) ⊆ (univ : Finset κ).image a := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hn
      apply hi
      have hn' : i ∉ Set.range a := by
        rintro ⟨k, rfl⟩; exact hn (Finset.mem_image_of_mem a (Finset.mem_univ k))
      have : ∀ k, (Pi.single (a k) (1:F) : ι → F) i = 0 := by
        intro k; rw [Pi.single_apply, if_neg]; rintro rfl; exact hn' ⟨k, rfl⟩
      have hn'' : ∀ k, ¬ a k = i := fun k hk => hn' ⟨k, hk⟩
      simp [x, hn'', this]
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ] at h3
    have h4 := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
      (fun i => x i = 1)
    rw [Finset.card_univ] at h4
    simp only [ne_eq] at h3
    omega

/-! ## Boolean points and the delta basis. -/
def bool (z : Fin n → Bool) : Fin n → F := fun i => if z i then 1 else 0

noncomputable def delta (z : Fin n → Bool) : MvPolynomial (Fin n) F :=
  ∏ i, (if z i then X i else 1 - X i)

lemma eval_delta_bool (z b : Fin n → Bool) :
    eval (bool b) (delta z : MvPolynomial (Fin n) F) = if z = b then 1 else 0 := by
  unfold delta bool
  rw [map_prod]
  split_ifs with h
  · subst h; exact Finset.prod_eq_one (fun i _ => by cases h : z i <;> simp [h])
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      cases hz : z i <;> cases hb : b i <;> simp_all)

lemma degreeOf_delta_le (z : Fin n → Bool) (i : Fin n) :
    degreeOf i (delta z : MvPolynomial (Fin n) F) ≤ 1 := by
  unfold delta
  refine (degreeOf_prod_le i _ _).trans ?_
  have : ∀ j, degreeOf i (if z j then X j else 1 - X j : MvPolynomial (Fin n) F) ≤
      if j = i then 1 else 0 := by
    intro j
    have hX : degreeOf i (X j : MvPolynomial (Fin n) F) ≤ if j = i then 1 else 0 := by
      rw [degreeOf_X]; split_ifs <;> simp_all
    by_cases hz : z j = true
    · rw [if_pos hz]; exact hX
    · rw [if_neg hz]
      refine (degreeOf_sub_le i _ _).trans (max_le ?_ hX)
      have : degreeOf i (1 : MvPolynomial (Fin n) F) = 0 := by
        rw [← C_1, degreeOf_C]
      omega
  calc ∑ j, degreeOf i (if z j then X j else 1 - X j : MvPolynomial (Fin n) F)
      ≤ ∑ j, (if j = i then 1 else 0) := Finset.sum_le_sum (fun j _ => this j)
    _ = 1 := by simp

/-- Multilinear polynomial with Boolean values `m` (the delta-basis form). -/
noncomputable def ext (m : (Fin n → Bool) → F) : MvPolynomial (Fin n) F :=
  ∑ z, C (m z) * delta z

lemma eval_ext_bool (m : (Fin n → Bool) → F) (b : Fin n → Bool) :
    eval (bool b) (ext m) = m b := by
  simp [ext, map_sum, eval_delta_bool]

lemma degreeOf_ext_le (m : (Fin n → Bool) → F) (i : Fin n) : degreeOf i (ext m) ≤ 1 := by
  unfold ext
  refine (degreeOf_sum_le i _ _).trans (Finset.sup_le (fun z _ => ?_))
  refine (degreeOf_mul_le i _ _).trans ?_
  simpa [degreeOf_C] using degreeOf_delta_le (F := F) z i

/-! ## Lemma 4.2 (AW): multilinear m, zero on t points, equal to 1 on ≥ 2^n - t Boolean points. -/
theorem lemma_4_2 {t : ℕ} (ys : Fin t → Fin n → F) :
    ∃ m : (Fin n → Bool) → F, (∀ i, eval (ys i) (ext m) = 0) ∧
      2 ^ n ≤ (univ.filter (fun z => eval (bool z) (ext m) = 1)).card + t := by
  classical
  obtain ⟨x, hx, hcard⟩ := many_ones (F := F)
    (fun z : Fin n → Bool => (fun i : Fin t => eval (ys i) (delta z : MvPolynomial (Fin n) F)))
  refine ⟨x, fun i => ?_, ?_⟩
  · have := congrFun hx i
    simpa [ext, map_sum, Finset.sum_apply] using this
  · simp only [eval_ext_bool]
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Module.finrank_fin_fun]
      using hcard

/-! ## Lemma 4.3 (AW): for ≥ 2^n - t Boolean w, a multiquadratic p, zero on the t points,
p(w) = 1, p(z) = 0 for every other Boolean z. -/
def IsGood {t : ℕ} (ys : Fin t → Fin n → F) (w : Fin n → Bool) : Prop :=
  ∃ p : MvPolynomial (Fin n) F, (∀ i, degreeOf i p ≤ 2) ∧ (∀ i, eval (ys i) p = 0) ∧
    eval (bool w) p = 1 ∧ ∀ z, z ≠ w → eval (bool z) p = 0

theorem lemma_4_3 {t : ℕ} (ys : Fin t → Fin n → F) :
    ∃ W : Finset (Fin n → Bool), 2 ^ n ≤ W.card + t ∧ ∀ w ∈ W, IsGood ys w := by
  classical
  obtain ⟨m, hm0, hmc⟩ := lemma_4_2 ys
  refine ⟨_, hmc, fun w hw => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  refine ⟨ext m * delta w, fun i => ?_, fun i => ?_, ?_, fun z hz => ?_⟩
  · exact (degreeOf_mul_le i _ _).trans (by
      have := degreeOf_ext_le m i; have := degreeOf_delta_le (F := F) w i; omega)
  · simp [hm0 i]
  · simp [hw, eval_delta_bool]
  · simp [eval_delta_bool, Ne.symm hz]

/-! ## Theorem 4.4 (AW), adversary form: an adaptive deterministic algorithm making T < 2^n
queries to a multiquadratic extension cannot decide OR. -/
/-- Answers after k queries: `next` picks the query from the answers so far. -/
def run (next : List F → (Fin n → F)) (O : (Fin n → F) → F) : ℕ → List F
  | 0 => []
  | k + 1 => run next O k ++ [O (next (run next O k))]

lemma run_zero_eq (next : List F → (Fin n → F)) (O : (Fin n → F) → F)
    (h : ∀ k, O (next (List.replicate k 0)) = 0) : ∀ k, run next O k = List.replicate k 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [run, ih, h k, List.replicate_succ']

theorem theorem_4_4 {T : ℕ} (hT : T < 2 ^ n) (next : List F → (Fin n → F))
    (out : List F → Bool) :
    ∃ p : MvPolynomial (Fin n) F, (∀ i, degreeOf i p ≤ 2) ∧
      (∀ z, eval (bool z) p = 0 ∨ eval (bool z) p = 1) ∧ (∃ w, eval (bool w) p = 1) ∧
      out (run next (fun y => eval y p) T) = out (run next (fun y => eval y (0 : MvPolynomial (Fin n) F)) T) := by
  classical
  obtain ⟨W, hW, hgood⟩ := lemma_4_3 (fun k : Fin T => next (List.replicate k.val 0))
  have hne : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at hW; omega
  obtain ⟨w, hw⟩ := hne
  obtain ⟨p, hdeg, hzero, h1, h0⟩ := hgood w hw
  refine ⟨p, hdeg, fun z => ?_, ⟨w, h1⟩, ?_⟩
  · by_cases hz : z = w
    · subst hz; exact Or.inr h1
    · exact Or.inl (h0 z hz)
  · -- both oracles answer 0 along the all-zero transcript for the first T queries
    have key : ∀ k ≤ T, run next (fun y => eval y p) k = List.replicate k 0 := by
      intro k
      induction k with
      | zero => intro; rfl
      | succ k ih =>
        intro hk
        have ihk := ih (by omega)
        simp only [run, ihk, List.replicate_succ']
        congr 2
        exact hzero ⟨k, by omega⟩
    rw [key T le_rfl, run_zero_eq next _ (fun k => by simp)]

/-! ## (a) Center-average formula: why multilinear is not enough. -/
theorem eval_ext_half (m : (Fin n → Bool) → ℚ) :
    eval (fun _ => (1/2 : ℚ)) (ext m) = (∑ z, m z) / 2 ^ n := by
  have hd : ∀ z : Fin n → Bool, eval (fun _ => (1/2 : ℚ)) (delta z) = (1/2) ^ n := by
    intro z; unfold delta; rw [map_prod]
    rw [Finset.prod_congr rfl (g := fun _ => (1/2 : ℚ))]
    · simp
    · intro i _; cases z i <;> norm_num
  simp only [ext, map_sum, map_mul, eval_C, hd]
  rw [← Finset.sum_mul, eq_div_iff (by positivity), mul_assoc, ← mul_pow]; norm_num

/-- Uniqueness: a multilinear polynomial is determined by its Boolean values. -/
theorem eq_ext_of_multilinear (q : MvPolynomial (Fin n) F) (hq : ∀ i, degreeOf i q ≤ 1) :
    q = ext (fun z => eval (bool z) q) := by
  classical
  rw [← sub_eq_zero]
  apply eq_zero_of_eval_zero_at_prod_finset _ (fun _ => {0, 1})
  · intro i
    have := degreeOf_sub_le i q (ext (fun z => eval (bool z) q))
    have h2 := degreeOf_ext_le (fun z => eval (bool z) q) i
    have h3 := hq i
    have : Finset.card ({0, 1} : Finset F) = 2 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    omega
  · intro x hx
    have hxb : x = bool (fun i => decide (x i = 1)) := by
      funext i
      have := hx i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h <;> simp [bool, h]
    rw [hxb, map_sub, eval_ext_bool, sub_self]

/-- General n: one query at the center decides "all zero" for 0/1-valued multilinear oracles. -/
theorem one_query_decides (q : MvPolynomial (Fin n) ℚ) (hq : ∀ i, degreeOf i q ≤ 1)
    (hb : ∀ z, eval (bool z) q = 0 ∨ eval (bool z) q = 1)
    (hc : eval (fun _ => (1/2 : ℚ)) q = 0) : ∀ z, eval (bool z) q = 0 := by
  rw [eq_ext_of_multilinear q hq, eval_ext_half] at hc
  have hs : ∑ z, eval (bool z) q = 0 := by
    have : (2:ℚ) ^ n ≠ 0 := by positivity
    field_simp at hc; linarith
  intro z
  have hnn : ∀ z ∈ (univ : Finset (Fin n → Bool)), 0 ≤ eval (bool z) q := by
    intro z _; rcases hb z with h | h <;> simp [h]
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs z (Finset.mem_univ z)

end HHH.AW
#print axioms HHH.AW.lemma_4_2
#print axioms HHH.AW.lemma_4_3
#print axioms HHH.AW.theorem_4_4
#print axioms HHH.AW.one_query_decides
