import Mathlib
import Relativization
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
/-! HHH: Aaronson-Wigderson Theorem 5.3 (NP^A not in P^Ã), query-machine form.
Appended after AW.lean by build53.sh (no separate lake package). -/
namespace HHH.AW
open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [Field F]

/-- Hiding polynomial: from Lemma 4.3, for t < 2^n queries. -/
theorem exists_hide {n t : ℕ} (ht : t < 2 ^ n) (ys : Fin t → Fin n → F) :
    ∃ p : MvPolynomial (Fin n) F, (∀ i, degreeOf i p ≤ 2) ∧ (∀ k, eval (ys k) p = 0) ∧
      (∀ z, eval (bool z) p = 0 ∨ eval (bool z) p = 1) ∧ ∃ w, eval (bool w) p = 1 := by
  obtain ⟨W, hW, hgood⟩ := lemma_4_3 ys
  have hne : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at hW; omega
  obtain ⟨w, hw⟩ := hne
  obtain ⟨p, hdeg, hzero, h1, h0⟩ := hgood w hw
  refine ⟨p, hdeg, hzero, fun z => ?_, ⟨w, h1⟩⟩
  by_cases hz : z = w
  · subst hz; exact Or.inr h1
  · exact Or.inl (h0 z hz)

/-- A query machine: on input 1^n it makes `time n` adaptive queries (length m, point y)
to the algebraic oracle and then outputs a bit. -/
structure QM (F : Type*) where
  time : ℕ → ℕ
  next : ℕ → List F → ℕ × (ℕ → F)
  out : ℕ → List F → Bool

abbrev Orc (F : Type*) := ℕ → (ℕ → F) → F

def ans (O : Orc F) (q : ℕ × (ℕ → F)) : F := O q.1 q.2

def runQ (M : QM F) (n : ℕ) (O : Orc F) : ℕ → List F
  | 0 => []
  | k + 1 => runQ M n O k ++ [ans O (M.next n (runQ M n O k))]

def qs (M : QM F) (n : ℕ) (O : Orc F) : ℕ → List (ℕ × (ℕ → F))
  | 0 => []
  | k + 1 => qs M n O k ++ [M.next n (runQ M n O k)]

lemma qs_length (M : QM F) (n : ℕ) (O : Orc F) (k : ℕ) : (qs M n O k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [qs, ih]

lemma runQ_congr (M : QM F) (n : ℕ) (O O' : Orc F) : ∀ k,
    (∀ q ∈ qs M n O k, ans O q = ans O' q) → runQ M n O' k = runQ M n O k := by
  intro k
  induction k with
  | zero => intro; rfl
  | succ k ih =>
    intro h
    have ih' := ih (fun q hq => h q (by simp [qs, hq]))
    have hl := h (M.next n (runQ M n O k)) (by simp [qs])
    simp only [runQ, ih', hl]

/-- Oracle from a family of polynomials, one per input length. -/
noncomputable def toOrc (P : (m : ℕ) → MvPolynomial (Fin m) F) : Orc F :=
  fun m y => eval (fun i : Fin m => y i) (P m)

structure St (F : Type*) [Field F] where
  b : ℕ
  P : (m : ℕ) → MvPolynomial (Fin m) F

variable (M : ℕ → QM F) (N : ℕ → ℕ) (hN : ∀ i n, N i ≤ n → (M i).time n < 2 ^ n)
include hN

/-- stage i data -/
noncomputable def stN (s : St F) (i : ℕ) : ℕ := max s.b (N i)
noncomputable def stQ (s : St F) (i : ℕ) : List (ℕ × (ℕ → F)) :=
  qs (M i) (stN N s i) (toOrc s.P) ((M i).time (stN N s i))
noncomputable def stOut (s : St F) (i : ℕ) : Bool :=
  (M i).out (stN N s i) (runQ (M i) (stN N s i) (toOrc s.P) ((M i).time (stN N s i)))
noncomputable def stQn (s : St F) (i : ℕ) : List (ℕ × (ℕ → F)) :=
  (stQ M N s i).filter (fun q => q.1 = stN N s i)
noncomputable def stYs (s : St F) (i : ℕ) :
    Fin (stQn M N s i).length → Fin (stN N s i) → F :=
  fun k j => ((stQn M N s i).get k).2 j

omit hN in
lemma stQn_lt (s : St F) (i : ℕ) (hN : ∀ i n, N i ≤ n → (M i).time n < 2 ^ n) :
    (stQn M N s i).length < 2 ^ (stN N s i) := by
  have h1 : (stQn M N s i).length ≤ (stQ M N s i).length := List.length_filter_le _ _
  rw [stQ, qs_length] at h1
  exact lt_of_le_of_lt h1 (hN i _ (le_max_right _ _))

noncomputable def stP (s : St F) (i : ℕ) : MvPolynomial (Fin (stN N s i)) F :=
  Classical.choose (exists_hide (stQn_lt M N s i hN) (stYs M N s i))

lemma stP_spec (s : St F) (i : ℕ) :
    (∀ j, degreeOf j (stP M N hN s i) ≤ 2) ∧ (∀ k, eval (stYs M N s i k) (stP M N hN s i) = 0) ∧
      (∀ z, eval (bool z) (stP M N hN s i) = 0 ∨ eval (bool z) (stP M N hN s i) = 1) ∧
      ∃ w, eval (bool w) (stP M N hN s i) = 1 :=
  Classical.choose_spec (exists_hide (stQn_lt M N s i hN) (stYs M N s i))

noncomputable def step (s : St F) (i : ℕ) : St F where
  b := stN N s i + 1 + ((stQ M N s i).map Prod.fst).sum
  P := if stOut M N s i = true then s.P else Function.update s.P (stN N s i) (stP M N hN s i)

noncomputable def st : ℕ → St F
  | 0 => ⟨0, fun _ => 0⟩
  | i + 1 => step M N hN (st i) i

lemma step_P_ne (s : St F) (i m : ℕ) (hm : m ≠ stN N s i) :
    (step M N hN s i).P m = s.P m := by
  unfold step; split_ifs <;> simp [Function.update_of_ne hm]

lemma step_P_true (s : St F) (i m : ℕ) (ho : stOut M N s i = true) :
    (step M N hN s i).P m = s.P m := by
  unfold step; simp [ho]

lemma step_P_at (s : St F) (i : ℕ) (ho : ¬ stOut M N s i = true) :
    (step M N hN s i).P (stN N s i) = stP M N hN s i := by
  unfold step; simp [ho]

lemma b_lt (i : ℕ) : (st M N hN i).b < (st M N hN (i+1)).b := by
  show (st M N hN i).b < (step M N hN (st M N hN i) i).b
  simp only [step, stN]; omega

lemma b_ge (i : ℕ) : i ≤ (st M N hN i).b := by
  induction i with
  | zero => simp
  | succ i ih => have := b_lt M N hN i; omega

lemma b_mono {i j : ℕ} (h : i ≤ j) : (st M N hN i).b ≤ (st M N hN j).b := by
  induction j, h using Nat.le_induction with
  | base => exact le_refl _
  | succ j _ ih => exact ih.trans (b_lt M N hN j).le

lemma frozen (i : ℕ) (m : ℕ) (hm : m < (st M N hN i).b) :
    ∀ j, i ≤ j → (st M N hN j).P m = (st M N hN i).P m := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    show (step M N hN (st M N hN j) j).P m = _
    rw [step_P_ne]
    · exact ih
    · have := b_mono M N hN hij
      have : (st M N hN j).b ≤ stN N (st M N hN j) j := le_max_left _ _
      omega

lemma zero_above (i m : ℕ) (hm : (st M N hN i).b ≤ m) : (st M N hN i).P m = 0 := by
  induction i generalizing m with
  | zero => rfl
  | succ i ih =>
    show (step M N hN (st M N hN i) i).P m = 0
    have h1 : stN N (st M N hN i) i < (st M N hN (i+1)).b := by
      show _ < (step M N hN (st M N hN i) i).b; simp only [step]; omega
    rw [step_P_ne _ _ _ _ _ _ (by omega)]
    exact ih m (by have := b_lt M N hN i; omega)

/-- The final oracle. -/
noncomputable def Pf (m : ℕ) : MvPolynomial (Fin m) F := (st M N hN (m+1)).P m

lemma Pf_eq (j m : ℕ) (hm : m < (st M N hN j).b) : Pf M N hN m = (st M N hN j).P m := by
  unfold Pf
  rcases le_total j (m+1) with h | h
  · exact frozen M N hN j m hm _ h
  · exact (frozen M N hN (m+1) m (by have := b_ge M N hN (m+1); omega) j h).symm

def Good {m : ℕ} (q : MvPolynomial (Fin m) F) : Prop :=
  (∀ j, degreeOf j q ≤ 2) ∧ ∀ z, eval (bool z) q = 0 ∨ eval (bool z) q = 1

omit hN in
lemma good_zero (m : ℕ) : Good (0 : MvPolynomial (Fin m) F) := ⟨fun j => by simp, fun z => by simp⟩

lemma st_good (i m : ℕ) : Good ((st M N hN i).P m) := by
  induction i generalizing m with
  | zero => exact good_zero m
  | succ i ih =>
    show Good ((step M N hN (st M N hN i) i).P m)
    by_cases hm : m = stN N (st M N hN i) i
    · subst hm
      unfold step
      split_ifs
      · exact ih _
      · simp only [Function.update_self]
        obtain ⟨h1, -, h3, -⟩ := stP_spec M N hN (st M N hN i) i
        exact ⟨h1, h3⟩
    · rw [step_P_ne _ _ _ _ _ _ hm]; exact ih m

/-- The stage lemma: machine i errs on input length n_i under the final oracle. -/
theorem stage_wins (i : ℕ) :
    ((M i).out (stN N (st M N hN i) i) (runQ (M i) (stN N (st M N hN i) i) (toOrc (Pf M N hN))
      ((M i).time (stN N (st M N hN i) i))) = true ↔
      ¬ ∃ z, eval (bool z) (Pf M N hN (stN N (st M N hN i) i)) = 1) := by
  set s := st M N hN i with hs
  set n := stN N s i with hn
  have hb : (st M N hN (i+1)).b = n + 1 + ((stQ M N s i).map Prod.fst).sum := rfl
  have hnb : n < (st M N hN (i+1)).b := by rw [hb]; omega
  have hsb : s.b ≤ n := le_max_left _ _
  -- the new state's oracle agrees with the old one on every query of the run
  have hA : ∀ q ∈ stQ M N s i, ans (toOrc s.P) q = ans (toOrc (st M N hN (i+1)).P) q := by
    intro q hq
    show ans (toOrc s.P) q = ans (toOrc (step M N hN s i).P) q
    by_cases hqn : q.1 = n
    · have h0 : s.P n = 0 := zero_above M N hN i n hsb
      unfold ans toOrc
      rw [hqn, h0]
      by_cases ho : stOut M N s i = true
      · rw [step_P_true M N hN s i n ho, h0]
      · rw [step_P_at M N hN s i ho, map_zero]
        have hmem : q ∈ stQn M N s i := List.mem_filter.mpr ⟨hq, by simpa using hqn⟩
        obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
        have := (stP_spec M N hN s i).2.1 k
        have hy : (stYs M N s i k) = fun j : Fin (stN N s i) => q.2 j := by funext j; show ((stQn M N s i).get k).2 j = q.2 j; rw [hk]
        rw [hy] at this
        first | exact this.symm | exact this
    · unfold ans toOrc
      rw [step_P_ne _ _ _ _ _ _ hqn]
  -- the final oracle agrees with the new state's oracle on every query of the run
  have hB : ∀ q ∈ stQ M N s i, ans (toOrc (st M N hN (i+1)).P) q = ans (toOrc (Pf M N hN)) q := by
    intro q hq
    unfold ans toOrc
    have hlt : q.1 < (st M N hN (i+1)).b := by
      rw [hb]
      have : q.1 ≤ ((stQ M N s i).map Prod.fst).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hq)
      omega
    rw [Pf_eq M N hN (i+1) q.1 hlt]
  have hrun : runQ (M i) n (toOrc (Pf M N hN)) ((M i).time n) =
      runQ (M i) n (toOrc s.P) ((M i).time n) :=
    runQ_congr _ _ _ _ _ (fun q hq => (hA q hq).trans (hB q hq))
  rw [hrun]
  have hPf : Pf M N hN n = (st M N hN (i+1)).P n := Pf_eq M N hN (i+1) n hnb
  rw [hPf]
  show stOut M N s i = true ↔ ¬∃ z, eval (bool z) ((step M N hN s i).P n) = 1
  by_cases ho : stOut M N s i = true
  · simp only [ho, true_iff]
    rw [step_P_true M N hN s i n ho, zero_above M N hN i n hsb]; simp
  · simp only [ho, Bool.false_eq_true, false_iff, not_not]
    rw [step_P_at M N hN s i ho]
    exact (stP_spec M N hN s i).2.2.2

/-- AW Theorem 5.3, query-machine form, one field F: for any sequence of query machines whose
query count is eventually below 2^n, there is a family of multiquadratic polynomials Ã_m
(Boolean 0/1 on {0,1}^m, so they extend Boolean A_m) such that every machine, given Ã,
fails to decide L(n) = "∃ w ∈ {0,1}^n, A_n(w) = 1" on some input length. -/
theorem theorem_5_3_query (M : ℕ → QM F) (hM : ∀ i, ∃ N, ∀ n, N ≤ n → (M i).time n < 2 ^ n) :
    ∃ P : (m : ℕ) → MvPolynomial (Fin m) F,
      (∀ m, (∀ j, degreeOf j (P m) ≤ 2) ∧ ∀ z, eval (bool z) (P m) = 0 ∨ eval (bool z) (P m) = 1) ∧
      ∀ i, ∃ n, ((M i).out n (runQ (M i) n (toOrc P) ((M i).time n)) = true ↔
        ¬ ∃ z, eval (bool z) (P n) = 1) := by
  choose N hN using hM
  exact ⟨Pf M N hN, fun m => st_good M N hN (m+1) m, fun i => ⟨_, stage_wins M N hN i⟩⟩

end HHH.AW
/-! HHH: AW Lemma 4.5 core (all fields at once) and Theorem 5.3 over a family of fields.
Appended after AW.lean + AW53.lean by build45.sh. -/
namespace HHH.AWB
open HHH.AW
open MvPolynomial Finset
open scoped Classical

/-- Lemma 4.5, core claim ("at least 2^n - t good points", t = total queries over all fields):
for a family of fields, at least 2^n - t Boolean points are good for every field at once. -/
theorem lemma_4_5_good {κ : Type*} (Fk : κ → Type*) [∀ k, Field (Fk k)] {n : ℕ}
    (S : Finset κ) (t : κ → ℕ) (ys : ∀ k, Fin (t k) → Fin n → Fk k) (h0 : ∀ k ∉ S, t k = 0) :
    ∃ G : Finset (Fin n → Bool), 2 ^ n ≤ G.card + ∑ k ∈ S, t k ∧
      ∀ w ∈ G, ∀ k, IsGood (ys k) w := by
  choose W hW hgood using fun k => lemma_4_3 (ys k)
  let bad := S.biUnion (fun k => univ \ W k)
  refine ⟨univ \ bad, ?_, ?_⟩
  · have h1 : bad.card ≤ ∑ k ∈ S, t k := by
      refine (card_biUnion_le).trans (Finset.sum_le_sum (fun k _ => ?_))
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin]
      have := hW k; omega
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    have : bad.card ≤ 2 ^ n := by
      have := card_le_univ bad; simpa [Fintype.card_fun] using this
    omega
  · intro w hw k
    simp only [mem_sdiff, mem_univ, true_and, bad, mem_biUnion, not_exists, not_and] at hw
    apply hgood k
    by_cases hk : k ∈ S
    · have := hw k hk; simpa using this
    · have hc : (W k).card = Fintype.card (Fin n → Bool) := by
        have := hW k; rw [h0 k hk] at this
        have := card_le_univ (W k)
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at *; omega
      rw [eq_univ_of_card _ hc]; exact mem_univ w

/-! ## Multi-field query machines. A query is (field index k, length m, point in Fk k). -/
variable {κ : Type*} (Fk : κ → Type*) [∀ k, Field (Fk k)]

abbrev MQ := Σ k, ℕ × (ℕ → Fk k)
abbrev MA := Σ k, Fk k

structure QMM where
  time : ℕ → ℕ
  next : ℕ → List (MA Fk) → MQ Fk
  out : ℕ → List (MA Fk) → Bool

abbrev MOrc := ∀ k, ℕ → (ℕ → Fk k) → Fk k

def mans (O : MOrc Fk) (q : MQ Fk) : MA Fk := ⟨q.1, O q.1 q.2.1 q.2.2⟩

variable {Fk}

def mrun (M : QMM Fk) (n : ℕ) (O : MOrc Fk) : ℕ → List (MA Fk)
  | 0 => []
  | k + 1 => mrun M n O k ++ [mans Fk O (M.next n (mrun M n O k))]

def mqs (M : QMM Fk) (n : ℕ) (O : MOrc Fk) : ℕ → List (MQ Fk)
  | 0 => []
  | k + 1 => mqs M n O k ++ [M.next n (mrun M n O k)]

lemma mqs_length (M : QMM Fk) (n : ℕ) (O : MOrc Fk) (k : ℕ) : (mqs M n O k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [mqs, ih]

lemma mrun_congr (M : QMM Fk) (n : ℕ) (O O' : MOrc Fk) : ∀ k,
    (∀ q ∈ mqs M n O k, mans Fk O q = mans Fk O' q) → mrun M n O' k = mrun M n O k := by
  intro k
  induction k with
  | zero => intro; rfl
  | succ k ih =>
    intro h
    have ih' := ih (fun q hq => h q (by simp [mqs, hq]))
    have hl := h (M.next n (mrun M n O k)) (by simp [mqs])
    simp only [mrun, ih', hl]

noncomputable def mOrc (P : ∀ k, (m : ℕ) → MvPolynomial (Fin m) (Fk k)) : MOrc Fk :=
  fun k m y => eval (fun i : Fin m => y i) (P k m)

structure MSt (Fk : κ → Type*) [∀ k, Field (Fk k)] where
  b : ℕ
  P : ∀ k, (m : ℕ) → MvPolynomial (Fin m) (Fk k)
  A : (m : ℕ) → (Fin m → Bool) → Bool

variable (M : ℕ → QMM Fk) (N : ℕ → ℕ) (hN : ∀ i n, N i ≤ n → (M i).time n < 2 ^ n)
include hN

noncomputable def mN (s : MSt Fk) (i : ℕ) : ℕ := max s.b (N i)
noncomputable def mQ (s : MSt Fk) (i : ℕ) : List (MQ Fk) :=
  mqs (M i) (mN N s i) (mOrc s.P) ((M i).time (mN N s i))
noncomputable def mOut (s : MSt Fk) (i : ℕ) : Bool :=
  (M i).out (mN N s i) (mrun (M i) (mN N s i) (mOrc s.P) ((M i).time (mN N s i)))
/-- length-n queries in field k -/
noncomputable def mQk (s : MSt Fk) (i : ℕ) (k : κ) : List (MQ Fk) :=
  (mQ M N s i).filter (fun q => q.2.1 = mN N s i ∧ q.1 = k)
noncomputable def mYs (s : MSt Fk) (i : ℕ) (k : κ) :
    Fin (mQk M N s i k).length → Fin (mN N s i) → Fk k :=
  fun j x => cast (congrArg Fk (by
    have := List.get_mem (mQk M N s i k) j
    simp only [mQk, List.mem_filter, decide_eq_true_eq] at this
    exact this.2.2)) (((mQk M N s i k).get j).2.2 x)

omit hN in
lemma mQk_sum (s : MSt Fk) (i : ℕ) :
    ∑ k ∈ ((mQ M N s i).map Sigma.fst).toFinset, (mQk M N s i k).length ≤ (mQ M N s i).length := by
  calc ∑ k ∈ ((mQ M N s i).map Sigma.fst).toFinset, (mQk M N s i k).length
      ≤ ∑ k ∈ ((mQ M N s i).map Sigma.fst).toFinset, ((mQ M N s i).map Sigma.fst).count k := by
        apply Finset.sum_le_sum; intro k _
        rw [List.count, List.countP_map, List.countP_eq_length_filter]
        apply List.Sublist.length_le
        apply List.monotone_filter_right
        intro q hq; simp only [decide_eq_true_eq] at hq ⊢; simp [Function.comp, hq.2]
    _ = (mQ M N s i).length := by rw [List.sum_toFinset_count_eq_length, List.length_map]

lemma m_exists_good (s : MSt Fk) (i : ℕ) : ∃ w, ∀ k, IsGood (mYs M N s i k) w := by
  obtain ⟨G, hG, hgood⟩ := lemma_4_5_good Fk ((mQ M N s i).map Sigma.fst).toFinset
    (fun k => (mQk M N s i k).length) (mYs M N s i) (by
      intro k hk
      rw [List.length_eq_zero_iff]; unfold mQk; rw [List.filter_eq_nil_iff]
      intro q hq hc
      simp only [decide_eq_true_eq] at hc
      exact hk (List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, hc.2⟩)))
  have hlt : ∑ k ∈ ((mQ M N s i).map Sigma.fst).toFinset, (mQk M N s i k).length < 2 ^ (mN N s i) := by
    refine lt_of_le_of_lt (mQk_sum M N s i) ?_
    rw [mQ, mqs_length]; exact hN i _ (le_max_right _ _)
  have : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at hG; omega
  obtain ⟨w, hw⟩ := this
  exact ⟨w, hgood w hw⟩

noncomputable def mW (s : MSt Fk) (i : ℕ) : Fin (mN N s i) → Bool :=
  Classical.choose (m_exists_good M N hN s i)
noncomputable def mPk (s : MSt Fk) (i : ℕ) (k : κ) : MvPolynomial (Fin (mN N s i)) (Fk k) :=
  Classical.choose (Classical.choose_spec (m_exists_good M N hN s i) k)
lemma mPk_spec (s : MSt Fk) (i : ℕ) (k : κ) :
    (∀ j, degreeOf j (mPk M N hN s i k) ≤ 2) ∧ (∀ j, eval (mYs M N s i k j) (mPk M N hN s i k) = 0) ∧
    eval (HHH.AW.bool (mW M N hN s i)) (mPk M N hN s i k) = 1 ∧
    ∀ z, z ≠ mW M N hN s i → eval (HHH.AW.bool z) (mPk M N hN s i k) = 0 :=
  Classical.choose_spec (Classical.choose_spec (m_exists_good M N hN s i) k)

noncomputable def mstep (s : MSt Fk) (i : ℕ) : MSt Fk where
  b := 2 * mN N s i + 1 + ((mQ M N s i).map (fun q => q.2.1)).sum
  P := if mOut M N s i = true then s.P else
    fun k => Function.update (s.P k) (mN N s i) (mPk M N hN s i k)
  A := if mOut M N s i = true then s.A else
    Function.update s.A (mN N s i) (fun z => decide (z = mW M N hN s i))

noncomputable def mst : ℕ → MSt Fk
  | 0 => ⟨0, fun _ _ => 0, fun _ _ => false⟩
  | i + 1 => mstep M N hN (mst i) i

lemma mstep_ne (s : MSt Fk) (i m : ℕ) (hm : m ≠ mN N s i) :
    (∀ k, (mstep M N hN s i).P k m = s.P k m) ∧ (mstep M N hN s i).A m = s.A m := by
  unfold mstep; split_ifs <;> simp [Function.update_of_ne hm]

lemma mstep_true (s : MSt Fk) (i : ℕ) (ho : mOut M N s i = true) :
    (mstep M N hN s i).P = s.P ∧ (mstep M N hN s i).A = s.A := by
  unfold mstep; simp [ho]

lemma mstep_at (s : MSt Fk) (i : ℕ) (ho : ¬ mOut M N s i = true) :
    (∀ k, (mstep M N hN s i).P k (mN N s i) = mPk M N hN s i k) ∧
    (mstep M N hN s i).A (mN N s i) = fun z => decide (z = mW M N hN s i) := by
  unfold mstep; simp [ho]

lemma mb_lt (i : ℕ) : (mst M N hN i).b < (mst M N hN (i+1)).b := by
  show (mst M N hN i).b < (mstep M N hN (mst M N hN i) i).b
  simp only [mstep, mN]; omega

lemma mb_ge (i : ℕ) : i ≤ (mst M N hN i).b := by
  induction i with
  | zero => simp
  | succ i ih => have := mb_lt M N hN i; omega

lemma mb_mono {i j : ℕ} (h : i ≤ j) : (mst M N hN i).b ≤ (mst M N hN j).b := by
  induction j, h using Nat.le_induction with
  | base => exact le_refl _
  | succ j _ ih => exact ih.trans (mb_lt M N hN j).le

lemma mfrozen (i m : ℕ) (hm : m < (mst M N hN i).b) : ∀ j, i ≤ j →
    (∀ k, (mst M N hN j).P k m = (mst M N hN i).P k m) ∧ (mst M N hN j).A m = (mst M N hN i).A m := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact ⟨fun _ => rfl, rfl⟩
  | succ j hij ih =>
    have hne : m ≠ mN N (mst M N hN j) j := by
      have := mb_mono M N hN hij
      have : (mst M N hN j).b ≤ mN N (mst M N hN j) j := le_max_left _ _
      omega
    obtain ⟨h1, h2⟩ := mstep_ne M N hN (mst M N hN j) j m hne
    exact ⟨fun k => (h1 k).trans (ih.1 k), h2.trans ih.2⟩

lemma mzero_above (i m : ℕ) (hm : (mst M N hN i).b ≤ m) :
    (∀ k, (mst M N hN i).P k m = 0) ∧ (mst M N hN i).A m = fun _ => false := by
  induction i generalizing m with
  | zero => exact ⟨fun _ => rfl, rfl⟩
  | succ i ih =>
    have h1 : mN N (mst M N hN i) i < (mst M N hN (i+1)).b := by
      show _ < (mstep M N hN (mst M N hN i) i).b; simp only [mstep]; omega
    obtain ⟨e1, e2⟩ := mstep_ne M N hN (mst M N hN i) i m (by omega)
    have ih' := ih m (by have := mb_lt M N hN i; omega)
    exact ⟨fun k => (e1 k).trans (ih'.1 k), e2.trans ih'.2⟩

noncomputable def mPf (k : κ) (m : ℕ) : MvPolynomial (Fin m) (Fk k) := (mst M N hN (m+1)).P k m
noncomputable def mAf (m : ℕ) : (Fin m → Bool) → Bool := (mst M N hN (m+1)).A m

lemma mPf_eq (j m : ℕ) (hm : m < (mst M N hN j).b) :
    (∀ k, mPf M N hN k m = (mst M N hN j).P k m) ∧ mAf M N hN m = (mst M N hN j).A m := by
  unfold mPf mAf
  rcases le_total j (m+1) with h | h
  · exact mfrozen M N hN j m hm _ h
  · have := mfrozen M N hN (m+1) m (by have := mb_ge M N hN (m+1); omega) j h
    exact ⟨fun k => (this.1 k).symm, this.2.symm⟩

/-- invariant: every field's polynomial is multiquadratic and extends the same Boolean A. -/
lemma mst_good (i m : ℕ) : ∀ k, (∀ j, degreeOf j ((mst M N hN i).P k m) ≤ 2) ∧
    ∀ z, eval (HHH.AW.bool z) ((mst M N hN i).P k m) = if (mst M N hN i).A m z then 1 else 0 := by
  induction i generalizing m with
  | zero => intro k; exact ⟨fun j => by simp [mst], fun z => by simp [mst]⟩
  | succ i ih =>
    intro k
    show (∀ j, degreeOf j ((mstep M N hN (mst M N hN i) i).P k m) ≤ 2) ∧
      ∀ z, eval (HHH.AW.bool z) ((mstep M N hN (mst M N hN i) i).P k m) =
        if (mstep M N hN (mst M N hN i) i).A m z then 1 else 0
    by_cases ho : mOut M N (mst M N hN i) i = true
    · obtain ⟨e1, e2⟩ := mstep_true M N hN (mst M N hN i) i ho
      rw [e1, e2]; exact ih m k
    · by_cases hm : m = mN N (mst M N hN i) i
      · subst hm
        obtain ⟨e1, e2⟩ := mstep_at M N hN (mst M N hN i) i ho
        rw [e1 k, e2]
        obtain ⟨d, -, h1, h0⟩ := mPk_spec M N hN (mst M N hN i) i k
        refine ⟨d, fun z => ?_⟩
        by_cases hz : z = mW M N hN (mst M N hN i) i
        · subst hz; simp [h1]
        · simp [hz, h0 z hz]
      · obtain ⟨e1, e2⟩ := mstep_ne M N hN (mst M N hN i) i m hm
        rw [e1 k, e2]; exact ih m k

theorem mstage_wins (i : ℕ) :
    ((M i).out (mN N (mst M N hN i) i) (mrun (M i) (mN N (mst M N hN i) i) (mOrc (mPf M N hN))
      ((M i).time (mN N (mst M N hN i) i))) = true ↔
      ¬ ∃ z, mAf M N hN (mN N (mst M N hN i) i) z = true) := by
  set s := mst M N hN i with hs
  set n := mN N s i with hn
  have hb : (mst M N hN (i+1)).b = 2 * n + 1 + ((mQ M N s i).map (fun q => q.2.1)).sum := rfl
  have hnb : n < (mst M N hN (i+1)).b := by rw [hb]; omega
  have hsb : s.b ≤ n := le_max_left _ _
  have hz0 := mzero_above M N hN i n hsb
  have hA : ∀ q ∈ mQ M N s i, mans Fk (mOrc s.P) q = mans Fk (mOrc (mst M N hN (i+1)).P) q := by
    intro q hq
    show mans Fk (mOrc s.P) q = mans Fk (mOrc (mstep M N hN s i).P) q
    obtain ⟨k, m, y⟩ := q
    unfold mans mOrc
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    by_cases hqn : m = n
    · subst hqn
      rw [hz0.1 k, map_zero]
      by_cases ho : mOut M N s i = true
      · rw [(mstep_true M N hN s i ho).1, hz0.1 k, map_zero]
      · rw [(mstep_at M N hN s i ho).1 k]
        have hmem : (⟨k, mN N s i, y⟩ : MQ Fk) ∈ mQk M N s i k :=
          List.mem_filter.mpr ⟨hq, by simp⟩
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
        have := (mPk_spec M N hN s i k).2.1 j
        have hy : mYs M N s i k j = fun x : Fin (mN N s i) => y x := by
          funext x
          unfold mYs
          have e : ((mQk M N s i k).get j) = ⟨k, mN N s i, y⟩ := hj
          rw [cast_eq_iff_heq]
          rw [e]
        rw [hy] at this; exact this.symm
    · rw [(mstep_ne M N hN s i m hqn).1 k]
  have hB : ∀ q ∈ mQ M N s i, mans Fk (mOrc (mst M N hN (i+1)).P) q = mans Fk (mOrc (mPf M N hN)) q := by
    intro q hq
    have hlt : q.2.1 < (mst M N hN (i+1)).b := by
      rw [hb]
      have : q.2.1 ≤ ((mQ M N s i).map (fun q => q.2.1)).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hq)
      omega
    unfold mans mOrc
    rw [(mPf_eq M N hN (i+1) q.2.1 hlt).1 q.1]
  have hrun : mrun (M i) n (mOrc (mPf M N hN)) ((M i).time n) =
      mrun (M i) n (mOrc s.P) ((M i).time n) :=
    mrun_congr _ _ _ _ _ (fun q hq => (hA q hq).trans (hB q hq))
  rw [hrun, (mPf_eq M N hN (i+1) n hnb).2]
  show mOut M N s i = true ↔ ¬∃ z, (mstep M N hN s i).A n z = true
  by_cases ho : mOut M N s i = true
  · simp only [ho, true_iff]
    rw [(mstep_true M N hN s i ho).2, hz0.2]; simp
  · simp only [ho, Bool.false_eq_true, false_iff, not_not]
    rw [(mstep_at M N hN s i ho).2]
    exact ⟨mW M N hN s i, by simp⟩

/-- AW Theorem 5.3 over an arbitrary family of fields (e.g. all finite fields GaloisField p k),
query-machine form: one Boolean oracle A and, for EVERY field in the family, a multiquadratic
extension Ã_{m,F} of A_m, such that every machine (querying any fields it likes, total
queries eventually < 2^n) is wrong on L(n) = ∃ w, A_n(w) at some n. -/
theorem theorem_5_3_allfields (M : ℕ → QMM Fk) (hM : ∀ i, ∃ N, ∀ n, N ≤ n → (M i).time n < 2 ^ n) :
    ∃ (A : (m : ℕ) → (Fin m → Bool) → Bool) (P : ∀ k, (m : ℕ) → MvPolynomial (Fin m) (Fk k)),
      (∀ k m, (∀ j, degreeOf j (P k m) ≤ 2) ∧ ∀ z, eval (HHH.AW.bool z) (P k m) = if A m z then 1 else 0) ∧
      ∀ i, ∃ n, ((M i).out n (mrun (M i) n (mOrc P) ((M i).time n)) = true ↔ ¬ ∃ z, A n z = true) := by
  choose N hN using hM
  refine ⟨mAf M N hN, mPf M N hN, fun k m => ?_, fun i => ⟨_, mstage_wins M N hN i⟩⟩
  exact mst_good M N hN (m+1) m k

noncomputable def nAt (j : ℕ) : ℕ := mN N (mst M N hN j) j

lemma b_succ_ge (j : ℕ) : 2 * nAt M N hN j + 1 ≤ (mst M N hN (j+1)).b := by
  show _ ≤ (mstep M N hN (mst M N hN j) j).b
  simp only [mstep, nAt]; omega

lemma nAt_ge_b (j : ℕ) : (mst M N hN j).b ≤ nAt M N hN j := le_max_left _ _

lemma nAt_spread {j i : ℕ} (h : j < i) : 2 * nAt M N hN j < nAt M N hN i := by
  have h1 := b_succ_ge M N hN j
  have h2 := mb_mono M N hN (show j + 1 ≤ i from h)
  have h3 := nAt_ge_b M N hN i
  omega

lemma mA_support (i : ℕ) : ∀ m z, (mst M N hN i).A m z = true → ∃ j < i, m = nAt M N hN j := by
  induction i with
  | zero => intro m z h; simp [mst] at h
  | succ i ih =>
    intro m z h
    by_cases hm : m = mN N (mst M N hN i) i
    · exact ⟨i, Nat.lt_succ_self i, hm⟩
    · have e := (mstep_ne M N hN (mst M N hN i) i m hm).2
      have h' : (mst M N hN i).A m z = true := by
        have : (mst M N hN (i+1)).A m z = (mst M N hN i).A m z := congrFun e z
        rw [← this]; exact h
      obtain ⟨j, hj, hj'⟩ := ih m z h'
      exact ⟨j, by omega, hj'⟩

lemma mAf_support (m : ℕ) (z : Fin m → Bool) (h : mAf M N hN m z = true) : ∃ j, m = nAt M N hN j := by
  obtain ⟨j, -, hj⟩ := mA_support M N hN (m+1) m z h; exact ⟨j, hj⟩

end HHH.AWB

namespace HHH.AWB
open HHH.AW MvPolynomial
/-- Theorem 5.3 (query form) with the stage lengths exposed: they are spread (n_{j+1} > 2 n_j),
A is zero off them, and machine i is wrong at n_i >= N i. -/
theorem theorem_5_3_spread {κ : Type*} {Fk : κ → Type*} [∀ k, Field (Fk k)] (M : ℕ → QMM Fk)
    (N : ℕ → ℕ) (hN : ∀ i n, N i ≤ n → (M i).time n < 2 ^ n) :
    ∃ (nA : ℕ → ℕ) (A : (m : ℕ) → (Fin m → Bool) → Bool) (P : ∀ k, (m : ℕ) → MvPolynomial (Fin m) (Fk k)),
      (∀ k m, (∀ j, degreeOf j (P k m) ≤ 2) ∧ ∀ z, eval (HHH.AW.bool z) (P k m) = if A m z then 1 else 0) ∧
      (∀ j i, j < i → 2 * nA j < nA i) ∧ (∀ m z, A m z = true → ∃ j, m = nA j) ∧
      ∀ i, ((M i).out (nA i) (mrun (M i) (nA i) (mOrc P) ((M i).time (nA i))) = true ↔
        ¬ ∃ z, A (nA i) z = true) :=
  ⟨nAt M N hN, mAf M N hN, mPf M N hN, fun k m => mst_good M N hN (m+1) m k,
    fun _ _ h => nAt_spread M N hN h, mAf_support M N hN, mstage_wins M N hN⟩
end HHH.AWB
namespace HHH.Bridge
open Relativization Turing HHH.AW HHH.AWB MvPolynomial Millennium
open scoped Classical

abbrev GFIdx := Σ _p : {p : ℕ // p.Prime}, ℕ
noncomputable abbrev GF (x : GFIdx) : Type := @GaloisField x.1.1 ⟨x.1.2⟩ x.2
noncomputable instance (x : GFIdx) : Field (GF x) := by
  letI : Fact x.1.1.Prime := ⟨x.1.2⟩; unfold GF; infer_instance

/-- Every finite field is isomorphic to some GaloisField p n (closes the GF-index gap). -/
theorem finite_field_iso_galois (K : Type*) [Field K] [Fintype K] :
    ∃ x : GFIdx, Nonempty (K ≃+* GF x) := by
  obtain ⟨p, hc⟩ := CharP.exists K
  obtain ⟨n, hp, hK⟩ := FiniteField.card K p
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine ⟨⟨⟨p, hp⟩, n⟩, ⟨FiniteField.ringEquivOfCardEq ?_⟩⟩
  rw [hK, ← Nat.card_eq_fintype_card, GaloisField.card p n n.ne_zero]

variable {κ : Type} {Fk : κ → Type} [∀ k, Field (Fk k)]

/-- Step 1: an encoding of field queries as bit strings, left abstract (any scheme works):
`dec s = some (q, i)` means "string s asks for bit i of the answer to field query q". -/
structure Enc (Fk : κ → Type) [∀ k, Field (Fk k)] where
  dec : List Bool → Option (MQ Fk × ℕ)
  bit : MA Fk → ℕ → Bool
  dummy : MQ Fk

def qOf (E : Enc Fk) (s : List Bool) : MQ Fk :=
  match E.dec s with | some (q, _) => q | none => E.dummy

def bitAns (E : Enc Fk) (s : List Bool) (a : MA Fk) : Bool :=
  match E.dec s with | some (_, i) => E.bit a i | none => false

/-- The Boolean oracle a BGS machine sees: bit-encoding of the field oracle O. -/
def Aenc (E : Enc Fk) (O : MOrc Fk) : Oracle := {s | bitAns E s (mans Fk O (qOf E s)) = true}

variable (E : Enc Fk) (tm : OracleFinTM2)

noncomputable def stepW (b : Bool) (c : tm.Cfg) : Option tm.Cfg := TM2.step (fun l => tm.m l b) c

lemma step_eq (A : Oracle) (c : tm.Cfg) : tm.step A c = stepW tm (decide (tm.query c ∈ A)) c := rfl

/-- Replay a TM from the list of field answers seen so far. -/
noncomputable def replay (inp : List (tm.Γ tm.k₀)) (as : List (MA Fk)) : Option tm.Cfg :=
  as.foldl (fun oc a => oc.bind (fun c => stepW tm (bitAns E (tm.query c) a) c)) (some (tm.initList inp))

lemma replay_snoc (inp : List (tm.Γ tm.k₀)) (as : List (MA Fk)) (a : MA Fk) :
    replay E tm inp (as ++ [a]) = (replay E tm inp as).bind (fun c => stepW tm (bitAns E (tm.query c) a) c) := by
  simp [replay, List.foldl_append]

/-- Step 2: the oracle TM as a query machine (one field query per TM step). -/
noncomputable def simQ (inp : ℕ → List (tm.Γ tm.k₀)) (acc : List (tm.Γ tm.k₁)) (T : ℕ → ℕ) : QMM Fk where
  time := T
  next n as := match replay E tm (inp n) as with | some c => qOf E (tm.query c) | none => E.dummy
  out n as := decide (∃ j ≤ as.length, replay E tm (inp n) (as.take j) = some (tm.haltList acc))

lemma mrun_length (M : QMM Fk) (n : ℕ) (O : MOrc Fk) : ∀ j, (mrun M n O j).length = j
  | 0 => rfl
  | j + 1 => by simp [mrun, mrun_length M n O j]

lemma mrun_take (M : QMM Fk) (n : ℕ) (O : MOrc Fk) : ∀ T j, j ≤ T → (mrun M n O T).take j = mrun M n O j
  | 0, j, h => by obtain rfl : j = 0 := by omega
                  rfl
  | T + 1, j, h => by
    rcases Nat.lt_or_ge j (T+1) with hj | hj
    · show (mrun M n O T ++ _).take j = _
      rw [List.take_append_of_le_length (by rw [mrun_length]; omega)]
      exact mrun_take M n O T j (by omega)
    · obtain rfl : j = T + 1 := by omega
      exact List.take_of_length_le (by rw [mrun_length])

variable (inp : ℕ → List (tm.Γ tm.k₀)) (acc : List (tm.Γ tm.k₁)) (T : ℕ → ℕ)

/-- Replay lemma: replaying the query machine's answers is the TM's run under Aenc E O. -/
lemma replay_mrun (n : ℕ) (O : MOrc Fk) : ∀ j,
    replay E tm (inp n) (mrun (simQ E tm inp acc T) n O j) =
      (flip bind (tm.step (Aenc E O)))^[j] (some (tm.initList (inp n)))
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', ← replay_mrun n O j]
    show replay E tm (inp n) (mrun (simQ E tm inp acc T) n O j ++ [_]) = _
    rw [replay_snoc]
    cases h : replay E tm (inp n) (mrun (simQ E tm inp acc T) n O j) with
    | none => rfl
    | some c =>
      show stepW tm _ c = tm.step (Aenc E O) c
      rw [step_eq]
      congr 1
      have hn : (simQ E tm inp acc T).next n (mrun (simQ E tm inp acc T) n O j) = qOf E (tm.query c) := by
        show (match replay E tm (inp n) _ with | some c => qOf E (tm.query c) | none => E.dummy) = _
        rw [h]
      rw [hn]
      simp [Aenc]

lemma out_iff (n : ℕ) (O : MOrc Fk) :
    (simQ E tm inp acc T).out n (mrun (simQ E tm inp acc T) n O (T n)) = true ↔
      Nonempty (OTM2OutputsInTime (Aenc E O) tm (inp n) (some acc) (T n)) := by
  show decide _ = true ↔ _
  rw [decide_eq_true_iff, mrun_length]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [mrun_take _ _ _ _ _ hj, replay_mrun] at h
    exact ⟨⟨⟨j, h⟩, hj⟩⟩
  · rintro ⟨⟨⟨j, h⟩, hj⟩⟩
    refine ⟨j, hj, ?_⟩
    rw [mrun_take _ _ _ _ _ hj, replay_mrun]; exact h

/-- AW Theorem 5.3 in the BGS Turing-machine model (steps 1-5): for every bit-encoding E of
field queries there are a Boolean oracle A (as a BGS oracle B), multiquadratic extensions P over
every field in the family, with sepLang B in NP^B but not in P^(Aenc E (mOrc P)). -/
theorem aw_tm_separation (E : Enc Fk) :
    ∃ (A : (m : ℕ) → (Fin m → Bool) → Bool) (P : ∀ k, (m : ℕ) → MvPolynomial (Fin m) (Fk k)) (B : Oracle),
      (∀ k m, (∀ j, degreeOf j (P k m) ≤ 2) ∧ ∀ z, eval (HHH.AW.bool z) (P k m) = if A m z then 1 else 0) ∧
      (∀ s, s ∈ B ↔ ∃ m z, A m z = true ∧ s = List.ofFn z ++ List.replicate m false) ∧
      InNP B (fin_encoding_string Bool) (sepLang B) ∧
      ¬ InP (Aenc E (mOrc P)) (fin_encoding_string Bool) (sepLang B) := by
  let Mi : ℕ → QMM Fk := fun i => simQ E (dEnum i).N.toOracleFinTM2 (dEnum i).input
    [(dEnum i).outE.symm true] (fun n => (dEnum i).time.eval n)
  have hT : ∀ i, ∃ N, ∀ n, N ≤ n → (Mi i).time n < 2 ^ n := fun i => eventually_eval_lt_two_pow _
  choose N hN using hT
  obtain ⟨nA, A, P, hext, hspread, hsupp, hwin⟩ := theorem_5_3_spread Mi N hN
  let B : Oracle := {s | ∃ m z, A m z = true ∧ s = List.ofFn z ++ List.replicate m false}
  refine ⟨A, P, B, hext, fun s => Iff.rfl, sepLang_inNP B, ?_⟩
  have hL : ∀ i, sepLang B (List.replicate (nA i) false) ↔ ∃ z, A (nA i) z = true := by
    intro i
    rw [sepLang_replicate_iff]
    constructor
    · rintro ⟨u, hu, m, z, hz, he⟩
      have hlen := congrArg List.length he
      simp only [List.length_append, List.length_replicate, List.length_ofFn] at hlen
      obtain ⟨j, rfl⟩ := hsupp m z hz
      have hji : j = i := by
        rcases lt_trichotomy j i with h | h | h
        · have := hspread j i h; omega
        · exact h
        · have := hspread i j h; omega
      subst hji; exact ⟨z, hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨List.ofFn z, by simp, nA i, z, hz, rfl⟩
  rintro ⟨f, h, hf⟩
  obtain ⟨c, -, hc⟩ := exists_dcode_decides h
  obtain ⟨i, rfl⟩ := dEnum_surjective c
  have hB := hc (List.replicate (nA i) false)
  rw [List.length_replicate] at hB
  obtain ⟨hB⟩ := hB
  have hout := out_iff E (dEnum i).N.toOracleFinTM2 (dEnum i).input [(dEnum i).outE.symm true]
    (fun n => (dEnum i).time.eval n) (nA i) (mOrc P)
  have hw := hwin i
  by_cases hz : ∃ z, A (nA i) z = true
  · have hf1 : f (List.replicate (nA i) false) = true := (hf _).mp ((hL i).mpr hz)
    rw [hf1] at hB
    exact (hw.mp (hout.mpr ⟨hB⟩)) hz
  · have h1 := hout.mp (hw.mpr hz)
    have h1' : Nonempty (OTM2OutputsInTime (Aenc E (mOrc P)) (dEnum i).N.toOracleFinTM2
        ((List.replicate (nA i) false).map (dEnum i).inE.symm) (some [(dEnum i).outE.symm true])
        ((dEnum i).time.eval (nA i))) := h1
    have e := (OTM2OutputsInTime.bool_iff (tm := (dEnum i).N.toOracleFinTM2) (dEnum i).outE hB true).mp h1'
    exact hz ((hL i).mp ((hf _).mpr e.symm))

end HHH.Bridge
namespace HHH.Bridge
open Relativization Turing HHH.AW HHH.AWB MvPolynomial Millennium
open scoped Classical

/-! Round 7: a concrete standard encoding for all finite fields GaloisField p k. -/

/-- Self-delimiting binary code of n: pairs (true, bit) LSB first, then a single false. -/
def wr (n : ℕ) : List Bool :=
  if h : n = 0 then [false] else true :: n.testBit 0 :: wr (n / 2)
decreasing_by omega

def readNum : List Bool → Option (ℕ × List Bool)
  | false :: r => some (0, r)
  | true :: b :: r => (readNum r).map fun p => (Nat.bit b p.1, p.2)
  | _ => none

theorem readNum_wr (n : ℕ) (r : List Bool) : readNum (wr n ++ r) = some (n, r) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [wr]
    split_ifs with h
    · subst h; rfl
    · simp only [List.cons_append, readNum]
      rw [ih (n / 2) (by omega)]
      have := Nat.bit_testBit_zero_shiftRight_one n
      rw [Nat.shiftRight_one] at this
      simp only [Option.map_some, this]

def readList : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, r => some ([], r)
  | m + 1, r => (readNum r).bind fun p => (readList m p.2).map fun q => (p.1 :: q.1, q.2)

theorem readList_wr (l : List ℕ) (r : List Bool) :
    readList l.length ((l.map wr).flatten ++ r) = some (l, r) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, readList,
      readNum_wr, Option.bind_some, ih, Option.map_some]

/-- field element <-> index in Fin (card) -/
noncomputable def code (x : GFIdx) (v : GF x) : ℕ := (Finite.equivFin (GF x) v).val
noncomputable def elt (x : GFIdx) (e : ℕ) : GF x :=
  if h : e < Nat.card (GF x) then (Finite.equivFin (GF x)).symm ⟨e, h⟩ else 0

theorem elt_code (x : GFIdx) (v : GF x) : elt x (code x v) = v := by
  unfold elt code
  rw [dif_pos (Finite.equivFin (GF x) v).isLt]
  simp

theorem code_injective (x : GFIdx) : Function.Injective (code x) := fun a b h => by
  rw [← elt_code x a, h, elt_code]

/-- the field-query point, read from a list of element codes -/
noncomputable def ptOf (x : GFIdx) (m : ℕ) (es : List ℕ) : ℕ → GF x :=
  fun j => if j < m then elt x (es.getD j 0) else 0

/-- The decoder: p, k, m, then m element codes, then the bit index i (all self-delimiting). -/
noncomputable def gfDec (s : List Bool) : Option (MQ GF × ℕ) :=
  match readNum s with
  | none => none
  | some (p, s1) =>
  match readNum s1 with
  | none => none
  | some (k, s2) =>
  match readNum s2 with
  | none => none
  | some (m, s3) =>
  match readList m s3 with
  | none => none
  | some (es, s4) =>
  match readNum s4 with
  | none => none
  | some (i, _) =>
    if hp : p.Prime then some (⟨⟨⟨p, hp⟩, k⟩, m, ptOf ⟨⟨p, hp⟩, k⟩ m es⟩, i) else none

/-- The concrete standard encoding: bit i of an answer is bit i of its element code. -/
noncomputable def gfEnc : Enc GF where
  dec := gfDec
  bit a i := (code a.1 a.2).testBit i
  dummy := ⟨⟨⟨2, Nat.prime_two⟩, 1⟩, 0, fun _ => 0⟩

/-- The encoder of the query "bit i of Ã_{m,GF x}(y)". -/
noncomputable def gfEncode (x : GFIdx) (m : ℕ) (y : Fin m → GF x) (i : ℕ) : List Bool :=
  wr x.1.1 ++ wr x.2 ++ wr m ++ ((List.ofFn fun j => code x (y j)).map wr).flatten ++ wr i

/-- Round trip: every field query and bit index has a code, decoded exactly. -/
theorem gfDec_encode (x : GFIdx) (m : ℕ) (y : Fin m → GF x) (i : ℕ) :
    gfDec (gfEncode x m y i) =
      some (⟨x, m, fun j => if h : j < m then y ⟨j, h⟩ else 0⟩, i) := by
  have hl : (List.ofFn fun j => code x (y j)).length = m := List.length_ofFn
  have hr := readList_wr (List.ofFn fun j => code x (y j)) (wr i)
  rw [hl] at hr
  unfold gfDec gfEncode
  simp only [List.append_assoc, readNum_wr, hr, List.append_nil]
  have hi := readNum_wr i []
  rw [List.append_nil] at hi
  rw [hi]
  simp only [dif_pos x.1.2]
  congr
  funext j
  unfold ptOf
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by rw [hl]; exact h), List.getElem_ofFn, elt_code]
  · rfl

/-- Bit answers determine the whole field element (relates Aenc to whole-element answers). -/
theorem bits_determine (x : GFIdx) (a b : GF x)
    (h : ∀ i, gfEnc.bit ⟨x, a⟩ i = gfEnc.bit ⟨x, b⟩ i) : a = b :=
  code_injective x (Nat.eq_of_testBit_eq h)

/-- AW Theorem 5.3 in the BGS TM model, concrete encoding, all finite fields GaloisField p k:
NP^B not contained in P^{Ã}, Ã the bit-encoded multiquadratic extensions over every GF(p^k). -/
theorem aw_tm_separation_galois :
    ∃ (A : (m : ℕ) → (Fin m → Bool) → Bool) (P : ∀ x : GFIdx, (m : ℕ) → MvPolynomial (Fin m) (GF x))
      (B : Oracle),
      (∀ x m, (∀ j, degreeOf j (P x m) ≤ 2) ∧
        ∀ z, eval (HHH.AW.bool z) (P x m) = if A m z then 1 else 0) ∧
      (∀ s, s ∈ B ↔ ∃ m z, A m z = true ∧ s = List.ofFn z ++ List.replicate m false) ∧
      InNP B (fin_encoding_string Bool) (sepLang B) ∧
      ¬ InP (Aenc gfEnc (mOrc P)) (fin_encoding_string Bool) (sepLang B) :=
  aw_tm_separation gfEnc

/-- The concrete oracle: gfEncode x m y i is in it iff bit i of the code of Ã_{m,x}(y) is 1. -/
theorem mem_Aenc_gf (O : MOrc GF) (x : GFIdx) (m : ℕ) (y : Fin m → GF x) (i : ℕ) :
    gfEncode x m y i ∈ Aenc gfEnc O ↔
      (code x (O x m (fun j => if h : j < m then y ⟨j, h⟩ else 0))).testBit i = true := by
  unfold Aenc bitAns qOf
  simp only [Set.mem_setOf_eq]
  rw [show gfEnc.dec = gfDec from rfl, gfDec_encode]
  rfl

end HHH.Bridge
