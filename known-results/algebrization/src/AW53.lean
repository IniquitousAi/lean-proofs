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
#print axioms HHH.AW.theorem_5_3_query
