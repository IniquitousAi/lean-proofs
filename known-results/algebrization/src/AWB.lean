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
