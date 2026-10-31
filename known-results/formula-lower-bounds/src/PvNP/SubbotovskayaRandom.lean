import PvNP.Subbotovskaya

/-! Round 10. (1) Parity bound without the "variables in V" hypothesis.
(2) Random-restriction form of Subbotovskaya shrinkage. -/

namespace Subb
open Fm

variable {n : ℕ}

/-! ## (1) Full textbook parity bound -/

theorem par_update_out (V : Finset (Fin n)) (j) (hj : j ∉ V) (b x) :
    par V (Function.update x j b) = par V x := by
  unfold par
  exact Finset.sum_congr rfl (fun i hi => by
    rw [Function.update_of_ne (by rintro rfl; exact hj hi)])

theorem reduce_outside (V : Finset (Fin n)) (hV : V.Nonempty) : ∀ N (F : Fm n),
    ∑ j ∈ Vᶜ, F.cnt j = N → (∃ c : ZMod 2, ∀ x, b2z (F.eval x) = c + par V x) →
    ∃ G, ComputesPar V G ∧ G.size ≤ F.size := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro F hN ⟨c, hc⟩
  by_cases hin : ∀ j, 0 < F.cnt j → j ∈ V
  · exact ⟨F, ⟨hin, c, hc⟩, le_rfl⟩
  push_neg at hin
  obtain ⟨j, hjpos, hjV⟩ := hin
  have hev : ∀ x, b2z (reval (restrict j false F) x) = c + par V x := by
    intro x; rw [reval_restrict, hc, par_update_out V j hjV]
  rcases hr : restrict j false F with c0 | G
  · rw [hr] at hev
    exact absurd (fun x => (hev x)) (par_nonconst V hV (b2z c0) c)
  · rw [hr] at hev
    have hs := rsize_restrict j false F
    rw [hr] at hs; simp only [rsize_inr] at hs
    have hlt : ∑ i ∈ Vᶜ, G.cnt i < N := by
      rw [← hN]
      apply Finset.sum_lt_sum
      · intro i _; have := rcnt_restrict j false i F; rw [hr] at this; simpa using this
      · refine ⟨j, Finset.mem_compl.mpr hjV, ?_⟩
        have := rcnt_restrict_self j false F; rw [hr] at this; simp at this; omega
    obtain ⟨G', hG', hsz⟩ := ih _ hlt G rfl ⟨c, hev⟩
    exact ⟨G', hG', by omega⟩

/-- SUBBOTOVSKAYA (textbook form). Any De Morgan formula F (over any variables) computing
XOR or XNOR of the variables in V satisfies |V|^3 ≤ size(F)^2. -/
theorem parity_formula_lb_full (V : Finset (Fin n)) (F : Fm n)
    (h : ∃ c : ZMod 2, ∀ x, b2z (F.eval x) = c + par V x) : V.card ^ 3 ≤ F.size ^ 2 := by
  rcases V.eq_empty_or_nonempty with hV | hV
  · simp [hV]
  obtain ⟨G, hG, hsz⟩ := reduce_outside V hV _ F rfl h
  exact (parity_formula_lb _ V rfl G hG).trans (Nat.pow_le_pow_left hsz 2)

/-! ## (2) Random restrictions -/

/-- r represents f using only variables in W. -/
def Rep (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (r : Res n) : Prop :=
  (∀ j, 0 < rcnt j r → j ∈ W) ∧ ∀ x, reval r x = f x

open Classical in
/-- Formula complexity L_W(f): minimal leaf-size (constants = 0) over W-formulas. -/
noncomputable def LW (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : ℕ :=
  if h : ∃ L, ∃ r, Rep W f r ∧ rsize r = L then Nat.find h else 0

open Classical in
theorem LW_spec {W : Finset (Fin n)} {f} (h : ∃ r, Rep W f r) :
    ∃ r, Rep W f r ∧ rsize r = LW W f := by
  obtain ⟨r, hr⟩ := h
  have h' : ∃ L, ∃ r, Rep W f r ∧ rsize r = L := ⟨_, r, hr, rfl⟩
  rw [LW, dif_pos h']; exact Nat.find_spec h'

open Classical in
theorem LW_le {W : Finset (Fin n)} {f r} (h : Rep W f r) : LW W f ≤ rsize r := by
  have h' : ∃ L, ∃ r, Rep W f r ∧ rsize r = L := ⟨_, r, h, rfl⟩
  rw [LW, dif_pos h']; exact Nat.find_min' h' ⟨r, h, rfl⟩

def rres (i : Fin n) (b : Bool) : Res n → Res n
  | .inl c => .inl c
  | .inr F => restrict i b F

/-- f with x_i fixed to b. -/
def fix (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool) : (Fin n → Bool) → Bool :=
  fun x => f (Function.update x i b)

theorem Rep_rres {W : Finset (Fin n)} {f r} (h : Rep W f r) (i b) :
    Rep (W.erase i) (fix f i b) (rres i b r) := by
  obtain ⟨hv, he⟩ := h
  rcases r with c | F
  · exact ⟨fun j hj => by simp [rres, rcnt] at hj, fun x => by
      simpa [rres, reval, fix] using he (Function.update x i b)⟩
  · refine ⟨fun j hj => ?_, fun x => ?_⟩
    · have h1 := rcnt_restrict i b j F
      have h2 := rcnt_restrict_self i b F
      simp only [rres] at hj
      refine Finset.mem_erase.mpr ⟨?_, hv j (by simp; omega)⟩
      rintro rfl; omega
    · simp only [rres, fix]; rw [reval_restrict]; exact he _

theorem rsize_rres (i b) (r : Res n) : rsize (rres i b r) ≤ rsize r := by
  rcases r with c | F
  · simp [rres, rsize]
  · have := rsize_restrict i b F; simp only [rres, rsize_inr]; omega

theorem LW_fix {W : Finset (Fin n)} {f} (h : ∃ r, Rep W f r) (i b) :
    (∃ r, Rep (W.erase i) (fix f i b) r) ∧ LW (W.erase i) (fix f i b) ≤ LW W f := by
  obtain ⟨r, hr, hs⟩ := LW_spec h
  exact ⟨⟨_, Rep_rres hr i b⟩, (LW_le (Rep_rres hr i b)).trans (hs ▸ rsize_rres i b r)⟩

/-- One-step shrinkage in complexity form (for L_W(f) ≥ 2). -/
theorem LW_step {W : Finset (Fin n)} {f} (h : ∃ r, Rep W f r) (hL : 2 ≤ LW W f) :
    ∑ i ∈ W, (LW (W.erase i) (fix f i false) + LW (W.erase i) (fix f i true)) + 3 * LW W f
      ≤ 2 * W.card * LW W f := by
  obtain ⟨r, hr, hs⟩ := LW_spec h
  rcases r with c | F
  · simp [rsize] at hs; omega
  simp only [rsize_inr] at hs
  have hN : Nice F := by
    by_contra hn
    obtain ⟨r', e, sz, rc⟩ := improve F hn
    have := LW_le (W := W) (f := f) (r := r') ⟨fun j hj => hr.1 j (by
      have := rc j; simp; omega), fun x => (e x).trans (hr.2 x)⟩
    omega
  have hvars : ∀ j, 0 < F.cnt j → j ∈ W := fun j hj => hr.1 j (by simpa using hj)
  have hsum := Finset.sum_le_sum (s := W) (fun i _ => shrink_pair i F hN (fun s he => by
    subst he; simp [Fm.size] at hs; omega))
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum
  rw [sum_cnt W F hvars] at hsum
  have hle : ∀ i b, LW (W.erase i) (fix f i b) ≤ rsize (restrict i b F) :=
    fun i b => LW_le (Rep_rres hr i b)
  have := Finset.sum_le_sum (s := W) (fun i _ => Nat.add_le_add (hle i false) (hle i true))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  rw [Finset.sum_add_distrib, ← hs]
  have e : W.card * (2 * F.size) = 2 * W.card * F.size := by ring
  omega

/-- Expected complexity after j more steps, each fixing a uniformly random remaining
variable i ∈ W to a uniformly random bit b. -/
noncomputable def Eres : ℕ → Finset (Fin n) → ((Fin n → Bool) → Bool) → ℝ
  | 0, W, f => LW W f
  | j + 1, W, f => if W.card = 0 then LW W f else
      (∑ i ∈ W, (Eres j (W.erase i) (fix f i false) + Eres j (W.erase i) (fix f i true)))
        / (2 * W.card)

theorem Eres_le_LW : ∀ j (W : Finset (Fin n)) f, (∃ r, Rep W f r) → Eres j W f ≤ LW W f := by
  intro j
  induction j with
  | zero => intros; simp [Eres]
  | succ j ih =>
    intro W f h
    simp only [Eres]
    split_ifs with h0
    · exact le_rfl
    have hm : (0 : ℝ) < 2 * W.card := by positivity
    rw [div_le_iff₀ hm]
    calc ∑ i ∈ W, (Eres j (W.erase i) (fix f i false) + Eres j (W.erase i) (fix f i true))
        ≤ ∑ i ∈ W, ((LW W f : ℝ) + LW W f) := by
          apply Finset.sum_le_sum; intro i _
          have a := LW_fix h i false; have b := LW_fix h i true
          have := ih _ _ a.1; have := ih _ _ b.1
          have : (LW (W.erase i) (fix f i false) : ℝ) ≤ LW W f := by exact_mod_cast a.2
          have : (LW (W.erase i) (fix f i true) : ℝ) ≤ LW W f := by exact_mod_cast b.2
          linarith
      _ = LW W f * (2 * W.card) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem bern (m : ℕ) (hm : 2 ≤ m) :
    1 - 3 / (2 * (m : ℝ)) ≤ (((m - 1 : ℕ) : ℝ) / m) ^ (3 / 2 : ℝ) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have e : (((m - 1 : ℕ) : ℝ) / m) = 1 + (-1 / (m : ℝ)) := by
    rw [Nat.cast_sub (by omega)]; field_simp; ring
  rw [e]
  have := one_add_mul_self_le_rpow_one_add (s := -1 / (m : ℝ))
    (by rw [le_div_iff₀ (by linarith)]; linarith) (p := 3 / 2) (by norm_num)
  have e2 : (1 : ℝ) - 3 / (2 * m) = 1 + 3 / 2 * (-1 / m) := by field_simp; ring
  rw [e2]; exact this

/-- SUBBOTOVSKAYA, RANDOM-RESTRICTION FORM. Start from f with complexity L = L_W(f), |W| = m.
Fix j random variables one at a time (uniform remaining variable, uniform bit), leaving
k = m - j free. Then  E[L(f_ρ)] ≤ (k/m)^(3/2) · L + 1. -/
theorem subbotovskaya_random : ∀ j (m : ℕ) (W : Finset (Fin n)) f, W.card = m → 1 ≤ m →
    j ≤ m → (∃ r, Rep W f r) →
    Eres j W f ≤ (((m - j : ℕ) : ℝ) / m) ^ (3 / 2 : ℝ) * LW W f + 1 := by
  intro j
  induction j with
  | zero =>
    intro m W f _ hm _ _
    have : ((m : ℝ) / m) = 1 := div_self (by positivity)
    simp [Eres, this]
  | succ j ih =>
    intro m W f hW hm hj h
    have hpow0 : (0 : ℝ) ≤ (((m - (j + 1) : ℕ) : ℝ) / m) ^ (3 / 2 : ℝ) := by positivity
    by_cases hL : LW W f ≤ 1
    · have := Eres_le_LW (j + 1) W f h
      have : (LW W f : ℝ) ≤ 1 := by exact_mod_cast hL
      nlinarith [mul_nonneg hpow0 (Nat.cast_nonneg (LW W f) : (0 : ℝ) ≤ LW W f)]
    push_neg at hL
    have hstep := LW_step h hL
    rw [hW] at hstep
    have hm2 : 2 ≤ m := by
      by_contra hc; have : m = 1 := by omega
      subst this; omega
    simp only [Eres]
    rw [if_neg (by omega)]
    set a := (((m - 1 - j : ℕ) : ℝ) / ((m - 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ) with ha
    have ha0 : 0 ≤ a := by positivity
    have hcard : ∀ i ∈ W, (W.erase i).card = m - 1 := fun i hi => by
      rw [Finset.card_erase_of_mem hi, hW]
    have hb : ∀ i ∈ W, ∀ b, Eres j (W.erase i) (fix f i b)
        ≤ a * LW (W.erase i) (fix f i b) + 1 := by
      intro i hi b
      have := ih (m - 1) (W.erase i) (fix f i b) (hcard i hi) (by omega) (by omega)
        (LW_fix h i b).1
      simpa [ha, Nat.sub_sub, Nat.add_comm 1 j] using this
    set L := (LW W f : ℝ)
    set S := ∑ i ∈ W, ((LW (W.erase i) (fix f i false) : ℝ) + LW (W.erase i) (fix f i true))
    have hS : S + 3 * L ≤ 2 * m * L := by
      have : ((∑ i ∈ W, (LW (W.erase i) (fix f i false) + LW (W.erase i) (fix f i true)) +
        3 * LW W f : ℕ) : ℝ) ≤ ((2 * m * LW W f : ℕ) : ℝ) := by exact_mod_cast hstep
      push_cast at this; exact this
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hpos : (0 : ℝ) < 2 * m := by linarith
    have hsum : ∑ i ∈ W, (Eres j (W.erase i) (fix f i false) + Eres j (W.erase i) (fix f i true))
        ≤ a * S + 2 * m := by
      calc _ ≤ ∑ i ∈ W, (a * ((LW (W.erase i) (fix f i false) : ℝ) +
              LW (W.erase i) (fix f i true)) + 2) := by
            apply Finset.sum_le_sum; intro i hi
            have := hb i hi false; have := hb i hi true; nlinarith
        _ = a * S + 2 * m := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hW]; simp; ring
    have hbern := bern m hm2
    have hprod : a * (((m - 1 : ℕ) : ℝ) / m) ^ (3 / 2 : ℝ)
        = (((m - (j + 1) : ℕ) : ℝ) / m) ^ (3 / 2 : ℝ) := by
      rw [ha, ← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      have h1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
        rw [Nat.cast_sub (by omega)]; push_cast; linarith
      rw [show m - 1 - j = m - (j + 1) by omega]
      field_simp
    rw [hW, div_le_iff₀ hpos, ← hprod]
    have hL0 : 0 ≤ L := Nat.cast_nonneg _
    have key : a * S ≤ a * ((1 - 3 / (2 * (m : ℝ))) * L) * (2 * m) := by
      have : S ≤ (1 - 3 / (2 * (m : ℝ))) * L * (2 * m) := by
        have : (1 - 3 / (2 * (m : ℝ))) * L * (2 * m) = 2 * m * L - 3 * L := by
          field_simp
        linarith
      nlinarith
    have key2 : a * ((1 - 3 / (2 * (m : ℝ))) * L)
        ≤ a * ((((m - 1 : ℕ) : ℝ) / m) ^ (3 / 2 : ℝ) * L) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbern hL0) ha0
    nlinarith

end Subb
