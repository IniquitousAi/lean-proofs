import Mathlib

/-! Subbotovskaya's shrinkage method for De Morgan formulas (1961), and its corollary
L(XOR_m)^2 ≥ m^3, i.e. leaf-size of parity ≥ m^(3/2).
Formulas: literals (x_i = s), binary AND, binary OR (NOT pushed to leaves). Size = leaves. -/

namespace Subb

inductive Fm (n : ℕ) where
  | lit : Fin n → Bool → Fm n
  | and : Fm n → Fm n → Fm n
  | or : Fm n → Fm n → Fm n
  deriving DecidableEq

variable {n : ℕ}

namespace Fm

def eval : Fm n → (Fin n → Bool) → Bool
  | lit j s, x => decide (x j = s)
  | and A B, x => eval A x && eval B x
  | or A B, x => eval A x || eval B x

def size : Fm n → ℕ
  | lit _ _ => 1
  | and A B => size A + size B
  | or A B => size A + size B

def cnt (i : Fin n) : Fm n → ℕ
  | lit j _ => if j = i then 1 else 0
  | and A B => cnt i A + cnt i B
  | or A B => cnt i A + cnt i B

theorem size_pos (F : Fm n) : 0 < size F := by
  induction F <;> simp [size] <;> omega

end Fm

open Fm

/-- Result of restricting: a constant or a formula. -/
abbrev Res (n : ℕ) := Bool ⊕ Fm n

def rsize : Res n → ℕ
  | .inl _ => 0
  | .inr F => F.size

def reval : Res n → (Fin n → Bool) → Bool
  | .inl c, _ => c
  | .inr F, x => F.eval x

def rcnt (i : Fin n) : Res n → ℕ
  | .inl _ => 0
  | .inr F => F.cnt i

def mkAnd : Res n → Res n → Res n
  | .inl false, _ => .inl false
  | .inl true, r => r
  | .inr A, .inl false => .inl false
  | .inr A, .inl true => .inr A
  | .inr A, .inr B => .inr (Fm.and A B)

def mkOr : Res n → Res n → Res n
  | .inl true, _ => .inl true
  | .inl false, r => r
  | .inr A, .inl true => .inl true
  | .inr A, .inl false => .inr A
  | .inr A, .inr B => .inr (Fm.or A B)

theorem reval_mkAnd (r s : Res n) (x) : reval (mkAnd r s) x = (reval r x && reval s x) := by
  rcases r with (_ | _) | A <;> rcases s with (_ | _) | B <;> simp [mkAnd, reval, Fm.eval]

theorem reval_mkOr (r s : Res n) (x) : reval (mkOr r s) x = (reval r x || reval s x) := by
  rcases r with (_ | _) | A <;> rcases s with (_ | _) | B <;> simp [mkOr, reval, Fm.eval]

theorem rsize_mkAnd (r s : Res n) : rsize (mkAnd r s) ≤ rsize r + rsize s := by
  rcases r with (_ | _) | A <;> rcases s with (_ | _) | B <;> simp [mkAnd, rsize, Fm.size]

theorem rsize_mkOr (r s : Res n) : rsize (mkOr r s) ≤ rsize r + rsize s := by
  rcases r with (_ | _) | A <;> rcases s with (_ | _) | B <;> simp [mkOr, rsize, Fm.size]

theorem rcnt_mkAnd (j) (r s : Res n) : rcnt j (mkAnd r s) ≤ rcnt j r + rcnt j s := by
  rcases r with (_ | _) | A <;> rcases s with (_ | _) | B <;> simp [mkAnd, rcnt, Fm.cnt]

theorem rcnt_mkOr (j) (r s : Res n) : rcnt j (mkOr r s) ≤ rcnt j r + rcnt j s := by
  rcases r with (_ | _) | A <;> rcases s with (_ | _) | B <;> simp [mkOr, rcnt, Fm.cnt]

/-- Restrict x_i := b and simplify constants away. -/
def restrict (i : Fin n) (b : Bool) : Fm n → Res n
  | Fm.lit j s => if j = i then .inl (decide (b = s)) else .inr (Fm.lit j s)
  | Fm.and A B => mkAnd (restrict i b A) (restrict i b B)
  | Fm.or A B => mkOr (restrict i b A) (restrict i b B)

theorem reval_restrict (i b) (F : Fm n) (x) :
    reval (restrict i b F) x = F.eval (Function.update x i b) := by
  induction F with
  | lit j s =>
    by_cases h : j = i
    · subst h; simp [restrict, reval, Fm.eval]
    · simp [restrict, reval, Fm.eval, h]
  | and A B iA iB => simp [restrict, reval_mkAnd, iA, iB, Fm.eval]
  | or A B iA iB => simp [restrict, reval_mkOr, iA, iB, Fm.eval]

theorem rsize_restrict (i b) (F : Fm n) : rsize (restrict i b F) + F.cnt i ≤ F.size := by
  induction F with
  | lit j s =>
    by_cases h : j = i
    · simp [restrict, rsize, Fm.cnt, Fm.size, h]
    · simp [restrict, rsize, Fm.cnt, Fm.size, h]
  | and A B iA iB =>
    have := rsize_mkAnd (restrict i b A) (restrict i b B)
    simp only [restrict, Fm.cnt, Fm.size]; omega
  | or A B iA iB =>
    have := rsize_mkOr (restrict i b A) (restrict i b B)
    simp only [restrict, Fm.cnt, Fm.size]; omega

theorem restrict_of_cnt_zero (i b) (F : Fm n) (h : F.cnt i = 0) : restrict i b F = .inr F := by
  induction F with
  | lit j s =>
    have : j ≠ i := by intro e; simp [Fm.cnt, e] at h
    simp [restrict, this]
  | and A B iA iB =>
    simp only [Fm.cnt] at h
    simp [restrict, iA (by omega), iB (by omega), mkAnd]
  | or A B iA iB =>
    simp only [Fm.cnt] at h
    simp [restrict, iA (by omega), iB (by omega), mkOr]

theorem rcnt_restrict (i b j) (F : Fm n) : rcnt j (restrict i b F) ≤ F.cnt j := by
  induction F with
  | lit k s =>
    by_cases h : k = i
    · simp [restrict, rcnt, h]
    · simp [restrict, rcnt, h, Fm.cnt]
  | and A B iA iB =>
    have := rcnt_mkAnd j (restrict i b A) (restrict i b B)
    simp only [restrict, Fm.cnt]; omega
  | or A B iA iB =>
    have := rcnt_mkOr j (restrict i b A) (restrict i b B)
    simp only [restrict, Fm.cnt]; omega

theorem rcnt_restrict_self (i b) (F : Fm n) : rcnt i (restrict i b F) = 0 := by
  induction F with
  | lit k s =>
    by_cases h : k = i
    · simp [restrict, rcnt, h]
    · simp [restrict, rcnt, h, Fm.cnt]
  | and A B iA iB =>
    have := rcnt_mkAnd i (restrict i b A) (restrict i b B)
    simp only [restrict]; omega
  | or A B iA iB =>
    have := rcnt_mkOr i (restrict i b A) (restrict i b B)
    simp only [restrict]; omega

/-! ## Nice formulas: a leaf's sibling never mentions the leaf's variable. -/

def Nice : Fm n → Prop
  | Fm.lit _ _ => True
  | Fm.and A B => Nice A ∧ Nice B ∧ (∀ j s, A = Fm.lit j s → B.cnt j = 0) ∧
      (∀ j s, B = Fm.lit j s → A.cnt j = 0)
  | Fm.or A B => Nice A ∧ Nice B ∧ (∀ j s, A = Fm.lit j s → B.cnt j = 0) ∧
      (∀ j s, B = Fm.lit j s → A.cnt j = 0)

/-- Subbotovskaya's key count: restricting x_i to both values removes, in total, at least
3 leaves per occurrence of x_i (the leaf twice, its sibling once). -/
theorem shrink_pair (i : Fin n) : ∀ F : Fm n, Nice F → (∀ s, F ≠ Fm.lit i s) →
    rsize (restrict i false F) + rsize (restrict i true F) + 3 * F.cnt i ≤ 2 * F.size := by
  intro F
  induction F with
  | lit j s =>
    intro _ hne
    have h : j ≠ i := by rintro rfl; exact hne s rfl
    simp [restrict, h, rsize, Fm.cnt, Fm.size]
  | and A B iA iB =>
    intro hN _
    obtain ⟨nA, nB, c1, c2⟩ := hN
    by_cases hA : ∃ s, A = Fm.lit i s
    · obtain ⟨s, rfl⟩ := hA
      have hB0 := c1 i s rfl
      have := Fm.size_pos B
      cases s <;> simp [restrict, restrict_of_cnt_zero i false B hB0,
        restrict_of_cnt_zero i true B hB0, mkAnd, rsize, Fm.cnt, Fm.size, hB0] <;> omega
    by_cases hB : ∃ s, B = Fm.lit i s
    · obtain ⟨s, rfl⟩ := hB
      have hA0 := c2 i s rfl
      have := Fm.size_pos A
      cases s <;> simp [restrict, restrict_of_cnt_zero i false A hA0,
        restrict_of_cnt_zero i true A hA0, mkAnd, rsize, Fm.cnt, Fm.size, hA0] <;>
        (try rcases (restrict i false A) with (_ | _) | _) <;> omega
    have hA' := iA nA (fun s h => hA ⟨s, h⟩)
    have hB' := iB nB (fun s h => hB ⟨s, h⟩)
    have m0 := rsize_mkAnd (restrict i false A) (restrict i false B)
    have m1 := rsize_mkAnd (restrict i true A) (restrict i true B)
    simp only [restrict, Fm.cnt, Fm.size]; omega
  | or A B iA iB =>
    intro hN _
    obtain ⟨nA, nB, c1, c2⟩ := hN
    by_cases hA : ∃ s, A = Fm.lit i s
    · obtain ⟨s, rfl⟩ := hA
      have hB0 := c1 i s rfl
      have := Fm.size_pos B
      cases s <;> simp [restrict, restrict_of_cnt_zero i false B hB0,
        restrict_of_cnt_zero i true B hB0, mkOr, rsize, Fm.cnt, Fm.size, hB0] <;> omega
    by_cases hB : ∃ s, B = Fm.lit i s
    · obtain ⟨s, rfl⟩ := hB
      have hA0 := c2 i s rfl
      have := Fm.size_pos A
      cases s <;> simp [restrict, restrict_of_cnt_zero i false A hA0,
        restrict_of_cnt_zero i true A hA0, mkOr, rsize, Fm.cnt, Fm.size, hA0] <;> omega
    have hA' := iA nA (fun s h => hA ⟨s, h⟩)
    have hB' := iB nB (fun s h => hB ⟨s, h⟩)
    have m0 := rsize_mkOr (restrict i false A) (restrict i false B)
    have m1 := rsize_mkOr (restrict i true A) (restrict i true B)
    simp only [restrict, Fm.cnt, Fm.size]; omega

theorem sum_cnt (V : Finset (Fin n)) : ∀ F : Fm n, (∀ j, 0 < F.cnt j → j ∈ V) →
    ∑ j ∈ V, F.cnt j = F.size := by
  intro F
  induction F with
  | lit k s =>
    intro hV
    have hk : k ∈ V := hV k (by simp [Fm.cnt])
    simp [Fm.cnt, Fm.size, Finset.sum_ite_eq, hk]
  | and A B iA iB =>
    intro hV
    simp only [Fm.cnt, Fm.size, Finset.sum_add_distrib]
    rw [iA (fun j h => hV j (by simp only [Fm.cnt]; omega)),
      iB (fun j h => hV j (by simp only [Fm.cnt]; omega))]
  | or A B iA iB =>
    intro hV
    simp only [Fm.cnt, Fm.size, Finset.sum_add_distrib]
    rw [iA (fun j h => hV j (by simp only [Fm.cnt]; omega)),
      iB (fun j h => hV j (by simp only [Fm.cnt]; omega))]

/-- SUBBOTOVSKAYA SHRINKAGE (deterministic one-step form). For a nice formula F whose
variables lie in V, |V| = m ≥ 2, some single restriction x_i := b (i ∈ V) leaves at most
(1 - 3/(2m)) · size F leaves. -/
theorem subbotovskaya_shrinkage (V : Finset (Fin n)) (F : Fm n) (hN : Nice F)
    (hV : ∀ j, 0 < F.cnt j → j ∈ V) (hm : 2 ≤ V.card) :
    ∃ i ∈ V, ∃ b, 2 * V.card * rsize (restrict i b F) + 3 * F.size ≤ 2 * V.card * F.size := by
  by_cases hl : ∃ j s, F = Fm.lit j s
  · obtain ⟨j, s, rfl⟩ := hl
    refine ⟨j, hV j (by simp [Fm.cnt]), false, ?_⟩
    simp [restrict, rsize, Fm.size]; omega
  push_neg at hl
  by_contra hcon
  push_neg at hcon
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  set m := V.card
  set L := F.size
  have h0 : ∑ i ∈ V, 2 * m * L < ∑ i ∈ V, (2 * m * rsize (restrict i false F) + 3 * L) :=
    Finset.sum_lt_sum_of_nonempty hne (fun i hi => hcon i hi false)
  have h1 : ∑ i ∈ V, 2 * m * L < ∑ i ∈ V, (2 * m * rsize (restrict i true F) + 3 * L) :=
    Finset.sum_lt_sum_of_nonempty hne (fun i hi => hcon i hi true)
  have h3 : ∑ i ∈ V, (rsize (restrict i false F) + rsize (restrict i true F) + 3 * F.cnt i)
      ≤ ∑ i ∈ V, 2 * L := Finset.sum_le_sum (fun i _ => shrink_pair i F hN (hl i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at h0 h1 h3
  rw [sum_cnt V F hV] at h3
  set R0 := ∑ i ∈ V, rsize (restrict i false F)
  set R1 := ∑ i ∈ V, rsize (restrict i true F)
  have h3' : 2 * m * (R0 + R1 + 3 * L) ≤ 2 * m * (m * (2 * L)) := Nat.mul_le_mul_left _ h3
  nlinarith

/-! ## Minimal formulas are nice. -/

@[simp] theorem reval_inr (F : Fm n) (x) : reval (.inr F) x = F.eval x := rfl
@[simp] theorem rsize_inr (F : Fm n) : rsize (.inr F) = F.size := rfl
@[simp] theorem rcnt_inr (j) (F : Fm n) : rcnt j (.inr F) = F.cnt j := rfl


theorem improve : ∀ F : Fm n, ¬ Nice F → ∃ r : Res n, (∀ x, reval r x = F.eval x) ∧
    rsize r < F.size ∧ ∀ j, rcnt j r ≤ F.cnt j := by
  intro F
  induction F with
  | lit j s => intro h; exact absurd trivial h
  | and A B iA iB =>
    intro h
    simp only [Nice, not_and_or] at h
    rcases h with hA | hB | hc | hc
    · obtain ⟨r, e, sz, c⟩ := iA hA
      refine ⟨mkAnd r (.inr B), fun x => ?_, ?_, fun j => ?_⟩
      · rw [reval_mkAnd, e]; rfl
      · have := rsize_mkAnd r (.inr B); simp only [rsize_inr, Fm.size] at this ⊢; omega
      · have := rcnt_mkAnd j r (.inr B); have := c j; simp only [rcnt_inr, Fm.cnt] at *; omega
    · obtain ⟨r, e, sz, c⟩ := iB hB
      refine ⟨mkAnd (.inr A) r, fun x => ?_, ?_, fun j => ?_⟩
      · rw [reval_mkAnd, e]; rfl
      · have := rsize_mkAnd (.inr A) r; simp only [rsize_inr, Fm.size] at this ⊢; omega
      · have := rcnt_mkAnd j (.inr A) r; have := c j; simp only [rcnt_inr, Fm.cnt] at *; omega
    · push_neg at hc
      obtain ⟨j, s, rfl, hb⟩ := hc
      refine ⟨mkAnd (.inr (Fm.lit j s)) (restrict j s B), fun x => ?_, ?_, fun k => ?_⟩
      · rw [reval_mkAnd, reval_restrict]
        by_cases hx : x j = s
        · have hu : Function.update x j s = x := by rw [← hx]; exact Function.update_eq_self j x
          simp [hu, Fm.eval, hx]
        · simp [Fm.eval, hx]
      · have := rsize_mkAnd (.inr (Fm.lit j s)) (restrict j s B)
        have := rsize_restrict j s B
        simp only [rsize_inr, Fm.size] at *; omega
      · have := rcnt_mkAnd k (.inr (Fm.lit j s)) (restrict j s B)
        have := rcnt_restrict j s k B
        simp only [rcnt_inr, Fm.cnt] at *; omega
    · push_neg at hc
      obtain ⟨j, s, rfl, hb⟩ := hc
      refine ⟨mkAnd (restrict j s A) (.inr (Fm.lit j s)), fun x => ?_, ?_, fun k => ?_⟩
      · rw [reval_mkAnd, reval_restrict]
        by_cases hx : x j = s
        · have hu : Function.update x j s = x := by rw [← hx]; exact Function.update_eq_self j x
          simp [hu, Fm.eval, hx]
        · simp [Fm.eval, hx]
      · have := rsize_mkAnd (restrict j s A) (.inr (Fm.lit j s))
        have := rsize_restrict j s A
        simp only [rsize_inr, Fm.size] at *; omega
      · have := rcnt_mkAnd k (restrict j s A) (.inr (Fm.lit j s))
        have := rcnt_restrict j s k A
        simp only [rcnt_inr, Fm.cnt] at *; omega
  | or A B iA iB =>
    intro h
    simp only [Nice, not_and_or] at h
    rcases h with hA | hB | hc | hc
    · obtain ⟨r, e, sz, c⟩ := iA hA
      refine ⟨mkOr r (.inr B), fun x => ?_, ?_, fun j => ?_⟩
      · rw [reval_mkOr, e]; rfl
      · have := rsize_mkOr r (.inr B); simp only [rsize_inr, Fm.size] at this ⊢; omega
      · have := rcnt_mkOr j r (.inr B); have := c j; simp only [rcnt_inr, Fm.cnt] at *; omega
    · obtain ⟨r, e, sz, c⟩ := iB hB
      refine ⟨mkOr (.inr A) r, fun x => ?_, ?_, fun j => ?_⟩
      · rw [reval_mkOr, e]; rfl
      · have := rsize_mkOr (.inr A) r; simp only [rsize_inr, Fm.size] at this ⊢; omega
      · have := rcnt_mkOr j (.inr A) r; have := c j; simp only [rcnt_inr, Fm.cnt] at *; omega
    · push_neg at hc
      obtain ⟨j, s, rfl, hb⟩ := hc
      refine ⟨mkOr (.inr (Fm.lit j s)) (restrict j (!s) B), fun x => ?_, ?_, fun k => ?_⟩
      · rw [reval_mkOr, reval_restrict]
        by_cases hx : x j = s
        · simp [Fm.eval, hx]
        · have hx' : x j = !s := by cases h : x j <;> cases s <;> simp_all
          have hu : Function.update x j (!s) = x := by rw [← hx']; exact Function.update_eq_self j x
          simp [hu, Fm.eval, hx]
      · have := rsize_mkOr (.inr (Fm.lit j s)) (restrict j (!s) B)
        have := rsize_restrict j (!s) B
        simp only [rsize_inr, Fm.size] at *; omega
      · have := rcnt_mkOr k (.inr (Fm.lit j s)) (restrict j (!s) B)
        have := rcnt_restrict j (!s) k B
        simp only [rcnt_inr, Fm.cnt] at *; omega
    · push_neg at hc
      obtain ⟨j, s, rfl, hb⟩ := hc
      refine ⟨mkOr (restrict j (!s) A) (.inr (Fm.lit j s)), fun x => ?_, ?_, fun k => ?_⟩
      · rw [reval_mkOr, reval_restrict]
        by_cases hx : x j = s
        · simp [Fm.eval, hx]
        · have hx' : x j = !s := by cases h : x j <;> cases s <;> simp_all
          have hu : Function.update x j (!s) = x := by rw [← hx']; exact Function.update_eq_self j x
          simp [hu, Fm.eval, hx]
      · have := rsize_mkOr (restrict j (!s) A) (.inr (Fm.lit j s))
        have := rsize_restrict j (!s) A
        simp only [rsize_inr, Fm.size] at *; omega
      · have := rcnt_mkOr k (restrict j (!s) A) (.inr (Fm.lit j s))
        have := rcnt_restrict j (!s) k A
        simp only [rcnt_inr, Fm.cnt] at *; omega

/-! ## Parity: L(±XOR_V)^2 ≥ |V|^3. -/

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def par (V : Finset (Fin n)) (x : Fin n → Bool) : ZMod 2 := ∑ j ∈ V, b2z (x j)

/-- F computes XOR or XNOR of the variables in V, and mentions only variables of V. -/
def ComputesPar (V : Finset (Fin n)) (F : Fm n) : Prop :=
  (∀ j, 0 < F.cnt j → j ∈ V) ∧ ∃ c : ZMod 2, ∀ x, b2z (F.eval x) = c + par V x

theorem par_update (V : Finset (Fin n)) (i) (hi : i ∈ V) (b x) :
    par V (Function.update x i b) = b2z b + par (V.erase i) x := by
  unfold par
  rw [← Finset.add_sum_erase V _ hi, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])

theorem par_nonconst (W : Finset (Fin n)) (hW : W.Nonempty) (c₁ c₂ : ZMod 2) :
    ¬ ∀ x, c₁ = c₂ + par W x := by
  intro h
  obtain ⟨j, hj⟩ := hW
  have h0 := h (fun _ => false)
  have h1 := h (Function.update (fun _ => false) j true)
  rw [par_update W j hj] at h1
  simp [par, b2z] at h0 h1
  rw [h0] at h1
  have : (1 : ZMod 2) = 0 := add_left_cancel (h1.symm.trans (add_zero c₂).symm)
  exact absurd this (by decide)

theorem arith (k g L : ℕ) (hg : (k + 1) ^ 3 ≤ g ^ 2)
    (h : 2 * (k + 2) * g + 3 * L ≤ 2 * (k + 2) * L) : (k + 2) ^ 3 ≤ L ^ 2 := by
  have h1 : 2 * (k + 2) * g ≤ (2 * k + 1) * L := by nlinarith
  have h2 := Nat.pow_le_pow_left h1 2
  have h3 : (k + 2) * (2 * k + 1) ^ 2 ≤ 4 * (k + 1) ^ 3 := by ring_nf; nlinarith
  have h4 : (k + 2) ^ 3 * (2 * k + 1) ^ 2 ≤ L ^ 2 * (2 * k + 1) ^ 2 := by
    calc (k + 2) ^ 3 * (2 * k + 1) ^ 2 = (k + 2) ^ 2 * ((k + 2) * (2 * k + 1) ^ 2) := by ring
      _ ≤ (k + 2) ^ 2 * (4 * g ^ 2) := by
          apply Nat.mul_le_mul_left; nlinarith
      _ = (2 * (k + 2) * g) ^ 2 := by ring
      _ ≤ ((2 * k + 1) * L) ^ 2 := h2
      _ = L ^ 2 * (2 * k + 1) ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

/-- SUBBOTOVSKAYA'S BOUND FOR PARITY. Any De Morgan formula computing XOR (or XNOR) of the
m variables in V has leaf-size L with L^2 ≥ m^3, i.e. L ≥ m^(3/2). -/
theorem parity_formula_lb : ∀ m (V : Finset (Fin n)), V.card = m → ∀ F : Fm n,
    ComputesPar V F → m ^ 3 ≤ F.size ^ 2 := by
  intro m
  induction m with
  | zero => intros; simp
  | succ k ih =>
    intro V hV F hF
    rcases k with _ | k
    · have := Fm.size_pos F; simp; nlinarith
    classical
    -- minimal-size formula computing ±par V
    have hex : ∃ L, ∃ G : Fm n, ComputesPar V G ∧ G.size = L := ⟨_, F, hF, rfl⟩
    obtain ⟨G, hG, hGs⟩ := Nat.find_spec hex
    have hmin : ∀ G' : Fm n, ComputesPar V G' → Nat.find hex ≤ G'.size :=
      fun G' h => Nat.find_min' hex ⟨G', h, rfl⟩
    have hle : G.size ≤ F.size := hGs ▸ hmin F hF
    have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hGv, c, hGc⟩ := hG
    have hNice : Nice G := by
      by_contra hn
      obtain ⟨r, e, sz, rc⟩ := improve G hn
      rcases r with c0 | G'
      · exact par_nonconst V hVne (b2z c0) c (fun x => by rw [← hGc x, ← e x]; rfl)
      · have := hmin G' ⟨fun j hj => hGv j (by have := rc j; simp at this; omega),
          c, fun x => by rw [← hGc x, ← e x]; rfl⟩
        simp at sz; omega
    obtain ⟨i, hi, b, hsh⟩ := subbotovskaya_shrinkage V G hNice hGv (by omega)
    have hW : (V.erase i).card = k + 1 := by rw [Finset.card_erase_of_mem hi]; omega
    have hWne : (V.erase i).Nonempty := Finset.card_pos.mp (by omega)
    have heval : ∀ x, b2z (reval (restrict i b G) x) = (c + b2z b) + par (V.erase i) x := by
      intro x; rw [reval_restrict, hGc, par_update V i hi]; ring
    rcases hr : restrict i b G with c0 | G'
    · rw [hr] at heval
      exact absurd (fun x => heval x) (par_nonconst _ hWne (b2z c0) (c + b2z b))
    · rw [hr] at heval hsh
      have hcomp : ComputesPar (V.erase i) G' := by
        refine ⟨fun j hj => ?_, c + b2z b, heval⟩
        have h1 := rcnt_restrict i b j G
        have h2 := rcnt_restrict_self i b G
        rw [hr] at h1 h2
        simp at h1 h2
        refine Finset.mem_erase.mpr ⟨?_, hGv j (by omega)⟩
        rintro rfl; omega
      have hg := ih (V.erase i) hW G' hcomp
      rw [hV] at hsh
      simp only [rsize_inr] at hsh
      have := arith k G'.size G.size hg (by linarith)
      calc (k + 1 + 1) ^ 3 = (k + 2) ^ 3 := by ring
        _ ≤ G.size ^ 2 := this
        _ ≤ F.size ^ 2 := Nat.pow_le_pow_left hle 2

end Subb
