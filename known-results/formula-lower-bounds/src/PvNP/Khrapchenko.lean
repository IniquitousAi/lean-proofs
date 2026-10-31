import PvNP.Andreev

/-! Round 12 (2), first Håstad-direction piece: KHRAPCHENKO'S THEOREM (1971).
For a De Morgan formula F, A ⊆ F⁻¹(1), B ⊆ F⁻¹(0), and e(A,B) = number of Hamming edges
between A and B:  e(A,B)^2 ≤ size(F)·|A|·|B|.  Corollary: L(XOR_n) ≥ n^2. This shows the
shrinkage exponent Γ cannot exceed 2 (Håstad: Γ = 2). -/

namespace Subb
open Finset

variable {n : ℕ}

def flip (a : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update a i (!a i)

theorem flip_flip (a : Fin n → Bool) (i : Fin n) : flip (flip a i) i = a := by
  funext j; by_cases h : j = i
  · subst h; simp [flip]
  · simp [flip, Function.update_of_ne h]

/-- Edges counted as pairs (a, i) with a ∈ A and flip a i ∈ B. -/
def edges (A B : Finset (Fin n → Bool)) : ℕ :=
  ∑ a ∈ A, (univ.filter (fun i => flip a i ∈ B)).card

theorem comb (e1 e2 L1 L2 x1 x2 y : ℕ) (h1 : e1 ^ 2 ≤ L1 * x1 * y) (h2 : e2 ^ 2 ≤ L2 * x2 * y) :
    (e1 + e2) ^ 2 ≤ (L1 + L2) * (x1 + x2) * y := by
  have huv : (e1 * e2) ^ 2 ≤ (L1 * x2 * y) * (L2 * x1 * y) := by
    have := Nat.mul_le_mul h1 h2
    calc (e1 * e2) ^ 2 = e1 ^ 2 * e2 ^ 2 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hs : 2 * (e1 * e2) ≤ L1 * x2 * y + L2 * x1 * y := by
    by_contra hc; push_neg at hc
    have := Nat.pow_lt_pow_left hc (two_ne_zero)
    nlinarith [sq_nonneg ((L1 * x2 * y : ℤ) - L2 * x1 * y)]
  nlinarith

theorem edges_split_B (A B : Finset (Fin n → Bool)) (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    edges A B = edges A (B.filter P) + edges A (B.filter (fun b => ¬ P b)) := by
  unfold edges; rw [← sum_add_distrib]; refine sum_congr rfl fun a _ => ?_
  rw [← card_filter_add_card_filter_not (s := univ.filter (fun i => flip a i ∈ B))
    (fun i => P (flip a i)), filter_filter, filter_filter]
  simp only [mem_filter]

theorem edges_split_A (A B : Finset (Fin n → Bool)) (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    edges A B = edges (A.filter P) B + edges (A.filter (fun b => ¬ P b)) B := by
  unfold edges; rw [sum_filter_add_sum_filter_not]

theorem khrapchenko : ∀ (F : Fm n) (A B : Finset (Fin n → Bool)),
    (∀ a ∈ A, F.eval a = true) → (∀ b ∈ B, F.eval b = false) →
    edges A B ^ 2 ≤ F.size * A.card * B.card := by
  intro F
  induction F with
  | lit i t =>
    intro A B hA hB
    have hle : edges A B ≤ (A.filter (fun a => flip a i ∈ B)).card := by
      unfold edges; rw [card_filter]
      refine sum_le_sum fun a ha => ?_
      have hsub : univ.filter (fun j => flip a j ∈ B) ⊆ (if flip a i ∈ B then {i} else ∅) := by
        intro j hj
        rw [mem_filter] at hj
        by_cases hji : j = i
        · subst hji; simp [hj.2]
        · exfalso
          have h1 := hA a ha; have h2 := hB _ hj.2
          simp only [Fm.eval, flip, Function.update_of_ne (Ne.symm hji)] at h1 h2
          rw [h1] at h2; exact absurd h2 (by simp)
      refine (card_le_card hsub).trans ?_
      split_ifs <;> simp
    have hA' : (A.filter (fun a => flip a i ∈ B)).card ≤ A.card := card_filter_le _ _
    have hB' : (A.filter (fun a => flip a i ∈ B)).card ≤ B.card := by
      apply card_le_card_of_injOn (fun a => flip a i)
      · intro a ha; exact (mem_filter.mp ha).2
      · intro a _ b _ h
        have := congrArg (fun z => flip z i) h; simpa [flip_flip] using this
    simp only [Fm.size, one_mul]
    nlinarith
  | and F1 F2 i1 i2 =>
    intro A B hA hB
    have hA1 : ∀ a ∈ A, F1.eval a = true := fun a ha => by
      have := hA a ha; simp [Fm.eval] at this; exact this.1
    have hA2 : ∀ a ∈ A, F2.eval a = true := fun a ha => by
      have := hA a ha; simp [Fm.eval] at this; exact this.2
    have h1 := i1 A (B.filter (fun b => F1.eval b = false)) hA1 (fun b hb => (mem_filter.mp hb).2)
    have h2 := i2 A (B.filter (fun b => ¬ F1.eval b = false)) hA2 (fun b hb => by
      obtain ⟨hb, h⟩ := mem_filter.mp hb
      have := hB b hb; simp only [Fm.eval] at this; simp at h; simpa [h] using this)
    rw [edges_split_B A B (fun b => F1.eval b = false), ← card_filter_add_card_filter_not
      (s := B) (fun b => F1.eval b = false)]
    simp only [Fm.size]
    have := comb _ _ _ _ _ _ A.card
      (by calc _ ≤ _ := h1
              _ = F1.size * (B.filter (fun b => F1.eval b = false)).card * A.card := by ring)
      (by calc _ ≤ _ := h2
              _ = F2.size * (B.filter (fun b => ¬ F1.eval b = false)).card * A.card := by ring)
    calc _ ≤ _ := this
      _ = _ := by ring
  | or F1 F2 i1 i2 =>
    intro A B hA hB
    have hB1 : ∀ b ∈ B, F1.eval b = false := fun b hb => by
      have := hB b hb; simp [Fm.eval] at this; exact this.1
    have hB2 : ∀ b ∈ B, F2.eval b = false := fun b hb => by
      have := hB b hb; simp [Fm.eval] at this; exact this.2
    have h1 := i1 (A.filter (fun a => F1.eval a = true)) B (fun a ha => (mem_filter.mp ha).2) hB1
    have h2 := i2 (A.filter (fun a => ¬ F1.eval a = true)) B (fun a ha => by
      obtain ⟨ha, h⟩ := mem_filter.mp ha
      have := hA a ha; simp only [Fm.eval] at this; simp at h; simpa [h] using this) hB2
    rw [edges_split_A A B (fun a => F1.eval a = true), ← card_filter_add_card_filter_not
      (s := A) (fun a => F1.eval a = true)]
    simp only [Fm.size]
    exact comb _ _ _ _ _ _ _ h1 h2

/-- If F flips value along every Hamming edge (e.g. parity), then size(F) ≥ n^2. -/
theorem khrapchenko_sensitive (F : Fm n) (hn : 1 ≤ n)
    (hF : ∀ x i, F.eval (flip x i) = !F.eval x) : n ^ 2 ≤ F.size := by
  set A := univ.filter (fun x => F.eval x = true)
  set B := univ.filter (fun x => F.eval x = false)
  have hk := khrapchenko F A B (fun a ha => (mem_filter.mp ha).2) (fun b hb => (mem_filter.mp hb).2)
  have he : edges A B = A.card * n := by
    unfold edges
    rw [sum_const_nat (m := n)]
    intro a ha
    rw [filter_true_of_mem, card_univ, Fintype.card_fin]
    intro i _
    simp only [B, mem_filter, mem_univ, true_and, hF, (mem_filter.mp ha).2]; rfl
  let i0 : Fin n := ⟨0, hn⟩
  have hAB : A.card ≤ B.card := by
    apply card_le_card_of_injOn (fun a => flip a i0)
    · intro a ha; simp [A, B, hF] at ha ⊢ <;> simp [ha]
    · intro a _ b _ h; have := congrArg (fun z => flip z i0) h; simpa [flip_flip] using this
  have hBA : B.card ≤ A.card := by
    apply card_le_card_of_injOn (fun a => flip a i0)
    · intro a ha; simp [A, B, hF] at ha ⊢ <;> simp [ha]
    · intro a _ b _ h; have := congrArg (fun z => flip z i0) h; simpa [flip_flip] using this
  have hpos : 0 < A.card := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · exfalso
      have : (univ : Finset (Fin n → Bool)).card = A.card + B.card :=
        (card_filter_add_card_filter_not (s := univ) (fun x => F.eval x = true)).symm.trans
          (by simp only [A, B, Bool.not_eq_true])
      have h0 : B.card = 0 := by omega
      rw [h, h0, card_univ, Fintype.card_fun, Fintype.card_bool] at this
      exact absurd this (by positivity)
    · exact h
  have hab : B.card = A.card := le_antisymm hBA hAB
  rw [he, hab] at hk
  have : n ^ 2 * (A.card * A.card) ≤ F.size * (A.card * A.card) := by
    calc _ = (A.card * n) ^ 2 := by ring
      _ ≤ _ := hk
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos hpos hpos)

/-- KHRAPCHENKO for parity: any De Morgan formula computing XOR or XNOR of all n ≥ 1
variables has at least n^2 leaves (tight: Γ ≤ 2). -/
theorem parity_khrapchenko (F : Fm n) (hn : 1 ≤ n)
    (h : ∃ c : ZMod 2, ∀ x, b2z (F.eval x) = c + par univ x) : n ^ 2 ≤ F.size := by
  obtain ⟨c, hc⟩ := h
  apply khrapchenko_sensitive F hn
  intro x i
  have e1 := hc (flip x i); have e2 := hc x
  have hp : par univ (flip x i) = 1 + par univ x := by
    have h1 := par_update univ i (mem_univ i) (!x i) x
    have h2 := par_update univ i (mem_univ i) (x i) x
    rw [Function.update_eq_self] at h2
    unfold flip; rw [h1, h2]
    generalize par (univ.erase i) x = q
    cases x i <;> revert q <;> decide
  rw [hp] at e1
  have : b2z (F.eval (flip x i)) = b2z (F.eval x) + 1 := by rw [e1, e2]; ring
  cases h1 : F.eval (flip x i) <;> cases h2 : F.eval x <;> rw [h1, h2] at this <;>
    first | rfl | (exfalso; revert this; decide)

end Subb
