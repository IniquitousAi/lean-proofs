import PvNP.Khrapchenko

/-! Round 13 (a): the easy upper bound L(XOR_{2^k}) ≤ 4^k, so with Khrapchenko
L(XOR_{2^k}) = 4^k exactly. -/

namespace Subb
open Finset

variable {n : ℕ}

def NN : ℕ → ℕ
  | 0 => 1
  | k + 1 => NN k + NN k

theorem NN_eq : ∀ k, NN k = 2 ^ k
  | 0 => rfl
  | k + 1 => by rw [NN, NN_eq k, pow_succ]; ring

/-- xorF k v true computes XOR of x(v i); xorF k v false computes XNOR. -/
def z0 : Fin (NN 0) := ⟨0, by simp [NN]⟩

def xorF : (k : ℕ) → (Fin (NN k) → Fin n) → Bool → Fm n
  | 0, v, b => Fm.lit (v z0) b
  | k + 1, v, true =>
      Fm.or (Fm.and (xorF k (fun i => v (Fin.castAdd _ i)) true) (xorF k (fun i => v (Fin.natAdd _ i)) false))
            (Fm.and (xorF k (fun i => v (Fin.castAdd _ i)) false) (xorF k (fun i => v (Fin.natAdd _ i)) true))
  | k + 1, v, false =>
      Fm.or (Fm.and (xorF k (fun i => v (Fin.castAdd _ i)) true) (xorF k (fun i => v (Fin.natAdd _ i)) true))
            (Fm.and (xorF k (fun i => v (Fin.castAdd _ i)) false) (xorF k (fun i => v (Fin.natAdd _ i)) false))

theorem z2b_add (a b : ZMod 2) : z2b (a + b) = xor (z2b a) (z2b b) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem xorF_spec : ∀ k (v : Fin (NN k) → Fin n) (x : Fin n → Bool),
    (xorF k v true).eval x = z2b (∑ i, b2z (x (v i))) ∧
    (xorF k v false).eval x = !z2b (∑ i, b2z (x (v i))) := by
  intro k; induction k with
  | zero =>
    intro v x
    have : (Finset.univ : Finset (Fin (NN 0))) = {z0} := by
      ext i; simp only [mem_univ, mem_singleton, true_iff]; ext; have := i.2; simp [NN] at this; simp [z0, this]
    rw [this, sum_singleton]
    simp only [xorF, Fm.eval]
    generalize x (v z0) = c
    constructor <;> cases c <;> rfl
  | succ k ih =>
    intro v x
    obtain ⟨a1, a2⟩ := ih (fun i => v (Fin.castAdd _ i)) x
    obtain ⟨b1, b2⟩ := ih (fun i => v (Fin.natAdd _ i)) x
    have hs : ∑ i : Fin (NN (k + 1)), b2z (x (v i)) =
        ∑ i : Fin (NN k), b2z (x (v (Fin.castAdd _ i))) + ∑ i : Fin (NN k), b2z (x (v (Fin.natAdd _ i))) :=
      Fin.sum_univ_add (fun i => b2z (x (v i)))
    rw [hs, z2b_add]
    simp only [xorF, Fm.eval, a1, a2, b1, b2]
    constructor <;> cases z2b (∑ i : Fin (NN k), b2z (x (v (Fin.castAdd _ i)))) <;>
      cases z2b (∑ i : Fin (NN k), b2z (x (v (Fin.natAdd _ i)))) <;> rfl

theorem xorF_size : ∀ k (v : Fin (NN k) → Fin n) b, (xorF k v b).size = 4 ^ k := by
  intro k; induction k with
  | zero => intro v b; simp [xorF, Fm.size]
  | succ k ih => intro v b; cases b <;> simp [xorF, Fm.size, ih, pow_succ] <;> ring

/-- PARITY UPPER BOUND: XOR of n = 2^k variables has a De Morgan formula with n^2 leaves. -/
theorem parity_upper (k : ℕ) : ∃ F : Fm (2 ^ k),
    (∀ x, b2z (F.eval x) = par univ x) ∧ F.size = (2 ^ k) ^ 2 := by
  have h := NN_eq k
  refine ⟨xorF k (Fin.cast h) true, fun x => ?_, ?_⟩
  · rw [(xorF_spec k _ x).1, b2z_z2b, par]
    exact Fintype.sum_equiv (finCongr h) _ _ (fun i => rfl)
  · rw [xorF_size, ← pow_mul, mul_comm, pow_mul]; norm_num

/-- Tight: L(XOR_{2^k}) = 4^k, combining parity_upper with parity_khrapchenko. -/
theorem parity_tight (k : ℕ) :
    (∃ F : Fm (2 ^ k), (∀ x, b2z (F.eval x) = par univ x) ∧ F.size = (2 ^ k) ^ 2) ∧
    ∀ F : Fm (2 ^ k), (∃ c : ZMod 2, ∀ x, b2z (F.eval x) = c + par univ x) → (2 ^ k) ^ 2 ≤ F.size :=
  ⟨parity_upper k, fun F hF => parity_khrapchenko F (Nat.one_le_two_pow) hF⟩

end Subb
