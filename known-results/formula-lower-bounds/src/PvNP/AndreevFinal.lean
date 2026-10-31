import PvNP.Andreev

/-! Round 11 (cont.): Shannon-type counting for formulas, the full Andreev function, and the
n^(2.5 - o(1)) lower bound from Subbotovskaya's exponent. -/

namespace Subb
open Fm

abbrev Tok (r : ℕ) := (Fin r × Bool) ⊕ Bool

def enc {r : ℕ} : Fm r → List (Tok r)
  | Fm.lit b s => [.inl (b, s)]
  | Fm.and A B => .inr false :: (enc A ++ enc B)
  | Fm.or A B => .inr true :: (enc A ++ enc B)

def dec {r : ℕ} : ℕ → List (Tok r) → Option (Fm r × List (Tok r))
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .inl (b, s) :: rest => some (Fm.lit b s, rest)
  | k + 1, .inr c :: rest =>
    match dec k rest with
    | none => none
    | some (A, r1) => match dec k r1 with
      | none => none
      | some (B, r2) => some (if c then Fm.or A B else Fm.and A B, r2)

theorem dec_enc {r : ℕ} : ∀ (F : Fm r) (k : ℕ) (rest : List (Tok r)),
    (enc F).length ≤ k → dec k (enc F ++ rest) = some (F, rest) := by
  intro F
  induction F with
  | lit b s => intro k rest hk; obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp [enc] at hk; omega⟩; rfl
  | and A B iA iB =>
    intro k rest hk
    simp only [enc, List.length_cons, List.length_append] at hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [enc, List.cons_append, List.append_assoc, dec]
    rw [iA k _ (by omega)]; dsimp only; rw [iB k _ (by omega)]; rfl
  | or A B iA iB =>
    intro k rest hk
    simp only [enc, List.length_cons, List.length_append] at hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [enc, List.cons_append, List.append_assoc, dec]
    rw [iA k _ (by omega)]; dsimp only; rw [iB k _ (by omega)]; rfl

theorem enc_inj {r : ℕ} {F G : Fm r} (h : enc F = enc G) : F = G := by
  have h1 := dec_enc F (enc F).length [] le_rfl
  have h2 := dec_enc G (enc F).length [] (by rw [h])
  rw [← h] at h2; rw [h1] at h2; simpa using h2

theorem enc_length {r : ℕ} (F : Fm r) : (enc F).length + 1 = 2 * F.size := by
  induction F with
  | lit b s => simp [enc, Fm.size]
  | and A B iA iB => simp only [enc, List.length_cons, List.length_append, Fm.size]; omega
  | or A B iA iB => simp only [enc, List.length_cons, List.length_append, Fm.size]; omega

def codeL {r : ℕ} (N : ℕ) (l : List (Tok r)) : Fin N → Option (Tok r) := fun i => l[i.1]?

theorem codeL_inj {r N : ℕ} {l l' : List (Tok r)} (hl : l.length ≤ N) (hl' : l'.length ≤ N)
    (h : codeL N l = codeL N l') : l = l' := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < N
  · exact congrFun h ⟨i, hi⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- SHANNON COUNTING for De Morgan formulas: if 2 + (2r+3)^(2L) < 2^(2^r) then some
r-bit function needs more than L leaves. -/
theorem exists_hard (r L : ℕ) (h : 2 + (2 * r + 3) ^ (2 * L) < 2 ^ (2 ^ r)) :
    ∃ g : (Fin r → Bool) → Bool, L < LW Finset.univ g := by
  classical
  by_contra hc
  push_neg at hc
  have hspec : ∀ g : (Fin r → Bool) → Bool, ∃ ρ, Rep Finset.univ g ρ ∧ rsize ρ = LW Finset.univ g :=
    fun g => LW_spec (rep_of_dep _ g (fun x y hxy => congrArg g (funext fun v => hxy v (by simp))))
  choose ρ hρ hsz using hspec
  let code : ((Fin r → Bool) → Bool) → Bool ⊕ (Fin (2 * L) → Option (Tok r)) := fun g =>
    match ρ g with
    | .inl c => .inl c
    | .inr F => .inr (codeL (2 * L) (enc F))
  have hinj : Function.Injective code := by
    intro g g' he
    have hrr : ρ g = ρ g' := by
      simp only [code] at he
      rcases hg : ρ g with c | F <;> rcases hg' : ρ g' with c' | F' <;> rw [hg, hg'] at he <;>
        simp at he
      · rw [he]
      · have s1 := hsz g; have s2 := hsz g'
        rw [hg] at s1; rw [hg'] at s2
        simp only [rsize_inr] at s1 s2
        have l1 := enc_length F; have l2 := enc_length F'
        have := hc g; have := hc g'
        rw [enc_inj (codeL_inj (by omega) (by omega) he)]
    funext y
    rw [← (hρ g).2 y, ← (hρ g').2 y, hrr]
  have := Fintype.card_le_of_injective code hinj
  simp [Fintype.card_sum, Fintype.card_option, Fintype.card_prod] at this
  rw [show r * 2 + 2 + 1 = 2 * r + 3 by ring] at this
  omega

theorem two_r_three (r : ℕ) (hr : 4 ≤ r) : 2 * r + 3 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

/-- For r ≥ 4 some r-bit function g has L(g) > (2^r - 2)/(2r) (as a real number). -/
theorem exists_hard' (r : ℕ) (hr : 4 ≤ r) :
    ∃ g : (Fin r → Bool) → Bool, ((2 : ℝ) ^ r - 2) / (2 * r) < LW Finset.univ g := by
  set L := (2 ^ r - 2) / (2 * r)
  have hL : 2 * r * L ≤ 2 ^ r - 2 := by
    rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have h4 : 4 ≤ 2 ^ r := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hr)
  have h1 : (2 * r + 3) ^ (2 * L) ≤ 2 ^ (2 ^ r - 2) := by
    calc (2 * r + 3) ^ (2 * L) ≤ (2 ^ r) ^ (2 * L) := Nat.pow_le_pow_left (two_r_three r hr) _
      _ = 2 ^ (2 * r * L) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ (2 ^ r - 2) := Nat.pow_le_pow_right (by norm_num) hL
  have h2 : 2 + 2 ^ (2 ^ r - 2) < 2 ^ (2 ^ r) := by
    have e : 2 ^ (2 ^ r) = 4 * 2 ^ (2 ^ r - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have : 1 ≤ 2 ^ (2 ^ r - 2) := Nat.one_le_two_pow
    omega
  obtain ⟨g, hg⟩ := exists_hard r L (by omega)
  refine ⟨g, lt_of_lt_of_le ?_ (by exact_mod_cast hg : ((L + 1 : ℕ) : ℝ) ≤ LW Finset.univ g)⟩
  have hrpos : (0 : ℝ) < 2 * r := by have : (4 : ℝ) ≤ r := by exact_mod_cast hr
                                     linarith
  rw [div_lt_iff₀ hrpos]
  have := Nat.lt_div_mul_add (a := 2 ^ r - 2) (b := 2 * r) (by omega)
  have hc : ((2 ^ r - 2 : ℕ) : ℝ) = (2 : ℝ) ^ r - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have : ((2 ^ r - 2 : ℕ) : ℝ) < ((L * (2 * r) + 2 * r : ℕ) : ℝ) := by exact_mod_cast this
  rw [hc] at this; push_cast at this ⊢; nlinarith

theorem one_sub_pow_le (r : ℕ) (hr : 4 ≤ r) :
    (r : ℝ) * (1 - (r : ℝ) / 2 ^ r) ^ (2 ^ r) ≤ 1 / 2 := by
  have hr' : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hpow : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hp : (0 : ℝ) < 2 ^ r := by positivity
  have h0 : 0 ≤ 1 - (r : ℝ) / 2 ^ r := by rw [sub_nonneg, div_le_one hp]; exact hpow
  have h1 : 1 - (r : ℝ) / 2 ^ r ≤ Real.exp (-((r : ℝ) / 2 ^ r)) := by
    linarith [Real.add_one_le_exp (-((r : ℝ) / 2 ^ r))]
  have h2 : (1 - (r : ℝ) / 2 ^ r) ^ (2 ^ r) ≤ Real.exp (-r) := by
    calc _ ≤ Real.exp (-((r : ℝ) / 2 ^ r)) ^ (2 ^ r) := pow_le_pow_left₀ h0 h1 _
      _ = Real.exp (-r) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have h3 : 2 * (r : ℝ) ≤ Real.exp r := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ r); nlinarith
  have h4 : (r : ℝ) * Real.exp (-r) ≤ 1 / 2 := by
    rw [Real.exp_neg]; rw [mul_inv_le_iff₀ (Real.exp_pos _)]; linarith
  calc (r : ℝ) * (1 - (r : ℝ) / 2 ^ r) ^ (2 ^ r) ≤ r * Real.exp (-r) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ ≤ 1 / 2 := h4

/-- ANDREEV'S BOUND WITH SUBBOTOVSKAYA'S EXPONENT (pre-Håstad). For r ≥ 4 and s = 2^r there is
an outer function g such that the function A_g(x) = g(XOR of each of the r blocks of size 2^r)
on m = r·2^r variables satisfies
  L(A_g) · (r/2^r)^(3/2) ≥ (2^r - 2)/(4r) - 1,
i.e. L(A_g) ≥ ((2^r-2)/(4r) - 1)·(2^r/r)^(3/2) = n^(2.5 - o(1)) for n = 2^r + r·2^r. -/
theorem andreev_subbotovskaya (r : ℕ) (hr : 4 ≤ r) :
    ∃ g : (Fin r → Bool) → Bool,
      ((2 : ℝ) ^ r - 2) / (4 * r) - 1 ≤
        ((r : ℝ) / 2 ^ r) ^ (3 / 2 : ℝ) * LW Finset.univ (AndreevG (s := 2 ^ r) g) := by
  obtain ⟨g, hg⟩ := exists_hard' r hr
  refine ⟨g, ?_⟩
  have hrr : r * r ≤ r * 2 ^ r := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self).le
  have hm : 1 ≤ r * 2 ^ r := Nat.mul_pos (by omega) (Nat.two_pow_pos r)
  have hred := andreev_reduction (s := 2 ^ r) g (r * 2 ^ r - r * r) hm (Nat.sub_le _ _)
  have hk : r * 2 ^ r - (r * 2 ^ r - r * r) = r * r := Nat.sub_sub_self hrr
  rw [hk] at hred
  have hp : (0 : ℝ) < 2 ^ r := by positivity
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have e1 : ((r * r : ℕ) : ℝ) / ((r * 2 ^ r : ℕ) : ℝ) = (r : ℝ) / 2 ^ r := by
    push_cast; field_simp
  have e2 : (((r * 2 ^ r - r * r : ℕ) : ℝ)) / ((r * 2 ^ r : ℕ) : ℝ) = 1 - (r : ℝ) / 2 ^ r := by
    rw [Nat.cast_sub hrr]; push_cast; field_simp
  rw [e1, e2] at hred
  have hq := one_sub_pow_le r hr
  set Lg := (LW Finset.univ g : ℝ)
  have hLg : 0 ≤ Lg := by
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ r - 2) / (2 * r) := by
      apply div_nonneg _ (by linarith)
      have : (4 : ℝ) ≤ 2 ^ r := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hr
        exact_mod_cast (le_trans (by norm_num) this)
      linarith
    linarith
  have hhalf : Lg * (1 / 2) ≤ Lg * (1 - r * (1 - (r : ℝ) / 2 ^ r) ^ (2 ^ r)) := by
    apply mul_le_mul_of_nonneg_left _ hLg; linarith
  have e3 : ((2 : ℝ) ^ r - 2) / (4 * r) = (((2 : ℝ) ^ r - 2) / (2 * r)) * (1 / 2) := by
    field_simp; ring
  rw [e3]
  nlinarith

/-! ## The full Andreev function (truth table of g as part of the input). -/

/-- Substitute literals: mapped variables become (possibly negated) target variables,
unmapped ones become the constant `val j`. -/
def substW {n n' : ℕ} (σ : Fin n → Option (Fin n' × Bool)) (val : Fin n → Bool) : Fm n → Res n'
  | Fm.lit j t => match σ j with
    | some (b, c) => .inr (Fm.lit b (xor t c))
    | none => .inl (decide (val j = t))
  | Fm.and A B => mkAnd (substW σ val A) (substW σ val B)
  | Fm.or A B => mkOr (substW σ val A) (substW σ val B)

def xyV {n n' : ℕ} (σ : Fin n → Option (Fin n' × Bool)) (val : Fin n → Bool) (y : Fin n' → Bool) :
    Fin n → Bool := fun j => match σ j with
    | some (b, c) => xor (y b) c
    | none => val j

theorem reval_substW {n n' : ℕ} (σ : Fin n → Option (Fin n' × Bool)) (val) (y) :
    ∀ F, reval (substW σ val F) y = F.eval (xyV σ val y) := by
  intro F
  induction F with
  | lit j t =>
    cases h : σ j with
    | none => simp [substW, xyV, h, reval, Fm.eval]
    | some p =>
      obtain ⟨b, c⟩ := p
      simp only [substW, xyV, h, reval_inr, Fm.eval]
      cases y b <;> cases c <;> cases t <;> rfl
  | and A B iA iB => simp [substW, reval_mkAnd, iA, iB, Fm.eval]
  | or A B iA iB => simp [substW, reval_mkOr, iA, iB, Fm.eval]

theorem rsize_substW {n n' : ℕ} (σ : Fin n → Option (Fin n' × Bool)) (val) :
    ∀ F, rsize (substW σ val F) ≤ F.size := by
  intro F
  induction F with
  | lit j t => cases h : σ j <;> simp [substW, h, rsize, Fm.size]
  | and A B iA iB =>
    have := rsize_mkAnd (substW σ val A) (substW σ val B); simp only [substW, Fm.size]; omega
  | or A B iA iB =>
    have := rsize_mkOr (substW σ val A) (substW σ val B); simp only [substW, Fm.size]; omega

/-- Subfunction monotonicity: substituting literals/constants cannot increase complexity. -/
theorem LW_subfun {n n' : ℕ} (σ : Fin n → Option (Fin n' × Bool)) (val : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) (h : (Fin n' → Bool) → Bool)
    (hh : ∀ y, h y = f (xyV σ val y)) : LW Finset.univ h ≤ LW Finset.univ f := by
  obtain ⟨ρ, hρ, hsz⟩ := LW_spec (rep_of_dep Finset.univ f
    (fun x y hxy => congrArg f (funext fun v => hxy v (Finset.mem_univ v))))
  rcases ρ with c | F
  · have hr : Rep Finset.univ h (.inl c) := ⟨fun j hj => by simp [rcnt] at hj, fun y => by
      rw [hh, ← hρ.2]; rfl⟩
    have := LW_le hr; simp [rsize] at this; omega
  · have hr : Rep Finset.univ h (substW σ val F) := ⟨fun j _ => Finset.mem_univ j, fun y => by
      rw [hh, ← hρ.2, reval_substW]; rfl⟩
    have := LW_le hr; have := rsize_substW σ val F; simp only [rsize_inr] at hsz; omega

noncomputable def eqvTT (r : ℕ) : (Fin r → Bool) ≃ Fin (2 ^ r) :=
  Fintype.equivFinOfCardEq (by simp)

/-- ANDREEV'S FUNCTION on 2^r + r·s bits: the first 2^r bits are a truth table T of an r-bit
function, the rest are r blocks of s bits; output T(XOR block_1, ..., XOR block_r). -/
noncomputable def Andreev (r s : ℕ) (x : Fin (2 ^ r + r * s) → Bool) : Bool :=
  x (Fin.castAdd (r * s) (eqvTT r (blk (s := s) (fun k => x (Fin.natAdd (2 ^ r) k)))))

theorem LW_AndreevG_le (r s : ℕ) (g : (Fin r → Bool) → Bool) :
    LW Finset.univ (AndreevG (s := s) g) ≤ LW Finset.univ (Andreev r s) := by
  apply LW_subfun (Fin.addCases (fun _ => none) (fun k => some (k, false)))
    (Fin.addCases (fun i => g ((eqvTT r).symm i)) (fun _ => false))
  intro y
  simp only [Andreev, xyV, Fin.addCases_left, Fin.addCases_right, Bool.xor_false,
    Equiv.symm_apply_apply, AndreevG]

/-- ANDREEV'S BOUND, pre-Håstad (Subbotovskaya exponent 3/2), for the explicit Andreev
function on n = 2^r + r·2^r bits, r ≥ 4:
  L(Andreev) · (r/2^r)^(3/2) ≥ (2^r - 2)/(4r) - 1.
Since n ≈ r·2^r this is L ≥ n^(5/2) / poly(log n), i.e. n^(2.5 - o(1)). -/
theorem andreev_lower_bound (r : ℕ) (hr : 4 ≤ r) :
    ((2 : ℝ) ^ r - 2) / (4 * r) - 1 ≤
      ((r : ℝ) / 2 ^ r) ^ (3 / 2 : ℝ) * LW Finset.univ (Andreev r (2 ^ r)) := by
  obtain ⟨g, hg⟩ := andreev_subbotovskaya r hr
  refine hg.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact_mod_cast LW_AndreevG_le r (2 ^ r) g

end Subb
