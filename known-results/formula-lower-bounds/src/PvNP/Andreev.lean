import PvNP.SubbotovskayaRandom

/-! Round 11: generic averaging over the sequential restriction process, block-survival
bound, and the Andreev reduction with Subbotovskaya's exponent 3/2. -/

namespace Subb
open Fm

variable {n : ℕ}

abbrev Pot (n : ℕ) := Finset (Fin n) → ((Fin n → Bool) → Bool) → ℝ

/-- Average of a potential over the sequential process (uniform remaining variable,
uniform bit), after j steps. -/
noncomputable def Avg (Φ : Pot n) : ℕ → Finset (Fin n) → ((Fin n → Bool) → Bool) → ℝ
  | 0, W, f => Φ W f
  | j + 1, W, f => if W.card = 0 then Φ W f else
      (∑ i ∈ W, (Avg Φ j (W.erase i) (fix f i false) + Avg Φ j (W.erase i) (fix f i true)))
        / (2 * W.card)

theorem Eres_eq_Avg : ∀ j (W : Finset (Fin n)) f,
    Eres j W f = Avg (fun W f => (LW W f : ℝ)) j W f := by
  intro j; induction j with
  | zero => intros; rfl
  | succ j ih => intro W f; simp only [Eres, Avg, ih]

theorem Avg_mono (I : Finset (Fin n) → ((Fin n → Bool) → Bool) → Prop)
    (hI : ∀ W f i b, I W f → I (W.erase i) (fix f i b)) (Φ Ψ : Pot n)
    (h : ∀ W f, I W f → Φ W f ≤ Ψ W f) : ∀ j W f, I W f → Avg Φ j W f ≤ Avg Ψ j W f := by
  intro j; induction j with
  | zero => intro W f hf; exact h W f hf
  | succ j ih =>
    intro W f hf; simp only [Avg]; split_ifs
    · exact h W f hf
    · exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
        add_le_add (ih _ _ (hI _ _ _ _ hf)) (ih _ _ (hI _ _ _ _ hf))) (by positivity)

theorem Avg_affine (Φ : Pot n) (a c : ℝ) : ∀ j W f,
    Avg (fun W f => a * Φ W f + c) j W f = a * Avg Φ j W f + c := by
  intro j; induction j with
  | zero => intros; rfl
  | succ j ih =>
    intro W f; simp only [Avg]; split_ifs with h0
    · rfl
    · simp only [ih]
      have hm : (W.card : ℝ) ≠ 0 := by exact_mod_cast h0
      rw [show (∑ i ∈ W, (a * Avg Φ j (W.erase i) (fix f i false) + c +
          (a * Avg Φ j (W.erase i) (fix f i true) + c))) = a * ∑ i ∈ W,
          (Avg Φ j (W.erase i) (fix f i false) + Avg Φ j (W.erase i) (fix f i true))
          + 2 * W.card * c by
        rw [Finset.mul_sum, show (2 * (W.card : ℝ) * c) = ∑ i ∈ W, 2 * c by
          rw [Finset.sum_const, nsmul_eq_mul]; ring, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)]
      field_simp

theorem Avg_sum {ι : Type*} (T : Finset ι) (Φ : ι → Pot n) : ∀ j W f,
    Avg (fun W f => ∑ b ∈ T, Φ b W f) j W f = ∑ b ∈ T, Avg (Φ b) j W f := by
  intro j; induction j with
  | zero => intros; rfl
  | succ j ih =>
    intro W f; simp only [Avg]; split_ifs
    · rfl
    · simp only [ih]
      rw [← Finset.sum_div]; congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib.symm)

theorem bern_pow (x d : ℝ) (hx : 0 ≤ x) (hd : 0 ≤ d) :
    ∀ u : ℕ, x ^ (u + 1) + (u + 1) * x ^ u * d ≤ (x + d) ^ (u + 1) := by
  intro u
  induction u with
  | zero => simp
  | succ u ih =>
    have h1 : 0 ≤ x + d := by linarith
    have h2 := mul_le_mul_of_nonneg_right ih h1
    have h3 : 0 ≤ x ^ u := pow_nonneg hx u
    push_cast
    calc x ^ (u + 1 + 1) + (u + 1 + 1) * x ^ (u + 1) * d
        ≤ (x ^ (u + 1) + (u + 1) * x ^ u * d) * (x + d) := by
          ring_nf; nlinarith [mul_nonneg (mul_nonneg h3 hd) hd, mul_nonneg h3 (Nat.cast_nonneg u : (0:ℝ) ≤ u)]
      _ ≤ (x + d) ^ (u + 1) * (x + d) := h2
      _ = (x + d) ^ (u + 1 + 1) := by ring

/-- One-step inequality for the block-survival recursion. -/
theorem surv_step (m j u : ℕ) (hj : j + 1 ≤ m) (hu : u + 1 ≤ m) :
    ((u + 1 : ℕ) : ℝ) * ((j : ℝ) / ((m - 1 : ℕ) : ℝ)) ^ u
      + ((m - (u + 1) : ℕ) : ℝ) * ((j : ℝ) / ((m - 1 : ℕ) : ℝ)) ^ (u + 1)
      ≤ m * (((j + 1 : ℕ) : ℝ) / m) ^ (u + 1) := by
  set x := (j : ℝ) / ((m - 1 : ℕ) : ℝ)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rcases Nat.eq_zero_or_pos (m - 1) with h | h
    · simp [x, h]
    · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast (by omega : j ≤ m - 1)
  have hy : (((j + 1 : ℕ) : ℝ) / m) = x + (1 - x) / m := by
    rcases Nat.eq_zero_or_pos (m - 1) with h | h
    · have : m = 1 := by omega
      have : j = 0 := by omega
      subst_vars; simp [x]
    · have hm1 : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hpos : (0 : ℝ) < m - 1 := by rw [← hm1]; exact_mod_cast h
      simp only [x, hm1]; field_simp; push_cast; ring
  rw [hy]
  have hd : 0 ≤ (1 - x) / m := div_nonneg (by linarith) (by linarith)
  have hb := bern_pow x ((1 - x) / m) hx0 hd u
  have hmu : ((m - (u + 1) : ℕ) : ℝ) = m - (u + 1) := by rw [Nat.cast_sub hu]; push_cast; ring
  rw [hmu]; push_cast
  have e : (m : ℝ) * ((u + 1) * x ^ u * ((1 - x) / m)) = (u + 1) * x ^ u * (1 - x) := by
    field_simp
  have h := mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ m)
  rw [mul_add, e] at h
  have eq : ((u : ℝ) + 1) * x ^ u + (m - (u + 1)) * x ^ (u + 1)
      = m * x ^ (u + 1) + (u + 1) * x ^ u * (1 - x) := by ring
  linarith

/-- Probability (under the sequential process) that a set B is entirely fixed after j steps
is at most (j/m)^|B ∩ W|. -/
theorem surv_bound (B : Finset (Fin n)) : ∀ j (W : Finset (Fin n)) f, j ≤ W.card →
    Avg (fun W _ => if Disjoint B W then (1 : ℝ) else 0) j W f
      ≤ ((j : ℝ) / W.card) ^ (B ∩ W).card := by
  intro j
  induction j with
  | zero =>
    intro W f _
    simp only [Avg]
    split_ifs with h
    · rw [Finset.disjoint_iff_inter_eq_empty.mp h]; simp
    · positivity
  | succ j ih =>
    intro W f hj
    simp only [Avg]
    rw [if_neg (by omega)]
    set m := W.card with hm
    set t := (B ∩ W).card with ht
    set x := (j : ℝ) / ((m - 1 : ℕ) : ℝ)
    have hcard : ∀ i ∈ W, (W.erase i).card = m - 1 := fun i hi => Finset.card_erase_of_mem hi
    have hQ : ∀ i ∈ W, ∀ b, Avg (fun W _ => if Disjoint B W then (1 : ℝ) else 0) j
        (W.erase i) (fix f i b) ≤ if i ∈ B then x ^ (t - 1) else x ^ t := by
      intro i hi b
      have := ih (W.erase i) (fix f i b) (by rw [hcard i hi]; omega)
      rw [hcard i hi, Finset.inter_erase] at this
      split_ifs with hB
      · rwa [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hB, hi⟩)] at this
      · rwa [Finset.erase_eq_of_notMem (fun h => hB (Finset.mem_inter.mp h).1)] at this
    have hpos : (0 : ℝ) < 2 * m := by
      have : 0 < m := by omega
      positivity
    rw [div_le_iff₀ hpos]
    calc _ ≤ ∑ i ∈ W, (2 * if i ∈ B then x ^ (t - 1) else x ^ t) :=
          Finset.sum_le_sum fun i hi => by have := hQ i hi false; have := hQ i hi true; linarith
      _ = 2 * ((t : ℝ) * x ^ (t - 1) + ((m - t : ℕ) : ℝ) * x ^ t) := by
          rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
            Finset.filter_mem_eq_inter, Finset.inter_comm, nsmul_eq_mul, nsmul_eq_mul]
          congr 3
          have := Finset.card_filter_add_card_filter_not (s := W) (p := fun i => i ∈ B)
          rw [Finset.filter_mem_eq_inter, Finset.inter_comm] at this
          rw [← ht] at this
          congr 1; omega
      _ ≤ (((j + 1 : ℕ) : ℝ) / m) ^ t * (2 * m) := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · rw [h0]; simp
          · obtain ⟨u, hu⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
            have htm : u + 1 ≤ m := by
              rw [← hu, ht]; exact Finset.card_le_card Finset.inter_subset_right
            have := surv_step m j u (by omega) htm
            rw [hu, Nat.add_sub_cancel]
            push_cast at this ⊢
            nlinarith
    -- leftover cast normalisation handled above

/-! ## Every function depending only on W has a W-formula (Shannon expansion). -/

def DepOn (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ j ∈ W, x j = y j) → f x = f y

theorem rep_of_dep (W : Finset (Fin n)) : ∀ f, DepOn W f → ∃ r, Rep W f r := by
  induction W using Finset.induction_on with
  | empty =>
    intro f hf
    exact ⟨.inl (f fun _ => false), fun j hj => by simp [rcnt] at hj,
      fun x => hf _ _ (by simp)⟩
  | insert i W hi ih =>
    intro f hf
    have hd : ∀ b, DepOn W (fix f i b) := fun b x y hxy => hf _ _ (fun j hj => by
      by_cases h : j = i
      · subst h; simp
      · rw [Function.update_of_ne h, Function.update_of_ne h]
        exact hxy j ((Finset.mem_insert.mp hj).resolve_left h))
    obtain ⟨r0, h0v, h0e⟩ := ih _ (hd false)
    obtain ⟨r1, h1v, h1e⟩ := ih _ (hd true)
    refine ⟨mkOr (mkAnd (.inr (Fm.lit i true)) r1) (mkAnd (.inr (Fm.lit i false)) r0),
      fun j hj => ?_, fun x => ?_⟩
    · have a := rcnt_mkOr j (mkAnd (.inr (Fm.lit i true)) r1) (mkAnd (.inr (Fm.lit i false)) r0)
      have b := rcnt_mkAnd j (.inr (Fm.lit i true)) r1
      have c := rcnt_mkAnd j (.inr (Fm.lit i false)) r0
      simp only [rcnt_inr, Fm.cnt] at b c
      by_cases h : i = j
      · subst h; exact Finset.mem_insert_self _ _
      · simp only [h, if_false] at b c
        apply Finset.mem_insert_of_mem
        by_cases h1 : 0 < rcnt j r1
        · exact h1v j h1
        · exact h0v j (by omega)
    · rw [reval_mkOr, reval_mkAnd, reval_mkAnd, h0e, h1e]
      simp only [reval_inr, Fm.eval, fix]
      have hu0 : ∀ b, x i = b → Function.update x i b = x :=
        fun b h => h ▸ Function.update_eq_self i x
      cases hx : x i <;> simp [hu0 _ hx]

/-! ## Andreev's function with a fixed outer function g. -/

def z2b (z : ZMod 2) : Bool := decide (z = 1)

theorem b2z_z2b (z : ZMod 2) : b2z (z2b z) = z := by fin_cases z <;> rfl
theorem z2b_b2z (a : Bool) : z2b (b2z a) = a := by cases a <;> decide
theorem b2z_xor (a c : Bool) : b2z (xor a c) = b2z a + b2z c := by
  cases a <;> cases c <;> decide
theorem zz (z : ZMod 2) : z + z = 0 := by fin_cases z <;> rfl

variable {r s : ℕ}

/-- Parity of block b (variables e(b,0..s-1)). -/
def blk (x : Fin (r * s) → Bool) (b : Fin r) : Bool :=
  z2b (∑ t : Fin s, b2z (x (finProdFinEquiv (b, t))))

/-- Andreev's function with outer function g: A_g(x) = g(XOR block_1, ..., XOR block_r). -/
def AndreevG (g : (Fin r → Bool) → Bool) : (Fin (r * s) → Bool) → Bool := fun x => g (blk x)

def block (b : Fin r) : Finset (Fin (r * s)) :=
  Finset.univ.image (fun t : Fin s => finProdFinEquiv (b, t))

theorem card_block (b : Fin r) : (block (s := s) b).card = s := by
  rw [block, Finset.card_image_of_injective _ (fun t t' h => by simpa using h)]; simp

/-- Substitution: chosen variables become (possibly negated) outer variables, the rest
become constant false. -/
def subst (σ : Fin (r * s) → Option (Fin r × Bool)) : Fm (r * s) → Res r
  | Fm.lit j t => match σ j with
    | some (b, c) => .inr (Fm.lit b (xor t c))
    | none => .inl (decide (false = t))
  | Fm.and A B => mkAnd (subst σ A) (subst σ B)
  | Fm.or A B => mkOr (subst σ A) (subst σ B)

def xy (σ : Fin (r * s) → Option (Fin r × Bool)) (y : Fin r → Bool) : Fin (r * s) → Bool :=
  fun j => match σ j with
    | some (b, c) => xor (y b) c
    | none => false

theorem reval_subst (σ : Fin (r * s) → Option (Fin r × Bool)) (y) :
    ∀ F, reval (subst σ F) y = F.eval (xy σ y) := by
  intro F
  induction F with
  | lit j t =>
    cases h : σ j with
    | none => simp [subst, xy, h, reval, Fm.eval]
    | some p =>
      obtain ⟨b, c⟩ := p
      simp only [subst, xy, h, reval_inr, Fm.eval]
      cases y b <;> cases c <;> cases t <;> rfl
  | and A B iA iB => simp [subst, reval_mkAnd, iA, iB, Fm.eval]
  | or A B iA iB => simp [subst, reval_mkOr, iA, iB, Fm.eval]

theorem rsize_subst (σ : Fin (r * s) → Option (Fin r × Bool)) :
    ∀ F, rsize (subst σ F) ≤ F.size := by
  intro F
  induction F with
  | lit j t => cases h : σ j <;> simp [subst, h, rsize, Fm.size]
  | and A B iA iB =>
    have := rsize_mkAnd (subst σ A) (subst σ B); simp only [subst, Fm.size]; omega
  | or A B iA iB =>
    have := rsize_mkOr (subst σ A) (subst σ B); simp only [subst, Fm.size]; omega

def substR (σ : Fin (r * s) → Option (Fin r × Bool)) : Res (r * s) → Res r
  | .inl c => .inl c
  | .inr F => subst σ F

/-- Invariant of the process started at A_g: f is A_g with the variables outside W fixed. -/
def Inv (g : (Fin r → Bool) → Bool) (W : Finset (Fin (r * s))) (f : (Fin (r * s) → Bool) → Bool) :
    Prop := ∃ z : Fin (r * s) → Bool, ∀ x, f x = AndreevG g (fun v => if v ∈ W then x v else z v)

theorem Inv_fix (g : (Fin r → Bool) → Bool) (W : Finset (Fin (r * s))) (f) (i : Fin (r * s)) (b : Bool) (h : Inv g W f) :
    Inv g (W.erase i) (fix f i b) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨fun v => if v = i then (if i ∈ W then b else z i) else z v, fun x => ?_⟩
  rw [fix, hz]; congr 1; funext v
  by_cases hv : v = i
  · subst hv; by_cases hi : v ∈ W <;> simp [hi]
  · by_cases hw : v ∈ W <;> simp [hv, hw, Function.update_of_ne hv]

theorem Inv_dep (g : (Fin r → Bool) → Bool) (W : Finset (Fin (r * s))) (f) (h : Inv g W f) : DepOn W f := by
  obtain ⟨z, hz⟩ := h
  intro x y hxy; rw [hz, hz]; congr 1; funext v
  by_cases hv : v ∈ W <;> simp [hv, hxy]

theorem block_mem (b : Fin r) (v : Fin (r * s)) : v ∈ block (s := s) b ↔ (finProdFinEquiv.symm v).1 = b := by
  constructor
  · intro h; obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h; simp
  · intro h; refine Finset.mem_image.mpr ⟨(finProdFinEquiv.symm v).2, Finset.mem_univ _, ?_⟩
    rw [← h, Prod.mk.eta]; exact finProdFinEquiv.apply_symm_apply v

/-- Subfunction lemma: if every block keeps a free variable, the restricted function is at
least as hard as g. -/
theorem LW_ge_g (g : (Fin r → Bool) → Bool) (W : Finset (Fin (r * s))) (f) (hI : Inv g W f)
    (hb : ∀ b, ∃ v ∈ W, v ∈ block (s := s) b) : LW Finset.univ g ≤ LW W f := by
  classical
  obtain ⟨ρ, hρ, hsz⟩ := LW_spec (rep_of_dep W f (Inv_dep g W f hI))
  obtain ⟨z, hz⟩ := hI
  choose vs hvW hvB using hb
  let bo : Fin (r * s) → Fin r := fun v => (finProdFinEquiv.symm v).1
  let w0 : Fin (r * s) → Bool := fun v => if v ∈ W then false else z v
  let c : Fin r → Bool := fun b => z2b (∑ t : Fin s, b2z (w0 (finProdFinEquiv (b, t))))
  let σ : Fin (r * s) → Option (Fin r × Bool) :=
    fun v => if v = vs (bo v) then some (bo v, c (bo v)) else none
  have hbo : ∀ b, bo (vs b) = b := fun b => (block_mem b _).mp (hvB b)
  have key : ∀ y, f (xy σ y) = g y := by
    intro y
    rw [hz]; unfold AndreevG; congr 1; funext b
    unfold blk
    have hu : ∀ t : Fin s, b2z ((fun v => if v ∈ W then xy σ y v else z v) (finProdFinEquiv (b, t)))
        = b2z (w0 (finProdFinEquiv (b, t))) +
          (if t = (finProdFinEquiv.symm (vs b)).2 then b2z (xor (y b) (c b)) else 0) := by
      intro t
      have hbt : bo (finProdFinEquiv (b, t)) = b := by simp only [bo, Equiv.symm_apply_apply]
      by_cases ht : t = (finProdFinEquiv.symm (vs b)).2
      · have hv : finProdFinEquiv (b, t) = vs b := by
          have : (b, t) = finProdFinEquiv.symm (vs b) := Prod.ext (hbo b).symm ht
          rw [this, Equiv.apply_symm_apply]
        simp only [ht, if_true]
        rw [← ht, hv]
        simp [hvW b, w0, xy, σ, hbo b, b2z]
      · have hv : finProdFinEquiv (b, t) ≠ vs b := by
          intro h; apply ht; rw [← h]; simp
        simp only [ht, if_false, add_zero]
        by_cases hw : finProdFinEquiv (b, t) ∈ W
        · simp [hw, w0, xy, σ, hbt, hv]
        · simp [hw, w0]
    simp only [hu, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      b2z_xor, b2z_z2b]
    rw [show b2z (c b) = ∑ t : Fin s, b2z (w0 (finProdFinEquiv (b, t))) from b2z_z2b _]
    rw [show ∀ P Q : ZMod 2, P + (Q + P) = Q from fun P Q => by
      rw [add_comm Q, ← add_assoc, zz, zero_add], z2b_b2z]
  have hrep : Rep Finset.univ g (substR σ ρ) := ⟨fun j _ => Finset.mem_univ j, fun y => by
    rw [← key y, ← hρ.2]
    rcases ρ with c0 | F
    · rfl
    · exact reval_subst σ y F⟩
  calc LW Finset.univ g ≤ rsize (substR σ ρ) := LW_le hrep
    _ ≤ rsize ρ := by rcases ρ with c0 | F; · exact le_rfl
                      · exact rsize_subst σ F
    _ = LW W f := hsz

/-- ANDREEV REDUCTION (Subbotovskaya exponent). For every outer function g on r bits and
every number j ≤ m = r·s of randomly fixed variables:
  L(g)·(1 - r·(j/m)^s) - 1 ≤ ((m-j)/m)^(3/2) · L(A_g). -/
theorem andreev_reduction (g : (Fin r → Bool) → Bool) (j : ℕ) (hm : 1 ≤ r * s) (hj : j ≤ r * s) :
    (LW Finset.univ g : ℝ) * (1 - r * ((j : ℝ) / ((r * s : ℕ) : ℝ)) ^ s) - 1
      ≤ ((((r * s) - j : ℕ) : ℝ) / ((r * s : ℕ) : ℝ)) ^ (3 / 2 : ℝ)
          * LW Finset.univ (AndreevG (s := s) g) := by
  classical
  set A := AndreevG (s := s) g
  set U := (Finset.univ : Finset (Fin (r * s)))
  set Lg := (LW Finset.univ g : ℝ)
  have hLg : 0 ≤ Lg := Nat.cast_nonneg _
  have hrep : ∃ ρ, Rep U A ρ :=
    rep_of_dep U A (fun x y h => congrArg A (funext fun v => h v (Finset.mem_univ v)))
  have hup := subbotovskaya_random j (r * s) U A (by simp [U]) hm hj hrep
  have hI0 : Inv g U A := ⟨fun _ => false, fun x => by simp [A, U]⟩
  let D : Fin r → Pot (r * s) := fun b W _ => if Disjoint (block b) W then 1 else 0
  have hpt : ∀ W f, Inv g W f → -Lg * (∑ b, D b W f) + Lg ≤ (LW W f : ℝ) := by
    intro W f hI
    by_cases hall : ∀ b, ¬ Disjoint (block (s := s) b) W
    · have h0 : (∑ b, D b W f) = 0 := Finset.sum_eq_zero fun b _ => by simp [D, hall b]
      rw [h0]
      have := LW_ge_g g W f hI (fun b => by
        obtain ⟨v, h1, h2⟩ := Finset.not_disjoint_iff.mp (hall b); exact ⟨v, h2, h1⟩)
      simp only [mul_zero, zero_add, Lg]; exact_mod_cast this
    · push_neg at hall
      obtain ⟨b0, hb0⟩ := hall
      have h1 : D b0 W f ≤ ∑ b, D b W f :=
        Finset.single_le_sum (f := fun b => D b W f) (fun b _ => by
          simp only [D]; split_ifs <;> norm_num) (Finset.mem_univ b0)
      have h2 : D b0 W f = 1 := by simp [D, hb0]
      have : (0 : ℝ) ≤ LW W f := Nat.cast_nonneg _
      nlinarith
  have hlow := Avg_mono (Inv g) (fun W f i b h => Inv_fix g W f i b h)
    (fun W f => -Lg * (∑ b, D b W f) + Lg) (fun W f => (LW W f : ℝ)) hpt j U A hI0
  rw [Avg_affine (fun W f => ∑ b, D b W f) (-Lg) Lg, Avg_sum, ← Eres_eq_Avg] at hlow
  have hD : ∀ b, Avg (D b) j U A ≤ ((j : ℝ) / ((r * s : ℕ) : ℝ)) ^ s := by
    intro b
    have := surv_bound (block (s := s) b) j U A (by simp [U, hj])
    simpa [U, card_block] using this
  have hsum : ∑ b, Avg (D b) j U A ≤ r * ((j : ℝ) / ((r * s : ℕ) : ℝ)) ^ s := by
    calc _ ≤ ∑ _b : Fin r, ((j : ℝ) / ((r * s : ℕ) : ℝ)) ^ s := Finset.sum_le_sum fun b _ => hD b
      _ = _ := by simp
  nlinarith [mul_le_mul_of_nonneg_left hsum hLg]

end Subb
