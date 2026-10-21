import Mathlib

/-!
# p02, p37, p52: coin runs and walks, proven about the step lists themselves

Each headline theorem counts, over all 2^n equally likely lists of n coin flips or walk steps (true = heads or +1), the lists
with the problem's own property, and states the exact chance the engine reports. The count is proven by splitting off the first
flip (a recursion over the flips left), then the kernel evaluates that recursion (`decide +kernel`, no extra axiom).
-/

open Finset

namespace Walks

/-- One step of a walk: +1 for true, -1 for false. -/
def st (b : Bool) : ℤ := if b then 1 else -1

theorem card_cons {n : ℕ} (P : (Fin (n+1) → Bool) → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter (fun t : Fin n → Bool => P (Fin.cons true t))).card
      + (univ.filter (fun t : Fin n → Bool => P (Fin.cons false t))).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (n+1) => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

theorem card_zero (P : (Fin 0 → Bool) → Prop) [DecidablePred P] (q : Prop) [Decidable q]
    (h : ∀ x, P x ↔ q) : (univ.filter P).card = if q then 1 else 0 := by
  rw [Finset.filter_congr (fun x _ => h x)]
  by_cases hq : q <;> simp [hq]

theorem card_all {n : ℕ} (P : (Fin n → Bool) → Prop) [DecidablePred P] (h : ∀ x, P x) :
    (univ.filter P).card = 2 ^ n := by
  rw [Finset.filter_true_of_mem (fun x _ => h x)]
  simp

theorem card_none {n : ℕ} (P : (Fin n → Bool) → Prop) [DecidablePred P] (h : ∀ x, ¬ P x) :
    (univ.filter P).card = 0 := by
  rw [Finset.filter_false_of_mem (fun x _ => h x)]
  simp

/-- The position after the first k steps, split at the first step. -/
theorem sum_cons {n : ℕ} (b : Bool) (t : Fin n → Bool) (k : ℕ) :
    (∑ i : Fin (n+1), if i.val < k then st ((Fin.cons b t : Fin (n+1) → Bool) i) else 0)
      = (if 0 < k then st b else 0) + ∑ i : Fin n, if i.val + 1 < k then st (t i) else 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]

theorem sum_cons_all {n : ℕ} (b : Bool) (t : Fin n → Bool) :
    (∑ i : Fin (n+1), st ((Fin.cons b t : Fin (n+1) → Bool) i)) = st b + ∑ i : Fin n, st (t i) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-! p37: reaching +3 within 12 steps. -/

/-- With n steps left and the walk now at p: it is at 3 or higher after some number k of those steps (k = 0 is now). -/
def Hits (n : ℕ) (p : ℤ) (x : Fin n → Bool) : Prop :=
  ∃ k : Fin (n+1), 3 ≤ p + ∑ i : Fin n, if i.val < k.val then st (x i) else 0

instance (n : ℕ) (p : ℤ) : DecidablePred (Hits n p) := fun x => by unfold Hits; infer_instance

theorem hits_zero (p : ℤ) (x : Fin 0 → Bool) : Hits 0 p x ↔ 3 ≤ p := by
  simp [Hits]

theorem hits_cons {n : ℕ} (p : ℤ) (b : Bool) (t : Fin n → Bool) :
    Hits (n+1) p (Fin.cons b t) ↔ 3 ≤ p ∨ Hits n (p + st b) t := by
  unfold Hits
  rw [Fin.exists_fin_succ]
  simp only [Fin.val_zero, Fin.val_succ, sum_cons]
  simp [add_assoc]

def g37 : ℕ → ℤ → ℕ
  | 0, p => if 3 ≤ p then 1 else 0
  | n+1, p => if 3 ≤ p then 2 ^ (n+1) else g37 n (p + 1) + g37 n (p - 1)

theorem hits_count (n : ℕ) : ∀ p : ℤ, (univ.filter (Hits n p)).card = g37 n p := by
  induction n with
  | zero => intro p; rw [card_zero _ (3 ≤ p) (hits_zero p)]; rfl
  | succ n ih =>
    intro p
    rw [card_cons, Finset.filter_congr (fun t _ => hits_cons p true t),
      Finset.filter_congr (fun t _ => hits_cons p false t)]
    by_cases h : 3 ≤ p
    · rw [card_all _ (fun t => Or.inl h), card_all _ (fun t => Or.inl h)]
      simp only [g37, if_pos h]; ring
    · simp only [h, false_or]
      rw [ih, ih]
      simp only [g37, if_neg h]
      rfl

/-! p52: never below the start and back at it after 12 steps. -/

/-- With n steps left and the walk now at p: it is never below 0 and ends at 0. -/
def Stays (n : ℕ) (p : ℤ) (x : Fin n → Bool) : Prop :=
  (∀ k : Fin (n+1), 0 ≤ p + ∑ i : Fin n, if i.val < k.val then st (x i) else 0) ∧ p + ∑ i : Fin n, st (x i) = 0

instance (n : ℕ) (p : ℤ) : DecidablePred (Stays n p) := fun x => by unfold Stays; infer_instance

theorem stays_zero (p : ℤ) (x : Fin 0 → Bool) : Stays 0 p x ↔ p = 0 := by
  simp [Stays]
  omega

theorem stays_cons {n : ℕ} (p : ℤ) (b : Bool) (t : Fin n → Bool) :
    Stays (n+1) p (Fin.cons b t) ↔ 0 ≤ p ∧ Stays n (p + st b) t := by
  unfold Stays
  rw [Fin.forall_fin_succ, sum_cons_all]
  simp only [Fin.val_zero, Fin.val_succ, sum_cons]
  simp [add_assoc, and_assoc]

def g52 : ℕ → ℤ → ℕ
  | 0, p => if p = 0 then 1 else 0
  | n+1, p => if 0 ≤ p then g52 n (p + 1) + g52 n (p - 1) else 0

theorem stays_count (n : ℕ) : ∀ p : ℤ, (univ.filter (Stays n p)).card = g52 n p := by
  induction n with
  | zero => intro p; rw [card_zero _ (p = 0) (stays_zero p)]; rfl
  | succ n ih =>
    intro p
    rw [card_cons, Finset.filter_congr (fun t _ => stays_cons p true t),
      Finset.filter_congr (fun t _ => stays_cons p false t)]
    by_cases h : 0 ≤ p
    · simp only [h, true_and]
      rw [ih, ih]
      simp only [g52, if_pos h]
      rfl
    · rw [card_none _ (fun t ht => h ht.1), card_none _ (fun t ht => h ht.1)]
      simp only [g52, if_neg h]

/-! p02: a run of 5 heads in 20 flips. -/

section Runs
open Classical

/-- The first m flips are all heads, and with r heads just before them that makes a run of at least 5. -/
def Lead (n r : ℕ) (x : Fin n → Bool) : Prop := ∃ m, m ≤ n ∧ 5 ≤ r + m ∧ ∀ j : Fin n, j.val < m → x j = true

/-- Five flips in a row, starting at flip i, are all heads. -/
def Win (n : ℕ) (x : Fin n → Bool) : Prop := ∃ i, i + 5 ≤ n ∧ ∀ j : Fin n, i ≤ j.val → j.val < i + 5 → x j = true

/-- With n flips left and a run of r heads just before them: a run of 5 heads happens. -/
def G (n r : ℕ) (x : Fin n → Bool) : Prop := Lead n r x ∨ Win n x

theorem lead_big {n r : ℕ} (x : Fin n → Bool) (h : 5 ≤ r) : Lead n r x :=
  ⟨0, Nat.zero_le _, by omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem lead_mono {n r r' : ℕ} {x : Fin n → Bool} (h : r ≤ r') : Lead n r x → Lead n r' x := by
  rintro ⟨m, hm, h5, hj⟩; exact ⟨m, hm, by omega, hj⟩

theorem lead0_win {n : ℕ} {x : Fin n → Bool} : Lead n 0 x → Win n x := by
  rintro ⟨m, hm, h5, hj⟩; exact ⟨0, by omega, fun j _ h2 => hj j (by omega)⟩

theorem G_zero (r : ℕ) (x : Fin 0 → Bool) : G 0 r x ↔ 5 ≤ r := by
  constructor
  · rintro (⟨m, hm, h5, -⟩ | ⟨i, hi, -⟩) <;> omega
  · intro h; exact Or.inl (lead_big x h)

theorem lead_cons {n : ℕ} (r : ℕ) (b : Bool) (t : Fin n → Bool) :
    Lead (n+1) r (Fin.cons b t) ↔ 5 ≤ r ∨ (b = true ∧ Lead n (r+1) t) := by
  constructor
  · rintro ⟨m, hm, h5, hj⟩
    rcases m with _ | m
    · left; omega
    · right
      refine ⟨by simpa using hj 0 (by simp), m, by omega, by omega, fun j hj' => ?_⟩
      simpa using hj j.succ (by simp only [Fin.val_succ]; omega)
  · rintro (h | ⟨hb, m, hm, h5, hj⟩)
    · exact lead_big _ h
    · refine ⟨m+1, by omega, by omega, fun j hj' => ?_⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simpa using hb
      · simp only [Fin.val_succ] at hj'
        simpa using hj j (by omega)

theorem win_cons {n : ℕ} (b : Bool) (t : Fin n → Bool) :
    Win (n+1) (Fin.cons b t) ↔ (b = true ∧ Lead n 1 t) ∨ Win n t := by
  constructor
  · rintro ⟨i, hi, hj⟩
    rcases i with _ | i
    · left
      refine ⟨by simpa using hj 0 (by simp) (by simp), 4, by omega, by omega, fun j hj' => ?_⟩
      simpa using hj j.succ (by simp) (by simp only [Fin.val_succ]; omega)
    · right
      refine ⟨i, by omega, fun j h1 h2 => ?_⟩
      simpa using hj j.succ (by simp only [Fin.val_succ]; omega) (by simp only [Fin.val_succ]; omega)
  · rintro (⟨hb, m, hm, h5, hj⟩ | ⟨i, hi, hj⟩)
    · refine ⟨0, by omega, fun j _ h2 => ?_⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simpa using hb
      · simp only [Fin.val_succ] at h2
        simpa using hj j (by omega)
    · refine ⟨i+1, by omega, fun j h1 h2 => ?_⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp at h1
      · simp only [Fin.val_succ] at h1 h2
        simpa using hj j (by omega) (by omega)

theorem G_true {n : ℕ} (r : ℕ) (t : Fin n → Bool) : G (n+1) r (Fin.cons true t) ↔ G n (r+1) t := by
  unfold G; rw [lead_cons, win_cons]
  constructor
  · rintro ((h | ⟨-, h⟩) | (⟨-, h⟩ | h))
    · exact Or.inl (lead_big t (by omega))
    · exact Or.inl h
    · exact Or.inl (lead_mono (by omega) h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr h)

theorem G_false {n : ℕ} (r : ℕ) (t : Fin n → Bool) : G (n+1) r (Fin.cons false t) ↔ 5 ≤ r ∨ G n 0 t := by
  unfold G; rw [lead_cons, win_cons]
  constructor
  · rintro ((h | ⟨hb, -⟩) | (⟨hb, -⟩ | h))
    · exact Or.inl h
    · cases hb
    · cases hb
    · exact Or.inr (Or.inr h)
  · rintro (h | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr (lead0_win h))
    · exact Or.inr (Or.inr h)

theorem G_win {n : ℕ} (x : Fin n → Bool) : G n 0 x ↔ Win n x :=
  ⟨fun h => h.elim lead0_win id, Or.inr⟩

/-- One flip: entry r (a run of r heads so far; 5 stands for a run already found) from the next flip's list. -/
def stepR (l : List ℕ) : List ℕ :=
  (List.range 6).map (fun r => if r < 5 then l.getD (r+1) 0 + l.getD 0 0 else 2 * l.getD 5 0)

def Rl : ℕ → List ℕ
  | 0 => [0, 0, 0, 0, 0, 1]
  | n+1 => stepR (Rl n)

theorem runs_count (n : ℕ) : ∀ r, r < 6 → (univ.filter (G n r)).card = (Rl n).getD r 0 := by
  induction n with
  | zero =>
    intro r hr
    rw [card_zero _ (5 ≤ r) (G_zero r)]
    interval_cases r <;> rfl
  | succ n ih =>
    intro r hr
    have e : (Rl (n+1)).getD r 0 = if r < 5 then (Rl n).getD (r+1) 0 + (Rl n).getD 0 0 else 2 * (Rl n).getD 5 0 := by
      rw [Rl, stepR, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]
      simp only [Option.map_some, Option.getD_some]
    rw [e, card_cons, Finset.filter_congr (fun t _ => G_true r t), Finset.filter_congr (fun t _ => G_false r t)]
    by_cases h5 : r < 5
    · have h : ¬ 5 ≤ r := by omega
      simp only [h, false_or, if_pos h5]
      rw [ih (r+1) (by omega), ih 0 (by omega)]
    · have h : 5 ≤ r := by omega
      rw [card_all (G n (r+1)) (fun t => Or.inl (lead_big t (by omega))),
        card_all (fun t => 5 ≤ r ∨ G n 0 t) (fun t => Or.inl h), if_neg h5,
        ← ih 5 (by omega), card_all (G n 5) (fun t => Or.inl (lead_big t (le_refl 5)))]
      ring

end Runs

end Walks

open Finset

theorem p37_random_walk_hits_three :
    ((univ.filter (fun x : Fin 12 → Bool =>
      ∃ k : Fin 13, 3 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0)).card : ℚ) / 2 ^ 12
      = 397 / 1024 := by
  have h1 : (univ.filter (fun x : Fin 12 → Bool =>
      ∃ k : Fin 13, 3 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0)).card
      = (univ.filter (Walks.Hits 12 0)).card := by
    rw [Finset.filter_congr (fun x _ => by simp only [Walks.Hits, Walks.st, zero_add] :
      ∀ x ∈ (univ : Finset (Fin 12 → Bool)), (∃ k : Fin 13, 3 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0) ↔ Walks.Hits 12 0 x)]
  have h2 : Walks.g37 12 0 = 1588 := by decide +kernel
  rw [h1, Walks.hits_count, h2]
  norm_num

theorem p52_random_walk_never_negative :
    ((univ.filter (fun x : Fin 12 → Bool =>
      (∀ k : Fin 13, 0 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0)
        ∧ ∑ i : Fin 12, (if x i then (1 : ℤ) else -1) = 0)).card : ℚ) / 2 ^ 12
      = 33 / 1024 := by
  have h1 : (univ.filter (fun x : Fin 12 → Bool =>
      (∀ k : Fin 13, 0 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0)
        ∧ ∑ i : Fin 12, (if x i then (1 : ℤ) else -1) = 0)).card
      = (univ.filter (Walks.Stays 12 0)).card := by
    rw [Finset.filter_congr (fun x _ => by simp only [Walks.Stays, Walks.st, zero_add] :
      ∀ x ∈ (univ : Finset (Fin 12 → Bool)), ((∀ k : Fin 13, 0 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0)
        ∧ ∑ i : Fin 12, (if x i then (1 : ℤ) else -1) = 0) ↔ Walks.Stays 12 0 x)]
  have h2 : Walks.g52 12 0 = 132 := by decide +kernel
  rw [h1, Walks.stays_count, h2]
  norm_num

open Classical in
theorem p02_coin_streaks :
    ((univ.filter (fun x : Fin 20 → Bool =>
      ∃ i, i + 5 ≤ 20 ∧ ∀ j : Fin 20, i ≤ j.val → j.val < i + 5 → x j = true)).card : ℚ) / 2 ^ 20
      = 32751 / 131072 := by
  have h1 : (univ.filter (fun x : Fin 20 → Bool =>
      ∃ i, i + 5 ≤ 20 ∧ ∀ j : Fin 20, i ≤ j.val → j.val < i + 5 → x j = true)).card
      = (univ.filter (Walks.G 20 0)).card := by
    exact congrArg Finset.card (Finset.filter_congr (fun x _ => (Walks.G_win x).symm))
  have h2 : (Walks.Rl 20).getD 0 0 = 262008 := by decide +kernel
  rw [h1, Walks.runs_count 20 0 (by norm_num), h2]
  norm_num

