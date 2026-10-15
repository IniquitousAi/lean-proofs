import Mathlib

/-!
# Answer bank results, proven in Lean 4 with Mathlib

Checker 6 of the engine's checker loop. Each theorem restates one answer-bank problem and lets Lean's kernel check it.
-/

/-- p01: of the 36 equally likely rolls of two fair dice (faces 1 to 6, written here as `Fin 6` plus one), six sum to 7. -/
theorem p01_dice_sum_seven_count :
    ((Finset.univ : Finset (Fin 6 × Fin 6)).filter (fun r => r.1.val + r.2.val + 2 = 7)).card = 6 := by
  decide

/-- p01: so the chance that two fair dice sum to 7 is exactly 1/6. -/
theorem p01_dice_sum_seven :
    (((Finset.univ : Finset (Fin 6 × Fin 6)).filter (fun r => r.1.val + r.2.val + 2 = 7)).card : ℚ)
      / (Fintype.card (Fin 6 × Fin 6) : ℚ) = 1 / 6 := by
  rw [p01_dice_sum_seven_count]
  simp [Fintype.card_prod, Fintype.card_fin]
  norm_num

/-- p06, the arithmetic only: C(20,10)/2^20 = 46189/262144. That a 20-step walk returns to its start with chance
C(20,10)/2^20 is taken from the bank's assumptions here, not proven (CHIEF's note, 2026-10-14). -/
theorem p06_walk_return : ((Nat.choose 20 10 : ℚ) / 2 ^ 20) = 46189 / 262144 := by
  rw [show Nat.choose 20 10 = 184756 by decide]
  norm_num

/-- p10: over all 36 equally likely rolls of two fair dice, the larger face (here `val + 1`) adds up to 161. -/
theorem p10_max_sum :
    (∑ r : Fin 6 × Fin 6, (max r.1.val r.2.val + 1)) = 161 := by
  decide

/-- p10: so the larger of two fair dice is 161/36 on average, counted over every roll. -/
theorem p10_max_of_two_dice :
    ((∑ r : Fin 6 × Fin 6, (max r.1.val r.2.val + 1) : ℕ) : ℚ) / (Fintype.card (Fin 6 × Fin 6) : ℚ) = 161 / 36 := by
  rw [p10_max_sum]
  simp [Fintype.card_prod, Fintype.card_fin]

/-- p41: of the 10! orders of ten cards, 1,334,961 leave no card where it started (Mathlib counts the derangements). -/
theorem p41_count : Fintype.card (derangements (Fin 10)) = 1334961 := by
  rw [card_derangements_eq_numDerangements, Fintype.card_fin]
  decide

/-- p41: so a uniform shuffle of ten cards leaves none in place with chance exactly 16481/44800. -/
theorem p41_shuffle_derangement_ten :
    (Fintype.card (derangements (Fin 10)) : ℚ) / (Fintype.card (Equiv.Perm (Fin 10)) : ℚ) = 16481 / 44800 := by
  rw [p41_count, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

/-- p07: the host opens a door that hides no car and is not the first pick (the lowest such door; which one does not change the count). -/
def mhHost (c p : Fin 3) : Fin 3 :=
  if (0 : Fin 3) ≠ c ∧ (0 : Fin 3) ≠ p then 0 else if (1 : Fin 3) ≠ c ∧ (1 : Fin 3) ≠ p then 1 else 2

/-- p07: switching goes to the one door that is neither the first pick nor the opened one. -/
def mhSwitch (p h : Fin 3) : Fin 3 :=
  if (0 : Fin 3) ≠ p ∧ (0 : Fin 3) ≠ h then 0 else if (1 : Fin 3) ≠ p ∧ (1 : Fin 3) ≠ h then 1 else 2

theorem p07_host_follows_the_rules : ∀ c p : Fin 3, mhHost c p ≠ c ∧ mhHost c p ≠ p := by decide

theorem p07_switch_is_the_other_closed_door : ∀ c p : Fin 3, mhSwitch p (mhHost c p) ≠ p ∧ mhSwitch p (mhHost c p) ≠ mhHost c p := by decide

/-- p07: over the 9 equally likely (car, first pick) pairs, switching finds the car in 6. -/
theorem p07_count : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun r => mhSwitch r.2 (mhHost r.1 r.2) = r.1)).card = 6 := by decide

theorem p07_monty_hall :
    (((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun r => mhSwitch r.2 (mhHost r.1 r.2) = r.1)).card : ℚ)
      / (Fintype.card (Fin 3 × Fin 3) : ℚ) = 2 / 3 := by
  rw [p07_count]
  simp [Fintype.card_prod, Fintype.card_fin]
  norm_num

/-- p31: the weather table; row is today (Sun, Cloud, Rain), column is tomorrow. -/
def weather : Matrix (Fin 3) (Fin 3) ℚ := !![3/5, 3/10, 1/10; 2/5, 2/5, 1/5; 1/5, 3/10, 1/2]

/-- p31: starting at Sun, the chance of Rain four days later is exactly 2137/10000. -/
theorem p31_markov_weather_four_steps : (weather ^ 4) 0 2 = 2137 / 10000 := by
  simp only [pow_succ, pow_zero, one_mul]
  simp [weather, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num
