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
