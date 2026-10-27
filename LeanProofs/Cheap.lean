import Mathlib

/-!
# The cheap lane (ORD-1027-AK step 3)

Bank problems whose answer is a finite count, proven by the kernel counting every case.
-/

namespace CheapLane

/-- The ways to place 4 aces among the 8 slots that the aces and kings fill in a shuffled deck.
Only the order of those 8 cards matters, and every placement is equally likely. -/
def aceSlots : Finset (Finset (Fin 8)) := Finset.powersetCard 4 Finset.univ

/-- A placement where every ace comes before every king. -/
def acesFirst (s : Finset (Fin 8)) : Prop := ∀ a ∈ s, ∀ k, k ∉ s → a < k

instance : DecidablePred acesFirst := fun s => by unfold acesFirst; infer_instance

/-- p45: of the 70 placements, exactly one puts all four aces before any king. -/
theorem p45_count : aceSlots.card = 70 ∧ (aceSlots.filter acesFirst).card = 1 := by
  decide

/-- p45: so all four aces appear before any king with chance 1/70. -/
theorem p45_aces_before_kings :
    ((aceSlots.filter acesFirst).card : ℚ) / (aceSlots.card : ℚ) = 1 / 70 := by
  rw [p45_count.1, p45_count.2]
  norm_num

/-- One step of a walk on a line: true is +1, false is -1. -/
def step (b : Bool) : ℤ := if b then 1 else -1

/-- The positions after step 1, step 2, and so on, starting from 0 (the start itself is left out). -/
def path {n : ℕ} (x : Fin n → Bool) : List ℤ := ((List.ofFn x).map step).scanl (· + ·) 0 |>.tail

/-- p40: of the 1,024 step lists of length 10, exactly 28 are back at 0 after step 10 and not before. -/
theorem p40_count :
    (Finset.univ.filter (fun x : Fin 10 → Bool =>
      (path x).getLast? = some 0 ∧ ∀ p ∈ (path x).dropLast, p ≠ 0)).card = 28 := by
  decide +kernel

/-- p40: so the first return to the start is exactly at step 10 with chance 7/256. -/
theorem p40_first_return_10 :
    ((Finset.univ.filter (fun x : Fin 10 → Bool =>
      (path x).getLast? = some 0 ∧ ∀ p ∈ (path x).dropLast, p ≠ 0)).card : ℚ)
      / (Fintype.card (Fin 10 → Bool) : ℚ) = 7 / 256 := by
  rw [p40_count]
  simp [Fintype.card_fin, Fintype.card_bool]
  norm_num

/-- The highest position after steps 1 to 10 (the start at time 0 does not count). Every position
is at least -10, so folding `max` from -10 gives exactly the highest one. -/
def top (x : Fin 10 → Bool) : ℤ := (path x).foldl max (-10)

/-- p39: the highest points of all 1,024 step lists of length 10 add up to 2,008. -/
theorem p39_sum : (∑ x : Fin 10 → Bool, top x) = 2008 := by
  decide +kernel

/-- p39: so the expected highest point in 10 steps is 2008/1024 = 251/128. -/
theorem p39_expected_max :
    ((∑ x : Fin 10 → Bool, top x : ℤ) : ℚ) / (Fintype.card (Fin 10 → Bool) : ℚ) = 251 / 128 := by
  rw [p39_sum]
  simp [Fintype.card_fin, Fintype.card_bool]
  norm_num

/-- One step on the square grid: 0 north, 1 south, 2 east, 3 west. -/
def move (d : Fin 4) : ℤ × ℤ :=
  match d with
  | 0 => (0, 1)
  | 1 => (0, -1)
  | 2 => (1, 0)
  | 3 => (-1, 0)

/-- Where a list of grid steps ends, starting from (0, 0). -/
def finish {n : ℕ} (x : Fin n → Fin 4) : ℤ × ℤ := ((List.ofFn x).map move).foldl (· + ·) (0, 0)

/-- p38: of the 4,096 lists of 6 grid steps, exactly 400 end back at (0, 0). -/
theorem p38_count : (Finset.univ.filter (fun x : Fin 6 → Fin 4 => finish x = (0, 0))).card = 400 := by
  decide +kernel

/-- p38: so a 6-step grid walk is back at the start with chance 25/256. -/
theorem p38_random_walk_2d :
    ((Finset.univ.filter (fun x : Fin 6 → Fin 4 => finish x = (0, 0))).card : ℚ)
      / (Fintype.card (Fin 6 → Fin 4) : ℚ) = 25 / 256 := by
  rw [p38_count]
  simp [Fintype.card_fin]
  norm_num

end CheapLane
