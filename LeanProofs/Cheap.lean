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

/-- The urn after some draws, as (red, blue, weight): the weight is the product of the counts of the
colour drawn at each step, so a draw order's chance is its weight over 3 * 4 * 5 * 6 * 7 = 2520. -/
def urnDraw (s : ℕ × ℕ × ℕ) (red : Bool) : ℕ × ℕ × ℕ :=
  if red then (s.1 + 1, s.2.1, s.2.2 * s.1) else (s.1, s.2.1 + 1, s.2.2 * s.2.1)

/-- The weight of five draws from an urn starting with 2 red and 1 blue. -/
def urnWeight (x : Fin 5 → Bool) : ℕ := ((List.ofFn x).foldl urnDraw (2, 1, 1)).2.2

/-- The number of reds among the five draws. -/
def reds (x : Fin 5 → Bool) : ℕ := (List.ofFn x).count true

/-- p49: the 32 draw orders' weights add up to 2520 (so the chances add up to 1), and the orders with
exactly three reds weigh 480. -/
theorem p49_count :
    (∑ x : Fin 5 → Bool, urnWeight x) = 2520 ∧
      (∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Bool => reds x = 3), urnWeight x) = 480 := by
  decide +kernel

/-- p49: so exactly three of the first five draws are red with chance 480/2520 = 4/21. -/
theorem p49_polya_three_reds :
    ((∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Bool => reds x = 3), urnWeight x : ℕ) : ℚ)
      / ((∑ x : Fin 5 → Bool, urnWeight x : ℕ) : ℚ) = 4 / 21 := by
  rw [p49_count.1, p49_count.2]
  norm_num

/-- One card dealt from a deck with (aces left, other cards left), keeping a weight: the product of how many cards of the
kind dealt were left at each deal. A deal order's weight is the number of ordered five-card deals that follow it, so the
weights add up to 52 * 51 * 50 * 49 * 48, and every five-card hand is equally likely. -/
def deal (s : ℕ × ℕ × ℕ) (ace : Bool) : ℕ × ℕ × ℕ :=
  if ace then (s.1 - 1, s.2.1, s.2.2 * s.1) else (s.1, s.2.1 - 1, s.2.2 * s.2.1)

/-- The weight of five deals (true = an ace) from a 52-card deck with 4 aces. -/
def handWeight (x : Fin 5 → Bool) : ℕ := ((List.ofFn x).foldl deal (4, 48, 1)).2.2

/-- The number of aces among the five cards. -/
def aces (x : Fin 5 → Bool) : ℕ := (List.ofFn x).count true

/-- p04: the 32 ace patterns weigh 311,875,200 in all (every ordered five-card deal), and the patterns with exactly two
aces weigh 12,453,120. -/
theorem p04_count :
    (∑ x : Fin 5 → Bool, handWeight x) = 311875200 ∧
      (∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Bool => aces x = 2), handWeight x) = 12453120 := by
  decide +kernel

/-- p04: so five cards hold exactly two aces with chance 12453120/311875200 = 2162/54145. -/
theorem p04_two_aces_in_five :
    ((∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Bool => aces x = 2), handWeight x : ℕ) : ℚ)
      / ((∑ x : Fin 5 → Bool, handWeight x : ℕ) : ℚ) = 2162 / 54145 := by
  rw [p04_count.1, p04_count.2]
  norm_num

/-- Ten rolls grouped by which rolls are sixes (true): a pattern stands for 5^(rolls that are not a six) roll lists, since
each of those rolls is one of the 5 other faces. -/
def rollWeight (x : Fin 10 → Bool) : ℕ := 5 ^ ((List.ofFn x).count false)

/-- p12: the 1,024 six patterns stand for 6^10 = 60,466,176 roll lists in all, and those with three or more sixes for
13,591,176. -/
theorem p12_count :
    (∑ x : Fin 10 → Bool, rollWeight x) = 60466176 ∧
      (∑ x ∈ Finset.univ.filter (fun x : Fin 10 → Bool => 3 ≤ (List.ofFn x).count true), rollWeight x)
        = 13591176 := by
  decide +kernel

/-- p12: so ten rolls show three or more sixes with chance 13591176/60466176 = 566299/2519424. -/
theorem p12_three_plus_sixes :
    ((∑ x ∈ Finset.univ.filter (fun x : Fin 10 → Bool => 3 ≤ (List.ofFn x).count true), rollWeight x : ℕ) : ℚ)
      / ((∑ x : Fin 10 → Bool, rollWeight x : ℕ) : ℚ) = 566299 / 2519424 := by
  rw [p12_count.1, p12_count.2]
  norm_num

/-- How many b in 1..m share no factor with a, counted one b at a time. -/
def coprimeRow (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => coprimeRow a m + if Nat.gcd a (m + 1) = 1 then 1 else 0

/-- How many pairs (a, b) with a in 1..k and b in 1..m share no factor, counted one a at a time. -/
def coprimeRows (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => coprimeRows m k + coprimeRow (k + 1) m

theorem coprimeRow_eq (a m : ℕ) :
    coprimeRow a m = ∑ b ∈ Finset.Icc 1 m, if Nat.gcd a b = 1 then 1 else 0 := by
  induction m with
  | zero => simp [coprimeRow]
  | succ m ih => rw [coprimeRow, ih, Finset.sum_Icc_succ_top (by omega)]

theorem coprimeRows_eq (m k : ℕ) :
    coprimeRows m k = ∑ a ∈ Finset.Icc 1 k, ∑ b ∈ Finset.Icc 1 m, if Nat.gcd a b = 1 then 1 else 0 := by
  induction k with
  | zero => simp [coprimeRows]
  | succ k ih => rw [coprimeRows, ih, Finset.sum_Icc_succ_top (by omega), coprimeRow_eq]

/-- The pairs (a, b) with both in 1..m and no common factor are counted by the row recursion. -/
theorem coprime_pairs_card (m : ℕ) :
    ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = 1)).card
      = coprimeRows m m := by
  rw [coprimeRows_eq, Finset.card_filter, Finset.sum_product]

/-- p63: of the 1,000,000 pairs of numbers from 1 to 1000, exactly 608,383 have greatest common divisor 1. -/
theorem p63_count :
    ((Finset.Icc 1 1000 ×ˢ Finset.Icc 1 1000).filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = 1)).card = 608383 := by
  rw [coprime_pairs_card]
  decide +kernel

/-- p63: so two numbers drawn from 1 to 1000 share no common factor with chance 608383/1000000 (the finite range, not the
6/pi^2 limit). -/
theorem p63_trap_coprime_pair_finite :
    (((Finset.Icc 1 1000 ×ˢ Finset.Icc 1 1000).filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = 1)).card : ℚ)
      / ((Finset.Icc 1 1000 ×ˢ Finset.Icc 1 1000).card : ℚ) = 608383 / 1000000 := by
  rw [p63_count]
  simp

end CheapLane
