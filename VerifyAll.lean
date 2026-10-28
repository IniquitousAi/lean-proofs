import LeanProofs

/-!
# VerifyAll: the headline statements, restated and checked

For each of the 42 problems labeled Proven, this file copies the headline theorem's statement word for word
from its source file and asks Lean to accept the named theorem as a proof of it (`example : <statement> := <theorem>`).
If a source theorem ever states something else (anything not the same statement up to definitional unfolding),
this file stops compiling.
Each example sits in the same namespace, with the same `open`s, as its source theorem, so names resolve the same way.
No new notation or definitions are introduced here.

Then `#print axioms` lists what each headline theorem rests on. check.sh fails unless every list is a subset of
`propext`, `Quot.sound`, `Classical.choice` (the three standard axioms of Lean and Mathlib).

No problem is held at Guess: every problem with a Lean theorem is restated below.
p32 has two entries: its headline equation (the limit equals 4/7) and the convergence statement it comes from.
Daniel's Root Theorem (LeanProofs/Root.lean, not an answer-bank problem) is restated last, so all 36 headline
statements in the project are bound to their theorems here.
-/

/-! ## LeanProofs/Bank.lean -/
section Bank

-- p01_dice_odds (Bank.lean)
example :
    (((Finset.univ : Finset (Fin 6 × Fin 6)).filter (fun r => r.1.val + r.2.val + 2 = 7)).card : ℚ)
      / (Fintype.card (Fin 6 × Fin 6) : ℚ) = 1 / 6 :=
  p01_dice_sum_seven

-- p06_random_walk (Bank.lean)
example :
    ((Finset.univ.filter (fun x : Fin 20 → Bool => (∑ i, (if x i then (1 : ℤ) else -1)) = 0)).card : ℚ) / 2 ^ 20
      = 46189 / 262144 :=
  p06_random_walk

-- p07_monty_hall (Bank.lean)
example :
    (((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun r => mhSwitch r.2 (mhHost r.1 r.2) = r.1)).card : ℚ)
      / (Fintype.card (Fin 3 × Fin 3) : ℚ) = 2 / 3 :=
  p07_monty_hall

-- p10_max_of_two_dice (Bank.lean)
example :
    ((∑ r : Fin 6 × Fin 6, (max r.1.val r.2.val + 1) : ℕ) : ℚ) / (Fintype.card (Fin 6 × Fin 6) : ℚ) = 161 / 36 :=
  p10_max_of_two_dice

-- p31_markov_weather_four_steps (Bank.lean)
example : (weather ^ 4) 0 2 = 2137 / 10000 :=
  p31_markov_weather_four_steps

-- p41_shuffle_derangement_ten (Bank.lean)
example :
    (Fintype.card (derangements (Fin 10)) : ℚ) / (Fintype.card (Equiv.Perm (Fin 10)) : ℚ) = 16481 / 44800 :=
  p41_shuffle_derangement_ten

end Bank

/-! ## LeanProofs/Walks.lean -/
section Walks
open Finset

-- p02_coin_streaks (Walks.lean)
open Classical in
example :
    ((univ.filter (fun x : Fin 20 → Bool =>
      ∃ i, i + 5 ≤ 20 ∧ ∀ j : Fin 20, i ≤ j.val → j.val < i + 5 → x j = true)).card : ℚ) / 2 ^ 20
      = 32751 / 131072 :=
  p02_coin_streaks

-- p37_random_walk_hits_three (Walks.lean)
example :
    ((univ.filter (fun x : Fin 12 → Bool =>
      ∃ k : Fin 13, 3 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0)).card : ℚ) / 2 ^ 12
      = 397 / 1024 :=
  p37_random_walk_hits_three

-- p52_random_walk_never_negative (Walks.lean)
example :
    ((univ.filter (fun x : Fin 12 → Bool =>
      (∀ k : Fin 13, 0 ≤ ∑ i : Fin 12, if i.val < k.val then (if x i then (1 : ℤ) else -1) else 0)
        ∧ ∑ i : Fin 12, (if x i then (1 : ℤ) else -1) = 0)).card : ℚ) / 2 ^ 12
      = 33 / 1024 :=
  p52_random_walk_never_negative

end Walks

/-! ## LeanProofs/Cheap.lean -/
namespace CheapLane

-- p04_card_draws (Cheap.lean)
example :
    ((∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Bool => aces x = 2), handWeight x : ℕ) : ℚ)
      / ((∑ x : Fin 5 → Bool, handWeight x : ℕ) : ℚ) = 2162 / 54145 :=
  CheapLane.p04_two_aces_in_five

-- p12_three_plus_sixes (Cheap.lean)
example :
    ((∑ x ∈ Finset.univ.filter (fun x : Fin 10 → Bool => 3 ≤ (List.ofFn x).count true), rollWeight x : ℕ) : ℚ)
      / ((∑ x : Fin 10 → Bool, rollWeight x : ℕ) : ℚ) = 566299 / 2519424 :=
  CheapLane.p12_three_plus_sixes

-- p32_markov_token_absorption (Cheap.lean)
example :
    Filter.limUnder Filter.atTop (fun n : ℕ => (P32.winWithin n 1 : ℝ)) = 4 / 7 :=
  CheapLane.p32_markov_token_absorption_limit

-- p36_birthday_expected_distinct (Cheap.lean)
example : (P36.distinctTotal 365 30 : ℚ) / 365 ^ 30
    = 5840637997733944304472717260382885356354745452713098221901782271034552207449 / 202531728519726872798204574491055504334773427222006304748356342315673828125 :=
  CheapLane.p36_birthday_expected_distinct

-- p38_random_walk_2d_return (Cheap.lean)
example :
    ((Finset.univ.filter (fun x : Fin 6 → Fin 4 => finish x = (0, 0))).card : ℚ)
      / (Fintype.card (Fin 6 → Fin 4) : ℚ) = 25 / 256 :=
  CheapLane.p38_random_walk_2d

-- p39_random_walk_expected_max (Cheap.lean)
example :
    ((∑ x : Fin 10 → Bool, top x : ℤ) : ℚ) / (Fintype.card (Fin 10 → Bool) : ℚ) = 251 / 128 :=
  CheapLane.p39_expected_max

-- p40_random_walk_first_return_10 (Cheap.lean)
example :
    ((Finset.univ.filter (fun x : Fin 10 → Bool =>
      (path x).getLast? = some 0 ∧ ∀ p ∈ (path x).dropLast, p ≠ 0)).card : ℚ)
      / (Fintype.card (Fin 10 → Bool) : ℚ) = 7 / 256 :=
  CheapLane.p40_first_return_10

-- p42_shuffle_expected_cycles (Cheap.lean)
open Equiv Finset in
example :
    ((∑ σ : Perm (Fin 20), numCycles σ : ℕ) : ℚ) / (Fintype.card (Perm (Fin 20)) : ℚ)
      = 55835135 / 15519504 :=
  CheapLane.p42_shuffle_expected_cycles

-- p43_shuffle_kept_neighbours (Cheap.lean)
example :
    ((shuffles10.filter (fun l => keepsNeighbours l = true)).card : ℚ) / (shuffles10.card : ℚ)
      = 2160343 / 3628800 :=
  CheapLane.p43_shuffle_kept_neighbours

-- p44_bridge_hand_no_spades (Cheap.lean)
open Finset in
example :
    ((hands.filter NoSpadesAllElse).card : ℚ) / (hands.card : ℚ) = 8091223647 / 635013559600 :=
  CheapLane.p44_bridge_hand_no_spades

-- p45_aces_before_kings (Cheap.lean)
example :
    ((aceSlots.filter acesFirst).card : ℚ) / (aceSlots.card : ℚ) = 1 / 70 :=
  CheapLane.p45_aces_before_kings

-- p49_polya_exactly_three_reds (Cheap.lean)
example :
    ((∑ x ∈ Finset.univ.filter (fun x : Fin 5 → Bool => reds x = 3), urnWeight x : ℕ) : ℚ)
      / ((∑ x : Fin 5 → Bool, urnWeight x : ℕ) : ℚ) = 4 / 21 :=
  CheapLane.p49_polya_three_reds

-- p53_birthday_expected_pairs (Cheap.lean)
example : (P53.pairTotal 365 28 : ℚ) / 365 ^ 28 = 378 / 365 :=
  CheapLane.p53_birthday_expected_pairs

-- p63_trap_coprime_pair_finite (Cheap.lean)
example :
    (((Finset.Icc 1 1000 ×ˢ Finset.Icc 1 1000).filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = 1)).card : ℚ)
      / ((Finset.Icc 1 1000 ×ˢ Finset.Icc 1 1000).card : ℚ) = 608383 / 1000000 :=
  CheapLane.p63_trap_coprime_pair_finite

-- p32_markov_token_absorption (Cheap.lean)
example :
    Filter.Tendsto (fun n : ℕ => (P32.winWithin n 1 : ℝ)) Filter.atTop (nhds (4 / 7 : ℝ)) :=
  CheapLane.p32_markov_token_absorption

end CheapLane

/-! ## LeanProofs/Tower.lean -/
namespace TowerBatch
open Finset

-- p05_birthday_problem (Tower.lean)
example :
    ((univ.filter (fun f : Fin 23 → Fin 365 => ¬ Function.Injective f)).card : ℚ) / 365 ^ 23 = (38093904702297390785243708291056390518886454060947061 : ℚ) / 75091883268515350125426207425223147563269805908203125 :=
  TowerBatch.p05_birthday_problem

-- p13_cards_to_first_ace (Tower.lean)
example :
    (∑ σ : Equiv.Perm (Fin 52), (firstPlace σ (fun c => rank c = 1) : ℚ)) / (Fintype.card (Equiv.Perm (Fin 52)) : ℚ) = (53 : ℚ) / 5 :=
  TowerBatch.p13_cards_to_first_ace

-- p17_three_of_five_vote (Tower.lean)
example :
    (∑ x : Fin 5 → Bool, if 3 ≤ heads x then rowChance (3 / 5) x else 0) = (2133 : ℚ) / 3125 :=
  TowerBatch.p17_three_of_five_vote

-- p21_rare_one_in_1000 (Tower.lean)
example :
    ((univ.filter (fun x : Fin 1000 => x.val = 0)).card : ℚ) / 1000 = (1 : ℚ) / 1000 :=
  TowerBatch.p21_rare_one_in_1000

-- p22_st_petersburg_capped (Tower.lean)
example :
    (∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) * 2 ^ (min (j + 1) 20)) = (21 : ℝ) :=
  TowerBatch.p22_st_petersburg_capped

-- p48_third_success_by_twelve (Tower.lean)
example :
    (∑ x : Fin 12 → Bool, if 3 ≤ heads x then rowChance (1 / 3) x else 0) = (435185 : ℚ) / 531441 :=
  TowerBatch.p48_third_success_by_twelve

-- p65_trap_bridge_aces_kings (Tower.lean)
example :
    (((powersetCard 13 (univ : Finset (Fin 52))).filter (fun h => (h.filter (fun c => rank c = 1)).card = 4 ∧ (h.filter (fun c => rank c = 13)).card = 4)).card : ℚ) / (Nat.choose 52 13 : ℚ) = (11 : ℚ) / 6431950 :=
  TowerBatch.p65_trap_bridge_aces_kings

-- p65_trap_medical_test_positive (Tower.lean)
example :
    (∑ s : Bool, ∑ a : Bool, ∑ b : Bool, if s = true ∧ (if s then a else b) = true then (if s then (1 : ℚ) / 1000 else 999 / 1000) * (if a then 99 / 100 else 1 / 100) * (if b then 1 / 100 else 99 / 100) else 0) / (∑ s : Bool, ∑ a : Bool, ∑ b : Bool, if (if s then a else b) = true then (if s then (1 : ℚ) / 1000 else 999 / 1000) * (if a then 99 / 100 else 1 / 100) * (if b then 1 / 100 else 99 / 100) else 0) = (11 : ℚ) / 122 :=
  TowerBatch.p65_trap_medical_test_positive

-- p68_trap_common_shock_failure (Tower.lean)
example :
    (∑ a : Bool, ∑ x : Fin 5 → Bool, if a = true ∨ heads x = 5 then (if a then (1 : ℚ) / 1000 else 999 / 1000) * rowChance (1 / 100) x else 0) = (10000000999 : ℚ) / 10000000000000 :=
  TowerBatch.p68_trap_common_shock_failure

-- p69_trap_twenty_dice_low_tail (Tower.lean)
example :
    ((univ.filter (fun f : Fin 20 → Fin 6 => (∑ i, (f i).val) + 20 ≤ 30)).card : ℚ) / 6 ^ 20 = (9944165 : ℚ) / 1218719480020992 :=
  TowerBatch.p69_trap_twenty_dice_low_tail

-- p69_trap_two_records_in_row (Tower.lean)
example :
    ((univ.filter (fun σ : Equiv.Perm (Fin 101) => σ 100 = 100 ∧ σ 99 = 99)).card : ℚ) / (Fintype.card (Equiv.Perm (Fin 101)) : ℚ) = (1 : ℚ) / 10100 :=
  TowerBatch.p69_trap_two_records_in_row

end TowerBatch

/-! ## LeanProofs/Root.lean: Daniel's Root Theorem (not an answer-bank problem) -/
section Root

-- DanielRootTheorem (Root.lean)
example (c n : ℕ) :
    (1 ≤ n → c ≤ n * c) ∧ (2 ≤ n → 0 < c → c < n * c) :=
  DanielRootTheorem c n

end Root

/-! ## LeanProofs/Calculus.lean: the calculus lane (ORD-1028-BQ) -/
namespace CalculusLane
open Real intervalIntegral

-- p30_area_under_square (Calculus.lean)
example : ∫ x in (0:ℝ)..3, x ^ 2 = 9 :=
  CalculusLane.p30_area_under_square

-- p92_sine_arch (Calculus.lean)
example : ∫ x in (0:ℝ)..π, sin x = 2 :=
  CalculusLane.p92_sine_arch

-- p91_exp_area (Calculus.lean)
example : ∫ x in (0:ℝ)..1, exp x = exp 1 - 1 :=
  CalculusLane.p91_exp_area

end CalculusLane

/-! ## LeanProofs/Series.lean: the series lane (ORD-1028-BQ) -/
namespace SeriesLane
open Filter Topology

-- p99_telescoping (Series.lean)
example : HasSum (fun k : ℕ => (1:ℝ) / ((k + 1) * (k + 2))) 1 :=
  SeriesLane.p99_telescoping

-- p94_k_over_two_pow (Series.lean)
example : HasSum (fun k : ℕ => (k:ℝ) / 2 ^ k) 2 :=
  SeriesLane.p94_k_over_two_pow

end SeriesLane

/-! ## LeanProofs/CalculusLog.lean, Waiting.lean, Roots.lean (ORD-1028-BQ) -/
namespace CalculusLane
open Real

-- p100_log_over_x (CalculusLog.lean)
example : ∫ x in (1:ℝ)..exp 1, log x / x = 1 / 2 :=
  CalculusLane.p100_log_over_x

end CalculusLane

namespace WaitingLane

-- p09_rolls_to_first_six (Waiting.lean)
example : HasSum (fun k : ℕ => ((k:ℝ) + 1) * ((5/6) ^ k * (1/6))) 6 :=
  WaitingLane.p09_rolls_to_first_six

end WaitingLane

namespace RootsLane
open Real

-- p95_positive_root_of_two (Roots.lean)
example : (0 < √2 ∧ √2 ^ 2 = 2) ∧ ∀ x : ℝ, 0 < x → x ^ 2 = 2 → x = √2 :=
  RootsLane.p95_positive_root_of_two

end RootsLane

/-! ## Axioms each headline theorem rests on -/
#print axioms p01_dice_sum_seven
#print axioms p02_coin_streaks
#print axioms CheapLane.p04_two_aces_in_five
#print axioms TowerBatch.p05_birthday_problem
#print axioms p06_random_walk
#print axioms p07_monty_hall
#print axioms p10_max_of_two_dice
#print axioms CheapLane.p12_three_plus_sixes
#print axioms TowerBatch.p13_cards_to_first_ace
#print axioms TowerBatch.p17_three_of_five_vote
#print axioms TowerBatch.p21_rare_one_in_1000
#print axioms TowerBatch.p22_st_petersburg_capped
#print axioms p31_markov_weather_four_steps
#print axioms CheapLane.p32_markov_token_absorption_limit
#print axioms CheapLane.p36_birthday_expected_distinct
#print axioms p37_random_walk_hits_three
#print axioms CheapLane.p38_random_walk_2d
#print axioms CheapLane.p39_expected_max
#print axioms CheapLane.p40_first_return_10
#print axioms p41_shuffle_derangement_ten
#print axioms CheapLane.p42_shuffle_expected_cycles
#print axioms CheapLane.p43_shuffle_kept_neighbours
#print axioms CheapLane.p44_bridge_hand_no_spades
#print axioms CheapLane.p45_aces_before_kings
#print axioms TowerBatch.p48_third_success_by_twelve
#print axioms CheapLane.p49_polya_three_reds
#print axioms p52_random_walk_never_negative
#print axioms CheapLane.p53_birthday_expected_pairs
#print axioms CheapLane.p63_trap_coprime_pair_finite
#print axioms TowerBatch.p65_trap_bridge_aces_kings
#print axioms TowerBatch.p65_trap_medical_test_positive
#print axioms TowerBatch.p68_trap_common_shock_failure
#print axioms TowerBatch.p69_trap_twenty_dice_low_tail
#print axioms TowerBatch.p69_trap_two_records_in_row
#print axioms CheapLane.p32_markov_token_absorption
#print axioms DanielRootTheorem
#print axioms CalculusLane.p30_area_under_square
#print axioms CalculusLane.p92_sine_arch
#print axioms CalculusLane.p91_exp_area
#print axioms SeriesLane.p99_telescoping
#print axioms SeriesLane.p94_k_over_two_pow
#print axioms CalculusLane.p100_log_over_x
#print axioms WaitingLane.p09_rolls_to_first_six
#print axioms RootsLane.p95_positive_root_of_two
