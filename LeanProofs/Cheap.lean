import Mathlib

/-!
# The cheap lane (ORD-1027-AK step 3)

Bank problems whose answer is a finite count, proven by the kernel counting every case.
p32 is a limit, not a count: its chance of having won within n moves is proven to close in on 4/7 by a factor
of 3/4 each move.
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

section BridgeHand

open Finset

/-- p44: a card is (suit, rank); suit 0 is spades. -/
abbrev Card := Fin 4 × Fin 13

/-- Every 13-card hand from the 52-card deck, each equally likely. -/
def hands : Finset (Finset Card) := powersetCard 13 univ

/-- A hand with no spades but at least one card of each other suit. -/
def NoSpadesAllElse (h : Finset Card) : Prop :=
  (∀ c ∈ h, c.1 ≠ 0) ∧ ∀ s : Fin 4, s ≠ 0 → ∃ c ∈ h, c.1 = s

instance : DecidablePred NoSpadesAllElse := fun h => by unfold NoSpadesAllElse; infer_instance

/-- The cards not of suit s. -/
def notSuit (s : Fin 4) : Finset Card := univ.filter (fun c => c.1 ≠ s)

/-- The hands made only of cards from U. -/
def within (U : Finset Card) : Finset (Finset Card) := hands.filter (· ⊆ U)

theorem within_eq (U : Finset Card) : within U = powersetCard 13 U := by
  ext h
  simp only [within, hands, mem_filter, mem_powersetCard, subset_univ, true_and]
  tauto

theorem card_within (U : Finset Card) : (within U).card = U.card.descFactorial 13 / Nat.factorial 13 := by
  rw [within_eq, card_powersetCard, Nat.choose_eq_descFactorial_div_factorial]

theorem within_inter (U V : Finset Card) : within U ∩ within V = within (U ∩ V) := by
  ext x : 1
  simp only [within, mem_inter, mem_filter, subset_inter_iff]
  generalize (x ∈ hands) = a
  generalize (x ⊆ U) = u
  generalize (x ⊆ V) = v
  tauto

theorem within_mono {U V : Finset Card} (hUV : U ⊆ V) : within U ⊆ within V := by
  intro h
  simp only [within, mem_filter]
  exact fun ⟨a, b⟩ => ⟨a, b.trans hUV⟩

theorem has_suit (h : Finset Card) (s : Fin 4) : (∃ c ∈ h, c.1 = s) ↔ ¬ h ⊆ notSuit s := by
  simp [notSuit, subset_iff]

theorem good_eq :
    hands.filter NoSpadesAllElse =
      within (notSuit 0) \ (within (notSuit 0 ∩ notSuit 1) ∪ within (notSuit 0 ∩ notSuit 2)
        ∪ within (notSuit 0 ∩ notSuit 3)) := by
  ext h : 1
  have h0 : (∀ c ∈ h, c.1 ≠ 0) ↔ h ⊆ notSuit 0 := by simp [notSuit, subset_iff]
  have hs : (∀ s : Fin 4, s ≠ 0 → ∃ c ∈ h, c.1 = s) ↔
      (¬ h ⊆ notSuit 1 ∧ ¬ h ⊆ notSuit 2 ∧ ¬ h ⊆ notSuit 3) := by
    rw [← has_suit, ← has_suit, ← has_suit]
    constructor
    · intro H; exact ⟨H 1 (by decide), H 2 (by decide), H 3 (by decide)⟩
    · rintro ⟨a, b, c⟩ s hs0
      fin_cases s
      · exact absurd rfl hs0
      · exact a
      · exact b
      · exact c
  simp only [mem_filter, NoSpadesAllElse, h0, hs, mem_sdiff, mem_union, within, subset_inter_iff]
  generalize (h ∈ hands) = a
  generalize (h ⊆ notSuit 0) = p0
  generalize (h ⊆ notSuit 1) = p1
  generalize (h ⊆ notSuit 2) = p2
  generalize (h ⊆ notSuit 3) = p3
  tauto

/-- p44: of the 635,013,559,600 hands of 13 cards, 8,091,223,647 have no spades but every other suit: the
hands within the 39 non-spades, less those that also miss hearts, diamonds or clubs (inclusion and exclusion). -/
theorem p44_count : (hands.filter NoSpadesAllElse).card = 8091223647 ∧ hands.card = 635013559600 := by
  set B1 := within (notSuit 0 ∩ notSuit 1)
  set B2 := within (notSuit 0 ∩ notSuit 2)
  set B3 := within (notSuit 0 ∩ notSuit 3)
  have hsub : B1 ∪ B2 ∪ B3 ⊆ within (notSuit 0) :=
    union_subset (union_subset (within_mono inter_subset_left) (within_mono inter_subset_left))
      (within_mono inter_subset_left)
  have e1 := card_union_add_card_inter B1 B2
  have e2 := card_union_add_card_inter (B1 ∪ B2) B3
  rw [union_inter_distrib_right] at e2
  have e3 := card_union_add_card_inter (B1 ∩ B3) (B2 ∩ B3)
  have cA : (within (notSuit 0)).card = 8122425444 := by rw [card_within]; decide +kernel
  have c1 : B1.card = 10400600 := by rw [card_within]; decide +kernel
  have c2 : B2.card = 10400600 := by rw [card_within]; decide +kernel
  have c3 : B3.card = 10400600 := by rw [card_within]; decide +kernel
  have c12 : (B1 ∩ B2).card = 1 := by rw [within_inter, card_within]; decide +kernel
  have c13 : (B1 ∩ B3).card = 1 := by rw [within_inter, card_within]; decide +kernel
  have c23 : (B2 ∩ B3).card = 1 := by rw [within_inter, card_within]; decide +kernel
  have c123 : (B1 ∩ B3 ∩ (B2 ∩ B3)).card = 0 := by
    rw [within_inter, within_inter, within_inter, card_within]; decide +kernel
  have cH : hands.card = 635013559600 := by
    rw [hands, card_powersetCard, Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  refine ⟨?_, cH⟩
  rw [good_eq, card_sdiff_of_subset hsub, cA]
  omega

/-- p44: so a 13-card hand has no spades but every other suit with chance 8091223647/635013559600. -/
theorem p44_bridge_hand_no_spades :
    ((hands.filter NoSpadesAllElse).card : ℚ) / (hands.card : ℚ) = 8091223647 / 635013559600 := by
  rw [p44_count.1, p44_count.2]
  norm_num

end BridgeHand

section Cycles

open Equiv Finset

/-- The cycles of a permutation of 20 cards: its cycles of length 2 or more (Mathlib's `cycleFactorsFinset`) plus its
fixed points (the cycles of length 1). -/
def numCycles {n : ℕ} (σ : Perm (Fin n)) : ℕ := #σ.cycleFactorsFinset + #{x | σ x = x}

/-- The lists, largest part first, with every part from 2 to M, parts adding up to at most N, and at most f parts:
every possible list of cycle lengths (2 or more) of a permutation. -/
def cycleShapes : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | f + 1, N, M => [] :: (List.range' 2 (M - 1)).flatMap
      (fun a => if a ≤ N then (cycleShapes f (N - a) a).map (a :: ·) else [])

theorem mem_cycleShapes : ∀ (f N M : ℕ) (l : List ℕ), l.Pairwise (· ≥ ·) →
    (∀ x ∈ l, 2 ≤ x ∧ x ≤ M) → l.sum ≤ N → l.length ≤ f → l ∈ cycleShapes f N M
  | 0, _, _, [], _, _, _, _ => by simp [cycleShapes]
  | _ + 1, _, _, [], _, _, _, _ => by simp [cycleShapes]
  | 0, _, _, _ :: _, _, _, _, h => by simp at h
  | f + 1, N, M, a :: t, hp, hx, hs, hl => by
    rw [List.pairwise_cons] at hp
    have ha := hx a List.mem_cons_self
    simp only [List.sum_cons, List.length_cons] at hs hl
    simp only [cycleShapes, List.mem_cons, List.mem_flatMap, List.mem_range'_1]
    right
    refine ⟨a, ⟨by omega, by omega⟩, ?_⟩
    split_ifs with haN
    · exact List.mem_map.2 ⟨t, mem_cycleShapes f (N - a) a t hp.2
        (fun x hx' => ⟨(hx x (List.mem_cons_of_mem _ hx')).1, hp.1 x hx'⟩) (by omega) (by omega), rfl⟩
    · omega

theorem le_sum_of_mem' : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | a :: t, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem' t x h
      simp only [List.sum_cons]; omega

theorem two_mul_length_le : ∀ (l : List ℕ), (∀ x ∈ l, 2 ≤ x) → 2 * l.length ≤ l.sum
  | [], _ => by simp
  | a :: t, h => by
    have := two_mul_length_le t (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h a List.mem_cons_self
    simp only [List.sum_cons, List.length_cons]; omega

/-- Every listed shape is sorted, largest part first, with no part above M. -/
theorem cycleShapes_sorted : ∀ (f N M : ℕ), ∀ l ∈ cycleShapes f N M, l.Pairwise (· ≥ ·) ∧ ∀ x ∈ l, x ≤ M
  | 0, _, _, l, h => by
    simp only [cycleShapes, List.mem_singleton] at h
    subst h; simp
  | f + 1, N, M, l, h => by
    simp only [cycleShapes, List.mem_cons, List.mem_flatMap, List.mem_range'_1] at h
    rcases h with rfl | ⟨a, ⟨ha2, haM⟩, h⟩
    · simp
    · split_ifs at h with haN
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
        have ih := cycleShapes_sorted f (N - a) a t ht
        refine ⟨List.pairwise_cons.2 ⟨fun x hx => ih.2 x hx, ih.1⟩, fun x hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · have := ih.2 x hx; omega
      · simp at h

/-- No shape is listed twice. -/
theorem cycleShapes_nodup : ∀ (f N M : ℕ), (cycleShapes f N M).Nodup
  | 0, _, _ => by simp [cycleShapes]
  | f + 1, N, M => by
    rw [cycleShapes, List.nodup_cons]
    constructor
    · simp only [List.mem_flatMap, not_exists, not_and]
      intro a _ h
      split_ifs at h
      · simp at h
      · simp at h
    · rw [List.nodup_flatMap]
      constructor
      · intro a _
        split_ifs
        · exact (cycleShapes_nodup f (N - a) a).map (fun _ _ h => List.cons_injective h)
        · exact List.nodup_nil
      · refine List.Nodup.pairwise_of_forall_ne List.nodup_range' fun a _ b _ hab => ?_
        rw [Function.onFun, List.disjoint_left]
        intro l hla hlb
        split_ifs at hla hlb <;> simp only [List.mem_map, List.not_mem_nil] at hla hlb
        obtain ⟨t, _, rfl⟩ := hla
        obtain ⟨u, _, hu⟩ := hlb
        exact hab (List.cons_eq_cons.1 hu).1.symm

/-- The 627 cycle shapes of permutations of 20 cards. -/
def shapes20 : List (List ℕ) := cycleShapes 10 20 20

/-- The shapes as multisets (Mathlib's `cycleType` is a multiset); no two are the same, since each list is sorted. -/
def shapeSet : Finset (Multiset ℕ) :=
  ⟨↑(shapes20.map (fun l : List ℕ => (l : Multiset ℕ))), Multiset.coe_nodup.2 <|
    (cycleShapes_nodup 10 20 20).map_on fun x hx y hy h =>
      List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (cycleShapes_sorted 10 20 20 x hx).1
        (cycleShapes_sorted 10 20 20 y hy).1 (Multiset.coe_eq_coe.1 h)⟩

/-- Every permutation of 20 cards has one of the listed shapes. -/
theorem cycleType_mem_shapeSet (σ : Perm (Fin 20)) : σ.cycleType ∈ shapeSet := by
  set l := σ.cycleType.sort (· ≥ ·)
  have hl : (l : Multiset ℕ) = σ.cycleType := Multiset.sort_eq _ _
  have hsum : l.sum ≤ 20 := by
    have := Perm.sum_cycleType_le σ
    rw [← hl, Multiset.sum_coe, Fintype.card_fin] at this
    exact this
  have h2 : ∀ x ∈ l, 2 ≤ x := fun x hx =>
    Perm.two_le_of_mem_cycleType ((Multiset.mem_sort (· ≥ ·)).1 hx)
  have hmem : l ∈ shapes20 :=
    mem_cycleShapes 10 20 20 l (Multiset.pairwise_sort _ _)
      (fun x hx => ⟨h2 x hx, (le_sum_of_mem' l x hx).trans hsum⟩) hsum
      (by have := two_mul_length_le l h2; omega)
  show σ.cycleType ∈ (↑(shapes20.map (fun l : List ℕ => (l : Multiset ℕ))) : Multiset (Multiset ℕ))
  rw [Multiset.mem_coe, List.mem_map]
  exact ⟨l, hmem, hl⟩

theorem numCycles_eq (σ : Perm (Fin 20)) :
    numCycles σ = Multiset.card σ.cycleType + (20 - σ.cycleType.sum) := by
  have h1 : Multiset.card σ.cycleType = #σ.cycleFactorsFinset := by
    rw [Perm.cycleType_def, Multiset.card_map]; rfl
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin 20))) (fun x => σ x = x)
  have h3 : #σ.support = #(univ.filter fun x => ¬ σ x = x) := by
    congr 1
  simp only [card_univ, Fintype.card_fin] at h2
  rw [Perm.sum_cycleType, h1, numCycles]
  omega

/-- p42: over all 20! permutations of 20 cards, the cycles add up to 8,752,948,036,761,600,000 = 20! * H(20): the
permutations are grouped by cycle shape, and Mathlib's `card_of_cycleType` counts each group. -/
theorem p42_total : ∑ σ : Perm (Fin 20), numCycles σ = 8752948036761600000 := by
  simp only [numCycles_eq]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := shapeSet) (g := Perm.cycleType)
    (fun σ _ => cycleType_mem_shapeSet σ)]
  have hfib : ∀ m ∈ shapeSet,
      (∑ σ ∈ univ.filter (fun σ : Perm (Fin 20) => σ.cycleType = m),
        (Multiset.card σ.cycleType + (20 - σ.cycleType.sum)))
        = #{σ : Perm (Fin 20) | σ.cycleType = m} * (Multiset.card m + (20 - m.sum)) := by
    intro m _
    rw [Finset.sum_congr rfl (g := fun _ => Multiset.card m + (20 - m.sum))
      (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]), Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_congr rfl hfib]
  simp only [Equiv.Perm.card_of_cycleType, Fintype.card_fin]
  decide +kernel

/-- p42: so a uniformly random permutation of 20 cards has 55835135/15519504 cycles on average (= H(20), fixed points
counted as cycles of length 1). -/
theorem p42_shuffle_expected_cycles :
    ((∑ σ : Perm (Fin 20), numCycles σ : ℕ) : ℚ) / (Fintype.card (Perm (Fin 20)) : ℚ)
      = 55835135 / 15519504 := by
  have hf : (20 : ℕ).factorial = 2432902008176640000 := by decide +kernel
  rw [p42_total, Fintype.card_perm, Fintype.card_fin, hf]
  norm_num

end Cycles

section Shuffles

/-- After card a, the cards l keep a neighbouring pair: some card is immediately followed by the card one above it. -/
def keepsAfter : ℕ → List ℕ → Bool
  | _, [] => false
  | a, b :: t => (b == a + 1) || keepsAfter b t

/-- A shuffled order keeps some originally neighbouring pair together, in order: some card i is immediately followed by
card i + 1. -/
def keepsNeighbours : List ℕ → Bool
  | [] => false
  | a :: t => keepsAfter a t

theorem keepsAfter_iff : ∀ (a : ℕ) (t : List ℕ), keepsAfter a t = true ↔ ∃ i, [i, i + 1] <:+: a :: t
  | a, [] => by
    simp only [keepsAfter, Bool.false_eq_true, false_iff, not_exists]
    intro i h
    have := h.length_le
    simp at this
  | a, b :: t => by
    have ih := keepsAfter_iff b t
    simp only [keepsAfter, Bool.or_eq_true, beq_iff_eq, ih]
    constructor
    · rintro (h | ⟨i, hi⟩)
      · exact ⟨a, List.infix_cons_iff.2 (Or.inl (by simp [h]))⟩
      · exact ⟨i, List.infix_cons_iff.2 (Or.inr hi)⟩
    · rintro ⟨i, h⟩
      rcases List.infix_cons_iff.1 h with h | h
      · left
        simp only [List.cons_prefix_cons] at h
        omega
      · exact Or.inr ⟨i, h⟩

/-- `keepsNeighbours` says exactly that the two-card run [i, i + 1] appears somewhere in the shuffled order. -/
theorem keepsNeighbours_iff (l : List ℕ) : keepsNeighbours l = true ↔ ∃ i, [i, i + 1] <:+: l := by
  cases l with
  | nil => simp [keepsNeighbours]
  | cons a t => exact keepsAfter_iff a t

/-- Every order of the cards in r, one card at a time (n is the number of cards still to place). -/
def orders : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | _ + 1, [] => [[]]
  | n + 1, r@(_ :: _) => r.flatMap fun x => (orders n (r.erase x)).map (x :: ·)

theorem orders_step (n : ℕ) (r : List ℕ) (hr : r ≠ []) :
    orders (n + 1) r = r.flatMap fun x => (orders n (r.erase x)).map (x :: ·) := by
  cases r with
  | nil => exact absurd rfl hr
  | cons _ _ => rfl

theorem mem_orders : ∀ (n : ℕ) (r l : List ℕ), r.Nodup → r.length ≤ n → (l ∈ orders n r ↔ l.Perm r)
  | 0, r, l, _, hn => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)]
    simp [orders]
  | _ + 1, [], l, _, _ => by simp [orders]
  | n + 1, c :: cs, l, hr, hn => by
    rw [orders_step _ _ (List.cons_ne_nil c cs), List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, hl⟩
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      have h' := (mem_orders n _ l' (hr.erase x) (by rw [List.length_erase_of_mem hx]; simp at hn ⊢; omega)).1 hl'
      exact (h'.cons x).trans (List.perm_cons_erase hx).symm
    · intro hp
      cases l with
      | nil => exact absurd hp.symm.eq_nil (List.cons_ne_nil c cs)
      | cons x l' =>
        have hx : x ∈ c :: cs := hp.subset List.mem_cons_self
        refine ⟨x, hx, List.mem_map.2 ⟨l', ?_, rfl⟩⟩
        refine (mem_orders n _ l' (hr.erase x) (by rw [List.length_erase_of_mem hx]; simp at hn ⊢; omega)).2 ?_
        exact (hp.trans (List.perm_cons_erase hx)).cons_inv

theorem orders_nodup : ∀ (n : ℕ) (r : List ℕ), r.Nodup → (orders n r).Nodup
  | 0, _, _ => by simp [orders]
  | _ + 1, [], _ => by simp [orders]
  | n + 1, c :: cs, hr => by
    rw [orders_step _ _ (List.cons_ne_nil c cs), List.nodup_flatMap]
    constructor
    · intro x _
      exact (orders_nodup n _ (hr.erase x)).map (fun _ _ h => List.cons_injective h)
    · refine hr.pairwise_of_forall_ne fun a _ b _ hab => ?_
      rw [Function.onFun, List.disjoint_left]
      intro l hla hlb
      obtain ⟨t, _, rfl⟩ := List.mem_map.1 hla
      obtain ⟨u, _, hu⟩ := List.mem_map.1 hlb
      exact hab (List.cons_eq_cons.1 hu).1.symm

/-- How many orders of the cards in r, placed after card a, keep no neighbouring pair (counted one card at a time, a
branch stops as soon as a pair is kept). -/
def free : ℕ → ℕ → List ℕ → ℕ
  | 0, _, _ => 1
  | _ + 1, _, [] => 1
  | n + 1, a, r@(_ :: _) => (r.map fun x => if x = a + 1 then 0 else free n x (r.erase x)).sum

theorem free_step (n a : ℕ) (r : List ℕ) (hr : r ≠ []) :
    free (n + 1) a r = (r.map fun x => if x = a + 1 then 0 else free n x (r.erase x)).sum := by
  cases r with
  | nil => exact absurd rfl hr
  | cons _ _ => rfl

/-- `free` counts the orders that keep no neighbouring pair. -/
theorem countP_orders : ∀ (n a : ℕ) (r : List ℕ),
    (orders n r).countP (fun l => !keepsAfter a l) = free n a r
  | 0, _, _ => by simp [orders, free, keepsAfter]
  | _ + 1, _, [] => by simp [orders, free, keepsAfter]
  | n + 1, a, c :: cs => by
    rw [orders_step _ _ (List.cons_ne_nil c cs), free_step _ _ _ (List.cons_ne_nil c cs), List.countP_flatMap]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, List.countP_map]
    split_ifs with h
    · subst h
      exact List.countP_eq_zero.2 fun l _ => by simp [keepsAfter]
    · rw [← countP_orders n x]
      congr 1
      funext l
      simp [keepsAfter, h]

/-- Every order of the 10 cards 0..9 (all 10! = 3,628,800 shuffles, each equally likely). -/
def shuffles10 : Finset (List ℕ) := ⟨↑(orders 10 (List.range 10)), Multiset.coe_nodup.2 (orders_nodup _ _ List.nodup_range)⟩

theorem mem_shuffles10 (l : List ℕ) : l ∈ shuffles10 ↔ l.Perm (List.range 10) := by
  show l ∈ (↑(orders 10 (List.range 10)) : Multiset (List ℕ)) ↔ _
  rw [Multiset.mem_coe, mem_orders _ _ _ List.nodup_range (by simp)]

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 0 that keep no neighbouring pair: 133496. -/
theorem free_first_0 : free 9 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 0) = 133496 := by
  show free 9 0 [1, 2, 3, 4, 5, 6, 7, 8, 9] = 133496
  have h2 : free 8 2 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 2) = 16687 := by decide +kernel
  have h3 : free 8 3 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 3) = 16687 := by decide +kernel
  have h4 : free 8 4 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 4) = 16687 := by decide +kernel
  have h5 : free 8 5 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 5) = 16687 := by decide +kernel
  have h6 : free 8 6 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 6) = 16687 := by decide +kernel
  have h7 : free 8 7 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 7) = 16687 := by decide +kernel
  have h8 : free 8 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 8) = 16687 := by decide +kernel
  have h9 : free 8 9 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase 9) = 16687 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h4, h5, h6, h7, h8, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 1 that keep no neighbouring pair: 148329. -/
theorem free_first_1 : free 9 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 1) = 148329 := by
  show free 9 1 [0, 2, 3, 4, 5, 6, 7, 8, 9] = 148329
  have h0 : free 8 0 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 0) = 16687 := by decide +kernel
  have h3 : free 8 3 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 3) = 18806 := by decide +kernel
  have h4 : free 8 4 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 4) = 18806 := by decide +kernel
  have h5 : free 8 5 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 5) = 18806 := by decide +kernel
  have h6 : free 8 6 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 6) = 18806 := by decide +kernel
  have h7 : free 8 7 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 7) = 18806 := by decide +kernel
  have h8 : free 8 8 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 8) = 18806 := by decide +kernel
  have h9 : free 8 9 ([0, 2, 3, 4, 5, 6, 7, 8, 9].erase 9) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h3, h4, h5, h6, h7, h8, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 2 that keep no neighbouring pair: 148329. -/
theorem free_first_2 : free 9 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 2) = 148329 := by
  show free 9 2 [0, 1, 3, 4, 5, 6, 7, 8, 9] = 148329
  have h0 : free 8 0 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 0) = 16687 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 1) = 18806 := by decide +kernel
  have h4 : free 8 4 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 4) = 18806 := by decide +kernel
  have h5 : free 8 5 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 5) = 18806 := by decide +kernel
  have h6 : free 8 6 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 6) = 18806 := by decide +kernel
  have h7 : free 8 7 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 7) = 18806 := by decide +kernel
  have h8 : free 8 8 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 8) = 18806 := by decide +kernel
  have h9 : free 8 9 ([0, 1, 3, 4, 5, 6, 7, 8, 9].erase 9) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h4, h5, h6, h7, h8, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 3 that keep no neighbouring pair: 148329. -/
theorem free_first_3 : free 9 3 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 3) = 148329 := by
  show free 9 3 [0, 1, 2, 4, 5, 6, 7, 8, 9] = 148329
  have h0 : free 8 0 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 0) = 16687 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 1) = 18806 := by decide +kernel
  have h2 : free 8 2 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 2) = 18806 := by decide +kernel
  have h5 : free 8 5 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 5) = 18806 := by decide +kernel
  have h6 : free 8 6 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 6) = 18806 := by decide +kernel
  have h7 : free 8 7 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 7) = 18806 := by decide +kernel
  have h8 : free 8 8 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 8) = 18806 := by decide +kernel
  have h9 : free 8 9 ([0, 1, 2, 4, 5, 6, 7, 8, 9].erase 9) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h5, h6, h7, h8, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 4 that keep no neighbouring pair: 148329. -/
theorem free_first_4 : free 9 4 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 4) = 148329 := by
  show free 9 4 [0, 1, 2, 3, 5, 6, 7, 8, 9] = 148329
  have h0 : free 8 0 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 0) = 16687 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 1) = 18806 := by decide +kernel
  have h2 : free 8 2 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 2) = 18806 := by decide +kernel
  have h3 : free 8 3 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 3) = 18806 := by decide +kernel
  have h6 : free 8 6 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 6) = 18806 := by decide +kernel
  have h7 : free 8 7 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 7) = 18806 := by decide +kernel
  have h8 : free 8 8 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 8) = 18806 := by decide +kernel
  have h9 : free 8 9 ([0, 1, 2, 3, 5, 6, 7, 8, 9].erase 9) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h6, h7, h8, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 5 that keep no neighbouring pair: 148329. -/
theorem free_first_5 : free 9 5 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 5) = 148329 := by
  show free 9 5 [0, 1, 2, 3, 4, 6, 7, 8, 9] = 148329
  have h0 : free 8 0 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 0) = 16687 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 1) = 18806 := by decide +kernel
  have h2 : free 8 2 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 2) = 18806 := by decide +kernel
  have h3 : free 8 3 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 3) = 18806 := by decide +kernel
  have h4 : free 8 4 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 4) = 18806 := by decide +kernel
  have h7 : free 8 7 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 7) = 18806 := by decide +kernel
  have h8 : free 8 8 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 8) = 18806 := by decide +kernel
  have h9 : free 8 9 ([0, 1, 2, 3, 4, 6, 7, 8, 9].erase 9) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4, h7, h8, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 6 that keep no neighbouring pair: 148329. -/
theorem free_first_6 : free 9 6 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 6) = 148329 := by
  show free 9 6 [0, 1, 2, 3, 4, 5, 7, 8, 9] = 148329
  have h0 : free 8 0 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 0) = 16687 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 1) = 18806 := by decide +kernel
  have h2 : free 8 2 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 2) = 18806 := by decide +kernel
  have h3 : free 8 3 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 3) = 18806 := by decide +kernel
  have h4 : free 8 4 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 4) = 18806 := by decide +kernel
  have h5 : free 8 5 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 5) = 18806 := by decide +kernel
  have h8 : free 8 8 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 8) = 18806 := by decide +kernel
  have h9 : free 8 9 ([0, 1, 2, 3, 4, 5, 7, 8, 9].erase 9) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4, h5, h8, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 7 that keep no neighbouring pair: 148329. -/
theorem free_first_7 : free 9 7 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 7) = 148329 := by
  show free 9 7 [0, 1, 2, 3, 4, 5, 6, 8, 9] = 148329
  have h0 : free 8 0 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 0) = 16687 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 1) = 18806 := by decide +kernel
  have h2 : free 8 2 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 2) = 18806 := by decide +kernel
  have h3 : free 8 3 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 3) = 18806 := by decide +kernel
  have h4 : free 8 4 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 4) = 18806 := by decide +kernel
  have h5 : free 8 5 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 5) = 18806 := by decide +kernel
  have h6 : free 8 6 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 6) = 18806 := by decide +kernel
  have h9 : free 8 9 ([0, 1, 2, 3, 4, 5, 6, 8, 9].erase 9) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4, h5, h6, h9]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 8 that keep no neighbouring pair: 148329. -/
theorem free_first_8 : free 9 8 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 8) = 148329 := by
  show free 9 8 [0, 1, 2, 3, 4, 5, 6, 7, 9] = 148329
  have h0 : free 8 0 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 0) = 16687 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 1) = 18806 := by decide +kernel
  have h2 : free 8 2 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 2) = 18806 := by decide +kernel
  have h3 : free 8 3 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 3) = 18806 := by decide +kernel
  have h4 : free 8 4 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 4) = 18806 := by decide +kernel
  have h5 : free 8 5 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 5) = 18806 := by decide +kernel
  have h6 : free 8 6 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 6) = 18806 := by decide +kernel
  have h7 : free 8 7 ([0, 1, 2, 3, 4, 5, 6, 7, 9].erase 7) = 18806 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4, h5, h6, h7]
  decide

set_option maxHeartbeats 4000000 in
/-- The orders of the other nine cards after card 9 that keep no neighbouring pair: 148329. -/
theorem free_first_9 : free 9 9 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase 9) = 148329 := by
  show free 9 9 [0, 1, 2, 3, 4, 5, 6, 7, 8] = 148329
  have h0 : free 8 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 0) = 14833 := by decide +kernel
  have h1 : free 8 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 1) = 16687 := by decide +kernel
  have h2 : free 8 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 2) = 16687 := by decide +kernel
  have h3 : free 8 3 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 3) = 16687 := by decide +kernel
  have h4 : free 8 4 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 4) = 16687 := by decide +kernel
  have h5 : free 8 5 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 5) = 16687 := by decide +kernel
  have h6 : free 8 6 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 6) = 16687 := by decide +kernel
  have h7 : free 8 7 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 7) = 16687 := by decide +kernel
  have h8 : free 8 8 ([0, 1, 2, 3, 4, 5, 6, 7, 8].erase 8) = 16687 := by decide +kernel
  refine (free_step _ _ _ (by decide)).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  decide


/-- p43: there are 10! = 3,628,800 shuffles of 10 cards. -/
theorem p43_card_shuffles : shuffles10.card = 3628800 := by
  have h : (shuffles10.val) = ↑(List.range 10).permutations := by
    show (↑(orders 10 (List.range 10)) : Multiset (List ℕ)) = _
    rw [Multiset.coe_eq_coe]
    refine (List.perm_ext_iff_of_nodup (orders_nodup _ _ List.nodup_range)
      (List.nodup_permutations _ List.nodup_range)).2 fun l => ?_
    rw [mem_orders _ _ _ List.nodup_range (by simp), List.mem_permutations]
  rw [Finset.card, h, Multiset.coe_card, List.length_permutations, List.length_range]
  decide

/-- 1,468,457 of the shuffles keep no neighbouring pair: the shuffles grouped by first card, each group counted by `free`
(the ten `free_first` lemmas). -/
theorem orders_none_count : (orders 10 (List.range 10)).countP (fun l => !keepsNeighbours l) = 1468457 := by
  rw [show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl,
    orders_step _ _ (List.cons_ne_nil _ _), List.countP_flatMap]
  have e : ∀ x : ℕ, (List.countP (fun l => !keepsNeighbours l) ∘ fun x =>
      (orders 9 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase x)).map (x :: ·)) x
      = free 9 x ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].erase x) := by
    intro x
    rw [Function.comp_apply, List.countP_map, ← countP_orders]
    rfl
  simp only [e, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, free_first_0, free_first_1, free_first_2,
    free_first_3, free_first_4, free_first_5, free_first_6, free_first_7, free_first_8, free_first_9]
  norm_num

theorem card_keeps_eq_countP : (shuffles10.filter (fun l => keepsNeighbours l = true)).card
    = (orders 10 (List.range 10)).countP keepsNeighbours := by
  rw [List.countP_eq_length_filter]
  show Multiset.card (Multiset.filter _ (↑(orders 10 (List.range 10)) : Multiset (List ℕ))) = _
  rw [Multiset.filter_coe, Multiset.coe_card]
  simp only [Bool.decide_eq_true]

theorem orders_length : (orders 10 (List.range 10)).length = 3628800 := by
  have := p43_card_shuffles
  rwa [Finset.card, show shuffles10.val = ↑(orders 10 (List.range 10)) from rfl, Multiset.coe_card] at this

theorem countP_add_countP_not (p : List ℕ → Bool) :
    ∀ L : List (List ℕ), L.countP p + L.countP (fun l => !p l) = L.length
  | [] => rfl
  | a :: t => by
    have := countP_add_countP_not p t
    cases h : p a <;> simp [h] <;> omega

/-- p43: so 3,628,800 - 1,468,457 = 2,160,343 shuffles keep some originally neighbouring pair together in order. -/
theorem p43_count : (shuffles10.filter (fun l => keepsNeighbours l = true)).card = 2160343 := by
  have e := countP_add_countP_not keepsNeighbours (orders 10 (List.range 10))
  rw [orders_none_count, orders_length] at e
  exact card_keeps_eq_countP.trans ((Nat.eq_sub_of_add_eq e).trans (by norm_num))

/-- p43: so a shuffle of 10 cards keeps some neighbouring pair (a card i right before card i + 1) together in order with
chance 2160343/3628800. -/
theorem p43_shuffle_kept_neighbours :
    ((shuffles10.filter (fun l => keepsNeighbours l = true)).card : ℚ) / (shuffles10.card : ℚ)
      = 2160343 / 3628800 := by
  rw [p43_count, p43_card_shuffles]
  norm_num

end Shuffles

section MarkovToken

/-!
# p32: Markov token, reaching the win square before the lose square (bank answer 4/7)

Squares 0, 1, 2, 3. The token starts on square 1. Square 0 loses and square 3 wins; both stop the game.
From square 1 it moves to 0, stays on 1, or moves to 2 with chances 1/4, 1/4, 1/2.
From square 2 it moves to 1, stays on 2, or moves to 3 with chances 1/4, 1/4, 1/2.

`winWithin n s` is the chance that a token on square s is on the win square after n moves. The stopped squares keep
the token (chance 1 of staying), so this is the chance of having won within n moves. The chance of reaching the win
square before the lose square is the limit of `winWithin n 1` as n grows.
-/

namespace P32

/-- `move s t`: the chance of going from square s to square t in one move. -/
def move : Fin 4 → Fin 4 → ℚ :=
  ![![1, 0, 0, 0],
    ![1/4, 1/4, 1/2, 0],
    ![0, 1/4, 1/4, 1/2],
    ![0, 0, 0, 1]]

/-- The chance of being on square 3 (won) after n moves, starting from square s. -/
def winWithin : ℕ → Fin 4 → ℚ
  | 0, s => if s = 3 then 1 else 0
  | n + 1, s => ∑ t : Fin 4, move s t * winWithin n t

end P32

/-- p32: a token starting on square 1 reaches the win square before the lose square with chance exactly 4/7: the chance
of having won within n moves tends to 4/7 as n grows. -/
theorem p32_markov_token_absorption :
    Filter.Tendsto (fun n : ℕ => (P32.winWithin n 1 : ℝ)) Filter.atTop (nhds (4 / 7 : ℝ)) := by
  have h0 : ∀ n, P32.winWithin n 0 = 0 := by
    intro n
    induction n with
    | zero => simp [P32.winWithin]
    | succ n ih => simp [P32.winWithin, Fin.sum_univ_four, P32.move, ih]
  have h3 : ∀ n, P32.winWithin n 3 = 1 := by
    intro n
    induction n with
    | zero => simp [P32.winWithin]
    | succ n ih => simp [P32.winWithin, Fin.sum_univ_four, P32.move, ih]
  have hrec1 : ∀ n, P32.winWithin (n+1) 1 = 1/4 * P32.winWithin n 1 + 1/2 * P32.winWithin n 2 := by
    intro n
    simp [P32.winWithin, Fin.sum_univ_four, P32.move, h0]
  have hrec2 : ∀ n, P32.winWithin (n+1) 2 = 1/4 * P32.winWithin n 1 + 1/4 * P32.winWithin n 2 + 1/2 := by
    intro n
    simp [P32.winWithin, Fin.sum_univ_four, P32.move, h3]
  have ra : ∀ n, (P32.winWithin (n+1) 1 : ℝ) = 1/4 * (P32.winWithin n 1 : ℝ) + 1/2 * (P32.winWithin n 2 : ℝ) := by
    intro n
    rw [hrec1]; push_cast; ring
  have rb : ∀ n, (P32.winWithin (n+1) 2 : ℝ) = 1/4 * (P32.winWithin n 1 : ℝ) + 1/4 * (P32.winWithin n 2 : ℝ) + 1/2 := by
    intro n
    rw [hrec2]; push_cast; ring
  have aux : ∀ e f : ℝ, |1/4*e+1/2*f| + |1/4*e+1/4*f| ≤ 3/4*(|e|+|f|) := by
    intro e f
    rcases abs_cases e with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases f with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases abs_cases (1/4*e+1/2*f) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
    rcases abs_cases (1/4*e+1/4*f) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
    linarith
  have step : ∀ n, |(P32.winWithin (n+1) 1 : ℝ) - 4/7| + |(P32.winWithin (n+1) 2 : ℝ) - 6/7|
      ≤ 3/4 * (|(P32.winWithin n 1 : ℝ) - 4/7| + |(P32.winWithin n 2 : ℝ) - 6/7|) := by
    intro n
    have e1 : (P32.winWithin (n+1) 1 : ℝ) - 4/7
        = 1/4 * ((P32.winWithin n 1 : ℝ) - 4/7) + 1/2 * ((P32.winWithin n 2 : ℝ) - 6/7) := by
      rw [ra]; ring
    have e2 : (P32.winWithin (n+1) 2 : ℝ) - 6/7
        = 1/4 * ((P32.winWithin n 1 : ℝ) - 4/7) + 1/4 * ((P32.winWithin n 2 : ℝ) - 6/7) := by
      rw [rb]; ring
    rw [e1, e2]
    exact aux _ _
  have key : ∀ n, |(P32.winWithin n 1 : ℝ) - 4/7| + |(P32.winWithin n 2 : ℝ) - 6/7|
      ≤ (3/4 : ℝ)^n * (|(P32.winWithin 0 1 : ℝ) - 4/7| + |(P32.winWithin 0 2 : ℝ) - 6/7|) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc _ ≤ 3/4 * (|(P32.winWithin n 1 : ℝ) - 4/7| + |(P32.winWithin n 2 : ℝ) - 6/7|) := step n
        _ ≤ 3/4 * ((3/4 : ℝ)^n * (|(P32.winWithin 0 1 : ℝ) - 4/7| + |(P32.winWithin 0 2 : ℝ) - 6/7|)) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by ring
  have hg : Filter.Tendsto (fun n : ℕ => (3/4 : ℝ)^n * (|(P32.winWithin 0 1 : ℝ) - 4/7| + |(P32.winWithin 0 2 : ℝ) - 6/7|))
      Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3/4 : ℝ)) (by norm_num) (by norm_num)).mul_const
      (|(P32.winWithin 0 1 : ℝ) - 4/7| + |(P32.winWithin 0 2 : ℝ) - 6/7|)
    simpa using this
  have hz : Filter.Tendsto (fun n : ℕ => (P32.winWithin n 1 : ℝ) - 4/7) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs]
    have := key n
    have := abs_nonneg ((P32.winWithin n 2 : ℝ) - 6/7)
    linarith
  exact (tendsto_sub_nhds_zero_iff).mp hz

end MarkovToken

end CheapLane
