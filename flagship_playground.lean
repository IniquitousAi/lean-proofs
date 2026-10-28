import Mathlib

/-!
# Flagship: a random shuffle of 20 cards has exactly 55835135/15519504 cycles on average

Self-contained copy of the p42 proof from `LeanProofs/Cheap.lean` (section `Cycles`, copied unchanged) in
github.com/IniquitousAi/lean-proofs. Created by Daniel Steadham, Humanities Helping Hands.

Plain-English claim: pick one of the 20! = 2,432,902,008,176,640,000 orderings (permutations) of 20 cards, all equally
likely. Follow each card to the place it moved to, and so on, until you come back: that loop is a cycle (a card that
stays put is a cycle of length 1). The average number of cycles is exactly 55835135/15519504 (about 3.598), which is
the 20th harmonic number 1 + 1/2 + ... + 1/20.

How it is proven: there are far too many permutations to list, so the proof groups them by cycle shape. `cycleShapes`
lists the 627 possible shapes; `cycleType_mem_shapeSet` proves every permutation of 20 cards has one of them;
Mathlib's `Equiv.Perm.card_of_cycleType` counts the permutations of each shape; the kernel adds up the 627 groups
(`decide +kernel`, no extra axiom).

What `numCycles` counts: Mathlib's `cycleFactorsFinset` (the cycles of length 2 or more) plus the fixed points.

The last line prints the axioms the headline rests on: expect propext, Classical.choice, Quot.sound.
-/

namespace CheapLane

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

#print axioms p42_shuffle_expected_cycles

end CheapLane
