import Mathlib

set_option linter.style.header false
set_option linter.unusedSimpArgs false

/-!
# Picking the root problem

A prompt compiler has to turn an English prompt into the next piece of work. This file
proves the two decision rules that apply when the gains and times are known, plus the
supporting bottleneck, diminishing-returns, and value-of-information facts. None of the
theorems uses `sorry`.

* `RootPick.adjacent_interchange` and `RootPick.wspt_minimizes_wct` are Smith's rule
  (Wayne E. Smith, *Various optimizers for single-stage production*, Naval Research
  Logistics Quarterly 3 (1956), 59–66): among tasks with known gain `g_i` and positive
  time `t_i`, any order that is pairwise nonincreasing in `g_i / t_i` (compared as the
  cross product `g_j * t_i ≤ g_i * t_j`) minimizes the weighted completion time
  `∑ g_i C_i`.
* `RootPick.Amdahl.larger_stage_higher_speedup`: under a serial pipeline, if a single
  stage can be sped by a common factor `s > 1`, speeding the stage with the larger time
  share yields a weakly higher overall speedup (Gene M. Amdahl, AFIPS 1967).
* `RootPick.Bottleneck.nonbottleneck_no_gain` and `elevate_unique_bottleneck`: in a
  serial chain, throughput is the minimum stage rate. Raising a strictly faster stage,
  without dropping it below the minimum, leaves throughput unchanged; raising the unique
  slowest stage strictly raises throughput (Goldratt's bottleneck fact, stated for rates).
* `RootPick.MarginalValue.optimal_threshold`: with diminishing increments, the net gain
  `∑ (δ_i - λ)` is maximized by taking every increment that is still at least the
  alternative rate `λ` (discrete form of Charnov's 1976 marginal value theorem).
* `RootPick.ValueOfInfo.evpi_nonneg` and `evpi_zero_of_same_action`: the expected value
  of perfect information is nonnegative, and is zero when one action is best in every
  state (Raiffa and Schlaifer, 1961).
* `RootPick.root_first_of_equal_time`: if two fixes take the same time, the one that
  saves `n` copied layers is weakly preferred by Smith's rule, because `c ≤ n * c`
  (Daniel's Root Theorem).

The Gittins index (Gittins and Jones, 1974) is the right rule when gains are *uncertain*.
It is not proved here. In the deterministic case it reduces to Smith's rule (known in
the scheduling literature; not claimed as a theorem of this file).

A runtime compiler decides the next task by the same cross-product test formalized as
`beats`, which is proved equivalent to `wsptRel`.
-/

namespace RootPick

/-- A candidate piece of work with a known gain and a known positive time. -/
structure Task where
  gain : ℕ
  time : ℕ
  time_pos : 0 < time

/-- Smith's ratio test, cross-multiplied so we never divide:
    `wsptRel i j` means `g_i / t_i ≥ g_j / t_j` when times are positive. -/
def wsptRel (i j : Task) : Prop := j.gain * i.time ≤ i.gain * j.time

/-- The Boolean form a runtime prompt compiler can evaluate. -/
def beats (i j : Task) : Bool := decide (j.gain * i.time ≤ i.gain * j.time)

@[simp] theorem beats_iff (i j : Task) : beats i j = true ↔ wsptRel i j := by
  simp [beats, wsptRel]

/-- Weighted completion time of a list of tasks, starting the clock at `s`.
    Each task `t` finishing at time `C` contributes `t.gain * C`. -/
def wctFrom (s : ℕ) : List Task → ℕ
  | [] => 0
  | t :: rest => t.gain * (s + t.time) + wctFrom (s + t.time) rest

/-- Weighted completion time from time 0. The quantity Smith's rule minimizes. -/
def wct (jobs : List Task) : ℕ := wctFrom 0 jobs

@[simp] theorem wctFrom_nil (s : ℕ) : wctFrom s [] = 0 := rfl

@[simp] theorem wctFrom_cons (s : ℕ) (t : Task) (rest : List Task) :
    wctFrom s (t :: rest) = t.gain * (s + t.time) + wctFrom (s + t.time) rest := rfl

/-- The two-job cost identity behind the adjacent-interchange argument:
    the rest of the list starts at the same time either way, and the two-job
    difference is exactly the cross product `g_i t_j - g_j t_i`. -/
theorem adjacent_swap_identity (s : ℕ) (i j : Task) (rest : List Task) :
    wctFrom s (i :: j :: rest) + i.gain * j.time =
      wctFrom s (j :: i :: rest) + j.gain * i.time := by
  have hclock : s + i.time + j.time = s + j.time + i.time := by ac_rfl
  simp only [wctFrom_cons, Nat.add_assoc, hclock]
  ring

/-- Smith's adjacent interchange: if `i` weakly beats `j` on the ratio test,
    doing `i` then `j` then the rest is never more expensive than doing `j` then `i`
    then the rest. -/
theorem adjacent_interchange (s : ℕ) (i j : Task) (rest : List Task)
    (h : wsptRel i j) :
    wctFrom s (i :: j :: rest) ≤ wctFrom s (j :: i :: rest) := by
  have eq := adjacent_swap_identity s i j rest
  have :
      wctFrom s (i :: j :: rest) + i.gain * j.time ≤
        wctFrom s (j :: i :: rest) + i.gain * j.time := by
    rw [eq]
    exact Nat.add_le_add_left h _
  exact Nat.le_of_add_le_add_right this

/-- The two-task decision a compiler makes: pick the higher `g / t` first. -/
theorem pick_max_ratio_first (i j : Task) (h : wsptRel i j) :
    wct [i, j] ≤ wct [j, i] :=
  adjacent_interchange 0 i j [] h

/-- Moving a max-ratio task from anywhere in the list to the front never raises cost. -/
theorem move_to_front (s : ℕ) (a : Task) (left right : List Task)
    (h : ∀ x ∈ left, wsptRel a x) :
    wctFrom s (a :: (left ++ right)) ≤ wctFrom s (left ++ a :: right) := by
  induction left generalizing s with
  | nil => simp
  | cons x xs ih =>
    have hx : wsptRel a x := h x (by simp)
    have hxs : ∀ y ∈ xs, wsptRel a y := fun y hy => h y (by simp [hy])
    calc
      wctFrom s (a :: ((x :: xs) ++ right))
          = wctFrom s (a :: x :: (xs ++ right)) := by simp
      _ ≤ wctFrom s (x :: a :: (xs ++ right)) :=
          adjacent_interchange s a x (xs ++ right) hx
      _ = x.gain * (s + x.time) + wctFrom (s + x.time) (a :: (xs ++ right)) := by
          simp
      _ ≤ x.gain * (s + x.time) + wctFrom (s + x.time) (xs ++ a :: right) :=
          Nat.add_le_add_left (ih (s + x.time) hxs) _
      _ = wctFrom s ((x :: xs) ++ a :: right) := by simp

theorem wsptRel_refl (i : Task) : wsptRel i i := le_rfl

theorem wsptRel_trans {i j k : Task} (hij : wsptRel i j) (hjk : wsptRel j k) :
    wsptRel i k := by
  unfold wsptRel at *
  have htj : 0 < j.time := j.time_pos
  have h1 : k.gain * i.time * j.time ≤ i.gain * k.time * j.time := by
    calc
      k.gain * i.time * j.time = (k.gain * j.time) * i.time := by ring
      _ ≤ (j.gain * k.time) * i.time := Nat.mul_le_mul_right _ hjk
      _ = k.time * (j.gain * i.time) := by ring
      _ ≤ k.time * (i.gain * j.time) := Nat.mul_le_mul_left _ hij
      _ = i.gain * k.time * j.time := by ring
  exact Nat.le_of_mul_le_mul_right h1 htj

theorem wsptRel_total (i j : Task) : wsptRel i j ∨ wsptRel j i :=
  le_total (j.gain * i.time) (i.gain * j.time)

/-- A list is in Smith's (WSPT) order when every earlier task weakly beats every later one. -/
def IsWSPT (jobs : List Task) : Prop := jobs.Pairwise wsptRel

theorem perm_move_to_front {α : Type*} (a : α) (left right : List α) :
    (a :: (left ++ right)).Perm (left ++ a :: right) := by
  induction left with
  | nil => simp
  | cons x xs ih =>
    -- `Perm.swap x a l` is `a :: x :: l ~ x :: a :: l`.
    have hswap : (a :: x :: (xs ++ right)).Perm (x :: a :: (xs ++ right)) :=
      List.Perm.swap x a (xs ++ right)
    have hih : (x :: a :: (xs ++ right)).Perm (x :: (xs ++ a :: right)) := ih.cons x
    have htail : x :: (xs ++ a :: right) = x :: xs ++ a :: right := by simp
    exact (hswap.trans hih).trans (List.Perm.of_eq htail)

/-- Smith's rule: a WSPT order minimizes weighted completion time among all permutations
    of the same tasks. -/
theorem wctFrom_le_of_wspt (s : ℕ) {L M : List Task}
    (hL : IsWSPT L) (hperm : L.Perm M) :
    wctFrom s L ≤ wctFrom s M := by
  induction L generalizing s M with
  | nil =>
    have hM : M = [] := List.Perm.eq_nil hperm.symm
    simp [hM]
  | cons a rest ih =>
    have ha : ∀ x ∈ rest, wsptRel a x := (List.pairwise_cons.mp hL).1
    have hrest : IsWSPT rest := (List.pairwise_cons.mp hL).2
    have hin : a ∈ M := hperm.mem_iff.mp (List.mem_cons_self)
    obtain ⟨left, right, hM⟩ := List.mem_iff_append.mp hin
    subst hM
    have hmid : (a :: (left ++ right)).Perm (left ++ a :: right) :=
      perm_move_to_front a left right
    have hperm_rest : rest.Perm (left ++ right) :=
      List.Perm.cons_inv (hperm.trans hmid.symm)
    have hleft : ∀ x ∈ left, wsptRel a x := by
      intro x hx
      have hx' : x ∈ left ++ right := List.mem_append.mpr (Or.inl hx)
      exact ha x (hperm_rest.mem_iff.mpr hx')
    calc
      wctFrom s (a :: rest)
          = a.gain * (s + a.time) + wctFrom (s + a.time) rest := rfl
      _ ≤ a.gain * (s + a.time) + wctFrom (s + a.time) (left ++ right) :=
          Nat.add_le_add_left (ih (s + a.time) hrest hperm_rest) _
      _ = wctFrom s (a :: (left ++ right)) := rfl
      _ ≤ wctFrom s (left ++ a :: right) := move_to_front s a left right hleft

/-- Smith's rule, starting the clock at 0. -/
theorem wspt_minimizes_wct {L M : List Task} (hL : IsWSPT L) (hperm : L.Perm M) :
    wct L ≤ wct M :=
  wctFrom_le_of_wspt 0 hL hperm

/-- If two fixes take the same time, the one that saves `n` copied layers is weakly
    preferred to the one that saves a single layer. Uses `c ≤ n * c` (Daniel's Root
    Theorem) inside Smith's test. -/
theorem root_first_of_equal_time (c n t : ℕ) (ht : 0 < t) (hn : 1 ≤ n) :
    wsptRel ⟨n * c, t, ht⟩ ⟨c, t, ht⟩ ∧
      wct [⟨n * c, t, ht⟩, ⟨c, t, ht⟩] ≤ wct [⟨c, t, ht⟩, ⟨n * c, t, ht⟩] := by
  have hrel : wsptRel ⟨n * c, t, ht⟩ ⟨c, t, ht⟩ :=
    Nat.mul_le_mul_right t (Nat.le_mul_of_pos_left c hn)
  exact ⟨hrel, pick_max_ratio_first _ _ hrel⟩

/-! ## Amdahl: speed the largest-share stage of a serial pipeline. -/

namespace Amdahl

/-- New total time after speeding a stage of duration `t` by a factor `s`. -/
def newTime (T t s : ℚ) : ℚ := T - t + t / s

theorem newTime_rewrite (T t s : ℚ) (hs : s ≠ 0) :
    newTime T t s = T + t * (1 / s - 1) := by
  unfold newTime
  field_simp
  ring

theorem newTime_rewrite' (T t s : ℚ) (hs : s ≠ 0) :
    newTime T t s = T - t * (1 - 1 / s) := by
  unfold newTime
  field_simp
  ring

/-- For a fixed speedup factor `s > 1`, a larger stage duration yields a weakly
    smaller new total time. -/
theorem larger_stage_lower_time {T t₁ t₂ s : ℚ} (hs : 1 < s) (h : t₂ ≤ t₁) :
    newTime T t₁ s ≤ newTime T t₂ s := by
  have hs0 : s ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hneg : 1 / s - 1 < 0 := by
    rw [sub_lt_zero]
    exact (div_lt_one (lt_trans zero_lt_one hs)).mpr hs
  rw [newTime_rewrite _ _ _ hs0, newTime_rewrite _ _ _ hs0]
  have hmul := mul_le_mul_of_nonpos_right h hneg.le
  linarith

def speedup (T t s : ℚ) : ℚ := T / newTime T t s

theorem newTime_pos {T t s : ℚ} (hT : 0 < T) (_ht : 0 ≤ t) (hle : t ≤ T) (hs : 1 < s) :
    0 < newTime T t s := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hfac : 0 ≤ 1 - 1 / s := by
    rw [sub_nonneg]
    exact (div_le_one hs0).mpr hs.le
  have hle' : t * (1 - 1 / s) ≤ T * (1 - 1 / s) :=
    mul_le_mul_of_nonneg_right hle hfac
  have hfloor : T - T * (1 - 1 / s) = T / s := by
    field_simp
    ring
  have hpos : 0 < T / s := div_pos hT hs0
  have : T / s ≤ T - t * (1 - 1 / s) := by
    have : T - T * (1 - 1 / s) ≤ T - t * (1 - 1 / s) :=
      sub_le_sub_left hle' T
    rwa [hfloor] at this
  rw [newTime_rewrite' _ _ _ hsne]
  exact lt_of_lt_of_le hpos this

/-- For a fixed factor `s > 1`, speeding the larger stage yields a weakly higher
    overall speedup `T / T_new`. -/
theorem larger_stage_higher_speedup {T t₁ t₂ s : ℚ}
    (hT : 0 < T) (hs : 1 < s)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hle₁ : t₁ ≤ T) (hle₂ : t₂ ≤ T)
    (h : t₂ ≤ t₁) :
    speedup T t₂ s ≤ speedup T t₁ s := by
  have hp1 : 0 < newTime T t₁ s := newTime_pos hT ht₁ hle₁ hs
  have hp2 : 0 < newTime T t₂ s := newTime_pos hT ht₂ hle₂ hs
  have hNT : newTime T t₁ s ≤ newTime T t₂ s := larger_stage_lower_time hs h
  unfold speedup
  have hinv : (newTime T t₂ s)⁻¹ ≤ (newTime T t₁ s)⁻¹ := inv_anti₀ hp1 hNT
  have := mul_le_mul_of_nonneg_left hinv hT.le
  simpa [div_eq_mul_inv] using this

end Amdahl

/-! ## Theory of Constraints: throughput is the slowest stage. -/

namespace Bottleneck

/-- Raising a strictly non-bottleneck stage, without dropping it to or below the
    current minimum, leaves the minimum (the throughput of a serial chain) unchanged. -/
theorem nonbottleneck_no_gain {rates : List ℚ} {i : ℕ} {r' m : ℚ}
    (hi : i < rates.length) (hmin : rates.min? = some m)
    (hnot : m < rates[i]'hi) (hstill : m ≤ r') :
    (rates.set i r').min? = some m := by
  have hchar : m ∈ rates ∧ ∀ b, b ∈ rates → m ≤ b :=
    (List.min?_eq_some_iff (α := ℚ)).1 hmin
  have hm_kept : m ∈ rates.set i r' := by
    obtain ⟨j, hj, hjv⟩ := (List.mem_iff_getElem).1 hchar.1
    have hji : j ≠ i := by
      intro h
      subst h
      exact (ne_of_gt hnot) hjv
    refine (List.mem_iff_getElem).2 ⟨j, by simpa [List.length_set] using hj, ?_⟩
    rw [List.getElem_set_ne (Ne.symm hji)]
    exact hjv
  have hle : ∀ b, b ∈ rates.set i r' → m ≤ b := by
    intro b hb
    obtain ⟨j, hj, hjv⟩ := (List.mem_iff_getElem).1 hb
    have hj' : j < rates.length := by simpa [List.length_set] using hj
    by_cases hji : i = j
    · subst hji
      have hb' : b = r' := by
        have : (rates.set i r')[i] = r' := List.getElem_set_self _
        exact hjv.symm.trans this
      exact hb' ▸ hstill
    · have hb' : b = rates[j]'hj' := by
        have : (rates.set i r')[j] = rates[j]'hj' := List.getElem_set_ne hji _
        exact hjv.symm.trans this
      exact hchar.2 b (hb' ▸ List.getElem_mem hj')
  exact (List.min?_eq_some_iff (α := ℚ)).2 ⟨hm_kept, hle⟩

/-- Raising the unique slowest stage strictly raises the minimum, hence the
    throughput of the serial chain. -/
theorem elevate_unique_bottleneck {rates : List ℚ} {k : ℕ} {r' m : ℚ}
    (hk : k < rates.length) (_hmin : rates.min? = some m)
    (_hat : rates[k]'hk = m)
    (unique : ∀ j (hj : j < rates.length), j ≠ k → m < rates[j]'hj)
    (hup : m < r') :
    ∃ m', (rates.set k r').min? = some m' ∧ m < m' := by
  set rates' := rates.set k r'
  have hne : rates' ≠ [] := by
    have : rates ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hk)
    intro hempty
    have hlen : rates'.length = 0 := by simp [hempty]
    have : rates.length = 0 := by simpa [rates', List.length_set] using hlen
    omega
  have : rates'.min? ≠ none := by
    simp [List.min?_eq_none_iff, hne]
  obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp this
  refine ⟨m', hm', ?_⟩
  have hchar : m' ∈ rates' ∧ ∀ a, a ∈ rates' → m' ≤ a :=
    (List.min?_eq_some_iff (α := ℚ)).1 hm'
  have hgt : ∀ a, a ∈ rates' → m < a := by
    intro a ha
    obtain ⟨j, hj, hjv⟩ := (List.mem_iff_getElem).1 ha
    have hj' : j < rates.length := by simpa [rates', List.length_set] using hj
    by_cases hji : k = j
    · subst hji
      have : a = r' := by
        have : rates'[k] = r' := by
          simp [rates', List.getElem_set_self]
        exact hjv.symm.trans this
      exact this ▸ hup
    · have : a = rates[j]'hj' := by
        have : rates'[j] = rates[j]'hj' := by
          simp [rates', List.getElem_set_ne hji]
        exact hjv.symm.trans this
      exact this ▸ unique j hj' (Ne.symm hji)
  exact hgt m' hchar.1

end Bottleneck

/-! ## Discrete marginal value: stop a depleting line of work at the alternative rate. -/

namespace MarginalValue

/-- Net gain of taking the first `t` increments, each charged the alternative rate `alt`. -/
def net (δ : ℕ → ℚ) (alt : ℚ) (t : ℕ) : ℚ :=
  ∑ i ∈ Finset.range t, (δ i - alt)

def Nonincreasing (δ : ℕ → ℚ) : Prop :=
  Antitone δ

/-- Staying through any prefix of still-worthwhile increments never hurts. -/
theorem stay_while_above {δ : ℕ → ℚ} {alt : ℚ} {t u : ℕ}
    (hkeep : ∀ i, i < t → alt ≤ δ i) (hu : u ≤ t) :
    net δ alt u ≤ net δ alt t := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun i => δ i - alt) hu
  have hnn : 0 ≤ ∑ i ∈ Finset.Ico u t, (δ i - alt) := by
    apply Finset.sum_nonneg
    intro i hi
    have hiu : u ≤ i ∧ i < t := Finset.mem_Ico.mp hi
    linarith [hkeep i hiu.2]
  simp only [net]
  linarith

/-- Once increments have fallen to or below `alt`, further steps cannot raise the net. -/
theorem leave_when_below {δ : ℕ → ℚ} {alt : ℚ} {t u : ℕ}
    (hmono : Nonincreasing δ) (hdrop : δ t ≤ alt) (hu : t ≤ u) :
    net δ alt u ≤ net δ alt t := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun i => δ i - alt) hu
  have hnp : ∑ i ∈ Finset.Ico t u, (δ i - alt) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hit : t ≤ i := (Finset.mem_Ico.mp hi).1
    have : δ i ≤ δ t := hmono hit
    linarith
  simp only [net]
  linarith

/-- Discrete marginal-value rule: any threshold `t` that keeps exactly the increments
    still worth at least `alt` maximizes net gain. -/
theorem optimal_threshold {δ : ℕ → ℚ} {alt : ℚ} {t : ℕ}
    (hmono : Nonincreasing δ)
    (hkeep : ∀ i, i < t → alt ≤ δ i)
    (hdrop : ∀ i, t ≤ i → δ i ≤ alt) :
    ∀ u, net δ alt u ≤ net δ alt t := by
  intro u
  rcases le_total u t with hu | hu
  · exact stay_while_above hkeep hu
  · exact leave_when_below hmono (hdrop t le_rfl) hu

end MarginalValue

/-! ## Value of information: do not spend time on a check that cannot change the pick. -/

namespace ValueOfInfo

variable {State Act : Type} [Fintype State] [Fintype Act] [Nonempty Act]

def expectedU (u : Act → State → ℚ) (p : State → ℚ) (a : Act) : ℚ :=
  ∑ s : State, p s * u a s

def bestPrior (u : Act → State → ℚ) (p : State → ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (expectedU u p)

def euPerfect (u : Act → State → ℚ) (p : State → ℚ) : ℚ :=
  ∑ s : State, p s * (Finset.univ.sup' Finset.univ_nonempty (fun a => u a s))

def evpi (u : Act → State → ℚ) (p : State → ℚ) : ℚ :=
  euPerfect u p - bestPrior u p

/-- For nonnegative weights, the expected value of perfect information is nonnegative:
    `E[max_a u(a,s)] ≥ max_a E[u(a,s)]`. -/
theorem evpi_nonneg (u : Act → State → ℚ) (p : State → ℚ)
    (hp : ∀ s, 0 ≤ p s) : 0 ≤ evpi u p := by
  unfold evpi euPerfect bestPrior
  obtain ⟨a0, -, ha0⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset Act))
      (H := Finset.univ_nonempty) (expectedU u p)
  have hle : expectedU u p a0 ≤
      ∑ s : State, p s * (Finset.univ.sup' Finset.univ_nonempty (fun a => u a s)) := by
    unfold expectedU
    apply Finset.sum_le_sum
    intro s _
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun a => u a s) (Finset.mem_univ a0)) (hp s)
  rw [ha0]
  linarith

/-- If one action is best in every state, perfect information cannot change the pick,
    so the expected value of that information is zero. -/
theorem evpi_zero_of_same_action (u : Act → State → ℚ) (p : State → ℚ)
    (aStar : Act) (hp : ∀ s, 0 ≤ p s)
    (hstate : ∀ s a, u a s ≤ u aStar s) :
    evpi u p = 0 := by
  have hsups : ∀ s, Finset.univ.sup' Finset.univ_nonempty (fun a => u a s) = u aStar s := by
    intro s
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun a _ => hstate s a)
    · exact Finset.le_sup' (fun a => u a s) (Finset.mem_univ aStar)
  have hprior : bestPrior u p = expectedU u p aStar := by
    unfold bestPrior
    apply le_antisymm
    · apply Finset.sup'_le
      intro a _
      unfold expectedU
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hstate s a) (hp s)
    · exact Finset.le_sup' (expectedU u p) (Finset.mem_univ aStar)
  unfold evpi euPerfect
  rw [hprior]
  simp [hsups, expectedU]

end ValueOfInfo

end RootPick
