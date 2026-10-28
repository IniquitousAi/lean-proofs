/-
Daniel's HHH stamp rule, in Lean (his pick 2026-10-28 01:37): a claim only carries the HHH stamp if it passed the checker,
so anything with the stamp is proven; and a planted claim that skipped the checker is refused.

Plain Lean, no libraries: `lean stamp/StampRule.lean`. The checker is the five checks of vibe-lab/tools/hhh_stamp.py, each a
yes or no the stamp tool works out (in the bank with an exact answer, a theorem saying exactly that, sources committed, no
unfinished step, only the three standard axioms). This file proves the rule about stamps; the five yes-or-no answers
themselves come from running the tool, which RERUN re-checks.
-/

/-- What the checker learned about one claim: the five checks, each passed or not. -/
structure Checks where
  inBank        : Bool   -- the claim is in the answer bank and its answer is an exact number
  statedExactly : Bool   -- a Lean theorem states exactly that answer
  committed     : Bool   -- the Lean sources are saved in the shared record
  noShortcuts   : Bool   -- no `sorry`, `admit` or `native_decide`
  standardOnly  : Bool   -- it rests only on propext, Classical.choice and Quot.sound
  deriving DecidableEq, Repr

/-- The checker passes a claim only when all five checks pass. -/
def passes (c : Checks) : Bool :=
  c.inBank && c.statedExactly && c.committed && c.noShortcuts && c.standardOnly

/-- A stamp can only be made together with the checker's pass: there is no other way to build one. -/
structure Stamp where
  claim : Checks
  passed : passes claim = true

/-- **The stamp rule.** Anything carrying the stamp passed every one of the five checks. -/
theorem stamp_means_proven (s : Stamp) :
    s.claim.inBank = true ∧ s.claim.statedExactly = true ∧ s.claim.committed = true ∧
    s.claim.noShortcuts = true ∧ s.claim.standardOnly = true := by
  have h := s.passed
  simp only [passes, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **No stamp without the checker.** A claim the checker does not pass can never carry the stamp. -/
theorem no_stamp_without_pass (c : Checks) (h : passes c = false) : ¬ ∃ s : Stamp, s.claim = c := by
  intro ⟨s, hs⟩
  have := s.passed
  rw [hs, h] at this
  exact Bool.false_ne_true this

/-- The planted claim: it is in the bank and its theorem says the answer, but it skipped the build check (`sorry` left in). -/
def planted : Checks :=
  { inBank := true, statedExactly := true, committed := true, noShortcuts := false, standardOnly := true }

/-- **The planted claim is refused.** -/
theorem planted_is_refused : ¬ ∃ s : Stamp, s.claim = planted :=
  no_stamp_without_pass planted (by decide)

/-- A claim that passes everything does get a stamp (the rule is not "never stamp"). -/
def honest : Checks := { inBank := true, statedExactly := true, committed := true, noShortcuts := true, standardOnly := true }

theorem honest_is_stamped : ∃ s : Stamp, s.claim = honest := ⟨⟨honest, by decide⟩, rfl⟩

#print axioms stamp_means_proven
#print axioms no_stamp_without_pass
#print axioms planted_is_refused
#print axioms honest_is_stamped
