import Mathlib

/-!
# Daniel's Founder's Claim

Credit: Daniel Steadham, 2026-10-29. His sentence: "the stack of proven facts grows faster than the cost of finding each new one".

Week by week, `facts n` is the size of the stack of proven facts after week `n`, and `cost n` is the cost of finding a new one
that week, both on one scale. The lead is `facts n - cost n`.

* `FounderClaim.lead_never_shrinks`: if every week the stack grows at least as much as the cost grows, the lead in any later
  week is at least the lead in any earlier week.
* `FounderClaim.lead_grows`: if every week the stack grows strictly more than the cost, the lead in a later week is strictly
  bigger.

Assumptions, stated plainly: the two are compared on one scale (the model does not say which; the weekly counts choose it), weeks
are whole steps, and the claim is only about weeks where the hypothesis held. Whether it holds in real weeks is a measured
question, not a Lean one.
-/

namespace FounderClaim

/-- If the stack grows at least as fast as the cost every week, the lead never shrinks. -/
theorem lead_never_shrinks (facts cost : ℕ → ℝ) (faster : ∀ n, cost (n + 1) - cost n ≤ facts (n + 1) - facts n)
    {m n : ℕ} (later : m ≤ n) : facts m - cost m ≤ facts n - cost n :=
  monotone_nat_of_le_succ (f := fun k => facts k - cost k) (fun k => by linarith [faster k]) later

/-- If the stack grows strictly faster than the cost every week, the lead strictly grows. -/
theorem lead_grows (facts cost : ℕ → ℝ) (faster : ∀ n, cost (n + 1) - cost n < facts (n + 1) - facts n)
    {m n : ℕ} (later : m < n) : facts m - cost m < facts n - cost n :=
  strictMono_nat_of_lt_succ (f := fun k => facts k - cost k) (fun k => by linarith [faster k]) later

end FounderClaim

/-- Daniel's Founder's Claim, both parts together. -/
theorem DanielFounderClaim (facts cost : ℕ → ℝ) :
    ((∀ n, cost (n + 1) - cost n ≤ facts (n + 1) - facts n) → Monotone (fun n => facts n - cost n)) ∧
    ((∀ n, cost (n + 1) - cost n < facts (n + 1) - facts n) → StrictMono (fun n => facts n - cost n)) :=
  ⟨fun h _ _ hmn => FounderClaim.lead_never_shrinks facts cost h hmn, fun h _ _ hmn => FounderClaim.lead_grows facts cost h hmn⟩

