/-!
# The HHH stamp: a claim carries it only if it passed the checker

Daniel's pick, 2026-10-28 20:55 CT: "Let's start at the bottom. Write the Lean proof that a claim can only carry the HHH stamp
if it passed the checker, make sure a planted fake gets refused, then build it and show me the receipt."

The claims here are exact arithmetic, the same kind CHECK AN ANSWER's math gate checks ("17 * 23 = 391"). The checker is
`check`; a `Stamp` is a claim together with Lean's proof that `check` passed it. There is no other way to make one.

* `HHHStamp.stamp_means_true`: every stamped claim is true (its two sides are equal).
* `HHHStamp.no_stamp_if_failed`: a claim the checker fails can carry no stamp at all.
* `HHHStamp.planted_fake_refused`: the planted fake "17 * 23 = 392" can carry no stamp; the real "17 * 23 = 391" carries one.

What this does not prove: that the Python checker in vibe-lab/app/gate.py matches `check`. This is the stamp rule, proven for a
checker written in Lean. Core Lean only, no Mathlib.
-/

namespace HHHStamp

/-- A whole-number arithmetic expression. -/
inductive Expr where
  | num : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → Nat → Expr

/-- Its exact value. -/
def Expr.eval : Expr → Nat
  | .num n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .pow a k => a.eval ^ k

/-- A claim "left = right". -/
structure Claim where
  left : Expr
  right : Expr

/-- The checker: exact, no rounding. -/
def check (c : Claim) : Bool := decide (c.left.eval = c.right.eval)

/-- The HHH stamp: a claim and the proof that the checker passed it. -/
structure Stamp where
  claim : Claim
  passed : check claim = true

/-- A stamp means the checker passed the claim. -/
theorem stamp_means_checked (s : Stamp) : check s.claim = true := s.passed

/-- A stamped claim is true. -/
theorem stamp_means_true (s : Stamp) : s.claim.left.eval = s.claim.right.eval :=
  of_decide_eq_true s.passed

/-- A claim the checker fails carries no stamp. -/
theorem no_stamp_if_failed (c : Claim) (failed : check c = false) : ¬ ∃ s : Stamp, s.claim = c := by
  intro ⟨s, hs⟩
  subst hs
  rw [s.passed] at failed
  exact Bool.noConfusion failed

/-- The planted fake: 17 * 23 = 392 (the true product is 391). -/
def plantedFake : Claim := ⟨.mul (.num 17) (.num 23), .num 392⟩

/-- The real claim: 17 * 23 = 391. -/
def realClaim : Claim := ⟨.mul (.num 17) (.num 23), .num 391⟩

/-- The planted fake is refused: no stamp can carry it. -/
theorem planted_fake_refused : ¬ ∃ s : Stamp, s.claim = plantedFake :=
  no_stamp_if_failed plantedFake (by decide)

/-- The real claim earns a stamp. -/
def realStamp : Stamp := ⟨realClaim, by decide⟩

end HHHStamp

/-- The HHH stamp rule, together: every stamped claim is true, a failed claim carries no stamp, and the planted fake is
refused while the real claim is stamped. -/
theorem HHHStampRule :
    (∀ s : HHHStamp.Stamp, s.claim.left.eval = s.claim.right.eval) ∧
    (∀ c : HHHStamp.Claim, HHHStamp.check c = false → ¬ ∃ s : HHHStamp.Stamp, s.claim = c) ∧
    (¬ ∃ s : HHHStamp.Stamp, s.claim = HHHStamp.plantedFake) ∧
    HHHStamp.realStamp.claim = HHHStamp.realClaim :=
  ⟨HHHStamp.stamp_means_true, HHHStamp.no_stamp_if_failed, HHHStamp.planted_fake_refused, rfl⟩
