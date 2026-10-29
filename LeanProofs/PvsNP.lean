/-
P vs NP, piece 1 (ORD-1029-CR, angle 1 in inbox/hhh/PVSNP_ANGLES.md): checking a proposed answer is easy.
A SAT formula in CNF is a list of clauses, each a list of literals (a variable and its sign). Given an assignment of
true/false to every variable, `evalCNF` says whether the formula is satisfied. Two facts, machine-checked:
  * it is right: true exactly when every clause has a true literal (`evalCNF_correct`);
  * it is fast: the counted checker takes at most size f + 1 steps, where size f is the number of literals plus the
    number of clauses, and it gives the same answer (`cnfCost_value`, `cnfCost_le`).
This is the "verifier runs in polynomial (here linear) time" half of the definition of NP. It does not touch the open
question; it is a known fact, now checked by Lean's kernel. Core Lean only, no Mathlib.
-/
namespace PvsNP

abbrev Lit := Nat × Bool       -- a variable and its polarity (true = the variable itself, false = its negation)
abbrev Clause := List Lit
abbrev CNF := List Clause

def evalLit (a : Nat → Bool) (l : Lit) : Bool := if l.2 then a l.1 else !(a l.1)
def evalClause (a : Nat → Bool) (c : Clause) : Bool := c.any (evalLit a)
def evalCNF (a : Nat → Bool) (f : CNF) : Bool := f.all (evalClause a)

theorem evalCNF_correct (a : Nat → Bool) (f : CNF) :
    evalCNF a f = true ↔ ∀ c ∈ f, ∃ l ∈ c, evalLit a l = true := by
  simp [evalCNF, evalClause, List.all_eq_true, List.any_eq_true]

/-- The checker with a step counter: one step per literal looked at; it stops at the first true literal. -/
def clauseCost (a : Nat → Bool) : Clause → Nat × Bool
  | [] => (0, false)
  | l :: ls => if evalLit a l then (1, true) else ((clauseCost a ls).1 + 1, (clauseCost a ls).2)

/-- One step per clause entered, plus one to finish; it stops at the first false clause. -/
def cnfCost (a : Nat → Bool) : CNF → Nat × Bool
  | [] => (1, true)
  | c :: cs => if (clauseCost a c).2 then ((clauseCost a c).1 + 1 + (cnfCost a cs).1, (cnfCost a cs).2)
               else ((clauseCost a c).1 + 1, false)

/-- The size of a formula: every literal and every clause counted once. -/
def size : CNF → Nat
  | [] => 0
  | c :: cs => c.length + 1 + size cs

theorem clauseCost_value (a : Nat → Bool) (c : Clause) : (clauseCost a c).2 = evalClause a c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    unfold clauseCost evalClause
    by_cases h : evalLit a l = true
    · simp [h]
    · simp only [h, List.any_cons, Bool.false_or]
      simpa [evalClause] using ih

theorem clauseCost_le (a : Nat → Bool) (c : Clause) : (clauseCost a c).1 ≤ c.length := by
  induction c with
  | nil => simp [clauseCost]
  | cons l ls ih =>
    unfold clauseCost
    by_cases h : evalLit a l = true
    · simp [h]
    · simp only [h, ite_false, Bool.false_eq_true, List.length_cons]
      omega

theorem cnfCost_value (a : Nat → Bool) (f : CNF) : (cnfCost a f).2 = evalCNF a f := by
  induction f with
  | nil => rfl
  | cons c cs ih =>
    unfold cnfCost evalCNF
    have hv := clauseCost_value a c
    by_cases h : (clauseCost a c).2 = true
    · have hc : evalClause a c = true := hv ▸ h
      simp only [h, ite_true, List.all_cons, hc, Bool.true_and]
      simpa [evalCNF] using ih
    · have hc : evalClause a c = false := by rw [← hv]; simpa using h
      simp [h, hc]

theorem cnfCost_le (a : Nat → Bool) (f : CNF) : (cnfCost a f).1 ≤ size f + 1 := by
  induction f with
  | nil => simp [cnfCost, size]
  | cons c cs ih =>
    have hc := clauseCost_le a c
    unfold cnfCost size
    by_cases h : (clauseCost a c).2 = true
    · simp only [h, ite_true]; omega
    · simp only [h, ite_false, Bool.false_eq_true]; omega

/-- The headline: the checker is right and takes at most size f + 1 steps, for every formula and every assignment. -/
theorem sat_check_is_fast_and_right (a : Nat → Bool) (f : CNF) :
    ((cnfCost a f).2 = true ↔ ∀ c ∈ f, ∃ l ∈ c, evalLit a l = true) ∧ (cnfCost a f).1 ≤ size f + 1 := by
  exact ⟨by rw [cnfCost_value]; exact evalCNF_correct a f, cnfCost_le a f⟩

end PvsNP
