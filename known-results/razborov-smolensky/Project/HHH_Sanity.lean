import Project.HHH_Final

/-! HHH Round 8 sanity: the circuit model is not empty. An explicit depth-1 AC0[3]
circuit (one NOT gate) computes MOD_2 on 0 + (2-1) = 1 input. -/

namespace HHH

open ACP

/-- One NOT gate on one input. All layers have type `Fin 1`. -/
def notCircuit : FeedForward (Fin 2) (Fin 1) (Fin 1) where
  depth := 1
  nodes := fun _ => Fin 1
  gates := fun _ _ => ⟨⟨Fin 1, fun x => 1 - x 0⟩, id⟩
  nodes_zero := rfl
  nodes_last := rfl

instance : ∀ i, Finite (notCircuit.nodes i) := fun _ => inferInstanceAs (Finite (Fin 1))

theorem notCircuit_uses : notCircuit.onlyUsesGates (ACp_GateOps 3) := by
  intro d u
  left; left
  simp [notCircuit]

theorem notCircuit_computes : ∀ x : Fin (0 + (2 - 1)) → Fin 2,
    notCircuit.eval₁ x = (modGateOp 2 (0 + (2 - 1))).func x := by
  decide

theorem notCircuit_size : notCircuit.size = 1 := by
  simp [FeedForward.size, notCircuit, Nat.card_eq_fintype_card]

end HHH
