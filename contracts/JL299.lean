import JonnyLean.Imperative.Equivalence

namespace JonnyLean.Contracts.JL299
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (x : Nat) (a b : AExp), ∀ s t, Exec (.seq (.assign x a) (.assign x b)) s t ↔ Exec (.assign x (AExp.subst x a b)) s t := by
  exact assignment_fusion

theorem definition_check : ∀ (c d : Cmd), Equivalent c d ↔ ∀ s t, Exec c s t ↔ Exec d s t := by
  intro c d; rfl

theorem boundary_check : (run 2 (.seq (.assign 0 (.lit 3)) (.assign 0 (.add (.var 0) (.lit 2)))) (fun _ => 0)).map (fun t => t 0) = some 5 := by
  rfl

end JonnyLean.Contracts.JL299

#print axioms JonnyLean.Imperative.assignment_fusion
#print axioms JonnyLean.Contracts.JL299.contract
