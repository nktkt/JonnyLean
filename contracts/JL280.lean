import JonnyLean.Imperative.Interpreter

namespace JonnyLean.Contracts.JL280
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd) (s t u : State) (n m : Nat), run n c s = some t → run m c s = some u → t = u := by
  exact run_fuel_unique

theorem definition_check : ∀ (c : Cmd) (s : State), run 0 c s = none := by
  intro c s; rfl

theorem boundary_check : (run 1 (.assign 2 (.lit 8)) (fun _ => 0)).map (fun t => t 2) = some 8 := by
  rfl

end JonnyLean.Contracts.JL280

#print axioms JonnyLean.Imperative.run_fuel_unique
#print axioms JonnyLean.Contracts.JL280.contract
