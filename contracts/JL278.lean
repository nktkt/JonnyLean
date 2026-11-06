import JonnyLean.Imperative.Interpreter

namespace JonnyLean.Contracts.JL278
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (n m : Nat), n ≤ m → ∀ (c : Cmd) (s t : State), run n c s = some t → run m c s = some t := by
  exact run_mono

theorem definition_check : ∀ (c : Cmd) (s : State), run 0 c s = none := by
  intro c s; rfl

theorem boundary_check : (run 10 (.assign 0 (.lit 3)) (fun _ => 0)).map (fun t => t 0) = some 3 := by
  rfl

end JonnyLean.Contracts.JL278

#print axioms JonnyLean.Imperative.run_mono
#print axioms JonnyLean.Contracts.JL278.contract
