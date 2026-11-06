import JonnyLean.Imperative.Interpreter

namespace JonnyLean.Contracts.JL277
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd) (s t : State), Exec c s t → ∃ n, run n c s = some t := by
  intro c s t h
  exact run_complete h

theorem definition_check : ∀ (c : Cmd) (s : State), run 0 c s = none := by
  intro c s; rfl

theorem boundary_check : run 1 .skip (fun _ => 9) = some (fun _ => 9) := by
  rfl

end JonnyLean.Contracts.JL277

#print axioms JonnyLean.Imperative.run_complete
#print axioms JonnyLean.Contracts.JL277.contract
