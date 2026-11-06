import JonnyLean.Imperative.Interpreter

namespace JonnyLean.Contracts.JL276
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (n : Nat) (c : Cmd) (s t : State), run n c s = some t → Exec c s t := by
  exact run_sound

theorem definition_check : ∀ (c : Cmd) (s : State), run 0 c s = none := by
  intro c s; rfl

theorem boundary_check : (run 2 (.seq (.assign 0 (.lit 7)) .skip) (fun _ => 0)).map (fun t => t 0) = some 7 := by
  rfl

end JonnyLean.Contracts.JL276

#print axioms JonnyLean.Imperative.run_sound
#print axioms JonnyLean.Contracts.JL276.contract
