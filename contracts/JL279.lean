import JonnyLean.Imperative.Interpreter

namespace JonnyLean.Contracts.JL279
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd) (s t : State), Exec c s t ↔ ∃ n, run n c s = some t := by
  exact exec_iff_run

theorem definition_check : ∀ (c : Cmd) (s : State), run 0 c s = none := by
  intro c s; rfl

theorem boundary_check : run 0 .skip (fun _ => 0) = none := by
  rfl

end JonnyLean.Contracts.JL279

#print axioms JonnyLean.Imperative.exec_iff_run
#print axioms JonnyLean.Contracts.JL279.contract
