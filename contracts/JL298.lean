import JonnyLean.Imperative.Equivalence

namespace JonnyLean.Contracts.JL298
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd), ∀ s t, Exec (.while (.truth false) c) s t ↔ Exec .skip s t := by
  exact false_loop

theorem definition_check : ∀ (c d : Cmd), Equivalent c d ↔ ∀ s t, Exec c s t ↔ Exec d s t := by
  intro c d; rfl

theorem boundary_check : run 1 (.while (.truth false) (.while (.truth true) .skip)) (fun _ => 7) = some (fun _ => 7) := by
  rfl

end JonnyLean.Contracts.JL298

#print axioms JonnyLean.Imperative.false_loop
#print axioms JonnyLean.Contracts.JL298.contract
