import JonnyLean.Imperative.Equivalence

namespace JonnyLean.Contracts.JL300
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd), ∀ s t, Exec c s t ↔ Exec (optimize c) s t := by
  exact optimize_correct

theorem definition_check : ∀ (c d : Cmd), Equivalent c d ↔ ∀ s t, Exec c s t ↔ Exec d s t := by
  intro c d; rfl

theorem boundary_check : optimize (.seq .skip (.ite (.truth true) (.seq .skip (.assign 0 (.lit 4))) (.while (.truth true) .skip))) = .assign 0 (.lit 4) := by
  rfl

end JonnyLean.Contracts.JL300

#print axioms JonnyLean.Imperative.optimize_correct
#print axioms JonnyLean.Contracts.JL300.contract
