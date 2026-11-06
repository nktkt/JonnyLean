import JonnyLean.Imperative.Divergence

namespace JonnyLean.Contracts.JL275
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (s t : State), ¬ Exec (.while (.truth true) .skip) s t := by
  exact spin_diverges

theorem definition_check : spin = .while (.truth true) .skip := by
  rfl

theorem boundary_check : run 20 (.while (.truth true) .skip) (fun _ => 0) = none := by
  rfl

end JonnyLean.Contracts.JL275

#print axioms JonnyLean.Imperative.spin_diverges
#print axioms JonnyLean.Contracts.JL275.contract
