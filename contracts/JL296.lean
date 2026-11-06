import JonnyLean.Imperative.Equivalence

namespace JonnyLean.Contracts.JL296
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (c : Cmd), (∀ s t, Exec (.seq .skip c) s t ↔ Exec c s t) ∧ (∀ s t, Exec (.seq c .skip) s t ↔ Exec c s t) := by
  exact sequence_identities

theorem definition_check : ∀ (c d : Cmd), Equivalent c d ↔ ∀ s t, Exec c s t ↔ Exec d s t := by
  intro c d; rfl

theorem boundary_check : run 1 (.seq .skip .skip) (fun _ => 0) = none := by
  rfl

end JonnyLean.Contracts.JL296

#print axioms JonnyLean.Imperative.sequence_identities
#print axioms JonnyLean.Contracts.JL296.contract
