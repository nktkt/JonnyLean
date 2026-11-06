import JonnyLean.Imperative.Equivalence

namespace JonnyLean.Contracts.JL297
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (b : Bool) (c d : Cmd), ∀ s t, Exec (.ite (.truth b) c d) s t ↔ Exec (if b then c else d) s t := by
  exact constant_branch

theorem definition_check : ∀ (c d : Cmd), Equivalent c d ↔ ∀ s t, Exec c s t ↔ Exec d s t := by
  intro c d; rfl

theorem boundary_check : Exec (.ite (.truth true) .skip (.while (.truth true) .skip)) (fun _ => 0) (fun _ => 0) := by
  exact .ifTrue rfl (.skip _)

end JonnyLean.Contracts.JL297

#print axioms JonnyLean.Imperative.constant_branch
#print axioms JonnyLean.Contracts.JL297.contract
