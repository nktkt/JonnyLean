import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL281
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P : State → Prop), ∀ s t, P s → Exec .skip s t → P t := by
  exact hoare_skip

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Hoare (fun s => s 0 = 4) .skip (fun s => s 0 = 4) := by
  exact hoare_skip _

end JonnyLean.Contracts.JL281

#print axioms JonnyLean.Imperative.hoare_skip
#print axioms JonnyLean.Contracts.JL281.contract
