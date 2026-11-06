import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL290
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P Q : State → Prop) (c : Cmd), Hoare P c Q ↔ ∀ s, P s → ∀ t, Exec c s t → Q t := by
  exact hoare_iff_wlp

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : wlp .skip (fun s => s 0 = 0) (fun _ => 0) := by
  intro t h; cases h; rfl

end JonnyLean.Contracts.JL290

#print axioms JonnyLean.Imperative.hoare_iff_wlp
#print axioms JonnyLean.Contracts.JL290.contract
