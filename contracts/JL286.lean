import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL286
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P P' Q Q' : State → Prop) (c : Cmd), (∀ s, P' s → P s) → (∀ s, Q s → Q' s) → Hoare P c Q → Hoare P' c Q' := by
  exact hoare_consequence

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Hoare (fun s => s 0 = 0) .skip (fun s => s 0 ≤ 1) := by
  intro s t h he; cases he; omega

end JonnyLean.Contracts.JL286

#print axioms JonnyLean.Imperative.hoare_consequence
#print axioms JonnyLean.Contracts.JL286.contract
