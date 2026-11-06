import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL288
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P R Q : State → Prop) (c : Cmd), Hoare P c Q → Hoare R c Q → Hoare (fun s => P s ∨ R s) c Q := by
  exact hoare_disjunction

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Hoare (fun s => s 0 = 0 ∨ s 0 = 1) .skip (fun s => s 0 ≤ 1) := by
  intro s t h he; cases he; rcases h with h | h <;> omega

end JonnyLean.Contracts.JL288

#print axioms JonnyLean.Imperative.hoare_disjunction
#print axioms JonnyLean.Contracts.JL288.contract
