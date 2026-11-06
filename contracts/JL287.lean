import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL287
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P Q R : State → Prop) (c : Cmd), Hoare P c Q → Hoare P c R → Hoare P c (fun s => Q s ∧ R s) := by
  exact hoare_conjunction

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Hoare (fun _ => True) .skip (fun _ => True ∧ True) := by
  intro s t _ _; exact ⟨True.intro, True.intro⟩

end JonnyLean.Contracts.JL287

#print axioms JonnyLean.Imperative.hoare_conjunction
#print axioms JonnyLean.Contracts.JL287.contract
