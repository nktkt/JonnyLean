import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL284
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P Q : State → Prop) (b : BExp) (c d : Cmd), Hoare (fun s => P s ∧ b.eval s = true) c Q → Hoare (fun s => P s ∧ b.eval s = false) d Q → Hoare P (.ite b c d) Q := by
  exact hoare_if

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Exec (.ite (.truth false) (.assign 0 (.lit 1)) .skip) (fun _ => 0) (fun _ => 0) := by
  exact .ifFalse rfl (.skip _)

end JonnyLean.Contracts.JL284

#print axioms JonnyLean.Imperative.hoare_if
#print axioms JonnyLean.Contracts.JL284.contract
