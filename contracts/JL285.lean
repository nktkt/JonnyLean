import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL285
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (I : State → Prop) (b : BExp) (c : Cmd), Hoare (fun s => I s ∧ b.eval s = true) c I → Hoare I (.while b c) (fun s => I s ∧ b.eval s = false) := by
  exact hoare_while

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Hoare (fun _ => True) (.while (.truth false) .skip) (fun s => True ∧ BExp.eval s (.truth false) = false) := by
  apply hoare_while
  intro s t h _
  exact h.1

end JonnyLean.Contracts.JL285

#print axioms JonnyLean.Imperative.hoare_while
#print axioms JonnyLean.Contracts.JL285.contract
