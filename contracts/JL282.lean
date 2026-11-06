import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL282
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (Q : State → Prop) (x : Nat) (e : AExp), ∀ s t, Q (update s x (AExp.eval s e)) → Exec (.assign x e) s t → Q t := by
  exact hoare_assign

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Hoare (fun s => s 0 + 1 = 5) (.assign 0 (.add (.var 0) (.lit 1))) (fun s => s 0 = 5) := by
  intro s t h he; cases he; simpa [AExp.eval] using h

end JonnyLean.Contracts.JL282

#print axioms JonnyLean.Imperative.hoare_assign
#print axioms JonnyLean.Contracts.JL282.contract
