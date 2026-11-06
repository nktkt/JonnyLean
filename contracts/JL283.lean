import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL283
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P R Q : State → Prop) (c d : Cmd), Hoare P c R → Hoare R d Q → Hoare P (.seq c d) Q := by
  exact hoare_seq

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : Hoare (fun s => s 0 = 2) (.seq .skip .skip) (fun s => s 0 = 2) := by
  exact hoare_seq _ _ _ _ _ (hoare_skip _) (hoare_skip _)

end JonnyLean.Contracts.JL283

#print axioms JonnyLean.Imperative.hoare_seq
#print axioms JonnyLean.Contracts.JL283.contract
