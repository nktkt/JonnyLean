import JonnyLean.Imperative.Hoare

namespace JonnyLean.Contracts.JL289
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (P Q R : State → Prop) (c : Cmd) (xs : List Nat), Hoare P c Q → (∀ s t, (∀ x ∈ xs, s x = t x) → (R s ↔ R t)) → (∀ x ∈ xs, x ∉ c.writes) → Hoare (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) := by
  exact hoare_frame

theorem definition_check : ∀ (P Q : Assertion) (c : Cmd), Hoare P c Q ↔ ∀ s t, P s → Exec c s t → Q t := by
  intro P Q c; rfl

theorem boundary_check : DependsOn [0] (fun s => s 0 = 2) := by
  intro s t h
  change s 0 = 2 ↔ t 0 = 2
  rw [h 0 (by simp)]

end JonnyLean.Contracts.JL289

#print axioms JonnyLean.Imperative.hoare_frame
#print axioms JonnyLean.Contracts.JL289.contract
