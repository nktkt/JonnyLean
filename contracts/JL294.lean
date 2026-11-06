import JonnyLean.Imperative.Examples

namespace JonnyLean.Contracts.JL294
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (x y : Nat), x ≠ y → ∀ (s : State), ∃ t, Exec (transfer x y) s t ∧ t x = 0 ∧ t y = s y + s x ∧ ∀ z, z ≠ x → z ≠ y → t z = s z := by
  exact transfer_correct

theorem definition_check : ∀ (x : Nat), countdown x = .while (.le (.lit 1) (.var x)) (.assign x (.sub (.var x) (.lit 1))) := by
  intro x; rfl

theorem boundary_check : (run 8 (transfer 0 1) (fun n => if n = 0 then 3 else 10)).map (fun t => (t 0,t 1,t 2)) = some (0,13,10) := by
  rfl

end JonnyLean.Contracts.JL294

#print axioms JonnyLean.Imperative.transfer_correct
#print axioms JonnyLean.Contracts.JL294.contract
