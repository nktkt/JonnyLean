import JonnyLean.Imperative.Examples

namespace JonnyLean.Contracts.JL291
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (x : Nat) (s : State), ∃ t, Exec (increment x) s t ∧ t x = s x + 1 ∧ ∀ y, y ≠ x → t y = s y := by
  exact increment_correct

theorem definition_check : ∀ (x : Nat), countdown x = .while (.le (.lit 1) (.var x)) (.assign x (.sub (.var x) (.lit 1))) := by
  intro x; rfl

theorem boundary_check : (run 1 (increment 0) (fun _ => 0)).map (fun t => t 0) = some 1 := by
  rfl

end JonnyLean.Contracts.JL291

#print axioms JonnyLean.Imperative.increment_correct
#print axioms JonnyLean.Contracts.JL291.contract
