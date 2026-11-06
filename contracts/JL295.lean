import JonnyLean.Imperative.Examples

namespace JonnyLean.Contracts.JL295
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (x y : Nat), x ≠ y → ∀ (s : State), ∃ t, Exec (accumulate x y) s t ∧ t x = 0 ∧ 2 * t y = 2 * s y + s x * (s x + 1) := by
  exact accumulate_correct

theorem definition_check : ∀ (x : Nat), countdown x = .while (.le (.lit 1) (.var x)) (.assign x (.sub (.var x) (.lit 1))) := by
  intro x; rfl

theorem boundary_check : (run 10 (accumulate 0 1) (fun n => if n = 0 then 4 else 2)).map (fun t => (t 0,t 1)) = some (0,12) := by
  rfl

end JonnyLean.Contracts.JL295

#print axioms JonnyLean.Imperative.accumulate_correct
#print axioms JonnyLean.Contracts.JL295.contract
