import JonnyLean.Imperative.Examples

namespace JonnyLean.Contracts.JL292
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (x y tmp : Nat), x ≠ y → x ≠ tmp → y ≠ tmp → ∀ (s : State), ∃ t, Exec (swap x y tmp) s t ∧ t x = s y ∧ t y = s x ∧ ∀ z, z ∉ [x,y,tmp] → t z = s z := by
  exact swap_correct

theorem definition_check : ∀ (x : Nat), countdown x = .while (.le (.lit 1) (.var x)) (.assign x (.sub (.var x) (.lit 1))) := by
  intro x; rfl

theorem boundary_check : (run 3 (swap 0 1 2) (fun n => n + 4)).map (fun t => (t 0, t 1, t 2, t 3)) = some (5,4,4,7) := by
  rfl

end JonnyLean.Contracts.JL292

#print axioms JonnyLean.Imperative.swap_correct
#print axioms JonnyLean.Contracts.JL292.contract
