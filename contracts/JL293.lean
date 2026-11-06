import JonnyLean.Imperative.Examples

namespace JonnyLean.Contracts.JL293
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (x : Nat) (s : State), Exec (countdown x) s (update s x 0) ∧ ∀ t, Exec (countdown x) s t → t = update s x 0 := by
  exact countdown_correct

theorem definition_check : ∀ (x : Nat), countdown x = .while (.le (.lit 1) (.var x)) (.assign x (.sub (.var x) (.lit 1))) := by
  intro x; rfl

theorem boundary_check : (run 7 (countdown 0) (fun _ => 5)).map (fun t => (t 0,t 1)) = some (0,5) := by
  rfl

end JonnyLean.Contracts.JL293

#print axioms JonnyLean.Imperative.countdown_correct
#print axioms JonnyLean.Contracts.JL293.contract
