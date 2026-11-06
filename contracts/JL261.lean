import JonnyLean.Imperative.State

namespace JonnyLean.Contracts.JL261
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (s : Nat → Nat) (x a b : Nat), update (update s x a) x b = update s x b := by
  exact update_shadow

theorem definition_check : ∀ (s : State) (x n y : Nat), update s x n y = if y = x then n else s y := by
  intro s x n y; rfl

theorem boundary_check : update (update (fun _ => 7) 0 2) 0 9 1 = 7 := by
  rfl

end JonnyLean.Contracts.JL261

#print axioms JonnyLean.Imperative.update_shadow
#print axioms JonnyLean.Contracts.JL261.contract
