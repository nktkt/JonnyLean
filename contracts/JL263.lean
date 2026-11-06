import JonnyLean.Imperative.State

namespace JonnyLean.Contracts.JL263
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (s : Nat → Nat) (x : Nat), update s x (s x) = s := by
  exact update_same

theorem definition_check : ∀ (s : State) (x n y : Nat), update s x n y = if y = x then n else s y := by
  intro s x n y; rfl

theorem boundary_check : update (fun n => n + 3) 0 3 4 = 7 := by
  rfl

end JonnyLean.Contracts.JL263

#print axioms JonnyLean.Imperative.update_same
#print axioms JonnyLean.Contracts.JL263.contract
