import JonnyLean.Imperative.State

namespace JonnyLean.Contracts.JL264
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (xs : List Nat) (s t : Nat → Nat) (x n : Nat), (∀ y ∈ xs, s y = t y) → ∀ y ∈ xs, update s x n y = update t x n y := by
  intro xs s t x n h
  exact agrees_update xs s t x n h

theorem definition_check : ∀ (s : State) (x n y : Nat), update s x n y = if y = x then n else s y := by
  intro s x n y; rfl

theorem boundary_check : Agrees [] (update (fun _ => 0) 0 1) (update (fun _ => 2) 0 1) := by
  intro y h; cases h

end JonnyLean.Contracts.JL264

#print axioms JonnyLean.Imperative.agrees_update
#print axioms JonnyLean.Contracts.JL264.contract
