import JonnyLean.Imperative.State

namespace JonnyLean.Contracts.JL262
open JonnyLean.Imperative

/-- The intended proposition is explicitly fixed independently of type inference. -/
theorem contract :
    ∀ (s : Nat → Nat) (x y a b : Nat), x ≠ y → update (update s x a) y b = update (update s y b) x a := by
  exact update_comm

theorem definition_check : ∀ (s : State) (x n y : Nat), update s x n y = if y = x then n else s y := by
  intro s x n y; rfl

theorem boundary_check : update (update (fun _ => 0) 2 3) 5 8 2 = 3 := by
  rfl

end JonnyLean.Contracts.JL262

#print axioms JonnyLean.Imperative.update_comm
#print axioms JonnyLean.Contracts.JL262.contract
