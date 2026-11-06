import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL112

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (n : Nat) (stack : List α), ((∃ taken rest, Stack.popMany n stack = some (taken, rest)) ↔ n ≤ stack.length) ∧ (∀ taken rest, Stack.popMany n stack = some (taken, rest) → stack = taken ++ rest ∧ taken.length = n) := by
  intro α n stack
  exact ⟨Stack.popMany_success_iff n stack, fun taken rest h => Stack.popMany_certificate n stack taken rest h⟩

theorem zero_on_empty : Stack.popMany 0 ([] : List Nat) = some ([], []) := rfl

theorem underflow : Stack.popMany 2 [7] = none := rfl

end JonnyLean.Contracts.JL112

#print axioms JonnyLean.DataStructures.Stack.popMany_success_iff
#print axioms JonnyLean.Contracts.JL112.contract
