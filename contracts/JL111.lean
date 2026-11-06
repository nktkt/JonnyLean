import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL111

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (xs stack : List α), Stack.popMany xs.length (Stack.pushMany xs stack) = some (xs.reverse, stack) := by
  intro α xs stack
  exact Stack.popMany_pushMany xs stack

theorem empty_batch : Stack.popMany 0 (Stack.pushMany ([] : List Nat) [9]) = some ([], [9]) := rfl

theorem lifo : Stack.popMany 2 (Stack.pushMany [1, 2] [9]) = some ([2, 1], [9]) := rfl

end JonnyLean.Contracts.JL111

#print axioms JonnyLean.DataStructures.Stack.popMany_pushMany
#print axioms JonnyLean.Contracts.JL111.contract
