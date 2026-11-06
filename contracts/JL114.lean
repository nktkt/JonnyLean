import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL114

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (q : Queue α) (x : α), queueView (Queue.enqueue q x) = queueView q ++ [x] := by
  intro α q x
  exact Queue.enqueue_contents q x

theorem first_enqueue : queueView (Queue.enqueue (⟨[], []⟩ : Queue Nat) 4) = [4] := rfl

theorem at_tail : queueView (Queue.enqueue (⟨[1], [3, 2]⟩ : Queue Nat) 4) = [1, 2, 3, 4] := rfl

end JonnyLean.Contracts.JL114

#print axioms JonnyLean.DataStructures.Queue.enqueue_contents
#print axioms JonnyLean.Contracts.JL114.contract
