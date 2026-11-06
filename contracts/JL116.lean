import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL116

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (q : Queue α) (xs : List α), queueView (Queue.enqueueMany q xs) = queueView q ++ xs := by
  intro α q xs
  exact Queue.enqueueMany_contents q xs

theorem empty_input : Queue.enqueueMany (⟨[1], [2]⟩ : Queue Nat) [] = ⟨[1], [2]⟩ := rfl

theorem batch_order : queueView (Queue.enqueueMany (⟨[], []⟩ : Queue Nat) [1, 2, 3]) = [1, 2, 3] := rfl

end JonnyLean.Contracts.JL116

#print axioms JonnyLean.DataStructures.Queue.enqueueMany_contents
#print axioms JonnyLean.Contracts.JL116.contract
