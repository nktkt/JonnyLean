import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL115

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (q : Queue α), match Queue.dequeue q with | none => queueView q = [] | some (x, rest) => queueView q = x :: queueView rest ∧ (rest.front = [] → rest.back = []) := by
  intro α q
  exact Queue.dequeue_spec q

theorem empty_dequeue : Queue.dequeue (⟨[], []⟩ : Queue Nat) = none := rfl

theorem back_only : Queue.dequeue (⟨[], [2, 1]⟩ : Queue Nat) = some (1, ⟨[2], []⟩) := rfl

end JonnyLean.Contracts.JL115

#print axioms JonnyLean.DataStructures.Queue.dequeue_spec
#print axioms JonnyLean.Contracts.JL115.contract
