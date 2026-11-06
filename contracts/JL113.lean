import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL113

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (q : Queue α), queueView (Queue.normalize q) = queueView q ∧ ((Queue.normalize q).front = [] → (Queue.normalize q).back = []) ∧ Queue.normalize (Queue.normalize q) = Queue.normalize q := by
  intro α q
  exact ⟨Queue.normalize_contents q, Queue.normalize_normal q, Queue.normalize_idempotent q⟩

theorem empty_queue : Queue.normalize (⟨[], []⟩ : Queue Nat) = ⟨[], []⟩ := rfl

theorem rotate_back : Queue.normalize (⟨[], [3, 2, 1]⟩ : Queue Nat) = ⟨[1, 2, 3], []⟩ := rfl

end JonnyLean.Contracts.JL113

#print axioms JonnyLean.DataStructures.Queue.normalize_contents
#print axioms JonnyLean.Contracts.JL113.contract
