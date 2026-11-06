import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL120

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (β : Type v) (f : α → β) (key : Nat) (m : List (Nat × α)), lookup key (Assoc.mapValues f m) = (lookup key m).map f := by
  intro α β f key m
  simpa only [lookup_matches] using Assoc.lookup_mapValues f key m

theorem missing_key : lookup 3 (Assoc.mapValues Nat.succ [(1, 7)]) = none := rfl

theorem first_duplicate : lookup 1 (Assoc.mapValues Nat.succ [(1, 7), (1, 9)]) = some 8 := rfl

end JonnyLean.Contracts.JL120

#print axioms JonnyLean.DataStructures.Assoc.lookup_mapValues
#print axioms JonnyLean.Contracts.JL120.contract
