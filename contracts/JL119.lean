import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL119

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (key : Nat) (left right : List (Nat × α)), lookup key (Assoc.union left right) = (lookup key left).or (lookup key right) := by
  intro α key left right
  simpa only [lookup_matches] using Assoc.lookup_union key left right

theorem left_wins : lookup 1 (Assoc.union [(1, 3)] [(1, 4)]) = some 3 := rfl

theorem right_fallback : lookup 2 (Assoc.union [(1, 3)] [(2, 4)]) = some 4 := rfl

end JonnyLean.Contracts.JL119

#print axioms JonnyLean.DataStructures.Assoc.lookup_union
#print axioms JonnyLean.Contracts.JL119.contract
