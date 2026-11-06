import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL117

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (query key : Nat) (value : α) (m : List (Nat × α)), lookup query (Assoc.put key value m) = if query = key then some value else lookup query m := by
  intro α query key value m
  simpa only [lookup_matches] using Assoc.lookup_put query key value m

theorem new_key : lookup 2 (Assoc.put 2 9 []) = some 9 := rfl

theorem shadowed_key : lookup 2 (Assoc.put 2 9 [(2, 4)]) = some 9 := rfl

end JonnyLean.Contracts.JL117

#print axioms JonnyLean.DataStructures.Assoc.lookup_put
#print axioms JonnyLean.Contracts.JL117.contract
