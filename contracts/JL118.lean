import JonnyLean.DataStructures.SpecificationModels

namespace JonnyLean.Contracts.JL118

universe u v w
open JonnyLean.DataStructures
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (query key : Nat) (m : List (Nat × α)), lookup query (Assoc.erase key m) = if query = key then none else lookup query m := by
  intro α query key m
  simpa only [lookup_matches] using Assoc.lookup_erase query key m

theorem all_duplicates : Assoc.erase 1 [(1, 3), (2, 4), (1, 5)] = [(2, 4)] := rfl

theorem absent_key : Assoc.erase 3 [(1, 8)] = [(1, 8)] := rfl

end JonnyLean.Contracts.JL118

#print axioms JonnyLean.DataStructures.Assoc.lookup_erase
#print axioms JonnyLean.Contracts.JL118.contract
