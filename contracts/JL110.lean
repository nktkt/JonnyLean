import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL110

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (t : Tree α), leaves t = nodes t + 1 := by
  intro α t
  simpa only [leaves_matches, nodes_matches] using Tree.externalLeaves_eq t

theorem empty_has_one_leaf : leaves (Tree.empty : Tree Nat) = 1 := rfl

theorem single_has_two : leaves (.node .empty 0 .empty) = 2 := rfl

end JonnyLean.Contracts.JL110

#print axioms JonnyLean.Trees.Tree.externalLeaves_eq
#print axioms JonnyLean.Contracts.JL110.contract
