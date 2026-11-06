import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL101

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (t : Tree α), (traversal t).length = nodes t := by
  intro α t
  simpa only [traversal_matches, nodes_matches] using Tree.inorder_length t

theorem empty_tree : (traversal (Tree.empty : Tree Nat)).length = 0 := rfl

theorem one_node : nodes (Tree.node .empty 7 .empty) = 1 := rfl

end JonnyLean.Contracts.JL101

#print axioms JonnyLean.Trees.Tree.inorder_length
#print axioms JonnyLean.Contracts.JL101.contract
