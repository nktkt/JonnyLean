import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL103

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (β : Type v) (f : α → β) (t : Tree α), traversal (Tree.map f t) = (traversal t).map f := by
  intro α β f t
  simpa only [traversal_matches] using Tree.inorder_map f t

theorem empty_map : Tree.map Nat.succ (Tree.empty : Tree Nat) = .empty := rfl

theorem mapped_node : traversal (Tree.map Nat.succ (.node .empty 3 .empty)) = [4] := rfl

end JonnyLean.Contracts.JL103

#print axioms JonnyLean.Trees.Tree.inorder_map
#print axioms JonnyLean.Contracts.JL103.contract
