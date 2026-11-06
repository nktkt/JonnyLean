import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL102

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (t : Tree α), traversal (Tree.mirror t) = (traversal t).reverse := by
  intro α t
  simpa only [traversal_matches] using Tree.inorder_mirror t

theorem empty_mirror : Tree.mirror (Tree.empty : Tree Nat) = .empty := rfl

theorem asymmetric : traversal (Tree.mirror (.node (.node .empty 1 .empty) 2 .empty)) = [2, 1] := rfl

end JonnyLean.Contracts.JL102

#print axioms JonnyLean.Trees.Tree.inorder_mirror
#print axioms JonnyLean.Contracts.JL102.contract
