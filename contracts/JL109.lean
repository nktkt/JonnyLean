import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL109

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (t : Tree α) (suffix : List α), Tree.inorderInto t suffix = traversal t ++ suffix := by
  intro α t suffix
  simpa only [traversal_matches] using Tree.inorderInto_spec t suffix

theorem empty_preserves_suffix : Tree.inorderInto (Tree.empty : Tree Nat) [8, 9] = [8, 9] := rfl

theorem nonempty_suffix : Tree.inorderInto (.node .empty 1 .empty) [2] = [1, 2] := rfl

end JonnyLean.Contracts.JL109

#print axioms JonnyLean.Trees.Tree.inorderInto_spec
#print axioms JonnyLean.Contracts.JL109.contract
