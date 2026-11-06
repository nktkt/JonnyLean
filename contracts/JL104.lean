import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL104

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (t : Tree α), levels t ≤ nodes t := by
  intro α t
  simpa only [levels_matches, nodes_matches] using Tree.height_le_size t

theorem empty_height : levels (Tree.empty : Tree Nat) = 0 := rfl

theorem branching_height : levels (.node (.node .empty 1 .empty) 2 (.node .empty 3 .empty)) = 2 := rfl

end JonnyLean.Contracts.JL104

#print axioms JonnyLean.Trees.Tree.height_le_size
#print axioms JonnyLean.Contracts.JL104.contract
