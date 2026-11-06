import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL106

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (s t : Tree α), nodes (Tree.graft s t) = nodes t + (nodes t + 1) * nodes s := by
  intro α s t
  simpa only [nodes_matches] using Tree.graft_size s t

theorem empty_target : Tree.graft (.node .empty 1 .empty) .empty = .node .empty 1 .empty := rfl

theorem two_replacements : nodes (Tree.graft (.node .empty 1 .empty) (.node .empty 2 .empty)) = 3 := rfl

end JonnyLean.Contracts.JL106

#print axioms JonnyLean.Trees.Tree.graft_size
#print axioms JonnyLean.Contracts.JL106.contract
