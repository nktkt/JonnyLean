import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL107

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (n : Nat) (t : Tree α), levels (Tree.prune n t) ≤ n ∧ (levels t ≤ n → Tree.prune n t = t) ∧ Tree.prune n (Tree.prune n t) = Tree.prune n t := by
  intro α n t
  refine ⟨?_, ?_, Tree.prune_idempotent n t⟩
  · simpa only [levels_matches] using Tree.prune_height n t
  · intro h
    exact Tree.prune_of_height_le n t (by simpa only [levels_matches] using h)

theorem depth_zero : Tree.prune 0 (.node .empty 1 .empty) = .empty := rfl

theorem empty_at_any_depth : ∀ n, Tree.prune n (Tree.empty : Tree Nat) = .empty := by intro n; cases n <;> rfl

end JonnyLean.Contracts.JL107

#print axioms JonnyLean.Trees.Tree.prune_height
#print axioms JonnyLean.Contracts.JL107.contract
