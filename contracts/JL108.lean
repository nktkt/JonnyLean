import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL108

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (p : α → Prop) (t : Tree α), treePredicate p t ↔ ∀ x ∈ traversal t, p x := by
  intro α p t
  simpa only [treePredicate_matches, traversal_matches] using Tree.all_iff_inorder p t

theorem empty_vacuous : treePredicate (fun _ : Nat => False) .empty := True.intro

theorem bad_node : ¬ treePredicate (fun x : Nat => x = 0) (.node .empty 1 .empty) := by simp [treePredicate]

end JonnyLean.Contracts.JL108

#print axioms JonnyLean.Trees.Tree.all_iff_inorder
#print axioms JonnyLean.Contracts.JL108.contract
