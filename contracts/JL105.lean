import JonnyLean.Trees.SpecificationModels

namespace JonnyLean.Contracts.JL105

universe u v w
open JonnyLean.Trees
open JonnyLean.VerifiedPrograms.Specification

/-- Fixed, explicit semantic contract. Models are independently defined and bridged. -/
theorem contract :
    ∀ (α : Type u) (β : Type v) (γ : Type w) (f : β → γ) (z : β) (step : β → α → β → β) (step' : γ → α → γ → γ), (∀ a x b, f (step a x b) = step' (f a) x (f b)) → ∀ t : Tree α, f (treeFold z step t) = treeFold (f z) step' t := by
  intro α β γ f z step step' h t
  simpa only [treeFold_matches] using Tree.fold_fusion f z step step' h t

theorem empty_fold : treeFold 4 (fun l (_ : Nat) r => l + r) .empty = 4 := rfl

theorem node_fold : treeFold 0 (fun l (x : Nat) r => l + x + r) (.node .empty 7 .empty) = 7 := rfl

end JonnyLean.Contracts.JL105

#print axioms JonnyLean.Trees.Tree.fold_fusion
#print axioms JonnyLean.Contracts.JL105.contract
