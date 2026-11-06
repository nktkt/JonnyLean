import JonnyLean.Logic.InjectiveImages

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-028. -/
theorem JL028 {α : Type u} {β : Type v} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (p q : α → Prop) :
    ∀ y, (∃ x, (p x ∧ q x) ∧ f x = y) ↔
      ((∃ x, p x ∧ f x = y) ∧ (∃ x, q x ∧ f x = y)) :=
  JonnyLean.Predicate.image_meet_of_injective f hf p q

example {α : Type u} {β : Type v} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (p : α → Prop) :
    ∀ x, (∃ a, p a ∧ f a = f x) ↔ p x :=
  JonnyLean.Predicate.preimage_image_of_injective f hf p
end JonnyLean.Contracts

#print axioms JonnyLean.Predicate.image_meet_of_injective
#print axioms JonnyLean.Contracts.JL028
