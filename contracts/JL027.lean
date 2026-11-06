import JonnyLean.Logic.Images

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-027. -/
theorem JL027 {α : Type u} {β : Type v} (f : α → β) (p : α → Prop) (q : β → Prop) :
    (∀ y, (∃ x, p x ∧ f x = y) → q y) ↔ (∀ x, p x → q (f x)) :=
  JonnyLean.Predicate.image_preimage_adjunction f p q

example {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (g : β → γ) (p : α → Prop) :
    ∀ z, (∃ x, p x ∧ g (f x) = z) ↔
      (∃ y, (∃ x, p x ∧ f x = y) ∧ g y = z) :=
  JonnyLean.Predicate.image_comp f g p
end JonnyLean.Contracts

#print axioms JonnyLean.Predicate.image_preimage_adjunction
#print axioms JonnyLean.Contracts.JL027
