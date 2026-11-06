import JonnyLean.Functions.Composition

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-029. -/
theorem JL029 {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ)
    (hf : (∀ a b, f a = f b → a = b) ∧ (∀ b, ∃ a, f a = b))
    (hg : (∀ a b, g a = g b → a = b) ∧ (∀ c, ∃ b, g b = c)) :
    (∀ a b, g (f a) = g (f b) → a = b) ∧ (∀ c, ∃ a, g (f a) = c) :=
  JonnyLean.Functions.bijective_comp hf hg

example {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ)
    (h : ∀ a b, g (f a) = g (f b) → a = b) :
    ∀ a b, f a = f b → a = b := JonnyLean.Functions.injective_of_comp h
end JonnyLean.Contracts

#print axioms JonnyLean.Functions.bijective_comp
#print axioms JonnyLean.Contracts.JL029
