import JonnyLean.Functions.Inverses

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-030. -/
theorem JL030 {α : Type u} {β : Type v} (f : α → β) (g h : β → α)
    (hg : ∀ x, g (f x) = x) (hh : ∀ y, f (h y) = y) :
    ∀ y, g y = h y :=
  JonnyLean.Functions.inverses_agree hg hh

example {α : Type u} {β : Type v} (f : α → β) (g : β → α)
    (h : ∀ x, g (f x) = x) : ∀ a b, f a = f b → a = b :=
  JonnyLean.Functions.injective_of_left_inverse h
end JonnyLean.Contracts

#print axioms JonnyLean.Functions.inverses_agree
#print axioms JonnyLean.Contracts.JL030
