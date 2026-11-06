import JonnyLean.Collections.InjectiveImage

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-040. -/
theorem JL040 {α : Type u} {β : Type v} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (A B : JonnyLean.FiniteSet α) :
    (∀ y, y ∈ JonnyLean.FiniteSet.mapInjective f hf A →
      y ∈ JonnyLean.FiniteSet.mapInjective f hf B) ↔
    (∀ x, x ∈ A → x ∈ B) :=
  JonnyLean.FiniteSet.mapInjective_reflects_subset f hf A B

example {α : Type u} {β : Type v} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (A : JonnyLean.FiniteSet α) :
    (JonnyLean.FiniteSet.mapInjective f hf A).elems.length = A.elems.length :=
  JonnyLean.FiniteSet.card_mapInjective f hf A
end JonnyLean.Contracts

#print axioms JonnyLean.FiniteSet.mapInjective_reflects_subset
#print axioms JonnyLean.Contracts.JL040
