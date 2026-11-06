import JonnyLean.Collections.Intersection

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-038. -/
theorem JL038 {α : Type u} [DecidableEq α] (A B C : JonnyLean.FiniteSet α) :
    ∀ x, x ∈ JonnyLean.FiniteSet.intersection A (JonnyLean.FiniteSet.union B C) ↔
      x ∈ JonnyLean.FiniteSet.union (JonnyLean.FiniteSet.intersection A B)
        (JonnyLean.FiniteSet.intersection A C) :=
  JonnyLean.FiniteSet.intersection_union_distrib A B C

example {α : Type u} [DecidableEq α] (A B : JonnyLean.FiniteSet α) (x : α) :
    x ∈ JonnyLean.FiniteSet.intersection A B ↔ x ∈ A ∧ x ∈ B :=
  JonnyLean.FiniteSet.mem_intersection A B x
end JonnyLean.Contracts

#print axioms JonnyLean.FiniteSet.intersection_union_distrib
#print axioms JonnyLean.Contracts.JL038
