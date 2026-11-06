import JonnyLean.Collections.Difference

namespace JonnyLean.Contracts

/-- Independent, fully quantified public target for JL-039. -/
theorem JL039 {α : Type u} [DecidableEq α] (A B : JonnyLean.FiniteSet α) :
    (JonnyLean.FiniteSet.intersection A B).elems.length +
      (JonnyLean.FiniteSet.difference A B).elems.length = A.elems.length :=
  JonnyLean.FiniteSet.card_intersection_add_difference A B

example {α : Type u} [DecidableEq α] (A B : JonnyLean.FiniteSet α) (x : α) :
    x ∈ JonnyLean.FiniteSet.difference A B ↔ x ∈ A ∧ x ∉ B :=
  JonnyLean.FiniteSet.mem_difference A B x
end JonnyLean.Contracts

#print axioms JonnyLean.FiniteSet.card_intersection_add_difference
#print axioms JonnyLean.Contracts.JL039
