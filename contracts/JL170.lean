import JonnyLean.Counting.FilteredProduct

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL170 (p : α → Bool) (q : β → Bool) (xs : List α) (ys : List β) : ((product xs ys).filter (fun z => p z.1 && q z.2)).length = (xs.filter p).length * (ys.filter q).length := length_filter_product p q xs ys

theorem contract_JL170_semantics (p : α → Bool) (q : β → Bool) (xs : List α) (ys : List β) : (product xs ys).filter (fun z => p z.1 && q z.2) = product (xs.filter p) (ys.filter q) := filter_product p q xs ys

theorem contract_JL170_boundary (p : α → Bool) (q : β → Bool) (ys : List β) : ((product [] ys).filter (fun z => p z.1 && q z.2)).length = 0 := rfl

#print axioms JonnyLean.Counting.length_filter_product
#print axioms contract_JL170
#print axioms contract_JL170_semantics
#print axioms contract_JL170_boundary
