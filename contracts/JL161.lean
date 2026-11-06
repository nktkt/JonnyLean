import JonnyLean.Counting.Product

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL161 (xs : List α) (ys : List β) : (product xs ys).length = xs.length * ys.length := length_product xs ys

theorem contract_JL161_semantics (x : α) (xs : List α) (ys : List β) : product (x :: xs) ys = ys.map (fun y => (x, y)) ++ product xs ys := rfl

theorem contract_JL161_boundary : (product [1, 1] [true, false]).length = 4 := rfl

#print axioms JonnyLean.Counting.length_product
#print axioms contract_JL161
#print axioms contract_JL161_semantics
#print axioms contract_JL161_boundary
