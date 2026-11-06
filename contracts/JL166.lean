import JonnyLean.Counting.Insertions

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL166 (a : α) {xs ys : List α} (h : ys ∈ insertions a xs) : ys.length = xs.length + 1 := insertion_length a h

theorem contract_JL166_semantics (a b : α) (xs : List α) : insertions a (b :: xs) = (a :: b :: xs) :: (insertions a xs).map (fun ys => b :: ys) := rfl

theorem contract_JL166_boundary : insertions 1 [1] = [[1, 1], [1, 1]] := rfl

#print axioms JonnyLean.Counting.insertion_length
#print axioms contract_JL166
#print axioms contract_JL166_semantics
#print axioms contract_JL166_boundary
