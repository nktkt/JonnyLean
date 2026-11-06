import JonnyLean.Counting.Permutations

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL167 (xs : List α) : (permutations xs).length = JonnyLean.factorial xs.length := length_permutations xs

theorem contract_JL167_semantics (a : α) (xs : List α) : permutations (a :: xs) = (permutations xs).flatMap (insertions a) := rfl

theorem contract_JL167_boundary : permutations [1, 1] = [[1, 1], [1, 1]] := rfl

#print axioms JonnyLean.Counting.length_permutations
#print axioms contract_JL167
#print axioms contract_JL167_semantics
#print axioms contract_JL167_boundary
