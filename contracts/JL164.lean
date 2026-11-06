import JonnyLean.Counting.Subsequences

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL164 (xs : List α) : (subsequences xs).length = 2 ^ xs.length := length_subsequences xs

theorem contract_JL164_semantics (a : α) (xs : List α) : subsequences (a :: xs) = subsequences xs ++ (subsequences xs).map (fun ys => a :: ys) := rfl

theorem contract_JL164_boundary : subsequences [1, 1] = [[], [1], [1], [1, 1]] := rfl

#print axioms JonnyLean.Counting.length_subsequences
#print axioms contract_JL164
#print axioms contract_JL164_semantics
#print axioms contract_JL164_boundary
