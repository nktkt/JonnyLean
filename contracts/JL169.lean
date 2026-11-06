import JonnyLean.Counting.Shuffle

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL169 (xs ys : List α) : (shuffles xs ys).length = JonnyLean.Combinatorics.binomial (xs.length + ys.length) xs.length := length_shuffles xs ys

theorem contract_JL169_semantics (a b : α) (xs ys : List α) : shuffles (a :: xs) (b :: ys) = (shuffles xs (b :: ys)).map (fun w => a :: w) ++ (shuffles (a :: xs) ys).map (fun w => b :: w) := by rw [shuffles]

theorem contract_JL169_boundary (ys : List α) : shuffles [] ys = [ys] := by rw [shuffles]

#print axioms JonnyLean.Counting.length_shuffles
#print axioms contract_JL169
#print axioms contract_JL169_semantics
#print axioms contract_JL169_boundary
