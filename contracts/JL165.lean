import JonnyLean.Counting.Splits

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL165 (xs u v : List α) : (u, v) ∈ splits xs ↔ u ++ v = xs := mem_splits

theorem contract_JL165_semantics (a : α) (xs : List α) : splits (a :: xs) = ([], a :: xs) :: (splits xs).map (fun p => (a :: p.1, p.2)) := rfl

theorem contract_JL165_boundary : splits ([] : List Nat) = [([], [])] := rfl

#print axioms JonnyLean.Counting.mem_splits
#print axioms contract_JL165
#print axioms contract_JL165_semantics
#print axioms contract_JL165_boundary
