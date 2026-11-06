import JonnyLean.Counting.WeightedSubsequences

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL168 (w : α → Nat) (xs : List α) : mass (wordWeight w) (subsequences xs) = wordWeight (fun a => 1 + w a) xs := weighted_subsequences w xs

theorem contract_JL168_semantics (w : α → Nat) (xs : List α) : wordWeight w xs = natProduct (xs.map w) := rfl

theorem contract_JL168_boundary (w : Nat → Nat) : mass (wordWeight w) (subsequences []) = 1 := rfl

#print axioms JonnyLean.Counting.weighted_subsequences
#print axioms contract_JL168
#print axioms contract_JL168_semantics
#print axioms contract_JL168_boundary
