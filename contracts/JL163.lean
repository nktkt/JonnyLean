import JonnyLean.Counting.Choices

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL163 (xss : List (List α)) : (choices xss).length = natProduct (xss.map List.length) := length_choices xss

theorem contract_JL163_semantics (xs : List α) (xss : List (List α)) : choices (xs :: xss) = xs.flatMap (fun x => (choices xss).map (fun w => x :: w)) := rfl

theorem contract_JL163_boundary : choices ([] : List (List Nat)) = [[]] := rfl

#print axioms JonnyLean.Counting.length_choices
#print axioms contract_JL163
#print axioms contract_JL163_semantics
#print axioms contract_JL163_boundary
