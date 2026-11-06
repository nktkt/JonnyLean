import JonnyLean.Counting.Dependent

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Counting JonnyLean.DiscreteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL162 (xs : List α) (cs : α → List β) : (fibers xs cs).length = mass (fun x => (cs x).length) xs := length_fibers xs cs

theorem contract_JL162_semantics (xs : List α) (cs : α → List β) (x : α) (y : β) : (x, y) ∈ fibers xs cs ↔ x ∈ xs ∧ y ∈ cs x := mem_fibers

theorem contract_JL162_boundary (xs : List α) : fibers xs (fun _ => ([] : List Nat)) = [] := by induction xs with | nil => rfl | cons a xs ih => exact ih

#print axioms JonnyLean.Counting.length_fibers
#print axioms contract_JL162
#print axioms contract_JL162_semantics
#print axioms contract_JL162_boundary
