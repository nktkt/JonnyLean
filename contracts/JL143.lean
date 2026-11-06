import JonnyLean.Languages.Concatenation

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL143 (L K M : Language α) : concat L (union K M) = union (concat L K) (concat L M) := concat_union L K M

theorem contract_JL143_semantics (L K : Language α) (w : List α) : concat L K w ↔ ∃ u v, L u ∧ K v ∧ u ++ v = w := Iff.rfl

theorem contract_JL143_boundary : ¬concat (epsilon : Language Nat) empty [] := by rintro ⟨u, v, hu, hv, he⟩; exact hv

#print axioms JonnyLean.Languages.concat_union
#print axioms contract_JL143
#print axioms contract_JL143_semantics
#print axioms contract_JL143_boundary
