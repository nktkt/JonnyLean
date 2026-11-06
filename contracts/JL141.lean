import JonnyLean.Languages.Basic

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL141 {L K : Language α} (h : ∀ w, L w → K w) (g : ∀ w, K w → L w) : L = K := included_antisymm h g

theorem contract_JL141_semantics (L K : Language α) : Included L K ↔ ∀ w, L w → K w := Iff.rfl

theorem contract_JL141_boundary : ¬(empty : Language Nat) [] := by intro h; exact h

#print axioms JonnyLean.Languages.included_antisymm
#print axioms contract_JL141
#print axioms contract_JL141_semantics
#print axioms contract_JL141_boundary
