import JonnyLean.Languages.Power

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL147 (L : Language α) (m n : Nat) : power L (m + n) = concat (power L m) (power L n) := power_add L m n

theorem contract_JL147_semantics (L : Language α) (n : Nat) : power L (n + 1) = concat L (power L n) := rfl

theorem contract_JL147_boundary : power (empty : Language Nat) 0 [] := rfl

#print axioms JonnyLean.Languages.power_add
#print axioms contract_JL147
#print axioms contract_JL147_semantics
#print axioms contract_JL147_boundary
