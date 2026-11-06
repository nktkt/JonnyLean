import JonnyLean.Languages.Quotient

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.Languages
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL146 (u v : List α) (L : Language α) : leftQuotient (u ++ v) L = leftQuotient v (leftQuotient u L) := quotient_append u v L

theorem contract_JL146_semantics (u w : List α) (L : Language α) : leftQuotient u L w ↔ L (u ++ w) := Iff.rfl

theorem contract_JL146_boundary : leftQuotient [1] (fun w : List Nat => w = [1, 2]) [2] := rfl

#print axioms JonnyLean.Languages.quotient_append
#print axioms contract_JL146
#print axioms contract_JL146_semantics
#print axioms contract_JL146_boundary
