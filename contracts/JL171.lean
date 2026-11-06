import JonnyLean.FiniteProbability.Measure

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL171 (μ ν : Measure α) : total (μ ++ ν) = total μ + total ν := total_append μ ν

theorem contract_JL171_semantics (a : α) (n : Nat) (μ : Measure α) : total ((a, n) :: μ) = n + total μ := rfl

theorem contract_JL171_boundary : total ([(1, 0), (1, 0)] : Measure Nat) = 0 := rfl

#print axioms JonnyLean.FiniteProbability.total_append
#print axioms contract_JL171
#print axioms contract_JL171_semantics
#print axioms contract_JL171_boundary
