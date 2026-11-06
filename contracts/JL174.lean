import JonnyLean.FiniteProbability.Product

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL174 (μ : Measure α) (ν : Measure β) (f : α → Nat) (g : β → Nat) : expect (product μ ν) (fun p => f p.1 * g p.2) = expect μ f * expect ν g := expect_product μ ν f g

theorem contract_JL174_semantics (μ : Measure α) (ν : Measure β) : product μ ν = μ.flatMap (fun p => ν.map (fun q => ((p.1, q.1), p.2 * q.2))) := rfl

theorem contract_JL174_boundary (ν : Measure β) : total (product ([] : Measure Nat) ν) = 0 := rfl

#print axioms JonnyLean.FiniteProbability.expect_product
#print axioms contract_JL174
#print axioms contract_JL174_semantics
#print axioms contract_JL174_boundary
