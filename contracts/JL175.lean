import JonnyLean.FiniteProbability.Events

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL175 (μ : Measure α) (ν : Measure β) (p : α → Bool) (q : β → Bool) : event (product μ ν) (fun z => p z.1 && q z.2) = event μ p * event ν q := event_product μ ν p q

theorem contract_JL175_semantics (μ : Measure α) (p : α → Bool) : event μ p = expect μ (fun a => if p a then 1 else 0) := rfl

theorem contract_JL175_boundary (μ : Measure α) : event μ (fun _ => false) = 0 := event_false μ

#print axioms JonnyLean.FiniteProbability.event_product
#print axioms contract_JL175
#print axioms contract_JL175_semantics
#print axioms contract_JL175_boundary
