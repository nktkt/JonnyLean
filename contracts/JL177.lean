import JonnyLean.FiniteProbability.Distribution

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL177 (d : Distribution α) (f : α → β) (p : β → Bool) : ((d.map f).probability p).numerator = (d.probability (fun a => p (f a))).numerator := Distribution.probability_map d f p

theorem contract_JL177_semantics (d : Distribution α) (p : α → Bool) : (d.probability p).denominator = total d.measure := rfl

theorem contract_JL177_boundary (d : Distribution α) : d.measure ≠ [] := Distribution.measure_nonempty d

#print axioms JonnyLean.FiniteProbability.Distribution.probability_map
#print axioms contract_JL177
#print axioms contract_JL177_semantics
#print axioms contract_JL177_boundary
