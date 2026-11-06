import JonnyLean.FiniteProbability.KernelComposition

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL180 (μ : Measure α) (k : α → Measure β) (l : β → Measure γ) : bind (bind μ k) l = bind μ (fun a => bind (k a) l) := bind_assoc μ k l

theorem contract_JL180_semantics (μ : Measure α) (f : α → β) : bind μ (fun a => dirac (f a)) = push f μ := bind_point_map μ f

theorem contract_JL180_boundary (μ : Measure α) : bind μ dirac = μ := bind_right_dirac μ

#print axioms JonnyLean.FiniteProbability.bind_assoc
#print axioms contract_JL180
#print axioms contract_JL180_semantics
#print axioms contract_JL180_boundary
