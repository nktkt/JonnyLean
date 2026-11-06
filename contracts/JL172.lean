import JonnyLean.FiniteProbability.Pushforward

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL172 (f : α → β) (μ : Measure α) : total (push f μ) = total μ := total_push f μ

theorem contract_JL172_semantics (f : α → β) (μ : Measure α) : push f μ = μ.map (fun p => (f p.1, p.2)) := rfl

theorem contract_JL172_boundary : push (fun _ : Nat => true) [(1, 2), (2, 3)] = [(true, 2), (true, 3)] := rfl

#print axioms JonnyLean.FiniteProbability.total_push
#print axioms contract_JL172
#print axioms contract_JL172_semantics
#print axioms contract_JL172_boundary
