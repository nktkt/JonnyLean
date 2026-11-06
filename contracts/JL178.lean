import JonnyLean.FiniteProbability.Mixture

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL178 (m : Nat) (μ : Measure α) (n : Nat) (ν : Measure α) (f : α → Nat) : expect (mix m μ n ν) f = m * expect μ f + n * expect ν f := expect_mix m μ n ν f

theorem contract_JL178_semantics (n : Nat) (μ : Measure α) : scale n μ = μ.map (fun p => (p.1, n * p.2)) := rfl

theorem contract_JL178_boundary : scale 0 ([(1, 2)] : Measure Nat) = [(1, 0)] := rfl

#print axioms JonnyLean.FiniteProbability.expect_mix
#print axioms contract_JL178
#print axioms contract_JL178_semantics
#print axioms contract_JL178_boundary
