import JonnyLean.FiniteProbability.Kernel

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL179 (μ : Measure α) (k : α → Measure β) (f : β → Nat) : expect (bind μ k) f = expect μ (fun a => expect (k a) f) := expect_bind μ k f

theorem contract_JL179_semantics (μ : Measure α) (k : α → Measure β) : bind μ k = μ.flatMap (fun p => scale p.2 (k p.1)) := rfl

theorem contract_JL179_boundary (a : α) (k : α → Measure β) : bind (dirac a) k = k a := bind_dirac a k

#print axioms JonnyLean.FiniteProbability.expect_bind
#print axioms contract_JL179
#print axioms contract_JL179_semantics
#print axioms contract_JL179_boundary
