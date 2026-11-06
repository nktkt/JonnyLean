import JonnyLean.FiniteProbability.Expectation

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL173 (μ : Measure α) (f g : α → Nat) : expect μ (fun a => f a + g a) = expect μ f + expect μ g := expect_add μ f g

theorem contract_JL173_semantics (a : α) (n : Nat) (μ : Measure α) (f : α → Nat) : expect ((a, n) :: μ) f = n * f a + expect μ f := rfl

theorem contract_JL173_boundary (f : Nat → Nat) : expect [] f = 0 := rfl

#print axioms JonnyLean.FiniteProbability.expect_add
#print axioms contract_JL173
#print axioms contract_JL173_semantics
#print axioms contract_JL173_boundary
