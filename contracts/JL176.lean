import JonnyLean.FiniteProbability.Restriction

/- Independent expected types, definition semantics, and boundary cases. -/
universe u v w
open JonnyLean.FiniteProbability
variable {α : Type u} {β : Type v} {γ : Type w}
variable {Q : Type u} {R : Type v}

theorem contract_JL176 (μ : Measure α) (p : α → Bool) (f : α → Nat) : expect (restrict μ p) f = expect μ (fun a => if p a then f a else 0) := expect_restrict μ p f

theorem contract_JL176_semantics (μ : Measure α) (p : α → Bool) : restrict μ p = μ.filter (fun z => p z.1) := rfl

theorem contract_JL176_boundary : restrict ([(1, 2), (2, 3)] : Measure Nat) (fun _ => false) = [] := rfl

#print axioms JonnyLean.FiniteProbability.expect_restrict
#print axioms contract_JL176
#print axioms contract_JL176_semantics
#print axioms contract_JL176_boundary
