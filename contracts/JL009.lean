import JonnyLean.NumberTheory.DivisibilitySums

/- Independent, named contract for JL-009. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL009


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ d a b x y : Nat, (∃ i : Nat, a = d * i) → (∃ j : Nat, b = d * j) → ∃ k : Nat, a * x + b * y = d * k :=
  JonnyLean.divides_linear_combination

theorem zero_coefficients : ∃ k : Nat, 6 * 0 + 9 * 0 = 3 * k := ⟨0, rfl⟩

theorem positive_combination : ∃ k : Nat, 6 * 4 + 9 * 2 = 3 * k := ⟨14, rfl⟩

theorem truncated_subtraction : ∃ k : Nat, 3 - 6 = 3 * k := ⟨0, rfl⟩

end JonnyLean.Contracts.JL009

#print axioms JonnyLean.divides_linear_combination
#print axioms JonnyLean.Contracts.JL009.contract
