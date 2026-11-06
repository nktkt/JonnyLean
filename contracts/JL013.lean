import JonnyLean.NumberTheory.Powers

/- Independent, named contract for JL-013. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL013


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ a m n : Nat, m ≤ n → ∃ k : Nat, a ^ n = a ^ m * k :=
  JonnyLean.power_divides_later

theorem zero_exponent : ∃ k : Nat, 0 ^ 0 = 0 ^ 0 * k := ⟨1, rfl⟩

theorem zero_base : ∃ k : Nat, 0 ^ 3 = 0 ^ 1 * k := ⟨0, rfl⟩

theorem power_example : ∃ k : Nat, 3 ^ 5 = 3 ^ 2 * k := ⟨27, rfl⟩

end JonnyLean.Contracts.JL013

#print axioms JonnyLean.power_divides_later
#print axioms JonnyLean.Contracts.JL013.contract
