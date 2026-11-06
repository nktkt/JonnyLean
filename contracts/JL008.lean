import JonnyLean.NumberTheory.Divisibility

/- Independent, named contract for JL-008. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL008


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ a b c d : Nat, (∃ i : Nat, c = a * i) → (∃ j : Nat, d = b * j) → ∃ k : Nat, c * d = (a * b) * k :=
  JonnyLean.divides_product

theorem zero_divisor : ∃ k : Nat, 0 * 6 = (0 * 3) * k := ⟨0, rfl⟩

theorem product_witness : ∃ k : Nat, 6 * 20 = (2 * 5) * k := ⟨12, rfl⟩

end JonnyLean.Contracts.JL008

#print axioms JonnyLean.divides_product
#print axioms JonnyLean.Contracts.JL008.contract
