import JonnyLean.NumberTheory.DivisibilityOrder

/- Independent, named contract for JL-010. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL010


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ a b : Nat, (∃ i : Nat, b = a * i) → (∃ j : Nat, a = b * j) → a = b :=
  JonnyLean.divides_antisymm

theorem zero_case : (0 : Nat) = 0 := rfl

theorem positive_case : (12 : Nat) = 12 := JonnyLean.divides_antisymm 12 12 ⟨1, rfl⟩ ⟨1, rfl⟩

theorem zero_not_divisor : ¬ (∃ k : Nat, 1 = 0 * k) := by simp

end JonnyLean.Contracts.JL010

#print axioms JonnyLean.divides_antisymm
#print axioms JonnyLean.Contracts.JL010.contract
