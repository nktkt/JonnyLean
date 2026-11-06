import JonnyLean.NumberTheory.ParityProducts

/- Independent, named contract for JL-007. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL007


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ n : Nat, (∃ k : Nat, n * n = 2 * k) ↔ (∃ k : Nat, n = 2 * k) :=
  JonnyLean.even_square_iff

theorem zero_square : ∃ k : Nat, 0 * 0 = 2 * k := ⟨0, rfl⟩

theorem odd_square : ¬ (∃ k : Nat, 3 * 3 = 2 * k) := by
  intro ⟨k, hk⟩
  omega

theorem even_square : ∃ k : Nat, 4 * 4 = 2 * k := ⟨8, rfl⟩

end JonnyLean.Contracts.JL007

#print axioms JonnyLean.even_square_iff
#print axioms JonnyLean.Contracts.JL007.contract
