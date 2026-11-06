import JonnyLean.NumberTheory.OddSums

/- Independent, named contract for JL-006. Natural numbers include zero. -/
namespace JonnyLean.Contracts.JL006


/-- The public declaration must satisfy this explicit mathematical proposition. -/
theorem contract :
    ∀ n : Nat, (∃ k : Nat, n = 2 * k) ∨ (∃ k : Nat, n = 2 * k + 1) :=
  JonnyLean.even_or_odd

theorem zero_even : ∃ k : Nat, 0 = 2 * k := ⟨0, rfl⟩

theorem one_odd : ∃ k : Nat, 1 = 2 * k + 1 := ⟨0, rfl⟩

theorem mixed_sum : ∃ k : Nat, 4 + 3 = 2 * k + 1 := ⟨3, rfl⟩

end JonnyLean.Contracts.JL006

#print axioms JonnyLean.even_or_odd
#print axioms JonnyLean.Contracts.JL006.contract
