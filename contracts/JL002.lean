import JonnyLean.NumberTheory.Consecutive

namespace JL002Contract

/-- Independent statement: do not use the implementation's Even predicate. -/
theorem target : ∀ n : Nat, ∃ k : Nat, n * (n + 1) = 2 * k :=
  JonnyLean.even_consecutive_product

example : ∃ k : Nat, 0 * (0 + 1) = 2 * k := target 0
example : ∃ k : Nat, 1 * (1 + 1) = 2 * k := target 1
example : ∃ k : Nat, 2 * (2 + 1) = 2 * k := target 2
example : ∃ k : Nat, 3 * (3 + 1) = 2 * k := target 3

-- Concrete witnesses cover zero and both parity cases.
example : 0 * (0 + 1) = 2 * 0 := rfl
example : 2 * (2 + 1) = 2 * 3 := rfl
example : 3 * (3 + 1) = 2 * 6 := rfl

end JL002Contract

#print axioms JonnyLean.even_consecutive_product
#print axioms JL002Contract.target
