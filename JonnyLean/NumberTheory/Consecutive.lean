import JonnyLean.NumberTheory.Parity

namespace JonnyLean

/-- Increasing the lower factor by one adds twice the next natural number. -/
theorem consecutive_product_step (n : Nat) :
    (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by
  rw [Nat.mul_add_one, Nat.add_one_mul, Nat.add_assoc, Nat.two_mul]

/-- The product of any two consecutive natural numbers is even, including zero. -/
theorem even_consecutive_product (n : Nat) : Even (n * (n + 1)) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    cases ih with
    | intro k hk =>
      refine ⟨k + (n + 1), ?_⟩
      change (n + 1) * (n + 1 + 1) = 2 * (k + (n + 1))
      rw [Nat.mul_add 2 k (n + 1), consecutive_product_step, hk]

end JonnyLean
