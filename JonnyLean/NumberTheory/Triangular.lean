import JonnyLean.NumberTheory.Consecutive

namespace JonnyLean

/-- The sum of the natural numbers from 1 through n; the empty sum is zero. -/
def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

/-- The division-free triangular number formula over all natural numbers. -/
theorem triangular_formula (n : Nat) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (triangular n + (n + 1)) = (n + 1) * (n + 1 + 1)
    rw [Nat.mul_add, ih, consecutive_product_step]

end JonnyLean
