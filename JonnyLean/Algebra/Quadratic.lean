import Std

namespace JonnyLean

theorem square_add (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.add_mul, Nat.mul_add,
    Nat.two_mul]
  ac_rfl

theorem square_succ (n : Nat) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  rw [square_add]
  simp

theorem square_add_symmetric (a b : Nat) :
    (a + b) ^ 2 + a ^ 2 + b ^ 2 = 2 * (a ^ 2 + a * b + b ^ 2) := by
  rw [square_add]
  simp only [Nat.two_mul, Nat.add_mul]
  omega

theorem square_product (a b : Nat) : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  ac_rfl

theorem square_gap (a b : Nat) : (a + b) ^ 2 - a ^ 2 = 2 * a * b + b ^ 2 := by
  rw [square_add]
  omega

theorem square_monotone (a b : Nat) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  exact Nat.mul_le_mul h h

end JonnyLean
