import JonnyLean.NumberTheory.Fibonacci

namespace JonnyLean

theorem fibonacci_add_pair (m n : Nat) :
    (fibonacci (m + n + 1) = fibonacci (m + 1) * fibonacci (n + 1) + fibonacci m * fibonacci n) ∧
    (fibonacci (m + n + 2) = fibonacci (m + 1) * fibonacci (n + 2) + fibonacci m * fibonacci (n + 1)) := by
  induction n with
  | zero =>
    constructor
    · simp [fibonacci, fibonacciPair]
    · rw [Nat.add_zero, fibonacci_recurrence]
      change fibonacci m + fibonacci (m + 1) = fibonacci (m + 1) * 1 + fibonacci m * 1
      omega
  | succ n ih =>
    constructor
    · simpa only [Nat.add_assoc] using ih.2
    · rw [show m + (n + 1) + 2 = (m + n + 1) + 2 by omega, fibonacci_recurrence]
      rw [show m + n + 1 + 1 = m + n + 2 by omega, ih.1, ih.2]
      rw [show n + 1 + 2 = (n + 1) + 2 by rfl, fibonacci_recurrence (n + 1)]
      rw [show n + 1 + 1 = n + 2 by omega, fibonacci_recurrence n]
      simp only [Nat.mul_add]
      omega

theorem fibonacci_addition (m n : Nat) :
    fibonacci (m + n + 1) = fibonacci (m + 1) * fibonacci (n + 1) + fibonacci m * fibonacci n :=
  (fibonacci_add_pair m n).1

theorem fibonacci_double_odd (n : Nat) :
    fibonacci (2 * n + 1) = fibonacci (n + 1) ^ 2 + fibonacci n ^ 2 := by
  rw [Nat.two_mul, fibonacci_addition]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

theorem fibonacci_double_even (n : Nat) :
    fibonacci (2 * n + 2) = fibonacci (n + 1) * (fibonacci n + fibonacci (n + 2)) := by
  rw [Nat.two_mul, (fibonacci_add_pair n n).2, Nat.mul_add]
  ac_rfl

theorem fibonacci_three_step (n : Nat) :
    fibonacci (n + 3) = fibonacci n + 2 * fibonacci (n + 1) := by
  rw [show n + 3 = (n + 1) + 2 by omega, fibonacci_recurrence (n + 1)]
  rw [show n + 1 + 1 = n + 2 by omega, fibonacci_recurrence n]
  omega

end JonnyLean
