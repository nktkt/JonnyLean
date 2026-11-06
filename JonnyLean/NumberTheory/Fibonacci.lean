import JonnyLean.Algebra.FiniteSum

namespace JonnyLean

/-- Compute consecutive Fibonacci numbers by one structural recursion. -/
def fibonacciPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let p := fibonacciPair n; (p.2, p.1 + p.2)

def fibonacci (n : Nat) : Nat := (fibonacciPair n).1

theorem fibonacci_recurrence (n : Nat) :
    fibonacci (n + 2) = fibonacci n + fibonacci (n + 1) := by rfl

theorem fibonacci_positive (n : Nat) : 0 < fibonacci (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, fibonacci_recurrence]
    omega

theorem fibonacci_step_le (n : Nat) : fibonacci n ≤ fibonacci (n + 1) := by
  cases n with
  | zero => decide
  | succ n =>
    rw [show n + 1 + 1 = n + 2 by omega, fibonacci_recurrence]
    omega

theorem fibonacci_mono (m n : Nat) (h : m ≤ n) : fibonacci m ≤ fibonacci n := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact Nat.le_refl _
  | succ n ih =>
    by_cases hmn : m ≤ n
    · exact Nat.le_trans (ih hmn) (fibonacci_step_le n)
    · have hm : m = n + 1 := by omega
      subst m
      exact Nat.le_refl _

theorem fibonacci_linear_lower_bound (n : Nat) : n ≤ fibonacci (n + 2) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [fibonacci_recurrence (n + 1)]
    change n + 1 ≤ fibonacci (n + 1) + fibonacci (n + 2)
    have hpos := fibonacci_positive n
    omega

theorem fibonacci_prefix_sum (n : Nat) :
    rangeSum (fun i => fibonacci (i + 1)) n + 1 = fibonacci (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (rangeSum (fun i => fibonacci (i + 1)) n + fibonacci (n + 1)) + 1 = _
    rw [fibonacci_recurrence (n + 1)]
    change (rangeSum (fun i => fibonacci (i + 1)) n + fibonacci (n + 1)) + 1 =
      fibonacci (n + 1) + fibonacci (n + 2)
    omega

end JonnyLean
